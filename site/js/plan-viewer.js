/* plan-viewer.js: play a MultiZenoTravel plan. Vanilla JS, no dependency.
 *
 * Markup: a root element with data-zs-plans="URL of plans.json" (written by site/gen_problem.py)
 * and the parts to fill, each optional, inside it or anywhere on the page with
 * data-for="<the root's id>":
 *
 *   <div data-part="picker">    one button per front point; selects the plan shown
 *   <div data-part="map">       planes and passengers moving between the cities
 *   <div data-part="controls">  restart, step back, play/pause, step forward, time slider
 *   <div data-part="story">     what happens at the current time (an aria-live region)
 *   <div data-part="gantt">     one row per plane, legs coloured by the passenger carried
 *   <div data-part="account">   how the cost and the makespan of the plan are computed
 *   <div data-part="front">     the instance's front (fronts.js), the shown plan ringed
 *
 * data-featured="COST" on the root picks the plan shown first (default: the first).
 *
 * Other scripts can drive the viewer: the root fires "zs-plan-select" each time a plan is shown,
 * the first one included, with detail { viewer, index, plan }; detail.viewer.select(i) shows the
 * i-th plan of plans.json and detail.viewer.play() plays it.
 * Colours: the tokens of styles/tokens.css (--zs-pax-1..4 for passengers, --zs-ink*, --zs-rule,
 * --zs-surface, --zs-series-*). Requires fronts.js for the front part.
 */
(function () {
  "use strict";

  var SVGNS = "http://www.w3.org/2000/svg";
  var UNIT_MS = 450; // one time unit of the plan, in milliseconds of animation

  function el(name, attrs, parent) {
    var e = document.createElementNS(SVGNS, name);
    for (var k in attrs) if (attrs[k] !== undefined && attrs[k] !== null) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }
  function html(tag, cls, parent, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    if (parent) parent.appendChild(e);
    return e;
  }
  function paxColor(k) { return k >= 1 && k <= 4 ? "var(--zs-pax-" + k + ")" : "var(--zs-ink-3)"; }
  function cityName(v) { return v === "CI" ? "C_I" : v === "CG" ? "C_G" : "city " + v.slice(1); }
  function isCentral(v) { return v.charAt(0) === "c"; }
  // Append text to an HTML element, writing C_I and C_G with a subscript.
  function rich(parent, text) {
    text.split(/(C_[IG])/).forEach(function (part) {
      var m = /^C_([IG])$/.exec(part);
      if (m) { parent.appendChild(document.createTextNode("C")); html("sub", null, parent, m[1]); }
      else if (part) parent.appendChild(document.createTextNode(part));
    });
    return parent;
  }
  // A hub name with its subscript, as SVG text content.
  function hubText(t, v) {
    if (!isCentral(v)) {
      t.appendChild(document.createTextNode("C"));
      el("tspan", { "baseline-shift": "sub", "font-size": "70%" }, t).textContent = v.charAt(1);
    } else {
      t.textContent = v.slice(1);
    }
    return t;
  }

  /* ---------- plan model ---------- */

  function Model(data, plan) {
    this.inst = data.instance;
    this.plan = plan;
    var journeys = {};
    plan.planes.forEach(function (route, i) {
      route.forEach(function (leg, j) {
        leg.plane = i + 1;
        leg.index = j;
        if (leg.pax) (journeys[leg.pax] = journeys[leg.pax] || []).push(leg);
      });
    });
    for (var p in journeys) journeys[p].sort(function (a, b) { return a.dep - b.dep; });
    this.journeys = journeys;
    var times = { 0: true };
    plan.planes.forEach(function (r) { r.forEach(function (l) { times[l.dep] = true; times[l.arr] = true; }); });
    this.times = Object.keys(times).map(Number).sort(function (a, b) { return a - b; });
    this.events = this._events();
  }

  Model.prototype.cost = function (v) { return this.inst.c[Number(v.slice(1)) - 1]; };

  // Where plane k (1-based) is at time tau: {leg, frac} while flying, {at} otherwise.
  Model.prototype.planeAt = function (k, tau) {
    var at = "CI", route = this.plan.planes[k - 1];
    for (var i = 0; i < route.length; i++) {
      var l = route[i];
      if (tau < l.dep) return { at: at, waitingFor: l };
      if (tau < l.arr) return { leg: l, frac: (tau - l.dep) / (l.arr - l.dep) };
      at = l.to;
    }
    return { at: at };
  };

  // Where passenger p is at time tau: {leg} aboard, {at} otherwise.
  Model.prototype.paxAt = function (p, tau) {
    var legs = this.journeys[p] || [], at = "CI";
    for (var i = 0; i < legs.length; i++) {
      var l = legs[i];
      if (tau < l.dep) return { at: at };
      if (tau < l.arr) return { leg: l };
      at = l.to;
    }
    return { at: at };
  };

  Model.prototype._events = function () {
    var self = this, ev = [];
    function next(l) {
      var js = self.journeys[l.pax], i = js.indexOf(l);
      return js[i + 1] || null;
    }
    function prev(l) {
      var js = self.journeys[l.pax], i = js.indexOf(l);
      return js[i - 1] || null;
    }
    this.plan.planes.forEach(function (route) {
      route.forEach(function (l) {
        var dep = "plane " + l.plane + " leaves " + cityName(l.from) + " for " + cityName(l.to);
        var before = l.pax ? prev(l) : null;
        if (l.pax && before && before.plane !== l.plane) {
          dep = "plane " + l.plane + " picks up passenger " + l.pax + " in " + cityName(l.from) +
            ", who waited there since " + before.arr + ", and leaves for " + cityName(l.to);
        } else if (l.pax) {
          dep += " with passenger " + l.pax;
        } else {
          dep += ", empty";
        }
        ev.push({ t: l.dep, order: 1, text: dep });
        var arr = "plane " + l.plane + " lands in " + cityName(l.to);
        if (isCentral(l.to)) arr += " (landing cost " + self.cost(l.to) + ")";
        if (l.pax) {
          var after = next(l);
          if (l.to === "CG") arr += "; passenger " + l.pax + " has arrived";
          else if (after && after.plane !== l.plane) {
            arr += " and drops passenger " + l.pax + ", who waits for plane " + after.plane;
          }
        }
        ev.push({ t: l.arr, order: 0, text: arr });
      });
    });
    ev.sort(function (a, b) { return a.t - b.t || a.order - b.order; });
    return ev;
  };

  /* ---------- map ---------- */

  function MapView(box, inst) {
    this.box = box;
    this.inst = inst;
    this.svg = el("svg", { role: "img", "class": "zs-map" }, box);
    this.layout = null;
  }

  MapView.prototype.build = function (model) {
    var W = this.box.clientWidth || 640;
    var vertical = W < 520;
    var inst = this.inst, n = inst.n, svg = this.svg, nodes = {};
    svg.textContent = "";
    this.vertical = vertical;
    var VW, VH;
    if (!vertical) {
      VW = 640; VH = 330;
      nodes.CI = [86, 165]; nodes.CG = [554, 165];
      for (var i = 1; i <= n; i++) nodes["c" + i] = [320, n === 1 ? 165 : 62 + (i - 1) * (206 / (n - 1))];
    } else {
      VW = 360; VH = 540;
      nodes.CI = [180, 74]; nodes.CG = [180, 452];
      for (var j = 1; j <= n; j++) nodes["c" + j] = [n === 1 ? 180 : 60 + (j - 1) * (240 / (n - 1)), 263];
    }
    this.nodes = nodes;
    svg.setAttribute("viewBox", "0 0 " + VW + " " + VH);
    svg.setAttribute("aria-label", "Map of the instance: C_I, " + n + " central cities, C_G; the planes and passengers of the plan move along the flights.");

    var gE = el("g", { "class": "zs-map-edges" }, svg);
    var gL = el("g", null, svg);
    for (var c = 1; c <= n; c++) {
      var v = "c" + c, a = nodes[v];
      [["CI", inst.d[c - 1]], ["CG", inst.dbar[c - 1]]].forEach(function (pair) {
        var h = nodes[pair[0]];
        el("line", { x1: h[0], y1: h[1], x2: a[0], y2: a[1], "class": "zs-map-edge" }, gE);
        var mx = (h[0] + a[0]) / 2, my = (h[1] + a[1]) / 2;
        var dx = a[0] - h[0], dy = a[1] - h[1], len = Math.sqrt(dx * dx + dy * dy) || 1;
        var nx = -dy / len, ny = dx / len;
        if (ny > 0 || (ny === 0 && nx < 0)) { nx = -nx; ny = -ny; } // label on the upper side
        var t = el("text", { x: mx + nx * 11, y: my + ny * 11 + 4, "text-anchor": "middle", "class": "zs-map-dur" }, gL);
        t.textContent = String(pair[1]);
      });
    }
    var gN = el("g", null, svg);
    ["CI", "CG"].forEach(function (h) {
      var p = nodes[h];
      el("circle", { cx: p[0], cy: p[1], r: 24, "class": "zs-map-hub" }, gN);
      hubText(el("text", { x: p[0], y: p[1] + 5, "text-anchor": "middle", "class": "zs-map-hub-label" }, gN), h);
    });
    for (var q = 1; q <= n; q++) {
      var pos = nodes["c" + q];
      el("circle", { cx: pos[0], cy: pos[1], r: 15, "class": "zs-map-city" }, gN);
      el("text", { x: pos[0], y: pos[1] + 5, "text-anchor": "middle", "class": "zs-map-city-label" }, gN).textContent = String(q);
      var lx = vertical ? pos[0] : pos[0], ly = vertical ? pos[1] - 24 : pos[1] - 23;
      el("text", { x: lx, y: ly, "text-anchor": "middle", "class": "zs-map-cost" }, gN).textContent = "cost " + inst.c[q - 1];
    }
    // Movers: one group per plane and per passenger, moved by transform.
    this.gPax = el("g", null, svg);
    this.gPlanes = el("g", null, svg);
    this.planes = [];
    this.pax = [];
    for (var k = 1; k <= inst.p; k++) {
      var g = el("g", { "class": "zs-map-plane" }, this.gPlanes);
      var body = el("path", { d: "M10,0 L-7,-7 L-3,0 L-7,7 Z", "class": "zs-map-plane-body" }, g);
      var lab = el("text", { "class": "zs-map-plane-label", "text-anchor": "middle" }, this.gPlanes);
      lab.textContent = String(k);
      this.planes.push({ g: g, body: body, label: lab });
    }
    for (var pp = 1; pp <= inst.t; pp++) {
      var d = el("circle", { r: 5.5, "class": "zs-map-pax" }, this.gPax);
      d.style.fill = paxColor(pp);
      var pl = el("text", { "class": "zs-map-pax-label", "text-anchor": "middle" }, this.gPax);
      pl.textContent = "p" + pp;
      this.pax.push({ dot: d, label: pl });
    }
  };

  MapView.prototype.draw = function (model, tau) {
    var nodes = this.nodes, inst = this.inst, vertical = this.vertical, self = this;
    var p = inst.p;
    var planePos = [];
    // Planes idle in a city are parked beside it; planes in flight keep a lane each.
    var parked = {};
    for (var k = 1; k <= p; k++) {
      var s = model.planeAt(k, tau), x, y, ang;
      if (s.leg) {
        var a = nodes[s.leg.from], b = nodes[s.leg.to];
        var dx = b[0] - a[0], dy = b[1] - a[1], len = Math.sqrt(dx * dx + dy * dy) || 1;
        var ux = dx / len, uy = dy / len;
        // Fly from the rim of one city to the rim of the other, each plane in its own lane.
        var ra = (isCentral(s.leg.from) ? 15 : 24) + 10, rb = (isCentral(s.leg.to) ? 15 : 24) + 10;
        var span = Math.max(0, len - ra - rb), off = (k - (p + 1) / 2) * 10;
        x = a[0] + ux * (ra + span * s.frac) - uy * off;
        y = a[1] + uy * (ra + span * s.frac) + ux * off;
        ang = Math.atan2(dy, dx) * 180 / Math.PI;
      } else {
        (parked[s.at] = parked[s.at] || []).push(k);
        planePos[k] = { at: s.at };
        continue;
      }
      planePos[k] = { x: x, y: y, ang: ang };
    }
    Object.keys(parked).forEach(function (v) {
      var ks = parked[v], c = nodes[v];
      ks.forEach(function (k, i) {
        var off = (i - (ks.length - 1) / 2) * 24, x, y;
        if (v === "CI") { x = vertical ? c[0] + off : c[0] - 44; y = vertical ? c[1] - 44 : c[1] + off; }
        else if (v === "CG") { x = vertical ? c[0] + off : c[0] + 44; y = vertical ? c[1] + 44 : c[1] + off; }
        else { x = c[0] + off; y = c[1] + (vertical ? 44 : 46); }
        planePos[k] = { x: x, y: y, ang: vertical ? 90 : 0 };
      });
    });
    for (var j = 1; j <= p; j++) {
      var q = planePos[j], m = this.planes[j - 1];
      m.g.setAttribute("transform", "translate(" + q.x.toFixed(1) + "," + q.y.toFixed(1) + ") rotate(" + q.ang.toFixed(1) + ")");
      m.label.setAttribute("x", q.x.toFixed(1));
      m.label.setAttribute("y", (q.y - 11).toFixed(1));
    }
    // Passengers: aboard, behind their plane; otherwise in a row beside their city.
    var waiting = {};
    for (var pp = 1; pp <= inst.t; pp++) {
      var st = model.paxAt(pp, tau), d = this.pax[pp - 1];
      if (st.leg) {
        var pl = planePos[st.leg.plane], rad = pl.ang * Math.PI / 180;
        var px = pl.x - Math.cos(rad) * 14, py = pl.y - Math.sin(rad) * 14;
        d.dot.setAttribute("cx", px.toFixed(1));
        d.dot.setAttribute("cy", py.toFixed(1));
        d.label.setAttribute("visibility", "hidden");
      } else {
        (waiting[st.at] = waiting[st.at] || []).push(pp);
      }
    }
    Object.keys(waiting).forEach(function (v) {
      var ps = waiting[v], c = nodes[v], hub = !isCentral(v);
      ps.forEach(function (pp, i) {
        var d = self.pax[pp - 1], off = (i - (ps.length - 1) / 2) * 20, x, y;
        if (vertical) {
          if (hub) { x = c[0] + 38 + i * 20; y = c[1] + 2; }
          else { x = c[0] + off; y = c[1] + 28; }
        } else {
          x = c[0] + off; y = c[1] + (hub ? 40 : 28);
        }
        d.dot.setAttribute("cx", x.toFixed(1));
        d.dot.setAttribute("cy", y.toFixed(1));
        d.label.setAttribute("x", x.toFixed(1));
        d.label.setAttribute("y", (y + 17).toFixed(1));
        d.label.setAttribute("visibility", "visible");
      });
    });
  };

  /* ---------- Gantt ---------- */

  function GanttView(box) {
    this.box = box;
    this.legend = html("div", "zs-gantt-legend", box);
    this.svg = el("svg", { role: "img", "class": "zs-gantt" }, box);
  }

  GanttView.prototype.build = function (model, onScrub) {
    var svg = this.svg, plan = model.plan, inst = model.inst;
    svg.textContent = "";
    var W = Math.max(300, Math.floor(this.box.clientWidth || 640));
    var L = 62, R = 12, rowH = 34, gap = 30, top = 22;
    var p = plan.planes.length, M = plan.makespan;
    var H = top + p * rowH + (p - 1) * gap + 30;
    svg.setAttribute("viewBox", "0 0 " + W + " " + H);
    svg.setAttribute("height", H);
    svg.setAttribute("aria-label", "Timeline of the plan of cost " + plan.cost + " and makespan " + M +
      ": one row per plane, one bar per flight, coloured by the passenger on board.");
    var X = function (t) { return L + t / M * (W - L - R); };
    this.X = X; this.M = M; this.W = W; this.L = L; this.R = R;
    var rowTop = function (k) { return top + (k - 1) * (rowH + gap); };
    var step = M <= 16 ? 1 : M <= 40 ? 2 : M <= 100 ? 5 : 10;
    var g = el("g", null, svg);
    for (var t = 0; t <= M; t += step) {
      el("line", { x1: X(t), x2: X(t), y1: top - 6, y2: H - 24, "class": "zs-gantt-grid" }, g);
      el("text", { x: X(t), y: H - 8, "text-anchor": "middle", "class": "zs-gantt-tick" }, g).textContent = String(t);
    }
    // Legs, with a 2px surface gap between consecutive bars.
    plan.planes.forEach(function (route, i) {
      var k = i + 1, y = rowTop(k);
      el("text", { x: 0, y: y + 26, "class": "zs-gantt-row" }, g).textContent = "plane " + k;
      route.forEach(function (l) {
        var x0 = X(l.dep) + 1, x1 = X(l.arr) - 1, w = Math.max(1, x1 - x0);
        var bar = el("rect", { x: x0, y: y + 16, width: w, height: 14, rx: 3, "class": "zs-gantt-leg" + (l.pax ? "" : " empty") }, g);
        if (l.pax) bar.style.fill = paxColor(l.pax);
        el("title", null, bar).textContent = "plane " + k + ": " + cityName(l.from) + " to " + cityName(l.to) +
          ", time " + l.dep + " to " + l.arr + (l.pax ? ", passenger " + l.pax : ", empty") +
          (isCentral(l.to) ? "; lands for " + model.cost(l.to) : "");
        var name = (l.from === "CI" ? "CI" : l.from === "CG" ? "CG" : l.from) + "→" + (l.to === "CI" ? "CI" : l.to === "CG" ? "CG" : l.to);
        var labels = l.pax ? [name + " p" + l.pax, name] : [name];
        for (var s = 0; s < labels.length; s++) {
          if (labels[s].length * 6.3 + 4 <= w) {
            el("text", { x: (x0 + x1) / 2, y: y + 11, "text-anchor": "middle", "class": "zs-gantt-label" }, g).textContent = labels[s];
            break;
          }
        }
      });
    });
    // Hand-offs: the passenger waits in the city between the drop and the pick-up.
    plan.handoffs.forEach(function (h) {
      var a = rowTop(h.from), b = rowTop(h.to), down = h.to > h.from;
      var y0 = down ? a + 30 : a + 16, y2 = down ? b + 16 : b + 30;
      var ym = down ? a + rowH + gap / 2 + 2 : b + rowH + gap / 2 + 2;
      var path = el("path", {
        d: "M" + X(h.drop) + "," + y0 + "V" + ym + "H" + X(h.pick) + "V" + y2,
        "class": "zs-gantt-wait"
      }, g);
      path.style.stroke = paxColor(h.pax);
      var txt = "p" + h.pax + " waits in " + cityName(h.city);
      var mid = (X(h.drop) + X(h.pick)) / 2;
      if (txt.length * 6.3 + 10 < X(h.pick) - X(h.drop)) {
        el("text", { x: mid, y: ym - 5, "text-anchor": "middle", "class": "zs-gantt-wait-label" }, g).textContent = txt;
      }
    });
    this.cursor = el("line", { y1: top - 10, y2: H - 24, "class": "zs-gantt-cursor" }, svg);
    var self = this;
    svg.onpointerdown = function (ev) {
      var r = svg.getBoundingClientRect(), x = (ev.clientX - r.left) * W / r.width;
      if (x >= L - 4) onScrub(Math.max(0, Math.min(M, (x - L) / (W - L - R) * M)));
    };
    // Legend: passengers, and the neutral empty leg.
    this.legend.textContent = "";
    for (var q = 1; q <= inst.t; q++) {
      var it = html("span", null, this.legend);
      html("i", "sw", it).style.background = paxColor(q);
      it.appendChild(document.createTextNode("passenger " + q));
    }
    var e = html("span", null, this.legend);
    html("i", "sw empty", e);
    e.appendChild(document.createTextNode("empty flight"));
    var w = html("span", null, this.legend);
    html("i", "sw wait", w);
    w.appendChild(document.createTextNode("waits for a hand-off"));
    return self;
  };

  GanttView.prototype.draw = function (tau) {
    var x = this.X(Math.min(tau, this.M));
    this.cursor.setAttribute("x1", x);
    this.cursor.setAttribute("x2", x);
  };

  /* ---------- account: cost and makespan ---------- */

  function account(box, model, tau) {
    var plan = model.plan;
    box.textContent = "";
    var t = html("table", "zs-account", box);
    var cap = html("caption", null, t, "Landings in central cities (hubs are free)");
    cap.className = "zs-account-cap";
    var hr = html("tr", null, html("thead", null, t));
    ["time", "plane", "city", "landing cost"].forEach(function (h) { html("th", null, hr, h); });
    var body = html("tbody", null, t), sofar = 0;
    plan.landings.forEach(function (l) {
      var r = html("tr", l.time <= tau + 1e-9 ? "done" : "todo", body);
      if (l.time <= tau + 1e-9) sofar += l.cost;
      html("td", null, r, String(l.time));
      html("td", null, r, String(l.plane));
      html("td", null, r, cityName(l.city));
      html("td", null, r, String(l.cost));
    });
    var f = html("tr", null, html("tfoot", null, t));
    html("td", null, f, "");
    html("td", null, f, "");
    html("td", null, f, "cost");
    var tot = html("td", null, f);
    html("strong", null, tot, String(plan.cost));
    var sum = html("p", "zs-account-sum", box);
    sum.appendChild(document.createTextNode("Cost = " + plan.landings.map(function (l) { return l.cost; }).join(" + ") + " = "));
    html("strong", null, sum, String(plan.cost));
    sum.appendChild(document.createTextNode(tau < plan.makespan ? " (so far: " + sofar + ")." : "."));
    var ends = plan.planes.map(function (r) { return r[r.length - 1].arr; });
    var ms = html("p", "zs-account-sum", box);
    rich(ms, "Makespan = last arrival in C_G = max(" + ends.join(", ") + ") = ");
    html("strong", null, ms, String(plan.makespan));
    ms.appendChild(document.createTextNode("."));
  }

  /* ---------- the viewer ---------- */

  function Viewer(root, data) {
    var self = this;
    this.root = root;
    this.data = data;
    this.parts = {};
    root.querySelectorAll("[data-part]").forEach(function (e) { self.parts[e.getAttribute("data-part")] = e; });
    if (root.id) {
      document.querySelectorAll('[data-part][data-for="' + root.id + '"]').forEach(function (e) {
        self.parts[e.getAttribute("data-part")] = e;
      });
    }
    var featured = Number(root.getAttribute("data-featured"));
    var idx = data.plans.findIndex(function (p) { return p.cost === featured; });
    this.index = idx >= 0 ? idx : 0;
    this.tau = 0;
    this.playing = false;
    if (this.parts.map) this.map = new MapView(this.parts.map, data.instance);
    if (this.parts.gantt) this.gantt = new GanttView(this.parts.gantt);
    this._picker();
    this._controls();
    if (this.parts.front && window.ZenoFronts) {
      this.front = ZenoFronts.render(this.parts.front, {
        front: data.front, highlight: this.index, table: true,
        onSelect: function (i) { self.select(i); }
      });
    }
    this.select(this.index);
    var lastW = 0;
    if (typeof ResizeObserver !== "undefined") {
      new ResizeObserver(function () {
        var w = root.clientWidth;
        if (Math.abs(w - lastW) > 4) { lastW = w; self._build(); self.draw(); }
      }).observe(root);
    }
  }

  Viewer.prototype.select = function (i) {
    this.pause();
    this.index = i;
    this.model = new Model(this.data, this.data.plans[i]);
    this.tau = 0;
    if (this.pickButtons) {
      this.pickButtons.forEach(function (b, j) { b.setAttribute("aria-pressed", String(j === i)); });
    }
    if (this.front) this.front.update({ highlight: i });
    this._build();
    this.draw(true);
    this.root.dispatchEvent(new CustomEvent("zs-plan-select", {
      detail: { viewer: this, index: i, plan: this.data.plans[i] }
    }));
  };

  Viewer.prototype._build = function () {
    var self = this;
    if (this.map) { this.map.build(this.model); }
    if (this.gantt) this.gantt.build(this.model, function (t) { self.pause(); self.seek(t, true); });
    if (this.slider) this.slider.max = String(this.model.plan.makespan);
  };

  Viewer.prototype._picker = function () {
    var box = this.parts.picker, self = this;
    if (!box) return;
    box.setAttribute("role", "group");
    box.setAttribute("aria-label", "Plan of the front to show");
    html("span", "zs-pick-label", box, "Plan (cost, makespan):");
    this.pickButtons = this.data.plans.map(function (p, i) {
      var b = html("button", "zs-pick", box, "(" + p.cost + ", " + p.makespan + ")");
      b.type = "button";
      b.addEventListener("click", function () { self.select(i); });
      return b;
    });
  };

  Viewer.prototype._controls = function () {
    var box = this.parts.controls, self = this;
    if (!box) return;
    function button(label, title, fn) {
      var b = html("button", "zs-ctl", box, label);
      b.type = "button";
      b.title = title;
      b.setAttribute("aria-label", title);
      b.addEventListener("click", fn);
      return b;
    }
    button("⏮", "Restart", function () { self.pause(); self.seek(0, true); });
    button("◀", "Step back to the previous event", function () { self.pause(); self.stepBy(-1); });
    this.playButton = button("▶ Play", "Play", function () { self.playing ? self.pause() : self.play(); });
    this.playButton.classList.add("zs-play");
    button("▶", "Step forward to the next event", function () { self.pause(); self.stepBy(1); });
    var s = html("input", "zs-slider", box);
    s.type = "range"; s.min = "0"; s.step = "0.05"; s.value = "0";
    s.setAttribute("aria-label", "Time");
    s.addEventListener("input", function () { self.pause(); self.seek(Number(s.value), false); });
    this.slider = s;
    this.clock = html("output", "zs-clock", box);
  };

  Viewer.prototype.stepBy = function (dir) {
    var ts = this.model.times, tau = this.tau, eps = 1e-6, t = null;
    if (dir > 0) { for (var i = 0; i < ts.length; i++) if (ts[i] > tau + eps) { t = ts[i]; break; } }
    else { for (var j = ts.length - 1; j >= 0; j--) if (ts[j] < tau - eps) { t = ts[j]; break; } }
    if (t !== null) this.seek(t, true);
  };

  Viewer.prototype.seek = function (t, announce) {
    this.tau = Math.max(0, Math.min(this.model.plan.makespan, t));
    this.draw(announce);
  };

  Viewer.prototype.play = function () {
    var self = this, M = this.model.plan.makespan;
    if (this.tau >= M) this.tau = 0;
    this.playing = true;
    if (this.playButton) { this.playButton.textContent = "❚❚ Pause"; this.playButton.title = "Pause"; this.playButton.setAttribute("aria-label", "Pause"); }
    if (this.parts.story) this.parts.story.setAttribute("aria-live", "off");
    var last = null;
    function frame(now) {
      if (!self.playing) return;
      if (last !== null) self.tau = Math.min(M, self.tau + (now - last) / UNIT_MS);
      last = now;
      self.draw(false);
      if (self.tau >= M) { self.pause(); self.draw(true); return; }
      self.raf = requestAnimationFrame(frame);
    }
    this.raf = requestAnimationFrame(frame);
  };

  Viewer.prototype.pause = function () {
    this.playing = false;
    if (this.raf) cancelAnimationFrame(this.raf);
    if (this.playButton) { this.playButton.textContent = "▶ Play"; this.playButton.title = "Play"; this.playButton.setAttribute("aria-label", "Play"); }
    if (this.parts.story) this.parts.story.setAttribute("aria-live", "polite");
  };

  Viewer.prototype.draw = function (announce) {
    var m = this.model, tau = this.tau;
    if (this.map) this.map.draw(m, tau);
    if (this.gantt) this.gantt.draw(tau);
    if (this.slider) this.slider.value = String(tau);
    if (this.clock) this.clock.textContent = "t = " + (Math.round(tau * 10) / 10) + " of " + m.plan.makespan;
    if (this.parts.account && (announce || this._lastDone !== this._doneCount(tau))) {
      this._lastDone = this._doneCount(tau);
      account(this.parts.account, m, tau);
    }
    if (this.parts.story) this._story(tau);
  };

  Viewer.prototype._doneCount = function (tau) {
    return this.model.plan.landings.filter(function (l) { return l.time <= tau + 1e-9; }).length +
      (tau >= this.model.plan.makespan ? 1000 : 0);
  };

  Viewer.prototype._story = function (tau) {
    var ev = this.model.events, box = this.parts.story, last = null;
    for (var i = 0; i < ev.length; i++) if (ev[i].t <= tau + 1e-9) last = ev[i].t;
    var key = this.index + ":" + last;
    if (this._storyKey === key) return;
    this._storyKey = key;
    box.textContent = "";
    if (last === null) { rich(box, "Time 0: every plane and passenger is in C_I."); return; }
    var now = ev.filter(function (e) { return e.t === last; }).map(function (e) { return e.text; });
    var strong = html("strong", null, box, "Time " + last + ": ");
    strong.className = "zs-story-t";
    rich(box, now.join("; ") + ".");
    if (last >= this.model.plan.makespan) rich(box, " Every passenger and every plane is in C_G: the plan is complete.");
  };

  function boot() {
    document.querySelectorAll("[data-zs-plans]").forEach(function (root) {
      fetch(root.getAttribute("data-zs-plans"))
        .then(function (r) { if (!r.ok) throw new Error(r.status); return r.json(); })
        .then(function (data) { new Viewer(root, data); })
        .catch(function (e) {
          var p = html("p", "zs-plan-error", null, "The plan viewer could not load its data (" + e.message + ").");
          root.insertBefore(p, root.firstChild);
        });
    });
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", boot);
  else boot();
})();
