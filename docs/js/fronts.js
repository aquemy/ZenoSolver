/* fronts.js: draw a Pareto front (cost, makespan) as a step plot. Vanilla JS, no dependency.
 *
 * A classic script: it defines window.ZenoFronts.
 *
 *   const chart = ZenoFronts.render(element, options);
 *
 * options
 *   front      [[cost, makespan], ...]  the front (any order; drawn by increasing cost)
 *   highlight  index into the front sorted by cost, or null: that point is ringed and labelled
 *   onSelect   function (index, [cost, makespan]): a point was clicked, or chosen with the arrow
 *              keys and Enter. Without it, points are not selectable.
 *   compact    true for small multiples: fewer ticks, tighter margins, no axis titles
 *   height     plot height in px (default: 0.62 x width, clamped to [150, 440])
 *   table      add a "Table" toggle listing the points (default false)
 *   xLabel, yLabel   axis titles (default "cost", "makespan")
 *   ariaLabel  accessible name (default: a summary of the front)
 *
 *   chart.update(partialOptions)  re-render with the options merged (e.g. {highlight: 2})
 *   chart.destroy()               remove the chart and its observer
 *
 * The staircase joins consecutive points: from (c_i, m_i) right to c_{i+1}, then down to
 * m_{i+1}, so it bounds the region of attainable (cost, makespan) pairs from below. Points are
 * dots with a 2px surface ring; on a dense front (more points than the width can separate) only
 * the line is drawn, and the tooltip still snaps to the nearest point. The tooltip shows on hover
 * and on keyboard focus (arrow keys); the table lists every point.
 *
 * Colours come from the CSS custom properties of styles/tokens.css (--zs-series-1 for the front,
 * --zs-series-2 for the highlight, --zs-ink, --zs-ink-2, --zs-ink-3, --zs-rule, --zs-surface), so
 * light and dark switch without a re-render. The module injects its own small stylesheet
 * (classes zsf-*) once. Charts re-render at their container's width, so text is never scaled.
 */
(function (global) {
  "use strict";

  var SVGNS = "http://www.w3.org/2000/svg";
  var STYLE_ID = "zsf-style";
  var CSS = [
    ".zsf{position:relative;color:var(--zs-ink);font-variant-numeric:tabular-nums}",
    ".zsf svg{display:block;width:100%;overflow:visible}",
    ".zsf svg:focus{outline:none}",
    ".zsf svg:focus-visible{outline:2px solid var(--zs-series-1);outline-offset:2px;border-radius:2px}",
    ".zsf-grid{stroke:var(--zs-rule);stroke-width:1;shape-rendering:crispEdges}",
    ".zsf-axis{stroke:var(--zs-ink-3);stroke-width:1;shape-rendering:crispEdges}",
    ".zsf-tick{fill:var(--zs-ink-2);font-size:11px}",
    ".zsf-title{fill:var(--zs-ink-2);font-size:12px}",
    ".zsf-line{fill:none;stroke:var(--zs-series-1);stroke-width:2;stroke-linejoin:round;stroke-linecap:round}",
    ".zsf-dot{fill:var(--zs-series-1);stroke:var(--zs-surface);stroke-width:2}",
    ".zsf-hl{fill:none;stroke:var(--zs-series-2);stroke-width:2.5}",
    ".zsf-hl-dot{fill:var(--zs-series-2);stroke:var(--zs-surface);stroke-width:2}",
    ".zsf-hl-label{fill:var(--zs-ink);font-size:12px;font-weight:600;paint-order:stroke;stroke:var(--zs-surface);stroke-width:4px;stroke-linejoin:round}",
    ".zsf-hover{fill:none;stroke:var(--zs-ink);stroke-width:1.5}",
    ".zsf-selectable .zsf-hit{cursor:pointer}",
    ".zsf-tip{position:absolute;pointer-events:none;z-index:5;background:var(--zs-surface);color:var(--zs-ink);",
    "border:1px solid var(--zs-rule);border-radius:4px;padding:5px 8px;font-size:12px;line-height:1.35;",
    "box-shadow:0 2px 8px rgba(0,0,0,.12);white-space:nowrap;opacity:0;transition:opacity .08s}",
    ".zsf-tip.on{opacity:1}",
    ".zsf-tip b{font-weight:600}",
    ".zsf-tip .n{color:var(--zs-ink-2)}",
    ".zsf-tools{display:flex;justify-content:flex-end;margin-top:2px}",
    ".zsf-btn{font:inherit;font-size:12px;color:var(--zs-ink-2);background:none;border:1px solid var(--zs-rule);",
    "border-radius:4px;padding:1px 8px;cursor:pointer}",
    ".zsf-btn:hover{color:var(--zs-ink);border-color:var(--zs-ink-3)}",
    ".zsf-table{max-height:260px;overflow:auto;margin-top:6px;border:1px solid var(--zs-rule);border-radius:4px}",
    ".zsf-table table{display:table;width:100%;margin:0;font-size:12px;border-collapse:collapse}",
    ".zsf-table th,.zsf-table td{padding:2px 8px;text-align:right;border-bottom:1px solid var(--zs-rule)}",
    ".zsf-table th{position:sticky;top:0;background:var(--zs-surface);color:var(--zs-ink-2);font-weight:600}",
    ".zsf-table tr.hl td{font-weight:600}"
  ].join("");

  function injectStyle() {
    if (document.getElementById(STYLE_ID)) return;
    var s = document.createElement("style");
    s.id = STYLE_ID;
    s.textContent = CSS;
    document.head.appendChild(s);
  }

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

  function fmtFull(v) { return Number(v).toLocaleString("en-US"); }

  // Tick labels: in full below 10,000, compact (12K, 1.5M) on an axis that reaches it.
  function tickFormatter(max) {
    if (Math.abs(max) < 10000) return fmtFull;
    return function (v) {
      var a = Math.abs(v);
      if (a >= 1e6) return +(v / 1e6).toFixed(2) + "M";
      if (a >= 1e3) return +(v / 1e3).toFixed(1) + "K";
      return String(v);
    };
  }

  function niceStep(span, count) {
    var raw = span / Math.max(1, count);
    var mag = Math.pow(10, Math.floor(Math.log10(raw)));
    var f = raw / mag;
    var step = (f >= Math.sqrt(50) ? 10 : f >= Math.sqrt(10) ? 5 : f >= Math.sqrt(2) ? 2 : 1) * mag;
    return step < 1 ? 1 : step; // costs and makespans are integers
  }

  // A padded domain [lo, hi] and the ticks inside it.
  function axis(values, count) {
    var lo = Math.min.apply(null, values), hi = Math.max.apply(null, values);
    if (lo === hi) { lo -= 1; hi += 1; }
    var pad = (hi - lo) * 0.06;
    var step = niceStep(hi - lo, count);
    var ticks = [];
    for (var v = Math.ceil((lo - pad) / step) * step; v <= hi + pad + 1e-9; v += step) {
      ticks.push(Math.round(v * 1000) / 1000 || 0); // never -0
    }
    return { lo: lo - pad, hi: hi + pad, ticks: ticks };
  }

  function Chart(element, options) {
    injectStyle();
    this.opt = {};
    this.wrap = html("div", "zsf", null);
    element.appendChild(this.wrap);
    this.svg = el("svg", { role: "img", tabindex: "0" }, this.wrap);
    this.tip = html("div", "zsf-tip", this.wrap);
    this.tip.setAttribute("aria-hidden", "true");
    this.tools = html("div", "zsf-tools", this.wrap);
    this.tableBox = html("div", "zsf-table", this.wrap);
    this.tableBox.hidden = true;
    this.width = 0;
    this.focus = null; // keyboard position in the front
    this._bind();
    var self = this;
    if (typeof ResizeObserver !== "undefined") {
      this.ro = new ResizeObserver(function () {
        var w = Math.floor(self.wrap.clientWidth);
        if (w > 0 && Math.abs(w - self.width) > 1) self._draw();
      });
      this.ro.observe(this.wrap);
    }
    this.update(options);
  }

  Chart.prototype.update = function (options) {
    for (var k in options) this.opt[k] = options[k];
    this.front = (this.opt.front || []).map(function (p) { return [p[0], p[1]]; })
      .sort(function (a, b) { return a[0] - b[0] || a[1] - b[1]; });
    this._tools();
    this._draw();
    if (!this.tableBox.hidden) this._table();
  };

  Chart.prototype.destroy = function () {
    if (this.ro) this.ro.disconnect();
    if (this.wrap.parentNode) this.wrap.parentNode.removeChild(this.wrap);
  };

  Chart.prototype._tools = function () {
    var self = this;
    this.tools.textContent = "";
    this.tools.hidden = !this.opt.table;
    if (!this.opt.table) return;
    var b = html("button", "zsf-btn", this.tools, this.tableBox.hidden ? "Table" : "Hide table");
    b.type = "button";
    b.setAttribute("aria-expanded", String(!this.tableBox.hidden));
    b.addEventListener("click", function () {
      self.tableBox.hidden = !self.tableBox.hidden;
      b.textContent = self.tableBox.hidden ? "Table" : "Hide table";
      b.setAttribute("aria-expanded", String(!self.tableBox.hidden));
      if (!self.tableBox.hidden) self._table();
    });
  };

  Chart.prototype._table = function () {
    var box = this.tableBox, hl = this.opt.highlight;
    box.textContent = "";
    var t = html("table", null, box);
    var head = html("tr", null, html("thead", null, t));
    html("th", null, head, "cost");
    html("th", null, head, "makespan");
    var body = html("tbody", null, t);
    this.front.forEach(function (p, i) {
      var r = html("tr", i === hl ? "hl" : null, body);
      html("td", null, r, fmtFull(p[0]));
      html("td", null, r, fmtFull(p[1]));
    });
  };

  Chart.prototype._draw = function () {
    var o = this.opt, svg = this.svg;
    var W = Math.floor(this.wrap.clientWidth);
    if (W <= 0) return; // hidden; the observer draws once a width is known
    this.width = W;
    svg.textContent = "";
    var pts = this.front;
    if (!pts.length) return;
    var compact = !!o.compact;
    var H = o.height || Math.max(150, Math.min(440, Math.round(W * 0.62)));
    var xa = axis(pts.map(function (p) { return p[0]; }), compact ? 3 : Math.max(3, Math.min(7, Math.floor(W / 90))));
    var ya = axis(pts.map(function (p) { return p[1]; }), compact ? 3 : Math.max(3, Math.min(6, Math.floor(H / 60))));
    var fx = tickFormatter(xa.hi), fy = tickFormatter(ya.hi);
    var yw = Math.max.apply(null, ya.ticks.map(function (v) { return fy(v).length; })) * 6.6 + 8;
    var m = { l: Math.round(yw + (compact ? 0 : 16)), r: 10, t: 10, b: compact ? 22 : 40 };
    var pw = W - m.l - m.r, ph = H - m.t - m.b;
    function X(v) { return m.l + (v - xa.lo) / (xa.hi - xa.lo) * pw; }
    function Y(v) { return m.t + (1 - (v - ya.lo) / (ya.hi - ya.lo)) * ph; }
    this.X = X; this.Y = Y;
    svg.setAttribute("viewBox", "0 0 " + W + " " + H);
    svg.setAttribute("height", H);
    svg.setAttribute("aria-label", o.ariaLabel || this._summary());
    svg.classList.toggle("zsf-selectable", !!o.onSelect);

    var g = el("g", null, svg);
    ya.ticks.forEach(function (v) {
      if (v < ya.lo || v > ya.hi) return;
      el("line", { x1: m.l, x2: m.l + pw, y1: Y(v), y2: Y(v), "class": "zsf-grid" }, g);
      el("text", { x: m.l - 6, y: Y(v) + 4, "text-anchor": "end", "class": "zsf-tick" }, g).textContent = fy(v);
    });
    el("line", { x1: m.l, x2: m.l + pw, y1: m.t + ph, y2: m.t + ph, "class": "zsf-axis" }, g);
    xa.ticks.forEach(function (v) {
      if (v < xa.lo || v > xa.hi) return;
      el("line", { x1: X(v), x2: X(v), y1: m.t + ph, y2: m.t + ph + 4, "class": "zsf-axis" }, g);
      el("text", { x: X(v), y: m.t + ph + 16, "text-anchor": "middle", "class": "zsf-tick" }, g).textContent = fx(v);
    });
    if (!compact) {
      el("text", { x: m.l + pw / 2, y: H - 4, "text-anchor": "middle", "class": "zsf-title" }, g).textContent = o.xLabel || "cost";
      el("text", { x: 12, y: m.t + ph / 2, "text-anchor": "middle", "class": "zsf-title",
                   transform: "rotate(-90 12 " + (m.t + ph / 2) + ")" }, g).textContent = o.yLabel || "makespan";
    }

    var d = "M" + X(pts[0][0]).toFixed(1) + "," + Y(pts[0][1]).toFixed(1);
    for (var i = 1; i < pts.length; i++) d += "H" + X(pts[i][0]).toFixed(1) + "V" + Y(pts[i][1]).toFixed(1);
    el("path", { d: d, "class": "zsf-line" }, svg);
    if (pts.length <= pw / 9) {
      pts.forEach(function (p) { el("circle", { cx: X(p[0]), cy: Y(p[1]), r: 4, "class": "zsf-dot" }, svg); });
    }

    var hl = o.highlight;
    if (hl !== null && hl !== undefined && pts[hl]) {
      var p = pts[hl], cx = X(p[0]), cy = Y(p[1]);
      el("circle", { cx: cx, cy: cy, r: 4.5, "class": "zsf-hl-dot" }, svg);
      el("circle", { cx: cx, cy: cy, r: 9, "class": "zsf-hl" }, svg);
      var label = "(" + fmtFull(p[0]) + ", " + fmtFull(p[1]) + ")";
      var right = cx + 16 + label.length * 7 < m.l + pw;
      el("text", { x: right ? cx + 14 : cx - 14, y: cy - 11, "text-anchor": right ? "start" : "end",
                   "class": "zsf-hl-label" }, svg).textContent = label;
    }
    this.hover = el("circle", { r: 7, "class": "zsf-hover", visibility: "hidden" }, svg);
    el("rect", { x: m.l - 12, y: m.t - 12, width: pw + 24, height: ph + 24, fill: "transparent", "class": "zsf-hit" }, svg);
  };

  Chart.prototype._summary = function () {
    var f = this.front;
    if (!f.length) return "Empty front";
    return "Pareto front of " + f.length + " point" + (f.length > 1 ? "s" : "") + ": cost from " +
      fmtFull(f[0][0]) + " to " + fmtFull(f[f.length - 1][0]) + ", makespan from " +
      fmtFull(f[0][1]) + " down to " + fmtFull(f[f.length - 1][1]) + ". Arrow keys move through the points.";
  };

  // The nearest point to (px, py) in screen space, within `max` px: {index, p}.
  Chart.prototype._nearest = function (px, py, max) {
    var best = null, bd = max * max, X = this.X, Y = this.Y, f = this.front;
    for (var i = 0; i < f.length; i++) {
      var dx = X(f[i][0]) - px, dy = Y(f[i][1]) - py, d = dx * dx + dy * dy;
      if (d < bd) { bd = d; best = { index: i, p: f[i] }; }
    }
    return best;
  };

  Chart.prototype._show = function (hit) {
    var tip = this.tip;
    if (!hit) {
      tip.classList.remove("on");
      if (this.hover) this.hover.setAttribute("visibility", "hidden");
      return;
    }
    var p = hit.p, cx = this.X(p[0]), cy = this.Y(p[1]);
    this.hover.setAttribute("cx", cx);
    this.hover.setAttribute("cy", cy);
    this.hover.setAttribute("visibility", "visible");
    tip.textContent = "";
    html("b", null, html("div", null, tip), "makespan " + fmtFull(p[1]));
    html("div", "n", tip, "cost " + fmtFull(p[0]));
    if (this.opt.onSelect && hit.index !== this.opt.highlight) html("div", "n", tip, "click to show this plan");
    tip.classList.add("on");
    var W = this.width, tw = tip.offsetWidth, th = tip.offsetHeight, top0 = this.svg.offsetTop;
    var left = cx + 12 + tw > W ? cx - 12 - tw : cx + 12;
    var top = top0 + cy - th - 10;
    if (top < 0) top = top0 + cy + 12;
    tip.style.left = Math.max(0, left) + "px";
    tip.style.top = top + "px";
  };

  Chart.prototype._bind = function () {
    var self = this, svg = this.svg;
    function local(ev) {
      var r = svg.getBoundingClientRect();
      return [(ev.clientX - r.left) * (self.width / r.width), ev.clientY - r.top];
    }
    svg.addEventListener("pointermove", function (ev) {
      if (!self.X) return;
      var q = local(ev);
      self._show(self._nearest(q[0], q[1], 28));
    });
    svg.addEventListener("pointerleave", function () { self._show(null); });
    svg.addEventListener("click", function (ev) {
      if (!self.opt.onSelect || !self.X) return;
      var q = local(ev), hit = self._nearest(q[0], q[1], 28);
      if (hit) self.opt.onSelect(hit.index, hit.p);
    });
    svg.addEventListener("keydown", function (ev) {
      var n = self.front.length, hl = self.opt.highlight;
      if (!n || !self.X) return;
      var fwd = ev.key === "ArrowRight" || ev.key === "ArrowDown";
      if (fwd || ev.key === "ArrowLeft" || ev.key === "ArrowUp") {
        var start = self.focus !== null ? self.focus : (hl !== null && hl !== undefined ? hl : (fwd ? -1 : n));
        self.focus = Math.max(0, Math.min(n - 1, start + (fwd ? 1 : -1)));
        self._show({ index: self.focus, p: self.front[self.focus] });
        ev.preventDefault();
      } else if ((ev.key === "Enter" || ev.key === " ") && self.focus !== null && self.opt.onSelect) {
        self.opt.onSelect(self.focus, self.front[self.focus]);
        ev.preventDefault();
      } else if (ev.key === "Escape") {
        self._show(null);
      }
    });
    svg.addEventListener("blur", function () { self.focus = null; self._show(null); });
  };

  global.ZenoFronts = {
    render: function (element, options) { return new Chart(element, options || {}); }
  };
})(window);
