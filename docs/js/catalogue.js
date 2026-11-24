/* catalogue.js: the instance catalogue (instances/index.qmd). Vanilla JS; needs fronts.js.
 *
 * Reads the JSON named by data-zs-fronts on an element of the page (instances/fronts.json, written
 * by site/gen_fronts.py) and fills every element with data-group="<group id>" with one card per
 * instance of that group: name, arguments, n, t, p, front size, zeno's notes, and a small plot of
 * the front. Charts are drawn when their card nears the viewport. "Enlarge" opens a dialog with a
 * large plot and the table of points.
 */
(function () {
  "use strict";

  var WIDE = 200; // fronts with at least this many points get a double-width card

  function html(tag, cls, parent, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    if (parent) parent.appendChild(e);
    return e;
  }

  function fmt(v) { return Number(v).toLocaleString("en-US"); }

  function meta(inst) {
    var k = inst.front.length;
    return "n = " + inst.n + ", t = " + inst.t + ", p = " + inst.p + " · " + fmt(k) +
      (inst.exact === false ? " achieved point" : " point") + (k === 1 ? "" : "s");
  }

  function badge(parent, inst) {
    if (inst.exact === undefined) return;
    var b = html("span", "zs-badge " + (inst.exact ? "exact" : "bracket"), parent,
      inst.exact ? "exact" : "bracket");
    b.title = inst.exact ? "zeno certifies every gap: these points are the front"
      : "zeno does not certify every gap: the front lies between these plans and its lower bounds";
  }

  // The arguments, wrapping between options but never inside one ("-n 12" stays whole).
  function args(parent, text, prefix) {
    var code = html("code", "zs-card-args", parent);
    var toks = ((prefix ? prefix + " " : "") + text).split(/\s+/), groups = [];
    toks.forEach(function (t) {
      if (groups.length && t.charAt(0) !== "-" && groups[groups.length - 1].length === 1 &&
          groups[groups.length - 1][0].charAt(0) === "-") groups[groups.length - 1].push(t);
      else groups.push([t]);
    });
    groups.forEach(function (g, i) {
      if (i) code.appendChild(document.createTextNode(" "));
      html("span", null, code, g.join(" "));
    });
    return code;
  }

  function notes(parent, inst) {
    if (!inst.notes) return;
    var d = html("details", "zs-card-zeno", parent);
    html("summary", null, d, "zeno says");
    inst.notes.forEach(function (n) { html("p", null, d, n); });
  }

  function Catalogue(root, data) {
    this.data = data;
    var self = this, byGroup = {};
    data.instances.forEach(function (i) { (byGroup[i.group] = byGroup[i.group] || []).push(i); });
    this.io = typeof IntersectionObserver !== "undefined" ? new IntersectionObserver(function (entries) {
      entries.forEach(function (e) {
        if (e.isIntersecting) { self.io.unobserve(e.target); e.target._draw(); }
      });
    }, { rootMargin: "300px 0px" }) : null;
    document.querySelectorAll("[data-group]").forEach(function (box) {
      box.setAttribute("role", "list");
      (byGroup[box.getAttribute("data-group")] || []).forEach(function (inst) { self.card(box, inst); });
    });
    this.dialog = this._dialog();
  }

  Catalogue.prototype.card = function (box, inst) {
    var self = this;
    var c = html("article", "zs-card" + (inst.front.length >= WIDE ? " wide" : ""), box);
    c.setAttribute("role", "listitem");
    var head = html("div", "zs-card-head", c);
    html("h3", "zs-card-name", head, inst.name);
    badge(head, inst);
    args(c, inst.args);
    html("p", "zs-card-meta", c, meta(inst));
    if (inst.comment) html("p", "zs-card-note", c, inst.comment);
    var plot = html("div", "zs-card-plot", c);
    plot.style.minHeight = (inst.front.length >= WIDE ? 190 : 150) + "px";
    c._draw = function () {
      window.ZenoFronts.render(plot, {
        front: inst.front, compact: true, height: inst.front.length >= WIDE ? 190 : 150,
        ariaLabel: "Front of " + inst.name + ": " + meta(inst) + ", cost from " + fmt(inst.front[0][0]) +
          " to " + fmt(inst.front[inst.front.length - 1][0]) + ", makespan from " + fmt(inst.front[0][1]) +
          " down to " + fmt(inst.front[inst.front.length - 1][1]) + "."
      });
    };
    if (this.io) this.io.observe(c); else c._draw();
    var foot = html("div", "zs-card-foot", c);
    notes(foot, inst);
    var b = html("button", "zs-card-open", foot, "Enlarge");
    b.type = "button";
    b.setAttribute("aria-label", "Enlarge the front of " + inst.name + ", with its table of points");
    b.addEventListener("click", function () { self.open(inst, b); });
  };

  Catalogue.prototype._dialog = function () {
    var d = html("dialog", "zs-dialog", document.body);
    d.setAttribute("aria-labelledby", "zs-dialog-title");
    var head = html("div", "zs-dialog-head", d);
    this.dTitle = html("h2", null, head);
    this.dTitle.id = "zs-dialog-title";
    var close = html("button", "zs-dialog-close", head, "Close");
    close.type = "button";
    close.addEventListener("click", function () { d.close(); });
    this.dArgs = html("div", null, d);
    this.dMeta = html("p", "zs-card-meta", d);
    this.dPlot = html("div", "zs-dialog-plot", d);
    this.dNotes = html("div", "zs-dialog-notes", d);
    var self = this;
    d.addEventListener("click", function (ev) { // a click on the backdrop closes
      var r = d.getBoundingClientRect();
      if (ev.target === d && (ev.clientX < r.left || ev.clientX > r.right || ev.clientY < r.top || ev.clientY > r.bottom)) d.close();
    });
    d.addEventListener("close", function () {
      if (self.chart) { self.chart.destroy(); self.chart = null; }
      if (self.opener) self.opener.focus();
    });
    return d;
  };

  Catalogue.prototype.open = function (inst, opener) {
    var d = this.dialog;
    this.opener = opener;
    this.dTitle.textContent = inst.name;
    badge(this.dTitle, inst);
    this.dArgs.textContent = "";
    args(this.dArgs, inst.args, "zeno");
    this.dMeta.textContent = meta(inst);
    this.dNotes.textContent = "";
    if (inst.comment) html("p", "zs-card-note", this.dNotes, inst.comment);
    notes(this.dNotes, inst);
    var det = this.dNotes.querySelector("details");
    if (det) det.open = true;
    if (typeof d.showModal === "function") d.showModal(); else d.setAttribute("open", "");
    this.chart = window.ZenoFronts.render(this.dPlot, { front: inst.front, table: true });
  };

  function boot() {
    var root = document.querySelector("[data-zs-fronts]");
    if (!root || !window.ZenoFronts) return;
    fetch(root.getAttribute("data-zs-fronts"))
      .then(function (r) { if (!r.ok) throw new Error(r.status); return r.json(); })
      .then(function (data) { new Catalogue(root, data); })
      .catch(function (e) {
        html("p", "zs-cat-error", root, "The catalogue could not load its data (" + e.message + ").");
      });
  }
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", boot);
  else boot();
})();
