// Figures 3 to 5 of the algorithm page (solver/algorithm.qmd), drawn from algorithm/data.json,
// which site/gen_algorithm.py writes and checks against zeno. Plain SVG and DOM, no library.
// Colours are classes of styles/algorithm.css that read the tokens of styles/tokens.css, so the
// figures follow the light and dark themes without being redrawn.
(function () {
  "use strict";

  const SVGNS = "http://www.w3.org/2000/svg";

  function svgEl(tag, attrs, parent) {
    const e = document.createElementNS(SVGNS, tag);
    for (const [k, v] of Object.entries(attrs || {})) e.setAttribute(k, String(v));
    if (parent) parent.appendChild(e);
    return e;
  }

  function svgText(parent, x, y, str, cls, anchor) {
    const t = svgEl("text", { x: x, y: y, class: cls || "", "text-anchor": anchor || "middle" }, parent);
    t.textContent = str;
    return t;
  }

  function htmlEl(tag, cls, parent, text) {
    const e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    if (parent) parent.appendChild(e);
    return e;
  }

  const sub = (k) => String(k).replace(/\d/g, (c) => "₀₁₂₃₄₅₆₇₈₉"[c]);
  const show = (v) =>(v === null || v === undefined ? "∞" : String(v));
  const groups = (gs) => (gs ? gs.map((g) => "{" + g.join(", ") + "}").join(" | ") : "none");
  const linear = (d0, d1, r0, r1) => (v) => r0 + ((v - d0) * (r1 - r0)) / (d1 - d0);
  const niceMax = (v) => {
    const step = v > 60 ? 20 : 10;
    return Math.max(step, Math.ceil(v / step) * step);
  };

  // ---------------------------------------------------------------- tooltip (one per page)

  const tip = htmlEl("div", "alg-tooltip", document.body);
  tip.setAttribute("role", "status");
  tip.hidden = true;

  // rows: [value, label] pairs; the value leads (bold), the label follows.
  function showTip(anchor, rows) {
    tip.replaceChildren();
    rows.forEach(([value, label], i) => {
      const line = htmlEl("div", i === 0 ? "alg-tip-head" : "alg-tip-row", tip);
      if (value) htmlEl("strong", "", line, value);
      if (label) line.appendChild(document.createTextNode((value ? " " : "") + label));
    });
    tip.hidden = false;
    let x, y;
    if (anchor && anchor.clientX !== undefined) {
      x = anchor.clientX;
      y = anchor.clientY;
    } else {
      const r = anchor.getBoundingClientRect();
      x = r.left + r.width / 2;
      y = r.bottom;
    }
    const vw = document.documentElement.clientWidth;
    const w = tip.offsetWidth;
    let left = x + 14;
    if (left + w > vw - 8) left = Math.max(8, x - w - 14);
    tip.style.left = left + window.scrollX + "px";
    tip.style.top = y + 16 + window.scrollY + "px";
  }

  function hideTip() {
    tip.hidden = true;
  }

  // A hit target that shows its tooltip on hover and on keyboard focus.
  function hoverable(el, rows, onEnter, onLeave) {
    el.setAttribute("tabindex", "0");
    const enter = (ev) => {
      if (onEnter) onEnter();
      showTip(ev.type === "focus" ? el : ev, rows());
    };
    const leave = () => {
      if (onLeave) onLeave();
      hideTip();
    };
    el.addEventListener("pointerenter", enter);
    el.addEventListener("pointermove", (ev) => showTip(ev, rows()));
    el.addEventListener("pointerleave", leave);
    el.addEventListener("focus", enter);
    el.addEventListener("blur", leave);
  }

  // ---------------------------------------------------------------- shared axes

  // Frame of a level chart: y grid with cost ticks, x ticks with the level T and the makespan.
  function levelFrame(host, opts) {
    const W = Math.max(300, Math.floor(host.clientWidth));
    const narrow = W < 560;
    const H = opts.height || (narrow ? 300 : 330);
    const m = { l: 38, r: 12, t: 30, b: 62 };
    const svg = svgEl("svg", {
      viewBox: `0 0 ${W} ${H}`, width: W, height: H, role: "img", "aria-label": opts.label,
    }, host);
    const y = linear(0, opts.yMax, H - m.b, m.t);
    const grid = svgEl("g", {}, svg);
    for (let v = 0; v <= opts.yMax; v += opts.yMax > 60 ? 20 : 10) {
      svgEl("line", { x1: m.l, x2: W - m.r, y1: y(v), y2: y(v), class: v === 0 ? "alg-axis" : "alg-gridline" }, grid);
      svgText(grid, m.l - 6, y(v) + 4, String(v), "alg-tick", "end");
    }
    svgText(svg, m.l - 6, m.t - 14, "cost", "alg-tick", "start");
    svgText(svg, m.l - 6, H - m.b + 19, "T", "alg-tick-muted", "end");
    svgText(svg, m.l - 6, H - m.b + 36, "M", "alg-tick-muted", "end");
    svgText(svg, (m.l + W - m.r) / 2, H - 6, "level T, and the makespan M = 2gT below it", "alg-tick-muted");
    return { svg, W, H, m, y, narrow };
  }

  function xTicks(f, levels, xOf) {
    for (const r of levels) {
      svgText(f.svg, xOf(r.T), f.H - f.m.b + 19, String(r.T), "alg-tick");
      svgText(f.svg, xOf(r.T), f.H - f.m.b + 36, String(r.makespan), "alg-tick-muted");
    }
  }

  // ---------------------------------------------------------------- figure 3: E(T) and its breakpoints

  function drawStaircase(host, ex) {
    host.replaceChildren();
    const T0 = ex.Tlo - 2, T1 = ex.Thi + 2;
    const levels = ex.levels.filter((r) => r.T >= T0 && r.T < T1);
    const finite = levels.filter((r) => r.E !== null);
    const f = levelFrame(host, {
      yMax: niceMax(Math.max(...finite.map((r) => r.E)) * 1.08),
      label: "E(T) as a staircase over the levels T; its drops are the front points.",
    });
    const { svg, W, H, m, y } = f;
    const x = linear(T0, T1, m.l + 16, W - m.r);
    const top = m.t, bottom = H - m.b;

    // No plan below T_lo; E is constant from T_hi on (Proposition 7.10).
    svgEl("rect", { x: x(T0), y: top, width: x(ex.Tlo) - x(T0), height: bottom - top, class: "alg-band" }, svg);
    svgText(svg, (x(T0) + x(ex.Tlo)) / 2, top + 16, "E = ∞", "alg-tick-muted");
    for (const [T, name] of [[ex.Tlo, "T_lo"], [ex.Thi, "T_hi"]]) {
      svgEl("line", { x1: x(T), x2: x(T), y1: top - 4, y2: bottom, class: "alg-marker" }, svg);
      svgText(svg, x(T), top - 8, name, "alg-tick-muted");
    }

    // The staircase: E(T) holds on [T, T + 1).
    let d = "";
    finite.forEach((r, i) => {
      d += (i === 0 ? `M ${x(r.T)} ${y(r.E)}` : ` V ${y(r.E)}`) + ` H ${x(r.T + 1)}`;
    });
    svgEl("path", { d: d, class: "alg-step" }, svg);

    const cursor = svgEl("rect", { x: 0, y: top, width: 0, height: bottom - top, class: "alg-cursor" }, svg);
    for (const r of finite) {
      if (r.T > ex.Thi) continue;
      if (r.breakpoint) {
        svgEl("circle", { cx: x(r.T), cy: y(r.E), r: 5, class: "alg-dot" }, svg);
        svgText(svg, x(r.T) + 7, y(r.E) - 9, `(${r.E}, ${r.makespan})`, "alg-pointlabel", "start");
      } else {
        svgEl("circle", { cx: x(r.T), cy: y(r.E), r: 4, class: "alg-dot-hollow" }, svg);
      }
    }
    xTicks(f, levels, x);

    for (const r of levels) {
      const hit = svgEl("rect", { x: x(r.T), y: top, width: x(r.T + 1) - x(r.T), height: bottom - top + 40, class: "alg-hit" }, svg);
      hit.setAttribute("aria-label", `level ${r.T}`);
      const prev = ex.levels.find((q) => q.T === r.T - 1);
      hoverable(hit, () => {
        const rows = [[`T = ${r.T}`, `makespan 2gT = ${r.makespan}`]];
        if (r.E === null) {
          rows.push(["E(T) = ∞", "no plan: below T_lo (Proposition 7.10)"]);
          return rows;
        }
        rows.push([`E(T) = ${r.E}`, "cheapest admissible groups"]);
        rows.push([groups(r.partition), ""]);
        if (r.T > ex.Thi) rows.push(["", `above T_hi: E stays s·c_min = ${r.E}`]);
        else if (r.breakpoint) rows.push([`(${r.E}, ${r.makespan})`, "front point: E drops here"]);
        else rows.push(["no point", `E(${r.T}) = E(${prev.T}) = ${prev.E}`]);
        return rows;
      }, () => {
        cursor.setAttribute("x", x(r.T));
        cursor.setAttribute("width", x(r.T + 1) - x(r.T));
      }, () => cursor.setAttribute("width", 0));
    }
  }

  // ---------------------------------------------------------------- figure 4: the bracket per level

  function drawBracket(host, inst) {
    host.replaceChildren();
    const levels = inst.levels.filter((r) => r.T >= inst.Tlo && r.T <= inst.Thi);
    const f = levelFrame(host, {
      yMax: niceMax(Math.max(...levels.map((r) => r.U)) * 1.08),
      label: "Per level T, the relaxation L, the pairs bound U and E; shaded levels are open, L < U.",
    });
    const { svg, W, H, m, y } = f;
    const bw = (W - m.r - m.l - 4) / levels.length;
    const cx = (i) => m.l + 4 + bw * (i + 0.5);
    const top = m.t, bottom = H - m.b;
    const tw = Math.max(4, Math.min(11, bw * 0.3));

    levels.forEach((r, i) => {
      if (r.L < r.U) {
        svgEl("rect", { x: cx(i) - bw / 2, y: top, width: bw, height: bottom - top, class: "alg-band" }, svg);
        svgText(svg, cx(i), top + 14, "open", "alg-tick-muted");
      }
    });
    const cursor = svgEl("rect", { x: 0, y: top, width: 0, height: bottom - top, class: "alg-cursor" }, svg);
    levels.forEach((r, i) => {
      const c = cx(i);
      if (r.L < r.U) svgEl("line", { x1: c, x2: c, y1: y(r.L), y2: y(r.U), class: "alg-gapline" }, svg);
      svgEl("line", { x1: c - tw, x2: c - 1.5, y1: y(r.L), y2: y(r.L), class: "alg-L" }, svg);
      svgEl("line", { x1: c + 1.5, x2: c + tw, y1: y(r.U), y2: y(r.U), class: "alg-U" }, svg);
      svgEl("circle", { cx: c, cy: y(r.E), r: 4.5, class: "alg-dot" }, svg);
    });
    xTicks(f, levels, (T) => cx(levels.findIndex((r) => r.T === T)));

    levels.forEach((r, i) => {
      const hit = svgEl("rect", { x: cx(i) - bw / 2, y: top, width: bw, height: bottom - top + 40, class: "alg-hit" }, svg);
      hit.setAttribute("aria-label", `level ${r.T}`);
      hoverable(hit, () => {
        const rows = [[`T = ${r.T}`, `makespan ${r.makespan}`]];
        rows.push([`L = ${r.L}`, groups(r.relaxed) + (r.relaxedAdmissible ? "" : ", not admissible")]);
        rows.push([`U = ${r.U}`, "pairs bound"]);
        rows.push([`E = ${r.E}`, groups(r.partition)]);
        rows.push(r.L === r.U
          ? ["closed", "L = U, so E = L = U"]
          : ["open", `L < U; E = U since q_max = ${inst.qmax} ≤ 2 (Proposition 7.4)`]);
        return rows;
      }, () => {
        cursor.setAttribute("x", cx(i) - bw / 2);
        cursor.setAttribute("width", bw);
      }, () => cursor.setAttribute("width", 0));
    });
  }

  function setupBracket(host, data) {
    const fig = host.closest("[data-figure]") || host.parentElement;
    const buttons = fig.querySelectorAll("[data-instance]");
    const stats = fig.querySelector("[data-stats]");
    const note = fig.querySelector("[data-note]");
    let current = "example";
    const render = () => {
      const inst = data[current];
      drawBracket(host, inst);
      if (stats) stats.textContent = inst.stats;
      if (note) {
        const open = inst.levels.filter((r) => r.T >= inst.Tlo && r.T <= inst.Thi && r.L < r.U).length;
        const total = inst.Thi - inst.Tlo + 1;
        note.textContent = open === 0
          ? `All ${total} levels are closed by the bracket.`
          : `${total - open} of ${total} levels are closed by the bracket; ${open} stay open and are settled by U, which is exact here.`;
      }
      buttons.forEach((b) => b.setAttribute("aria-pressed", String(b.dataset.instance === current)));
    };
    buttons.forEach((b) => b.addEventListener("click", () => {
      current = b.dataset.instance;
      render();
    }));
    render();
    return render;
  }

  // ---------------------------------------------------------------- figure 5: the one-plane table G

  function drawTable(host, ex, controls) {
    host.replaceChildren();
    const G = ex.G;
    const rows = G.values.length, cols = G.values[0].length;
    const grid = htmlEl("div", "alg-grid", host);
    grid.style.gridTemplateColumns = `minmax(2.4em, auto) repeat(${cols}, minmax(0, 1fr))`;
    grid.setAttribute("role", "img");
    grid.setAttribute("aria-label", "The one-plane table G[m][τ] of the worked example; the table view below lists the same values.");
    htmlEl("div", "alg-gh alg-corner", grid, "m \\ τ");
    for (let t = 0; t < cols; t++) htmlEl("div", "alg-gh", grid, String(t));
    const cells = [];
    for (let mm = 0; mm < rows; mm++) {
      htmlEl("div", "alg-gh", grid, String(mm));
      cells.push([]);
      for (let t = 0; t < cols; t++) {
        const v = G.values[mm][t];
        const cell = htmlEl("div", "alg-cell" + (v === null ? " alg-inf" : "") + (G.stair[mm][t] ? " alg-stair" : ""), grid, show(v));
        cells[mm].push(cell);
      }
    }
    const predOf = (mm, t) => {
      const i = G.pred[mm][t];
      return i === null ? null : [mm - 1, t - ex.d[i - 1]];
    };
    const mark = (mm, t, on) => {
      cells[mm][t].classList.toggle("is-active", on);
      const p = predOf(mm, t);
      if (p) cells[p[0]][p[1]].classList.toggle("is-pred", on);
    };
    const explain = (mm, t) => {
      const v = G.values[mm][t];
      const head = [`G[${mm}][${t}] = ${show(v)}`, ""];
      if (mm === 0) return [head, ["", "no landing costs nothing"]];
      if (v === null) {
        const dmin = Math.min(...ex.d);
        return [head, ["", `${mm} landings last at least ${mm}·${dmin} = ${mm * dmin} > ${t}`]];
      }
      const i = G.pred[mm][t];
      const [pm, pt] = predOf(mm, t);
      const out = [head,
        [`= c${sub(i)} + G[${pm}][${pt}]`,`= ${ex.c[i - 1]} + ${G.values[pm][pt]}: one landing in city ${i}, then the rest within ${t} − ${ex.d[i - 1]}`],
        [groups([G.witness[mm][t]]), "a cheapest group"]];
      if (G.stair[mm][t]) out.push(["staircase point", `G[${mm}] drops at τ = ${t}`]);
      return out;
    };
    for (let mm = 0; mm < rows; mm++) {
      for (let t = 0; t < cols; t++) {
        hoverable(cells[mm][t], () => explain(mm, t), () => mark(mm, t, true), () => mark(mm, t, false));
      }
    }

    // Replay the recurrence of Lemma 7.2 cell by cell, rows m = 1, 2, ... in order.
    let timer = null;
    const button = controls && controls.querySelector("button");
    const finish = () => {
      if (timer) clearInterval(timer);
      timer = null;
      cells.flat().forEach((c) => c.classList.remove("is-hidden", "is-active", "is-pred"));
      if (button) button.textContent = "Fill the table step by step";
    };
    if (button) {
      button.onclick = () => {
        if (timer) return finish();
        const reduce = window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;
        if (reduce) return finish();
        for (let mm = 1; mm < rows; mm++) cells[mm].forEach((c) => c.classList.add("is-hidden"));
        let k = 0, last = null;
        button.textContent = "Show the whole table";
        timer = setInterval(() => {
          if (last) mark(last[0], last[1], false);
          const mm = 1 + Math.floor(k / cols), t = k % cols;
          if (mm >= rows) return finish();
          cells[mm][t].classList.remove("is-hidden");
          mark(mm, t, true);
          last = [mm, t];
          k++;
        }, 220);
      };
    }
  }

  // ---------------------------------------------------------------- wiring

  function whenSized(host, draw) {
    let width = 0, frame = 0;
    const redraw = () => {
      const w = Math.floor(host.clientWidth);
      if (w && w !== width) {
        width = w;
        draw();
      }
    };
    if (window.ResizeObserver) {
      new ResizeObserver(() => {
        cancelAnimationFrame(frame);
        frame = requestAnimationFrame(redraw);
      }).observe(host);
    }
    redraw();
  }

  function fail(hosts, err) {
    hosts.forEach((h) => {
      if (h) htmlEl("p", "alg-error", h, "The figure data (algorithm/data.json) could not be loaded; the table view below has the same numbers.");
    });
    if (window.console) console.error(err);
  }

  function start() {
    const stair = document.getElementById("alg-staircase");
    const bracket = document.getElementById("alg-bracket");
    const table = document.getElementById("alg-table");
    if (!stair && !bracket && !table) return;
    const url = new URL("../algorithm/data.json", document.baseURI);
    fetch(url)
      .then((r) => {
        if (!r.ok) throw new Error(r.status + " " + url);
        return r.json();
      })
      .then((data) => {
        if (stair) whenSized(stair, () => drawStaircase(stair, data.example));
        if (bracket) {
          let render = null;
          whenSized(bracket, () => {
            render = render ? (render(), render) : setupBracket(bracket, data);
          });
        }
        if (table) {
          const controls = document.getElementById("alg-table-controls");
          drawTable(table, data.example, controls);
        }
      })
      .catch((err) => fail([stair, bracket, table], err));
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", start);
  else start();
})();
