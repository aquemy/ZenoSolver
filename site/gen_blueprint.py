#!/usr/bin/env python3
"""Generate the blueprint pages of the website.

    python3 site/gen_blueprint.py            # ask Lean (lean/ must be built: `lake build`)
    python3 site/gen_blueprint.py --no-lean  # reuse site/lean-status.json

The node registry `site/blueprint.toml` is the only hand-authored map. Everything else is derived:

* the statement, the proof and the remarks of a node are cut out of `doc/theory/exact-front.md`
  by its label, and its status (P / S / O / refuted) is read from the table of §0 of the note;
* the Lean facts (module, source range, kind, axioms) are asked of Lean itself
  (`findDeclarationRanges?`, `collectAxioms`) and kept in `site/lean-status.json`;
* the listings are the source text of those ranges (theorems up to their `:=`);
* the badges follow from the axioms: a node is machine-checked only if every declaration in its
  `lean` list uses no axiom beyond propext, Classical.choice and Quot.sound.

Outputs: `site/proofs/_<section>.qmd` (one partial per section), `site/proofs/_sections.qmd`
(includes them in order), `site/proofs/_summary.md` (the status table) and
`site/_blueprint-stats.md` (the counts quoted on the home page). The script fails if a label is not
found in the note or a declaration is missing in Lean, so the pages cannot silently drift.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

SITE = Path(__file__).resolve().parent
ROOT = SITE.parent
NOTE = ROOT / "doc" / "theory" / "exact-front.md"
LEAN = ROOT / "lean"
STATUS_JSON = SITE / "lean-status.json"
REPO = "https://github.com/aquemy/ZenoSolver"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FULL_LISTING_LINES = 60  # definitions up to this length are listed whole


# ---------------------------------------------------------------------------------------------
# The theory note
# ---------------------------------------------------------------------------------------------

HEADING = re.compile(r"^(#{1,6})\s+(?:(\d+(?:\.\d+)*)\.?\s+)?(.*)$")
OPENER = re.compile(r"^\*\*([^*]+?)\*\*")
PROOF_START = re.compile(r"^\*(Proof|Status)\b")
STATEMENT_KIND = re.compile(r"^(Lemma|Theorem|Corollary|Proposition|Conjecture|Statement|Notation)\b")
SQUARE = r"\square"


@dataclass
class Extract:
    title: str                      # the opener without its tags, or the heading
    where: str                      # "§2" or "§4.3": the section of the note it sits in
    statement: list[str]
    proof: list[str] = field(default_factory=list)
    remarks: list[str] = field(default_factory=list)


def paragraphs(lines: list[str]) -> list[str]:
    out, cur = [], []
    for line in lines:
        if line.strip():
            cur.append(line)
        elif cur:
            out.append("\n".join(cur))
            cur = []
    if cur:
        out.append("\n".join(cur))
    return out


class Note:
    def __init__(self, path: Path):
        self.lines = path.read_text(encoding="utf-8").splitlines()
        self.headings = []  # (index, level, number, title)
        for i, line in enumerate(self.lines):
            m = HEADING.match(line)
            if m:
                self.headings.append((i, len(m.group(1)), m.group(2), m.group(3).strip()))
        self.openers = [(i, m.group(1)) for i, line in enumerate(self.lines)
                        if (m := OPENER.match(line))]
        self.status = self._status_table()

    def _where(self, index: int) -> str:
        """The innermost numbered heading above a line, as '§4.3'."""
        number = None
        for i, _, num, _ in self.headings:
            if i > index:
                break
            if num:
                number = num
        return f"§{number}" if number else "§0"

    def _status_table(self) -> dict[str, dict[str, str]]:
        """Rows of the 'By statement' table of §0: number -> statement, hypotheses, status, uses."""
        start = next(i for i, line in enumerate(self.lines) if line.startswith("**By statement.**"))
        rows: dict[str, dict[str, str]] = {}
        for line in self.lines[start + 1:]:
            if line.startswith("## "):
                break
            if not line.startswith("|") or line.startswith("|---") or line.startswith("| # "):
                continue
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            if len(cells) != 5:
                continue
            number, statement, hyp, status, uses = cells
            for key in [k.strip() for k in number.split(",")]:
                rows[key] = {"statement": statement, "hypotheses": hyp, "status": status, "uses": uses}
        return rows

    def _block_end(self, start: int, level: int | None) -> int:
        """End (exclusive) of a block opened at `start`: the next opener or heading. For a
        heading, the next heading of the same or a higher level, or the next numbered
        statement (which is a node of its own)."""
        for i in range(start + 1, len(self.lines)):
            m = HEADING.match(self.lines[i])
            if m and (level is None or len(m.group(1)) <= level):
                return i
            opener = OPENER.match(self.lines[i])
            if opener and (level is None or STATEMENT_KIND.match(opener.group(1))):
                return i
        return len(self.lines)

    def extract(self, label: str, paras: int | None = None) -> Extract:
        if label.startswith("§"):
            number = label[1:]
            for i, level, num, title in self.headings:
                if num == number:
                    end = self._block_end(i, level)
                    return Extract(title=title, where=label,
                                   statement=paragraphs(self.lines[i + 1:end]))
            raise SystemExit(f"blueprint: no heading {label} in {NOTE.name}")
        pattern = re.compile(re.escape(label) + r"(?![\d.]\d)(?:[\s.(:,]|$)")
        for i, text in self.openers:
            if pattern.match(text):
                end = self._block_end(i, None)
                return self._split(text, self._where(i), paragraphs(self.lines[i:end]), paras)
        # a statement made inside a list item: "* **Conjecture 10.2.** ..."
        item = re.compile(r"^[*-] \*\*" + re.escape(label) + r"(?![\d.]\d)")
        for i, line in enumerate(self.lines):
            if item.match(line):
                body = [line[2:]]
                for nxt in self.lines[i + 1:]:
                    if not nxt.strip() or re.match(r"^[*-] ", nxt):
                        break
                    body.append(nxt.strip())
                title = re.sub(r"\s*\[[^\]]*\]", "", OPENER.match(body[0]).group(1)).strip().rstrip(".")
                return Extract(title=title, where=self._where(i), statement=["\n".join(body)])
        raise SystemExit(f"blueprint: no statement '{label}' in {NOTE.name}")

    @staticmethod
    def _split(opener: str, where: str, paras: list[str], n_statement: int | None) -> Extract:
        title = re.sub(r"\s*\[[^\]]*\]", "", opener).strip().rstrip(".").strip()
        start = next((k for k, p in enumerate(paras) if k > 0 and p.startswith("*Proof")), None)
        if start is None:
            start = next((k for k, p in enumerate(paras) if k > 0 and PROOF_START.match(p)), None)
        end = None
        if start is not None:
            end = next((k for k in range(start, len(paras)) if SQUARE in paras[k]), None)
        if start is None or end is None:
            # No proof in the note: the statement is its first paragraph and the lists or
            # displays that continue it, unless the registry says how many paragraphs it has.
            k = 1
            if n_statement is not None:
                k = n_statement
            else:
                while k < len(paras) and re.match(r"^(\* |- |\d+\. |\$\$|\(\w\) )", paras[k]):
                    k += 1
            return Extract(title=title, where=where, statement=paras[:k], remarks=paras[k:])
        return Extract(title=title, where=where, statement=paras[:start],
                       proof=paras[start:end + 1], remarks=paras[end + 1:])


# ---------------------------------------------------------------------------------------------
# Lean
# ---------------------------------------------------------------------------------------------

LEAN_QUERY = r"""
import ZenoFront
open Lean Elab Command

def blueprintNames : List String := [NAMES]

def kindOf (env : Environment) (n : Name) : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .inductInfo _ => if isStructure env n then "structure" else "inductive"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

def posJson (p : Position) : Json := Json.arr #[toJson p.line, toJson p.column]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut decls : Array Json := #[]
  for s in blueprintNames do
    let n := s.toName
    match env.find? n with
    | none => decls := decls.push (Json.mkObj [("name", toJson s), ("missing", toJson true)])
    | some ci =>
      let mod := (env.getModuleIdxFor? n).bind (fun i => env.header.moduleNames[i.toNat]?)
      let axs ← liftCoreM <| collectAxioms n
      let r ← liftCoreM <| findDeclarationRanges? n
      let range := match r with
        | some r => Json.mkObj [("start", posJson r.range.pos), ("end", posJson r.range.endPos),
                                ("name", posJson r.selectionRange.pos)]
        | none => Json.null
      decls := decls.push (Json.mkObj [
        ("name", toJson s), ("module", toJson (mod.map (·.toString))),
        ("kind", toJson (kindOf env n ci)), ("range", range),
        ("axioms", toJson (axs.toList.map (·.toString)))])
  -- the audit of scripts/CheckAxioms.lean, over every declaration of the library
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  let mut bad : Array Json := #[]
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless (`ZenoFront).isPrefixOf mod do continue
    checked := checked + 1
    if ci matches .thmInfo _ then theorems := theorems + 1
    let axs ← liftCoreM <| collectAxioms name
    let extra := axs.filter (· ∉ allowed)
    unless extra.isEmpty do
      bad := bad.push (Json.mkObj [("name", toJson name.toString),
                                   ("axioms", toJson (extra.toList.map (·.toString)))])
  let modules := env.header.moduleNames.filter (fun m => (`ZenoFront).isPrefixOf m)
  IO.println ("BLUEPRINT-JSON " ++ (Json.mkObj [
    ("decls", Json.arr decls),
    ("library", Json.mkObj [("declarations", toJson checked), ("theorems", toJson theorems),
                            ("modules", toJson modules.size), ("nonstandard", Json.arr bad)])]).compress)
"""


def query_lean(names: list[str]) -> dict:
    literal = ", ".join(json.dumps(n) for n in names)
    with tempfile.TemporaryDirectory() as tmp:
        script = Path(tmp) / "BlueprintQuery.lean"
        script.write_text(LEAN_QUERY.replace("NAMES", literal), encoding="utf-8")
        run = subprocess.run(["lake", "env", "lean", str(script)], cwd=LEAN,
                             capture_output=True, text=True)
    line = next((l for l in run.stdout.splitlines() if l.startswith("BLUEPRINT-JSON ")), None)
    if run.returncode != 0 or line is None:
        sys.stderr.write(run.stdout + run.stderr)
        raise SystemExit("blueprint: the Lean query failed (is lean/ built? run `lake build`)")
    data = json.loads(line[len("BLUEPRINT-JSON "):])
    meta = {
        "lean": (LEAN / "lean-toolchain").read_text().strip(),
        "mathlib": re.search(r'rev = "([^"]+)"', (LEAN / "lakefile.toml").read_text()).group(1),
    }
    return {"meta": meta, "library": data["library"],
            "decls": {d["name"]: d for d in data["decls"]}}


def git_ref() -> str:
    """The commit to link the listings to. It must exist on GitHub, so prefer origin/master when
    lean/ is identical there; else HEAD when lean/ has no uncommitted change; else `master`."""
    def rev(ref: str) -> str:
        return subprocess.run(["git", "rev-parse", ref], cwd=ROOT, capture_output=True,
                              text=True, check=True).stdout.strip()

    def same_lean(ref: str) -> bool:
        return subprocess.run(["git", "diff", "--quiet", ref, "--", "lean"], cwd=ROOT).returncode == 0

    try:
        for ref in ("origin/master", "HEAD"):
            try:
                if same_lean(ref):
                    return rev(ref)
            except subprocess.CalledProcessError:
                continue
    except OSError:
        pass
    return "master"


OPEN = "([{⟨⦃⟪⁅"
CLOSE = ")]}⟩⦄⟫⁆"


def signature_end(text: str, start: int) -> int | None:
    """Offset of the first `:=`, `where` or line-leading `|` at bracket depth 0 after `start`,
    skipping comments and strings."""
    depth, i, n = 0, start, len(text)
    while i < n:
        ch = text[i]
        if text.startswith("--", i):
            i = text.find("\n", i)
            if i < 0:
                return None
            continue
        if text.startswith("/-", i):
            level, i = 1, i + 2
            while i < n and level:
                if text.startswith("/-", i):
                    level, i = level + 1, i + 2
                elif text.startswith("-/", i):
                    level, i = level - 1, i + 2
                else:
                    i += 1
            continue
        if ch == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            continue
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif depth == 0:
            if text.startswith(":=", i):
                return i
            if re.match(r"\swhere\b", text[i - 1:i + 6]) and text.startswith("where", i):
                return i
            if ch == "|" and text[text.rfind("\n", 0, i) + 1:i].strip() == "":
                return i
        i += 1
    return None


@dataclass
class Listing:
    code: str
    path: str
    first: int
    last: int
    elided: bool


def listing(decl: dict) -> Listing:
    module = decl["module"]
    rel = "lean/" + module.replace(".", "/") + ".lean"
    lines = (ROOT / rel).read_text(encoding="utf-8").splitlines()
    (l0, c0), (l1, c1), (ln, cn) = decl["range"]["start"], decl["range"]["end"], decl["range"]["name"]
    body = lines[l0 - 1:l1]
    body[-1] = body[-1][:c1] if len(body) > 1 else body[-1][c0:c1]
    if len(body) > 1:
        body[0] = body[0][c0:]
    text = "\n".join(body)
    # offset of the declaration's name, where the signature starts
    name_off = sum(len(x) + 1 for x in body[:ln - l0]) + (cn - (c0 if ln == l0 else 0))
    elided = False
    if decl["kind"] == "theorem" or len(body) > FULL_LISTING_LINES:
        cut = signature_end(text, name_off)
        if cut is not None and text[cut:].strip():
            text = text[:cut].rstrip() + (" := …" if text.startswith(":=", cut) else "\n  …")
            elided = True
    return Listing(code=text, path=rel, first=l0, last=l1, elided=elided)


def kernel_status(decls: list[dict]) -> str:
    """'ok' (no axiom beyond the standard three), 'sorry', 'axiom' or 'missing'."""
    worst = "ok"
    for d in decls:
        if d.get("missing"):
            return "missing"
        extra = set(d["axioms"]) - STANDARD_AXIOMS
        if "sorryAx" in extra:
            worst = "sorry"
        elif extra and worst == "ok":
            worst = "axiom"
    return worst


def lean_badge(decls: list[dict]) -> str:
    status = kernel_status(decls)
    if status == "sorry":
        return "[open]{.badge .open}"
    if status == "axiom":
        return "[axiomatised]{.badge .axiom}"
    if all(d["kind"] != "theorem" for d in decls):
        return "[Lean definition]{.badge .ok}"
    return "[machine-checked]{.badge .ok}"


NOTE_BADGES = {
    "P": "[proof in the note]{.badge .informal}",
    "P (computed)": "[computed]{.badge .informal}",
    "S": "[sketch]{.badge .informal}",
    "O": "[open problem]{.badge .open}",
    "refuted": "[refuted]{.badge .refuted}",
    "definition": "[definition]{.badge .informal}",
}


# ---------------------------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------------------------

def slug(label: str) -> str:
    s = label.replace("§", "s").lower()
    return "node-" + re.sub(r"[^a-z0-9]+", "-", s).strip("-")


def number_of(label: str) -> str | None:
    if label.startswith("§"):
        return label
    m = re.search(r"\b(\d+\.\d+)\b", label)
    return m.group(1) if m else None


def html_and_pdf(title: str, body: list[str], icon: str = "note") -> list[str]:
    """A collapsed callout on the web, plain paragraphs in the PDF (titled unless the text
    already opens with *Proof.*)."""
    text = "\n\n".join(body)
    pdf_title = [] if text.startswith("*Proof") else [f"*{title}.*", ""]
    return [
        "::: {.content-visible when-format=\"html\"}",
        f"::: {{.callout-{icon} collapse=\"true\" appearance=\"simple\" title=\"{title}\"}}",
        text,
        ":::",
        ":::",
        "",
        "::: {.content-visible unless-format=\"html\"}",
        *pdf_title,
        text,
        ":::",
    ]


class Blueprint:
    def __init__(self, registry: dict, note: Note, lean: dict, ref: str):
        self.sections = registry["section"]
        self.nodes = registry["node"]
        self.note = note
        self.lean = lean
        self.ref = ref
        self.by_number: dict[str, str] = {}
        for node in self.nodes:
            num = number_of(node["label"])
            if num and num not in self.by_number:
                self.by_number[num] = slug(node["label"])
        self.rows: list[dict] = []

    def decl(self, name: str) -> dict:
        d = self.lean["decls"].get(name)
        if d is None or d.get("missing"):
            raise SystemExit(f"blueprint: Lean has no declaration {name}")
        if d.get("range") is None:
            raise SystemExit(f"blueprint: no source range for {name}")
        return d

    def note_status(self, node: dict, label: str) -> tuple[str | None, dict]:
        if "note_status" in node:
            num = number_of(label)
            return node["note_status"], self.note.status.get(num or "", {})
        num = number_of(label)
        row = self.note.status.get(num or "")
        if row:
            status = row["status"]
            if status in ("—", "-") or "definition" in row["hypotheses"]:
                status = "definition"
            return status, row
        if label.startswith(("§", "Definition", "Notation")):
            return "definition", {}
        return None, {}

    def link_uses(self, uses: str) -> str:
        if uses in ("—", ""):
            return ""

        def repl(m: re.Match) -> str:
            anchor = self.by_number.get(m.group(1))
            return f"[{m.group(1)}](#{anchor})" if anchor else m.group(1)

        return re.sub(r"(?<![\d.])(\d+\.\d+)(?![\d.]*\d)", repl, uses)

    def render_decl(self, name: str, heading: str) -> list[str]:
        d = self.decl(name)
        lst = listing(d)
        url = f"{REPO}/blob/{self.ref}/{lst.path}#L{lst.first}-L{lst.last}"
        note = " (statement only; the proof is elided)" if lst.elided and d["kind"] == "theorem" else (
            " (shortened)" if lst.elided else "")
        return [
            f"{heading} `{name}` {lean_badge([d])}",
            "",
            "```lean",
            lst.code,
            "```",
            "",
            f"[`{lst.path}`, lines {lst.first}–{lst.last}]({url}){{.lean-src}}{note}",
            "",
        ]

    def render_node(self, node: dict) -> list[str]:
        label = node["label"]
        ex = node.get("statement")
        if ex is None:
            extract = self.note.extract(label, node.get("paras"))
        else:
            extract = Extract(title=node.get("title", label), where="", statement=[ex.strip()])
        title = node.get("title", extract.title)
        lean_names = node.get("lean", [])
        leaf_names = node.get("leaves", [])
        lean_decls = [self.decl(n) for n in lean_names]
        leaf_decls = [self.decl(n) for n in leaf_names]
        status, row = self.note_status(node, label)

        if lean_decls:
            lean = lean_badge(lean_decls)
            lean_key = kernel_status(lean_decls)
            if lean_key == "ok":
                lean_key = "definition" if "definition" in lean else "checked"
        else:
            lean = "[informal]{.badge .informal}" + (" (parts in Lean)" if leaf_decls else "")
            lean_key = "partial" if leaf_decls else "informal"
        self.rows.append({"label": label, "title": title, "anchor": slug(label), "lean": lean,
                          "lean_key": lean_key, "note": NOTE_BADGES.get(status, "") if status else "",
                          "note_key": status})

        out = [f"### {title} {{#{slug(label)}}}", ""]
        facts = [f"**Lean** {lean}"]
        if status:
            facts.append(f"**Note** {NOTE_BADGES[status]}")
        if row.get("hypotheses") and row["hypotheses"] not in ("—", "definition"):
            facts.append(f"**Hypotheses** {row['hypotheses']}")
        if row.get("uses") and self.link_uses(row["uses"]):
            facts.append(f"**Uses** {self.link_uses(row['uses'])}")
        out += [" · ".join(facts), ""]

        for pid in node.get("paper", []):
            text = (SITE / "paper" / f"{pid}.md").read_text(encoding="utf-8").strip()
            out += ["::: {.from-paper}", text, ":::", ""]

        out.append("::: {.our-work}")
        where = f", {extract.where}" if extract.where else ""
        source = "theory note" if ex is None else "the Lean development"
        out += [f"**Statement** ({source}{where}).", ""]
        out += ["\n\n".join(extract.statement), ""]
        if extract.proof:
            out += html_and_pdf("Proof (theory note)", extract.proof, "tip") + [""]
        if extract.remarks:
            out += html_and_pdf("Remarks in the note", extract.remarks, "note") + [""]
        if node.get("covers"):
            out += [f"**In Lean.** {node['covers']}", ""]
        for n in lean_names:
            out += self.render_decl(n, "**Lean**")
        if leaf_names:
            out += ["**Formalised parts.** These declarations cover part of the statement; the "
                    "node keeps the status of the note.", ""]
            for n in leaf_names:
                out += self.render_decl(n, "*Part*")
        out += [":::", ""]

        if node.get("strengthen"):
            out += ["::: {.strengthen}", node["strengthen"].strip(), ":::", ""]
        return out

    def write(self) -> None:
        proofs = SITE / "proofs"
        proofs.mkdir(exist_ok=True)
        for old in proofs.glob("_*.qmd"):
            old.unlink()
        includes = []
        for sec in self.sections:
            body = [f"## {sec['title']} {{#sec-{sec['id']}}}", "", sec.get("intro", "").strip(), ""]
            for node in (n for n in self.nodes if n["section"] == sec["id"]):
                body += self.render_node(node)
            (proofs / f"_{sec['id']}.qmd").write_text("\n".join(body).rstrip() + "\n", encoding="utf-8")
            includes.append(f"{{{{< include proofs/_{sec['id']}.qmd >}}}}")
        (proofs / "_sections.qmd").write_text("\n\n".join(includes) + "\n", encoding="utf-8")
        self.write_summary(proofs / "_summary.md")
        self.write_stats(SITE / "_blueprint-stats.md")

    def write_summary(self, path: Path) -> None:
        lines = ["| Node | Lean | Note |", "|---|---|---|"]
        for r in self.rows:
            lines.append(f"| [{r['title']}](#{r['anchor']}) | {r['lean']} | {r['note']} |")
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def write_stats(self, path: Path) -> None:
        count = lambda key, val: sum(1 for r in self.rows if r[key] == val)
        lib = self.lean["library"]
        meta = self.lean["meta"]
        clean = "no declaration uses another axiom" if not lib["nonstandard"] else \
            f"{len(lib['nonstandard'])} declarations use other axioms"
        text = (
            f"The blueprint has **{len(self.rows)} nodes**. "
            f"**{count('lean_key', 'checked')}** are machine-checked theorems and "
            f"**{count('lean_key', 'definition')}** are Lean definitions. "
            f"**{count('lean_key', 'partial')}** have formalised parts, and "
            f"**{count('lean_key', 'informal')}** are not in Lean. "
            f"The library has {lib['declarations']:,} declarations "
            f"({lib['theorems']:,} theorems) in {lib['modules']} modules "
            f"(Lean `{meta['lean'].split(':')[-1]}`, Mathlib `{meta['mathlib']}`). "
            f"Apart from `propext`, `Classical.choice` and `Quot.sound`, {clean}: "
            f"no `sorry` and no `native_decide`."
        )
        path.write_text(text + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--no-lean", action="store_true", help="reuse site/lean-status.json")
    args = ap.parse_args()

    registry = tomllib.loads((SITE / "blueprint.toml").read_text(encoding="utf-8"))
    note = Note(NOTE)
    names = sorted({n for node in registry["node"] for n in node.get("lean", []) + node.get("leaves", [])})
    if args.no_lean:
        lean = json.loads(STATUS_JSON.read_text(encoding="utf-8"))
        missing = [n for n in names if n not in lean["decls"]]
        if missing:
            raise SystemExit(f"blueprint: {STATUS_JSON.name} lacks {missing}; run without --no-lean")
    else:
        lean = query_lean(names)
        STATUS_JSON.write_text(json.dumps(lean, indent=1, ensure_ascii=False, sort_keys=True) + "\n",
                               encoding="utf-8")
    bp = Blueprint(registry, note, lean, git_ref())
    bp.write()
    bad = [r["label"] for r in bp.rows if r["lean_key"] in ("sorry", "axiom", "missing")]
    print(f"blueprint: {len(bp.rows)} nodes, {len(names)} Lean declarations"
          + (f"; NOT clean: {bad}" if bad else "; every listed declaration is axiom-clean"))


if __name__ == "__main__":
    main()
