#!/usr/bin/env python3
"""Generate the blueprint pages of the website.

    python3 site/gen_blueprint.py            # ask Lean (lean/ must be built: `lake build`)
    python3 site/gen_blueprint.py --no-lean  # reuse site/lean-status.json

The node registry `site/blueprint.toml` is the only hand-authored map: one node per numbered
result of the theory note (revision 3), by label. Everything else is derived:

* the statement, the note's *Lean:* paragraph, the proof and the remarks of a node are cut out of
  `doc/theory/exact-front.md` by its label;
* its claim is the entry of the claim ledger `claims.toml` with the same `label` (archived entries,
  with `removed`, are skipped). Every node but Notation must have one;
* the Lean facts (module, source range, kind, axioms) are asked of Lean itself
  (`findDeclarationRanges?`, `collectAxioms`) and kept in `site/lean-status.json`;
* the listings are the source text of those ranges (theorems up to their `:=`);
* the badge follows the ledger: a node is machine-checked only if the ledger's effective status is
  math.machine-checked (Lean proves every assertion of the statement), and then its `lean`
  declarations must use no axiom beyond propext, Classical.choice and Quot.sound; otherwise it
  has parts in Lean (the ledger's `lean_partial`) or is informal. Definitions are badged "Lean
  definition".

Outputs: `site/proofs/_<section>.qmd` (one partial per section), `site/proofs/_sections.qmd`
(includes them in order), `site/proofs/_progress.md` (the one-line count at the top),
`site/proofs/_main.md` (the main results), `site/proofs/_summary.md` (the status table),
`site/_blueprint-stats.md` (the counts quoted on the About page), `site/_home-lean.md` (the Lean
tally of the home page) and `site/_nodes.json` (read by the `node` shortcode). The script fails if
a label is not found in the note, a declaration is missing in Lean, a numbered result has no node
or no claim, or a `{{< node "…" >}}` shortcode of the site names a label that is not a node, so the
pages cannot silently drift.
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
PROOF_START = re.compile(r"^\*Proof\b")
LEAN_PARA = re.compile(r"^\*Lean:\*")
STATEMENT_KIND = re.compile(r"^(Definition|Lemma|Theorem|Corollary|Proposition|Example|Notation)\b")
RESULT = re.compile(r"^((?:Definition|Lemma|Theorem|Corollary|Proposition|Example|Conjecture) \d+\.\d+)\b")
SQUARE = r"\square"


@dataclass
class Extract:
    title: str                      # the opener without its tags, or the heading
    where: str                      # "§2" or "§4.3": the section of the note it sits in
    statement: list[str]
    proof: list[str] = field(default_factory=list)
    remarks: list[str] = field(default_factory=list)
    lean: str = ""                  # the note's *Lean:* paragraph


PAPERS = re.compile(r"(?i)\b(both papers|the papers|papers'|papers’|paper's|paper’s|arXiv|EvoCOP)")
def mentions_papers(text: str) -> bool:
    return bool(PAPERS.search(text))


def without_paper_items(paragraph: str) -> str:
    """A list paragraph with the items that discuss the papers removed."""
    lines = paragraph.split("\n")
    if not re.match(r"^[*-] ", lines[0]):
        return paragraph
    items, cur = [], []
    for line in lines:
        if re.match(r"^[*-] ", line) and cur:
            items.append(cur)
            cur = []
        cur.append(line)
    items.append(cur)
    return "\n".join(l for item in items if not mentions_papers("\n".join(item)) for l in item)


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

    def results(self) -> list[str]:
        """The labels of the numbered results, in order."""
        return [m.group(1) for _, text in self.openers if (m := RESULT.match(text))]

    def _where(self, index: int) -> str:
        """The innermost numbered heading above a line, as '§4.3'."""
        number = None
        for i, _, num, _ in self.headings:
            if i > index:
                break
            if num:
                number = num
        return f"§{number}" if number else "§0"

    def _block_end(self, start: int, level: int | None) -> int:
        """End (exclusive) of a block opened at `start`: the next opener or heading. For a
        heading, the next heading of the same or a higher level, or the next statement (which is
        a node of its own)."""
        for i in range(start + 1, len(self.lines)):
            m = HEADING.match(self.lines[i])
            if m and (level is None or len(m.group(1)) <= level):
                return i
            opener = OPENER.match(self.lines[i])
            if opener and (level is None or STATEMENT_KIND.match(opener.group(1))):
                return i
        return len(self.lines)

    def line_of(self, label: str) -> int:
        """The line where a label is stated: its heading, its opener or its list item."""
        if label.startswith("§"):
            found = next((i for i, _, num, _ in self.headings if num == label[1:]), None)
        else:
            pattern = re.compile(re.escape(label) + r"(?![\d.]\d)(?:[\s.(:,]|$)")
            item = re.compile(r"^[*-] \*\*" + re.escape(label) + r"(?![\d.]\d)")
            found = next((i for i, text in self.openers if pattern.match(text)), None)
            if found is None:
                found = next((i for i, line in enumerate(self.lines) if item.match(line)), None)
        if found is None:
            raise SystemExit(f"blueprint: no statement '{label}' in {NOTE.name}")
        return found

    def extract(self, label: str, paras: int | None = None) -> Extract:
        """The node's text. Statements, proofs and the *Lean:* paragraph stay verbatim; remark
        paragraphs that discuss the 2015/2023 papers are left out (the statements that refute
        the papers say so themselves)."""
        ex = self._extract_raw(label, paras)
        ex.remarks = [p for p in map(without_paper_items, ex.remarks) if p and not mentions_papers(p)]
        return ex

    def _extract_raw(self, label: str, paras: int | None = None) -> Extract:
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
        """Statement, *Lean:* paragraph, proof, remarks: the layout of revision 3. The statement is
        everything before the *Lean:* paragraph (or, without one, the first paragraph and the
        lists or displays that continue it)."""
        title = re.sub(r"\s*\[[^\]]*\]", "", opener).strip().rstrip(".").strip()
        lean_at = next((k for k, p in enumerate(paras) if k > 0 and LEAN_PARA.match(p)), None)
        lean = ""
        if lean_at is not None and n_statement is None:
            lean = paras[lean_at]
            paras = paras[:lean_at] + paras[lean_at + 1:]
            n_statement = lean_at
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
            return Extract(title=title, where=where, statement=paras[:k], remarks=paras[k:],
                           lean=lean)
        k = start if n_statement is None else min(start, n_statement)
        return Extract(title=title, where=where, statement=paras[:k], proof=paras[start:end + 1],
                       remarks=paras[k:start] + paras[end + 1:], lean=lean)


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


def details(summary: str, body: list[str], pdf_title: str | None = None) -> list[str]:
    """A closed <details> block on the web. The markup is raw HTML, so the PDF shows the body as
    plain paragraphs, under `pdf_title` if one is given."""
    out = ["```{=html}", f'<details class="node-more"><summary>{summary}</summary>', "```", ""]
    if pdf_title:
        out += ["::: {.content-visible unless-format=\"html\"}", f"*{pdf_title}.*", ":::", ""]
    out += body
    out += ["", "```{=html}", "</details>", "```", ""]
    return out


BADGES = {"checked": "[machine-checked]{.badge .ok}", "definition": "[Lean definition]{.badge .ok}",
          "partial": "[parts in Lean]{.badge .informal}", "informal": "[informal]{.badge .informal}",
          "sorry": "[open]{.badge .open}", "axiom": "[axiomatised]{.badge .axiom}",
          "notation": "[notation]{.badge .informal}"}


def short_name(name: str) -> str:
    return name.removeprefix("ZenoFront.")


# ---------------------------------------------------------------------------------------------
# The claim ledger
# ---------------------------------------------------------------------------------------------

LEDGER = ROOT / "claims.toml"
def names_of(value) -> list[str]:
    """A ledger field of declarations: a comma-separated string or a list."""
    if not value:
        return []
    return [s.strip() for s in value.split(",")] if isinstance(value, str) else list(value)


def load_ledger() -> dict[str, dict]:
    """The active claims of the ledger by label: archived entries (`removed`) are skipped."""
    claims = tomllib.loads(LEDGER.read_text(encoding="utf-8"))["claims"]
    out: dict[str, dict] = {}
    for slug, claim in claims.items():
        if "removed" in claim or "label" not in claim:
            continue
        if claim["label"] in out:
            raise SystemExit(f"blueprint: two claims have the label {claim['label']!r}")
        out[claim["label"]] = dict(claim, slug=slug)
    return out


def ledger_names(registry: dict, ledger: dict[str, dict]) -> set[str]:
    """The declarations the ledger lists for the blueprint's nodes."""
    out = set()
    for node in registry["node"]:
        claim = ledger.get(node["label"])
        if claim:
            out |= set(names_of(claim.get("lean")) + names_of(claim.get("lean_partial")))
    return out


SHORTCODE = re.compile(r'\{\{<\s*node\s+"([^"]+)"')


def site_shortcodes() -> dict[str, list[str]]:
    """label -> the places (file:line) where a `{{< node "label" >}}` shortcode names it, in the
    site's sources (the generated partials included, since the section intros may use it)."""
    found: dict[str, list[str]] = {}
    skip = {".quarto", "_site", "graph", "fonts"}
    for path in sorted(SITE.rglob("*")):
        if path.suffix not in (".qmd", ".md") or skip & set(path.relative_to(SITE).parts):
            continue
        for k, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            for m in SHORTCODE.finditer(line):
                found.setdefault(m.group(1), []).append(f"{path.relative_to(ROOT)}:{k}")
    return found


class Blueprint:
    def __init__(self, registry: dict, note: Note, lean: dict, ref: str, ledger: dict[str, dict]):
        self.ledger = ledger
        self.sections = registry["section"]
        self.nodes = registry["node"]
        self.main = registry.get("main", [])
        if registry.get("note_only"):
            raise SystemExit("blueprint: `note_only` is gone; every label of the site is a node")
        self.note = note
        self.lean = lean
        self.ref = ref
        labels = [n["label"] for n in self.nodes]
        twice = sorted({l for l in labels if labels.count(l) > 1})
        if twice:
            raise SystemExit(f"blueprint: {twice} are nodes twice")
        missing = [l for l in note.results() if l not in labels]
        if missing:
            raise SystemExit(f"blueprint: the numbered results {missing} of {NOTE.name} have no node "
                             "in blueprint.toml")
        unknown = sorted(set(ledger) - set(labels))
        if unknown:
            raise SystemExit(f"blueprint: the ledger labels {unknown} are not nodes")
        sections = {sec["id"] for sec in self.sections}
        for node in self.nodes:
            if node["section"] not in sections:
                raise SystemExit(f"blueprint: {node['label']} is in an unknown section {node['section']!r}")
            if node.get("kind") != "notation" and node["label"] not in ledger:
                raise SystemExit(f"blueprint: {node['label']} has no claim in claims.toml (a `label`)")
        self.rows: list[dict] = []

    def decl(self, name: str) -> dict:
        d = self.lean["decls"].get(name)
        if d is None or d.get("missing"):
            raise SystemExit(f"blueprint: Lean has no declaration {name}")
        if d.get("range") is None:
            raise SystemExit(f"blueprint: no source range for {name}")
        return d

    def badge_of(self, node: dict) -> tuple[str, list[str], list[str]]:
        """The badge key of a node and its declarations: (key, whole, further).

        The badge follows the ledger's effective status, the `status` of claims.toml (a cache that
        gen_graph.py checks against the history): a node is machine-checked only if the ledger says
        so, and then its `lean` declarations must be axiom-clean. Otherwise it has parts in Lean
        when the ledger lists declarations for it, and is informal when not. The whole statement's
        declarations are the ledger's `lean`; the ledger's `lean_partial` and the other names of
        the note's *Lean:* paragraph (the registry's `lean`) are further declarations."""
        label = node["label"]
        if node.get("kind") == "notation":
            # no claim: badged by the kernel from the Lean definitions of the notation
            whole = node.get("lean", [])
            if not whole:
                return "notation", [], []
            if kernel_status([self.decl(n) for n in whole]) != "ok":
                raise SystemExit(f"blueprint: the definitions of {label} are not axiom-clean")
            return "definition", whole, []
        claim = self.ledger[label]
        whole, parts = names_of(claim.get("lean")), names_of(claim.get("lean_partial"))
        further = list(dict.fromkeys(n for n in parts + node.get("lean", []) if n not in whole))
        for n in whole + further:
            self.decl(n)
        if claim.get("status") == "math.machine-checked":
            if not whole:
                raise SystemExit(f"blueprint: the ledger has {label} machine-checked with no `lean`")
            if kernel_status([self.decl(n) for n in whole]) != "ok":
                raise SystemExit(f"blueprint: the ledger has {label} machine-checked, but {whole} "
                                 "are not axiom-clean")
            return ("definition" if claim.get("kind") == "definition" else "checked"), whole, further
        return ("partial" if whole + parts else "informal"), [], whole + further

    def source_url(self, name: str) -> str:
        lst = listing(self.decl(name))
        return f"{REPO}/blob/{self.ref}/{lst.path}#L{lst.first}-L{lst.last}"

    def lean_line(self, head: str, names: list[str]) -> list[str]:
        links = ", ".join(f"[`{short_name(n)}` ↗]({self.source_url(n)})" for n in names)
        return ["::: {.node-lean}", f"{head}: {links}", ":::", ""]

    def render_decl(self, name: str, heading: str) -> list[str]:
        d = self.decl(name)
        lst = listing(d)
        url = self.source_url(name)
        note = " (statement only; the proof is elided)" if lst.elided and d["kind"] == "theorem" else (
            " (shortened)" if lst.elided else "")
        prov = d.get("provenance")
        if prov:
            sha = prov.get("commit", "")
            note += (f". Axioms from the CI-audited commit footer of [`{sha[:7]}`]({REPO}/commit/{sha}) "
                     "(`#print axioms` output, re-checked by CI on every push), not from a local Lean run")
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
        extract = self.note.extract(label, node.get("paras"))
        title = node.get("title", extract.title)
        lean_key, lean_names, further = self.badge_of(node)
        claim = self.ledger.get(label, {})
        if lean_key == "partial" and not node.get("gap"):
            raise SystemExit(f"blueprint: {label} has parts in Lean but no `gap` line saying what "
                             "the Lean covers or misses")
        self.rows.append({"label": label, "title": title, "anchor": slug(label),
                          "lean": BADGES[lean_key], "lean_key": lean_key, "where": extract.where,
                          "slug": claim.get("slug", "")})

        # Shown: the title, one badge (with what the Lean misses, if it is not machine-checked),
        # the statement and one line naming the Lean declarations.
        # Closed: the proof, the remarks, and the Lean listings.
        badge = BADGES[lean_key]
        if lean_key == "partial":
            badge += f" [{' '.join(node['gap'].split())}]{{.node-gap}}"
        out = [f"### {title} {{#{slug(label)}}}", "", "::: {.node-badge}", badge, ":::", ""]
        out.append("::: {.node-body}")
        out += ["\n\n".join(extract.statement), ""]
        if lean_names:
            out += self.lean_line("Lean", lean_names)
        elif further:
            out += self.lean_line("Parts in Lean", further)

        facts = [f"theory note, {extract.where}"] if extract.where else []
        if claim.get("slug"):
            facts.append(f"ledger `{claim['slug']}`")
        facts_line = [" · ".join(facts), ""] if facts else []
        if extract.proof:
            proof = "\n\n".join(extract.proof)
            out += details("Proof", facts_line + [proof],
                           pdf_title=None if proof.startswith("*Proof") else "Proof")
        elif facts_line:
            out += details("In the note", facts_line)
        if extract.remarks:
            out += details("Remarks", ["\n\n".join(extract.remarks)], pdf_title="Remarks in the note")
        lean_body = [extract.lean, ""] if extract.lean else []
        if node.get("covers"):
            lean_body += [f"**In Lean.** {node['covers']}", ""]
        for n in lean_names:
            lean_body += self.render_decl(n, "**Lean**")
        if further and lean_names:
            # the proof's steps and the other declarations the note names: links, not listings
            lean_body += self.lean_line("Further declarations", further)
        elif further:
            lean_body += ["**Formalised parts.** These declarations prove part of the statement.", ""]
            for n in further:
                lean_body += self.render_decl(n, "*Part*")
        if lean_body:
            out += details("Lean statement and source", lean_body)
        out += [":::", ""]
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
        self.write_progress(proofs / "_progress.md")
        self.write_main(proofs / "_main.md")
        self.write_summary(proofs / "_summary.md")
        self.write_stats(SITE / "_blueprint-stats.md")
        self.write_home(SITE / "_home-lean.md")
        self.write_index(SITE / "_nodes.json")

    def is_result(self, row: dict) -> bool:
        """A numbered result other than a definition (definitions are counted on their own)."""
        return row["lean_key"] not in ("definition", "notation") and bool(RESULT.match(row["label"])) \
            and not row["label"].startswith("Definition")

    def counts(self) -> tuple[int, int, int, int, int]:
        """(results, machine-checked results, with parts in Lean, definitions, Lean definitions)."""
        results = [r for r in self.rows if self.is_result(r)]
        defs = [r for r in self.rows if r["label"].startswith("Definition")]
        return (len(results), sum(1 for r in results if r["lean_key"] == "checked"),
                sum(1 for r in results if r["lean_key"] == "partial"), len(defs),
                sum(1 for r in defs if r["lean_key"] == "definition"))

    def write_progress(self, path: Path) -> None:
        n, checked, partial, ndefs, ldefs = self.counts()
        text = f"**{checked} of {n} results are machine-checked"
        text += f"; {partial} more have parts in Lean" if partial else ""
        notation = all(r["lean_key"] == "definition" for r in self.rows if r["label"] == "Notation")
        text += (f", and all {ndefs} definitions" + (" and the notation" if notation else "")
                 + " are stated in Lean.**" if ldefs == ndefs else
                 f", and {ldefs} of the {ndefs} definitions are stated in Lean.**")
        path.write_text(text + "\n", encoding="utf-8")

    def write_main(self, path: Path) -> None:
        """The main results: a definition list of name, label, badge and one sentence."""
        rows = {r["label"]: r for r in self.rows}

        def ref(label: str) -> tuple[str, dict]:
            if label not in rows:
                raise SystemExit(f"blueprint: main result '{label}' is not a node")
            r = rows[label]
            text = label if number_of(label) else r["title"]
            return f"[{text}](#{r['anchor']}) {BADGES[r['lean_key']]}", r

        out = ["::: {.main-results}", ""]
        for entry in self.main:
            link, r = ref(entry["label"])
            head = f"**{entry['name']}** · {link}"
            text = " ".join(entry["text"].split())
            with_ = [f"{ref(w['label'])[0]} ({w['name']})" for w in entry.get("with", [])]
            if with_:
                text += " With " + (", ".join(with_[:-1]) + " and " + with_[-1]
                                    if len(with_) > 1 else with_[0]) + "."
            out += [head, f":   {text}", ""]
        out += [":::"]
        path.write_text("\n".join(out) + "\n", encoding="utf-8")

    def write_index(self, path: Path) -> None:
        """label -> anchor and badge, read by the `node` shortcode (shortcodes/node.lua)."""
        badge = {"checked": ("machine-checked", "ok"), "definition": ("Lean definition", "ok"),
                 "partial": ("parts in Lean", "informal"), "informal": ("informal", "informal"),
                 "sorry": ("open", "open"), "axiom": ("axiomatised", "axiom"),
                 "notation": ("notation", "informal")}
        index = {}
        for r in self.rows:
            text, cls = badge.get(r["lean_key"], ("informal", "informal"))
            index[r["label"]] = {"anchor": r["anchor"], "title": r["title"], "lean": text,
                                 "class": cls, "where": r["where"]}
        path.write_text(json.dumps(index, ensure_ascii=False, indent=0) + "\n", encoding="utf-8")

    def write_summary(self, path: Path) -> None:
        lines = ["| Node | Lean | Note | Ledger |", "|---|---|---|---|"]
        for r in self.rows:
            ledger = f"`{r['slug']}`" if r["slug"] else ""
            lines.append(f"| [{r['title']}](#{r['anchor']}) | {r['lean']} | {r['where']} | {ledger} |")
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def write_stats(self, path: Path) -> None:
        count = lambda key, val: sum(1 for r in self.rows if r[key] == val)
        lib = self.lean["library"]
        meta = self.lean["meta"]
        clean = "no declaration uses another axiom" if not lib["nonstandard"] else \
            f"{len(lib['nonstandard'])} declarations use other axioms"
        n, checked, partial, ndefs, ldefs = self.counts()
        text = (
            f"The blueprint has **{len(self.rows)} nodes**: the {n + ndefs} numbered results of the "
            f"theory note and its notation. **{checked}** of its {n} results are machine-checked and "
            f"**{ldefs}** of its {ndefs} definitions are Lean definitions"
            + (f"; **{partial}** results have parts in Lean" if partial else "")
            + (f", and **{count('lean_key', 'informal')}** are not in Lean" if count('lean_key', 'informal') else "")
            + ". These badges follow the claim "
            f"ledger [`claims.toml`]({REPO}/blob/master/claims.toml): a statement is machine-checked "
            "only if Lean proves every assertion of it. "
            f"The library has {lib['declarations']:,} declarations "
            f"({lib['theorems']:,} theorems) in {lib['modules']} modules "
            f"(Lean `{meta['lean'].split(':')[-1]}`, Mathlib `{meta['mathlib']}`). "
            f"Apart from `propext`, `Classical.choice` and `Quot.sound`, {clean}: "
            f"no `sorry` and no `native_decide`."
        )
        footer = [d for d in self.lean["decls"].values() if d.get("provenance")]
        if footer:
            text += (f" These counts are from the last local Lean audit; {len(footer)} declarations "
                     "added since then are badged from the `#print axioms` footers of their commits, "
                     "which CI re-checks on every push.")
        path.write_text(text + "\n", encoding="utf-8")

    def write_home(self, path: Path) -> None:
        """The Lean tally of the home page: one square per machine-checked result."""
        n, checked, partial, ndefs, ldefs = self.counts()
        rows = [min(12, checked - 12 * k) for k in range((checked + 11) // 12)]
        rects = "\n".join(f'    <rect y="{11 * k}" width="{11 * n - 2}" height="9" fill="url(#hw-on)"/>'
                          for k, n in enumerate(rows))
        more = f", {partial} more have parts in Lean," if partial else ""
        path.write_text(
            "<!-- Written by site/gen_blueprint.py from the claim ledger; do not edit. -->\n"
            "```{=html}\n"
            '<div class="lean-count">\n'
            f'  <svg class="waffle waffle-short" viewBox="0 0 130 {11 * len(rows) - 2}" role="img" '
            f'aria-label="{checked} squares, one per machine-checked result">\n{rects}\n  </svg>\n'
            f'  <p class="tally-figure tally-big">{checked}</p>\n'
            f'  <p class="tally-text">of the {n} results of the theory are <span class="nobr">'
            f"machine-checked</span> in Lean 4{more} and {ldefs} of its {ndefs} definitions are "
            "stated in Lean.</p>\n"
            '  <p class="lean-trust">No <code>sorry</code>, no <code>native_decide</code>, and no axiom '
            "beyond <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>.</p>\n"
            "</div>\n"
            "```\n", encoding="utf-8")

    def check_shortcodes(self) -> list[str]:
        """Every `{{< node "…" >}}` of the site must name a node: the problems, one per label."""
        labels = {r["label"] for r in self.rows}
        return [f"{label!r} ({', '.join(places[:4])}{', …' if len(places) > 4 else ''})"
                for label, places in sorted(site_shortcodes().items()) if label not in labels]


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--no-lean", action="store_true", help="reuse site/lean-status.json")
    args = ap.parse_args()

    registry = tomllib.loads((SITE / "blueprint.toml").read_text(encoding="utf-8"))
    note = Note(NOTE)
    ledger = load_ledger()
    names = sorted({n for node in registry["node"] for n in node.get("lean", [])}
                   | ledger_names(registry, ledger))
    if args.no_lean:
        lean = json.loads(STATUS_JSON.read_text(encoding="utf-8"))
        missing = [n for n in names if n not in lean["decls"]]
        if missing:
            raise SystemExit(f"blueprint: {STATUS_JSON.name} lacks {missing}; run without --no-lean")
    else:
        lean = query_lean(names)
        STATUS_JSON.write_text(json.dumps(lean, indent=1, ensure_ascii=False, sort_keys=True) + "\n",
                               encoding="utf-8")
    bp = Blueprint(registry, note, lean, git_ref(), ledger)
    bp.write()
    bad = [r["label"] for r in bp.rows if r["lean_key"] in ("sorry", "axiom", "missing")]
    print(f"blueprint: {len(bp.rows)} nodes, {len(names)} Lean declarations"
          + (f"; NOT clean: {bad}" if bad else "; every listed declaration is axiom-clean"))
    print("blueprint: " + (SITE / "proofs" / "_progress.md").read_text(encoding="utf-8").strip())
    unknown = bp.check_shortcodes()
    if unknown:
        raise SystemExit("blueprint: these `node` shortcodes name no node of the blueprint (use the "
                         "labels of revision 3, doc/theory/revision-3-map.md Table C):\n  "
                         + "\n  ".join(unknown))


if __name__ == "__main__":
    main()
