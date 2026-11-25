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
* the badges follow the claim ledger `claims.toml`: a node that is a claim there is machine-checked
  only if the ledger's effective status is math.machine-checked (Lean proves every assertion of
  the statement), and then its `lean` declarations must use no axiom beyond propext,
  Classical.choice and Quot.sound; otherwise it has parts in Lean (the ledger's `lean_partial`,
  with the registry's one-line `gap`) or is informal. Nodes that are not claims (the model's
  definitions, the Lean-only results) are badged from their own declarations' axioms.

Outputs: `site/proofs/_<section>.qmd` (one partial per section), `site/proofs/_sections.qmd`
(includes them in order), `site/proofs/_progress.md` (the one-line count at the top),
`site/proofs/_main.md` (the main results), `site/proofs/_summary.md` (the status table),
`site/_blueprint-stats.md` (the counts quoted on the About page), `site/_home-lean.md` (the Lean
tally of the home page) and `site/_nodes.json` (read by the
`node` shortcode; the registry's `note_only` labels point there to their section of the note on
GitHub). The script fails if a label is not found in the note or a declaration is missing in Lean,
so the pages cannot silently drift.
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
from urllib.parse import quote

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
STATEMENT_KIND = re.compile(r"^(Lemma|Theorem|Corollary|Proposition|Conjecture|Statement|Notation|Example)\b")
SQUARE = r"\square"


@dataclass
class Extract:
    title: str                      # the opener without its tags, or the heading
    where: str                      # "§2" or "§4.3": the section of the note it sits in
    statement: list[str]
    proof: list[str] = field(default_factory=list)
    remarks: list[str] = field(default_factory=list)


PAPERS = re.compile(r"(?i)\b(both papers|the papers|papers'|papers’|paper's|paper’s|arXiv|EvoCOP)")
# sentences of a statement that only cite the papers
PAPER_SENTENCES = [re.compile(r"\s*This is the EvoCOP 2015 assumption \(stated there with \$>\$\)\.")]


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


def cut_paper_sentences(text: str) -> str:
    for pattern in PAPER_SENTENCES:
        text = pattern.sub("", text)
    return text


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

    def github_anchor(self, label: str) -> str:
        """The GitHub anchor of the innermost heading at or above a label, as GitHub slugs it:
        lower case, punctuation dropped, spaces as hyphens."""
        index = self.line_of(label)
        line = self.lines[max(i for i, *_ in self.headings if i <= index)]
        text = line.lstrip("#").strip().lower()
        return re.sub(r"[^\w\- ]", "", text).replace(" ", "-")

    def extract(self, label: str, paras: int | None = None) -> Extract:
        """The node's text, without the note's remarks about the 2015/2023 papers: the site
        presents the theory on its own terms. Statements and proofs stay verbatim; only remark
        paragraphs (and paragraphs of a section block) that discuss the papers are left out."""
        ex = self._extract_raw(label, paras)
        ex.remarks = [p for p in map(without_paper_items, ex.remarks) if p and not mentions_papers(p)]
        if label.startswith("§"):
            ex.statement = [p for p in map(without_paper_items, ex.statement) if p and not mentions_papers(p)]
        ex.statement = [cut_paper_sentences(p) for p in ex.statement]
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


def note_badge(status: str) -> str:
    """The badge of a status-table entry; a composite entry (e.g. "P (computed) for (a)–(c); S for
    ...") is shown by its leading status, and anything unknown as written."""
    if status in NOTE_BADGES:
        return NOTE_BADGES[status]
    for key in ("P (computed)", "refuted", "P", "S", "O"):
        if status.startswith(key + " ") or status.startswith(key + ";"):
            return NOTE_BADGES[key] + " (partly; see the status table)"
    return f"[{status}]{{.badge .informal}}"


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
          "sorry": "[open]{.badge .open}", "axiom": "[axiomatised]{.badge .axiom}"}


def short_name(name: str) -> str:
    return name.removeprefix("ZenoFront.")


# ---------------------------------------------------------------------------------------------
# The claim ledger
# ---------------------------------------------------------------------------------------------

LEDGER = ROOT / "claims.toml"
KIND_SLUG = {"Definition": "def", "Lemma": "lem", "Theorem": "thm", "Proposition": "prop",
             "Corollary": "cor", "Conjecture": "conj", "Statement": "claim"}


def claim_slug(label: str) -> str | None:
    """The claims.toml slug of a blueprint label (Theorem 4.7 -> thm-4-7, §5 -> claim-5)."""
    if label.startswith("§") and label[1:].isdigit():
        return f"claim-{label[1:]}"
    parts = label.split(" ", 1)
    if len(parts) == 2 and parts[0] in KIND_SLUG and parts[1][:1].isdigit():
        return f"{KIND_SLUG[parts[0]]}-{parts[1].split(' ')[0].replace('.', '-')}"
    return None


def names_of(value) -> list[str]:
    """A ledger field of declarations: a comma-separated string or a list."""
    if not value:
        return []
    return [s.strip() for s in value.split(",")] if isinstance(value, str) else list(value)


def load_ledger() -> dict[str, dict]:
    return tomllib.loads(LEDGER.read_text(encoding="utf-8"))["claims"]


def ledger_names(registry: dict, ledger: dict[str, dict]) -> set[str]:
    """The declarations the ledger lists for the blueprint's nodes."""
    out = set()
    for node in registry["node"]:
        claim = ledger.get(claim_slug(node["label"]) or "")
        if claim:
            out |= set(names_of(claim.get("lean")) + names_of(claim.get("lean_partial")))
    return out


class Blueprint:
    def __init__(self, registry: dict, note: Note, lean: dict, ref: str, ledger: dict[str, dict]):
        self.ledger = ledger
        self.sections = registry["section"]
        self.nodes = registry["node"]
        self.main = registry.get("main", [])
        self.note_only = registry.get("note_only", [])
        both = {n["label"] for n in self.nodes} & set(self.note_only)
        if both:
            raise SystemExit(f"blueprint: {sorted(both)} are both nodes and note_only")
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

    def badge_of(self, node: dict) -> tuple[str, list[str], list[str], list[str]]:
        """The badge key of a node and its declarations: (key, whole, parts, related).

        A node that is a claim of the ledger takes its badge from the ledger's effective status,
        the `status` of claims.toml (a cache that gen_graph.py checks against the history): it is
        machine-checked only if the ledger says so, and then its `lean` declarations must be
        axiom-clean. Otherwise it has parts in Lean when the ledger lists declarations for it, and
        is informal when not. Its declarations are the ledger's `lean` and `lean_partial`; those
        the registry adds are shown as related. A node with no claim (the model's definitions, the
        Lean-only results) is badged by the kernel from its own declarations."""
        label = node["label"]
        mine = node.get("lean", []) + node.get("leaves", [])
        claim = self.ledger.get(claim_slug(label) or "")
        if claim is None:
            whole, parts = node.get("lean", []), node.get("leaves", [])
            if not whole:
                return ("partial" if parts else "informal"), [], parts, []
            decls = [self.decl(n) for n in whole]
            key = kernel_status(decls)
            if key == "ok":
                key = "definition" if all(d["kind"] != "theorem" for d in decls) else "checked"
            return key, whole, parts, []
        whole, parts = names_of(claim.get("lean")), names_of(claim.get("lean_partial"))
        related = [n for n in mine if n not in whole + parts]
        if claim.get("status") == "math.machine-checked":
            if not whole:
                raise SystemExit(f"blueprint: the ledger has {label} machine-checked with no `lean`")
            if kernel_status([self.decl(n) for n in whole]) != "ok":
                raise SystemExit(f"blueprint: the ledger has {label} machine-checked, but {whole} "
                                 "are not axiom-clean")
            return ("definition" if claim.get("kind") == "definition" else "checked"), whole, parts, related
        return ("partial" if whole + parts else "informal"), [], whole + parts, related

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
        ex = node.get("statement")
        if ex is None:
            extract = self.note.extract(label, node.get("paras"))
        else:
            extract = Extract(title=node.get("title", label), where="", statement=[ex.strip()])
        title = node.get("title", extract.title)
        status, row = self.note_status(node, label)
        lean_key, lean_names, leaf_names, related = self.badge_of(node)
        if lean_key == "partial" and not node.get("gap"):
            raise SystemExit(f"blueprint: {label} has parts in Lean but no `gap` line saying what "
                             "the Lean covers or misses")
        self.rows.append({"label": label, "title": title, "anchor": slug(label),
                          "lean": BADGES[lean_key], "lean_key": lean_key,
                          "note": note_badge(status) if status else "", "note_key": status})

        # Shown: the title, one badge (with what the Lean misses, if it is not machine-checked),
        # the statement and one line naming the Lean declarations.
        # Closed: the proof (with the note's status), the remarks, and the Lean listings.
        badge = BADGES[lean_key]
        if lean_key == "partial":
            badge += f" [{' '.join(node['gap'].split())}]{{.node-gap}}"
        out = [f"### {title} {{#{slug(label)}}}", "", "::: {.node-badge}", badge, ":::", ""]
        out.append("::: {.node-body}")
        out += ["\n\n".join(extract.statement), ""]
        if lean_names:
            out += self.lean_line("Lean", lean_names)
        elif leaf_names:
            out += self.lean_line("Parts in Lean", leaf_names)

        facts = []
        if status:
            facts.append(f"**Note** {note_badge(status)}")
        if extract.where:
            facts.append(f"theory note, {extract.where}")
        if row.get("hypotheses") and row["hypotheses"] not in ("—", "definition"):
            facts.append(f"**Hypotheses** {row['hypotheses']}")
        if row.get("uses") and self.link_uses(row["uses"]):
            facts.append(f"**Uses** {self.link_uses(row['uses'])}")
        facts_line = [" · ".join(facts), ""] if facts else []
        if extract.proof:
            proof = "\n\n".join(extract.proof)
            out += details("Proof", facts_line + [proof],
                           pdf_title=None if proof.startswith("*Proof") else "Proof")
        elif facts_line:
            out += details("In the note", facts_line)
        if extract.remarks:
            out += details("Remarks", ["\n\n".join(extract.remarks)], pdf_title="Remarks in the note")
        lean_body = [f"**In Lean.** {node['covers']}", ""] if node.get("covers") else []
        for n in lean_names:
            lean_body += self.render_decl(n, "**Lean**")
        if leaf_names:
            lean_body += ["**Formalised parts.** These declarations prove part of the statement; "
                          "the ledger records the statement as a written proof.", ""]
            for n in leaf_names:
                lean_body += self.render_decl(n, "*Part*")
        if related:
            lean_body += ["**Related declarations.** The ledger does not list these for the "
                          "statement.", ""]
            for n in related:
                lean_body += self.render_decl(n, "*Related*")
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
        return row["lean_key"] != "definition" and row["note_key"] != "definition"

    def write_progress(self, path: Path) -> None:
        results = [r for r in self.rows if self.is_result(r)]
        checked = sum(1 for r in results if r["lean_key"] == "checked")
        partial = sum(1 for r in results if r["lean_key"] == "partial")
        path.write_text(f"**{checked} of {len(results)} results are machine-checked; {partial} more "
                        "have parts in Lean.**\n", encoding="utf-8")

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
            head = f"**{entry['name']}** · {link}" if number_of(entry["label"]) else \
                f"[**{entry['name']}**](#{r['anchor']}) {BADGES[r['lean_key']]}"
            text = " ".join(entry["text"].split())
            with_ = [f"{ref(w['label'])[0]} ({w['name']})" for w in entry.get("with", [])]
            if with_:
                text += " With " + (", ".join(with_[:-1]) + " and " + with_[-1]
                                    if len(with_) > 1 else with_[0]) + "."
            out += [head, f":   {text}", ""]
        out += [":::"]
        path.write_text("\n".join(out) + "\n", encoding="utf-8")

    def write_index(self, path: Path) -> None:
        """label -> anchor and badges, read by the `node` shortcode (shortcodes/node.lua). The
        `note_only` labels get an `href` to their section of the theory note on GitHub instead."""
        badge = {"checked": ("machine-checked", "ok"), "definition": ("Lean definition", "ok"),
                 "partial": ("parts in Lean", "informal"), "informal": ("informal", "informal"),
                 "sorry": ("open", "open"), "axiom": ("axiomatised", "axiom")}
        index = {}
        for r in self.rows:
            text, cls = badge.get(r["lean_key"], ("informal", "informal"))
            index[r["label"]] = {"anchor": r["anchor"], "title": r["title"],
                                 "lean": text, "class": cls, "note": r["note_key"] or ""}
        note_url = f"{REPO}/blob/master/{NOTE.relative_to(ROOT).as_posix()}"
        for label in self.note_only:
            ex = self.note.extract(label)
            index[label] = {"href": f"{note_url}#{quote(self.note.github_anchor(label), safe='-')}",
                            "title": ex.title, "where": ex.where}
        path.write_text(json.dumps(index, ensure_ascii=False, indent=0) + "\n", encoding="utf-8")

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
            f"**{count('lean_key', 'checked')}** are machine-checked and "
            f"**{count('lean_key', 'definition')}** are Lean definitions. "
            f"**{count('lean_key', 'partial')}** have parts in Lean, and "
            f"**{count('lean_key', 'informal')}** are not in Lean. These badges follow the claim "
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
        results = [r for r in self.rows if self.is_result(r)]
        checked = sum(1 for r in results if r["lean_key"] == "checked")
        partial = sum(1 for r in results if r["lean_key"] == "partial")
        definitions = sum(1 for r in self.rows if r["lean_key"] == "definition")
        rows = [min(12, checked - 12 * k) for k in range((checked + 11) // 12)]
        rects = "\n".join(f'    <rect y="{11 * k}" width="{11 * n - 2}" height="9" fill="url(#hw-on)"/>'
                          for k, n in enumerate(rows))
        path.write_text(
            "<!-- Written by site/gen_blueprint.py from the claim ledger; do not edit. -->\n"
            "```{=html}\n"
            '<div class="lean-count">\n'
            f'  <svg class="waffle waffle-short" viewBox="0 0 130 {11 * len(rows) - 2}" role="img" '
            f'aria-label="{checked} squares, one per machine-checked result">\n{rects}\n  </svg>\n'
            f'  <p class="tally-figure tally-big">{checked}</p>\n'
            '  <p class="tally-text">results of the theory are <span class="nobr">machine-checked</span> '
            f"in Lean 4, {partial} more have parts in Lean, and {definitions} of its definitions are "
            "stated in Lean.</p>\n"
            '  <p class="lean-trust">No <code>sorry</code>, no <code>native_decide</code>, and no axiom '
            "beyond <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>.</p>\n"
            "</div>\n"
            "```\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--no-lean", action="store_true", help="reuse site/lean-status.json")
    args = ap.parse_args()

    registry = tomllib.loads((SITE / "blueprint.toml").read_text(encoding="utf-8"))
    note = Note(NOTE)
    ledger = load_ledger()
    names = sorted({n for node in registry["node"] for n in node.get("lean", []) + node.get("leaves", [])}
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


if __name__ == "__main__":
    main()
