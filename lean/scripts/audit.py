"""Generate the audit from Lean's imported declarations and the paper index."""
import csv
from collections import Counter
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

def read_rows(name):
    with (ROOT / name).open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))

def render(output):
    declarations = read_rows("DECLARATIONS.tsv")
    reports = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]+)\]$", output, re.M)
    expected = [row["declaration"] for row in declarations]
    if len(set(expected)) != len(expected) or Counter(n for n, _ in reports) != Counter(expected):
        raise ValueError("Lean's reports differ from the declaration inventory")
    axioms = {}
    for name, report in reports:
        if set(report.split(", ")) != STANDARD:
            raise ValueError(f"Unexpected axioms for {name}: {report}")
        axioms[name] = report
    target_names = {row["declaration"] for row in read_rows("TARGETS.tsv")}
    if len(target_names) != 95 or not target_names <= axioms.keys():
        raise ValueError("The 95 comparator targets must occur in the imported audit")
    claims = read_rows("CLAIM_MAP.tsv")
    lines = ["# Lean proof audit", "",
             "The main theorems take the fixed 168-box proposition as an explicit hypothesis. "
             "Lemma 6.5 takes the stated scalar interpolation inequality. "
             "The axiom report for each declaration concerns its Lean proof, including any explicit arguments.", "",
             "## Numbered statements", "", "| Paper | Status |", "|---|---|"]
    for row in claims:
        names = row["comparator_targets"].split()
        if set(names) - target_names:
            raise ValueError(f"Unknown comparison target at {row['claim']}")
        lines.append(f"| {row['claim']} | {row['status']} |")
    lines += ["", "## Imported theorem declarations", "",
              "| Declaration | Source | Axioms |", "|---|---|---|"]
    for row in declarations:
        name = row["declaration"]
        path, line = row["frozen_source"], row["line"]
        lines.append(f"| `{name}` | [{path}, line {line}]({path}#L{line}) | {axioms[name]} |")
    return "\n".join(lines) + "\n"

def main():
    policy = re.compile(r"\b(sorry|admit|sorryAx|native_decide|unsafe|extern|implemented_by|csimp|Lean\.ofReduceBool|debug\.skipKernelTC|axiom)\b")
    for path in [ROOT / "Liu.lean", *(ROOT / "Liu").rglob("*.lean"), *(ROOT / "checks").glob("*.lean")]:
        match = policy.search(path.read_text())
        if match:
            raise ValueError(f"Unexpected construct in {path.name}: {match.group()}")
    result = subprocess.run(["lake", "env", "lean", "-j1", "checks/AllAxioms.lean"],
                            cwd=ROOT, text=True, stdout=subprocess.PIPE)
    sys.stdout.write(result.stdout)
    result.check_returncode()
    (ROOT / "AUDIT.md").write_text(render(result.stdout), encoding="utf-8")
    print("Checked 977 Lean declarations against the three permitted standard axioms.")

if __name__ == "__main__":
    main()
