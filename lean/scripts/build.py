"""Compile the local proof modules in dependency order, one at a time."""
from graphlib import TopologicalSorter
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
paths = [root / "Liu.lean", *sorted((root / "Liu").glob("*.lean"))]
graph = {}
for path in paths:
    name = ".".join(path.relative_to(root).with_suffix("").parts)
    imports = re.findall(r"^\s*(?:public )?import ([^\n]+)", path.read_text(), re.M)
    graph[name] = {dep for line in imports for dep in line.partition("--")[0].split()
                   if dep.startswith("Liu.") or dep == "Liu"}

if set().union(*graph.values()) - graph.keys():
    raise ValueError("Missing local module in the import graph")
# An up-to-date checkout needs only one Lake invocation. A cold checkout
# builds in dependency order to bound peak memory on small machines.
if subprocess.run(["lake", "-q", "--no-build", "build", "Liu"], cwd=root).returncode:
    for name in TopologicalSorter(graph).static_order():
        subprocess.run(["lake", "-q", "build", f"+{name}:leanArts"], cwd=root, check=True)
    subprocess.run(["lake", "-q", "build", "Liu"], cwd=root, check=True)
