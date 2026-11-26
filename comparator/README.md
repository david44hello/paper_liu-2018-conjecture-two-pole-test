# Comparing the two-pole statements

The independent challenge gives the 95 statements in the [comparison roster](../lean/TARGETS.tsv). The solution proofs are in [the Lean project](../lean/). The configuration permits the three standard axioms. The numerical and scalar premises appear directly in the applicable statements.

On Linux with Git, elan and bubblewrap, run the following from the repository root in Bash. It builds the comparison in a fresh temporary directory.

```sh
./comparator/compare.sh
```

A successful comparison ends with `Your solution is okay!`.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0. See [LICENSE](../LICENSE).
