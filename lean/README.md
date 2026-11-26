# A two-pole test of the Liu (2018) conjecture on the norm of the Bergman projection

The paper’s link is on the [front page of this repository](https://github.com/david44hello/paper_liu-2018-conjecture-two-pole-test).

For each two-pole Pick function, Theorem 3.5 gives a positive deficit margin. Theorem 1.1 gives a strictly negative slope and a quotient below π²/12 for all sufficiently small positive exponent increments. Both deductions assume the computer-checked bounds of Proposition 6.1 on the paper’s 168 fixed boxes. Coincident poles are included. The cutoff can depend on the pair.

The [reading guide](WHAT_TO_READ.md) identifies the numerical input, the scalar interpolation bound used in Lemma 6.5, and the coverage of individual proofs.

## How to verify

Install Git, Python 3 and elan. From this directory run

```sh
./scripts/check.sh
```

The reader builds the proof, checks the imported axiom reports and regenerates AUDIT.md. Its final line is

```text
Checked 977 Lean declarations against the three permitted standard axioms.
```

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0. See [LICENSE](../LICENSE).
