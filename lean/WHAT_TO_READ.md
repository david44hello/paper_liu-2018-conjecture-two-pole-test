# Reading the two-pole proof

Start with [the two main deductions](Liu/CertificateConclusion.lean) and [their exact statements and numerical hypothesis](MAIN_TYPES.txt). For every physical pair of poles and positive masses, the deficit exceeds (π²/12) times the squared total mass. The second deduction also proves the slope is negative and gives a positive, pair-dependent cutoff below which the Bergman quotient is strictly less than π²/12. Both conclusions cover coincident poles. The paper tests a consequence of Liu’s conjecture near exponent two. The conjectured projection norm itself remains open.

## What the main theorems assume

Both proofs take one argument, `Liu.Certificate.boxBounds`, defined in [Gluing.lean](Liu/Gluing.lean). For each physical point of each fixed box the margin is positive for every depth at or above the box cutoff, and the margin at the cutoff exceeds or equals the recorded lower bound. The prefix integral below each cutoff has a separate analytic proof in Lean.

There are 168 boxes. For each one, let K be the count of low pieces (labelled “DEEP pieces” in the logs) starting from the logarithmic depth V_BOT. Its cutoff is exp(V_BOT − K). Its conservative margin bound is the displayed six-decimal lower endpoint minus one millionth. The [Lean data](Liu/BoxData.lean) and [exact rational table](boxes.tsv) identify the cells, cutoffs and bounds. The [certificate directory](../liu-2018-conjecture-two-pole-test/README.md) contains the interval programs, original logs, box list and file checksums. These computations supply Proposition 6.1(a,b) as a hypothesis.

## Scalar input for Lemma 6.5

For degree n ≥ 1, the maximum over the real interval [−1,1] of the sum of the absolute first-kind Lagrange cardinal functions is bounded above by (2/π) log(n+1) + 0.9734… . Reversing the node order permutes the sum. Lean takes the weaker upper bound with rational additive constant 974/1000 as the explicit proposition `Liu.firstKindLebesgueInput`. The full tensor interpolation estimate of Lemma 6.5 takes this input, called H4. Theorems 1.1 and 3.5 use the box proposition alone. [Scalar and tensor proofs](Liu/CitedInterpolation.lean) · [İbrahimoğlu (2016), §3.2, equation (13)](https://doi.org/10.1186/s13660-016-1030-3)

## Numbered results and individual passages

The [numbered map](CLAIM_MAP.tsv) covers 40 entries, including three definitions and the numerical proposition. Of the 36 mathematical results, 33 have Lean proofs with no external mathematical or numerical premise, two take the fixed-box hypothesis, and Lemma 6.5 takes the scalar bound.

The [passage map](PROOF_STEPS.tsv) gives each printed passage or diagram description, its location in the manuscript sources, the evidence status and the linked Lean declarations. Some proofs use a different argument. For Lemma 2.2, the formal proof derives the localized formula for smooth potentials using Green’s identity and a regularized reflected kernel. It controls the full real differential up to the boundary. A proof of the numbered result can therefore coexist with partial matches to individual steps. The disc integral at R0253 has a wider printed range than the formalized pairing. Sharper intermediate estimates and individual quadrature and spatial-tail formulas also retain gaps. [Dirichlet estimates](Liu/DirichletEstimates.lean) · [Reflected kernel](Liu/DirichletParametrix.lean)

The map contains 257 checked theorem links or stated specializations, 15 links conditional on the box bounds, 20 finite-data checks, 254 partial matches, 171 unresolved passages, eight background citations and 124 expository entries. Figure 1 uses two panels to distinguish the known one-pole benchmark, the two-pole result and the range beyond its pair-dependent cutoff. Its shaded regions illustrate the scope of the theorem. The Discussion distinguishes the result for two poles from the open many-pole, general-quotient and projection-norm questions.

## Machine checks

The [imported audit](AUDIT.md) covers 977 declarations. Every proof lists the three standard axioms `propext`, `Classical.choice` and `Quot.sound`. Explicit mathematical hypotheses appear in the theorem types. The [comparison roster](TARGETS.tsv) contains 95 statements, while the imported audit also covers supporting theorems.

On the accepted proof inputs, all 306 modules built from empty project outputs and each module passed binary replay. The standard Lake comparator accepted all 95 selected statements against the independent challenge. Five further checkers accepted the same solution export: paranoid Lean, lean4lean, NanoDa, con-leche and con-ron. A deliberately removed central box caused the cover check to fail. Removing one referenced expression from the exported proof caused the checker to reject it. The [comparator instructions](../comparator/README.md) describe how to repeat the native comparison.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0. See [LICENSE](../LICENSE).
