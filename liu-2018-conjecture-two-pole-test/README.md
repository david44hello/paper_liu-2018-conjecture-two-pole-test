# Computer certificate for "A two-pole test of the Liu (2018) conjecture on the norm of the Bergman projection"

This folder holds the program of Section 6 of the paper, the list of the 168 boxes of its cover (`boxes.csv`), the
certificate log of every box (`logs/`), and the SHA-256 checksum of every file in it (`SHA256SUMS`).

## 1. One program, in seven versions

All 168 boxes were certified by ONE program: a driver with three modules, in `programs/`. The driver changed while the
boxes were being run, so the 168 logs come from seven versions of it. The first line of every log names the MD5
checksums (first 8 hexadecimal digits) of the four source files that produced it. The three modules are the same files in
all 168 logs:

| module | file | MD5 |
|---|---|---|
| enclosure of the flux (the engine) | `F_arb.py` | 78206e94b6a773a6b139a1ebf30c8abf |
| Chebyshev interpolation and polynomial maxima | `cheb3.py` | 9da5f00a00c93296a4115a010b2a94ba |
| chain in depth and small-depth bound | `backchain.py` | 6dbc509fec07ddb7d84e2ee41f85bb1a |

| driver version | file | MD5 | boxes | what is new against the version before |
|---|---|---|---|---|
| 0.71 | `chartM_v071.py` | 4111368594b3ab0b3ff29f9e5835bb39 | 23 | first version: the large angles 0.53 <= gamma <= 1.571 |
| 0.72 | `chartM_v072.py` | 7309984f80846a4885bbbcda15eeab16 | 19 | the gamma range is cut into 3 balls inside the bounds M_m (was 1) |
| 1.31 | `chartM_v131.py` | a4cd94be742ad51ea3d48beda56476c3 | 5 | small angles: log gamma as the coordinate, moved paths of integration, refinement of wide balls, the corner gamma = 0 |
| 1.40 | `chartM_v140.py` | 804872b84609b1a715d25b0a19421b78 | 2 | a real s ball that still fails a width test is halved, and its halves again (depth 2 at most) |
| 1.41 | `chartM_v141.py` | 98197220660c5a0206ca57b619fc7bed | 10 | highest degree in gamma 20 -> 24 |
| 1.42 | `chartM_v142.py` | d12c2054bfb664b0c74ee7ab4fc1ea23 | 29 | highest degrees (20, 24, 32) -> (32, 32, 32) |
| 1.43 | `chartM_v143.py` | 8f8c2d880de9c1dfb46b08ca3dac2ceb | 80 | highest degrees -> (48, 48, 48) |
| | | | **168** | |

The 42 boxes with 0.53 <= gamma <= 1.571 ran versions 0.71 and 0.72; the 126 corner and row boxes ran versions 1.31 to
1.43. A highest degree only stops a cell that would need a larger one; it does not change a bound that is computed.
`programs/chartM_cover.py` (MD5 928bd9fc03fb648461e00ae510c2c004) lists the 168 boxes, proves that they cover the region,
and reads the logs (section 4).

## 2. A second evaluator: node values only

A second program with its own code (it uses only the Arb library, through python-flint, and nothing of the program above)
re-computed a sample of the values of phi_xi at the interpolation points ("node values"): every 20th logged node value in
65 boxes, every 40th in the other 103, and the first node of every cell in every box. A node passes when the ball it
computes overlaps the logged ball and its radius is at most the larger of 10^-9 and the logged radius. All 168 boxes pass.
This check covers NODE VALUES ONLY. It does not re-compute the bounds M_1, M_2, M_3, the interpolation remainders, the
polynomial maxima, the low pieces ("DEEP pieces" in the logs) or the small-depth bounds beta_B; those rest on the program of section 1 alone. The
proof in the paper does not use this check, and the program is not in this repository.

## 3. Two programs for gamma = 0 that the proof does not use

Two further programs certify Phi(s, 0, u) > 0 on the line gamma = 0 (equal depths), for s <= 0 (s >= 0 follows by
exchanging the poles). The proof does not use them: the nine corner boxes of the cover contain gamma = 0 (Section 6.1 of
the paper), and the program of section 1 certifies them. They are not in this repository.

## 4. How to verify

You need Python 3 and python-flint 0.9.0 (`pip install python-flint==0.9.0`); the program works at 96 bits. Run every
command from this folder.

1. The checksums: `sha256sum -c SHA256SUMS`
2. The cover: `python3 programs/chartM_cover.py --check` proves in exact rational arithmetic that the 168 boxes tile the
   region, and checks the three links between its parts in ball arithmetic. It exits 0 only if all hold.
3. The logs: `python3 programs/chartM_cover.py --status` gives the verdict of every log in `logs/`: PASS only if its first
   line names the checksums of an accepted version of the program and its result line says PASS. It exits 0 only if all
   168 pass.
4. One box again: `python3 programs/<driver> [--lambda] s_lo s_hi y_lo y_hi`, with the driver version that the box's log
   names and the box's edges as exact fractions (they are in the log's third line; a box whose third line says "lambda =
   log gamma" needs `--lambda`, and its y is lambda). It prints PASS and exits 0 only if every check succeeds; a failed
   check exits 1. Its output equals the box's log from the second line to the line before `rc=`, except the running time
   at the end of each cell line. It writes its node values into `logs/`. Each box runs as one process on one core;
   on our computer a box took between 1.9 and 17.9 hours (median 4.7 hours), about 1,140 core-hours for all 168.
