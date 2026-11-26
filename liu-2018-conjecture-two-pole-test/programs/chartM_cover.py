#!/usr/bin/env python3
# chartM_cover.py - P020 chart M, Program 1, COVER: the box list, its exact tiling check, units, status
##   centre boxes and the corner centre stopped at the cap 32) and ACCEPT v1.30, v1.31, v1.40, v1.41, v1.42 or v1.43. No other change.
##   s [25/27, 25/9] stopped on "gamma degree > 24", needs 25) and ACCEPT v1.30, v1.31, v1.40, v1.41 or v1.42. No other change.
##   their u-cell v [-11/2, -7/2] needed gamma degree >= 25-27, M_g 1e5-1e6; a half row needs 20, M_g 3.5e3, tune8 plans); the top
##   row, L_BOT, L_TOP, large and corner unchanged (117 lambda boxes, 168 in all). Lambda + corner RUN driver v1.41 (DEG_MAX gamma 24)
##   and ACCEPT v1.30, v1.31, v1.40 or v1.41.
##   width assert; lambda row 1 s [25/9, 125/27] stopped on one too-wide real s segment) and ACCEPT v1.30, v1.31 or v1.40. No other change.
##   row), then large. A finished lambda row is a reportable gamma band; the central-first orders finish no row by the clock. No other change.
##   assert; the first v1.30 lambda box stopped on one too-wide s-ball) and ACCEPT v1.30 or v1.31 (v1.30 stays first). No other change.
##   (d4cc7e5a: large runs v0.72, accepts v0.71 + v0.72); also the large line of the region table names v0.72. No other change.
##   (older version lines: versions/chartM_cover_version_0.91.py)
"""Usage: chartM_cover.py --check | --test | --status | --order large-first|small-first|rows-first | --done ARGS | --driver ARGS
   (ARGS = the driver's own words: [--lambda] s_lo s_hi y_lo y_hi)
The ONE source of truth for which certify boxes tile chart M (Program 1): s in [S_LO, S_HI] = [-25/3, 25/3] x gamma in [0, G_TOP].
  interface_v0.10.txt): lines 26-28: ratio min/max <= 2^-12 is covered by the accepted SM lemma, so r = a2/a1 in [2^-12, 2^12],
  |s| <= 12 log 2 = 8.3178 < 25/3; lines 36-46: chart M relabels so pole 1 is the shallower one and reflects z -> -conj(z) if
  needed, so 0 < gamma <= pi/2 (reflection preserves the normalized deficit). gamma in (pi/2, 1571/1000] is a mirror
  configuration: covering it is harmless. Rung [1] needs ALL of gamma in (0, pi/2].
  THREE REGIONS (a box = (s_lo, s_hi, y_lo, y_hi, gmap); y = gamma for "lin", y = lambda = log gamma for "log"):
    large  "lin" gamma in [G_SEAM, G_TOP] = [53/100, 1571/1000]            driver chartM_v072.py (v0.72; v0.71 logs accepted)
    lambda "log" lambda in [L_BOT, L_TOP] = [-1483/100, -63/100]    driver chartM_v143.py (v1.43; v1.30-v1.42 logs accepted)
    corner "lin" gamma in [0, G_CORNER] = [0, 2^-20]                 driver chartM_v143.py (v1.43; v1.30-v1.42 logs accepted)
  The regions OVERLAP at their seams (certified: e^L_TOP > G_SEAM and e^L_BOT < G_CORNER), so together they cover [0, G_TOP].
--check   exact (Fraction) proof that each region's boxes tile it (rows contiguous from its y_bot to its y_top, each row's s-boxes
          contiguous from S_LO to S_HI; a gap or an overlap breaks contiguity) + the certified (arb) links: 2 G_TOP > pi,
          e^L_TOP > G_SEAM, e^L_BOT < G_CORNER. Exit 0 iff all hold.
--status  per box: verdict of logs/cert_<tag>.log; PASS only under a DEPS quadruple in THAT REGION's ACCEPTED_DEPS. Exit 0 iff every
          box PASSES.
--done    exit 0 iff that box PASSES (same rule as --status); exit 10 iff it does not (yet) - a code Python never gives on its own
          (an uncaught exception or a failed import exits 1); exit 2 (loud) if the box is not in the cover; exit 3 (loud) on ANY
          error. run_cover.sh skips the boxes with exit 0, runs ONLY those with exit 10, stops on any other code. The arguments
          are the driver's own (v0.30 runners call it with 4 lin edges: unchanged).
--order   EVERY box whose region has a driver, one "driver tag args" line each, region by region (large-first: large, lambda,
          corner; small-first and rows-first: lambda, corner, large), central boxes first inside a region (large: the v0.30
          order) - except rows-first: lambda and corner row by row from the top row, central s first inside a row. Units do NOT
          split the list: run_cover.sh v0.60 CLAIMS a box (mkdir logs/claims/<tag>) before running it.
--driver  print the box's CURRENT driver file (its region's), exit 0; exit 2 (loud) if the box is not in the cover, 3 on any error.
          run_cover.sh v0.60 compares it with its list's driver before each box and STOPs on a mismatch (a list made under an
          older cover)."""
import re
import sys
from fractions import Fraction
from pathlib import Path

from flint import arb

S_LO, S_HI = Fraction(-25, 3), Fraction(25, 3)
G_SEAM, G_TOP = Fraction(53, 100), Fraction(1571, 1000)
L_BOT, L_TOP = Fraction(-1483, 100), Fraction(-63, 100)
L_ROW_WIDTH, N_LAMBDA_ROWS = Fraction(11, 10), 12      # v1.00: under the top row [-163/100, -63/100]: 12 rows of width 11/10 to L_BOT
G_CORNER = Fraction(1, 2 ** 20)
NOT_YET = 10                                            # --done "not (yet) PASS": the ONLY code on which run_cover.sh runs a box
N_S_SMALL = 9                                           # s-width 50/27: window_preflight passes on every lambda s-box (v0.90)
LOG_DIR = Path("logs")
ENGINE_ETC = ("78206e94", "9da5f00a", "6dbc509f")      # engine F_arb v1.30, cheb3 v0.20, backchain v0.50
SMALL_GAMMA_DEPS = {("8f7ff84d",) + ENGINE_ETC: "driver v1.30",
                    ("a4cd94be",) + ENGINE_ETC: "driver v1.31",
                    ("804872b8",) + ENGINE_ETC: "driver v1.40",
                    ("98197220",) + ENGINE_ETC: "driver v1.41",
                    ("d12c2054",) + ENGINE_ETC: "driver v1.42",
                    ("8f8c2d88",) + ENGINE_ETC: "driver v1.43"}
REGIONS = {
    "large": {"gmap": "lin", "y_bot": G_SEAM, "y_top": G_TOP, "driver": "chartM_v072.py",
              "rows": ((Fraction(53, 100), Fraction(1), 25), (Fraction(1), Fraction(1571, 1000), 17)),
              "accepted": {("41113685",) + ENGINE_ETC: "driver v0.71",
                           ("7309984f",) + ENGINE_ETC: "driver v0.72"}},
    "lambda": {"gmap": "log", "y_bot": L_BOT, "y_top": L_TOP, "driver": "chartM_v143.py",
               "rows": ((Fraction(-163, 100), L_TOP, N_S_SMALL),)
               + tuple((Fraction(-163, 100) - (kk + 1) * L_ROW_WIDTH, Fraction(-163, 100) - kk * L_ROW_WIDTH, N_S_SMALL)
                       for kk in range(N_LAMBDA_ROWS)),
               "accepted": SMALL_GAMMA_DEPS},
    "corner": {"gmap": "lin", "y_bot": Fraction(0), "y_top": G_CORNER, "driver": "chartM_v143.py",
               "rows": ((Fraction(0), G_CORNER, N_S_SMALL),), "accepted": SMALL_GAMMA_DEPS},
}
DEPS_LINE = re.compile(r"^DEPS driver ([0-9a-f]{8}) engine ([0-9a-f]{8}) cheb3 ([0-9a-f]{8}) backchain ([0-9a-f]{8})$", re.M)
BANNER = re.compile(r"driver md5 ([0-9a-f]{8}), engine md5 ([0-9a-f]{8}), cheb3 md5 ([0-9a-f]{8})")


def region_boxes(name):
    """Every box (s_lo, s_hi, y_lo, y_hi, gmap) of one region, row by row, s increasing."""
    region, out = REGIONS[name], []
    for y_lo, y_hi, n_s in region["rows"]:
        width = (S_HI - S_LO) / n_s
        out += [(S_LO + kk * width, S_LO + (kk + 1) * width, y_lo, y_hi, region["gmap"]) for kk in range(n_s)]
    return out


def boxes():
    """Every box of the cover, region by region."""
    return [box for name in REGIONS for box in region_boxes(name)]


def region_of(box):
    """The region name of a cover box (KeyError if the box is not in the cover)."""
    return {bb: name for name in REGIONS for bb in region_boxes(name)}[box]


def check_rows(box_list, y_bot, y_top):
    """Exact tiling check of one region's boxes; returns a list of problems (empty = they tile [S_LO, S_HI] x [y_bot, y_top])."""
    problems = []
    rows = sorted({(bb[2], bb[3]) for bb in box_list})
    if rows[0][0] != y_bot or rows[-1][1] != y_top:
        problems.append(f"rows span [{rows[0][0]}, {rows[-1][1]}], need [{y_bot}, {y_top}]")
    problems += [f"y gap/overlap at {lower[1]} vs {upper[0]}" for lower, upper in zip(rows, rows[1:]) if lower[1] != upper[0]]
    for y_lo, y_hi in rows:
        s_edges = sorted((bb[0], bb[1]) for bb in box_list if (bb[2], bb[3]) == (y_lo, y_hi))
        if s_edges[0][0] != S_LO or s_edges[-1][1] != S_HI:
            problems.append(f"row [{y_lo}, {y_hi}]: s spans [{s_edges[0][0]}, {s_edges[-1][1]}]")
        problems += [f"row [{y_lo}, {y_hi}]: s gap/overlap at {left[1]} vs {right[0]}" for left, right in zip(s_edges, s_edges[1:])
                     if left[1] != right[0]]
    return problems


def ex(value):
    """Exact rational -> arb (a ball containing it; exact when the denominator is a power of 2)."""
    return arb(value.numerator) / value.denominator


def check_links(l_bot, l_top):
    """Certified (arb) seam links; returns a list of problems. 2 G_TOP > pi: the large rows pass pi/2. e^l_top > G_SEAM: the lambda
    rows overlap the large rows. e^l_bot < G_CORNER: the lambda rows overlap the corner row."""
    problems = []
    if not 2 * ex(G_TOP) > arb.pi():
        problems.append(f"G_TOP = {G_TOP} not certified above pi/2")
    if not ex(l_top).exp() > ex(G_SEAM):
        problems.append(f"e^{l_top} not certified above G_SEAM = {G_SEAM}")
    if not ex(l_bot).exp() < ex(G_CORNER):
        problems.append(f"e^{l_bot} not certified below G_CORNER = {G_CORNER}")
    return problems


def check_tiling(box_list):
    """All problems of a candidate box list (empty = the regions tile and link up)."""
    problems, placed = check_links(L_BOT, L_TOP), 0
    for name, region in REGIONS.items():
        mine = [bb for bb in box_list if bb[4] == region["gmap"] and region["y_bot"] <= bb[2] and bb[3] <= region["y_top"]]
        placed += len(mine)
        problems += [f"{name}: {pp}" for pp in check_rows(mine, region["y_bot"], region["y_top"])] if mine else [f"{name}: no boxes"]
    if placed != len(box_list):
        problems.append(f"{len(box_list) - placed} box(es) in no region")
    return problems


ORDERS = {"large-first": ("large", "lambda", "corner"), "small-first": ("lambda", "corner", "large"),
          "rows-first": ("lambda", "corner", "large")}
ROWS_FIRST = ("rows-first",)   # v0.90: lambda and corner row by row from the top (a finished row = a reportable gamma band)


def region_key(name, order):
    """Sort key inside a region: large by (|s centre|, g_lo) as v0.30; lambda/corner by (|s centre|, top row first), or for a
    ROWS_FIRST order by (top row first, |s centre|)."""
    if name == "large":
        return lambda bb: (abs(bb[0] + bb[1]), bb[2])
    if order in ROWS_FIRST:
        return lambda bb: (-bb[3], abs(bb[0] + bb[1]))
    return lambda bb: (abs(bb[0] + bb[1]), -bb[3])


def order_boxes(order):
    """EVERY box with a driver, region by region in the ORDERS[order] sequence, sorted inside a region by region_key. Units do not
    split this list: run_cover.sh v0.60 CLAIMS each box (mkdir logs/claims/<tag>) before running it, so no two units ever run one
    box."""
    out = []
    for name in ORDERS[order]:
        if REGIONS[name]["driver"] is None:
            continue
        out += sorted(region_boxes(name), key=region_key(name, order))
    return out


def row_major(seq):
    """True iff seq runs row by row from the top row (y_hi never increases) and central s first inside each row."""
    return all((-aa[3], abs(aa[0] + aa[1])) <= (-bb[3], abs(bb[0] + bb[1])) for aa, bb in zip(seq, seq[1:]))


def tag(box):
    """Same tag rule as the driver's dump file name (lambda boxes: "L" prefix, driver certify v0.80+) and run_cover.sh's log name."""
    return ("L" if box[4] == "log" else "") + "_".join(str(edge).replace("/", "o") for edge in box[:4])


def driver_args(box):
    """The driver's command-line arguments for this box (the same words --done accepts)."""
    return (["--lambda"] if box[4] == "log" else []) + [str(edge) for edge in box[:4]]


def box_header(box):
    """The driver's own certify header for this box (chartM.certify prints it with str(Fraction) edges)."""
    y_text = f"gamma in [{box[2]}, {box[3]}]" if box[4] == "lin" else f"lambda = log gamma in [{box[2]}, {box[3]}]"
    return f"CHARTM box s in [{box[0]}, {box[1]}], {y_text}:"


def parse_log(text, box, accepted):
    """(verdict, detail) of one certify log. PASS only if ALL hold: the last CHARTM RESULT says PASS,
    the DEPS quadruple (written by run_cover.sh at box start) is in the box's region's ACCEPTED_DEPS (accepted) and the driver
    banner's (driver, engine, cheb3) agrees with it, the log ends with rc=0, and the log's own box header is this box."""
    deps, banner = DEPS_LINE.search(text), BANNER.search(text)
    quad = deps.groups() if deps else ("????????",) * 4
    md5 = quad[0]
    lines = text.rstrip().splitlines()
    results = [ln for ln in lines if ln.startswith("CHARTM RESULT")]
    if not results:
        ended = re.fullmatch(r"rc=(\d+)", lines[-1]) if lines else None   # C2: the runner's rc line = the driver has ended
        fails = [ln for ln in lines if ln.startswith("FAIL")]
        if ended:
            return f"FAILED rc={ended.group(1)}", f"md5 {md5} {fails[-1] if fails else 'no FAIL line'}"
        return "running/no result", f"md5 {md5}"
    verdict = re.search(r"-> (PASS|FAIL)$", results[-1])
    word = verdict.group(1) if verdict else "unparsed"
    if word == "PASS" and (quad not in accepted or not banner or banner.groups() != quad[:3]):
        word = "PASS-UNACCEPTED-MD5"
    elif word == "PASS" and text.rstrip().splitlines()[-1] != "rc=0":
        word = "PASS-NO-RC0"
    elif word == "PASS" and not any(ln.startswith(box_header(box)) for ln in text.splitlines()):
        word = "PASS-WRONG-BOX"
    return word, f"md5 {md5} {results[-1]}"


def box_status(box):
    path = LOG_DIR / f"cert_{tag(box)}.log"
    accepted = REGIONS[region_of(box)]["accepted"]
    return parse_log(path.read_text(encoding="utf-8"), box, accepted) if path.exists() else ("missing", "")


def parse_box_args(args):
    """The driver's own words ([--lambda] s_lo s_hi y_lo y_hi) -> box tuple; None if malformed."""
    gmap = "log" if args[:1] == ["--lambda"] else "lin"
    edges = args[1:] if gmap == "log" else args
    return tuple(Fraction(edge) for edge in edges) + (gmap,) if len(edges) == 4 else None


def main_check():
    problems = check_tiling(boxes())
    for name, region in REGIONS.items():
        print(f"REGION {name}: {len(region_boxes(name))} boxes ({region['gmap']}), rows "
              f"{[(str(lo), str(hi), nn) for lo, hi, nn in region['rows']]}, driver {region['driver']}")
    print(f"COVER {len(boxes())} boxes: {'TILES the region' if not problems else 'PROBLEMS: ' + '; '.join(problems)}")
    return not problems


def claim_text(box):
    """C2: the box's claim (logs/claims/<tag>/owner, first 60 characters), or '' if unclaimed."""
    owner = LOG_DIR / "claims" / tag(box) / "owner"
    return f" [claim: {owner.read_text(encoding='utf-8').strip()[:60]}]" if owner.exists() else ""


def main_status():
    counts = {}
    for box in boxes():
        verdict, detail = box_status(box)
        key = f"{region_of(box)} {verdict}"
        counts[key] = counts.get(key, 0) + 1
        claim = claim_text(box) if verdict != "PASS" else ""
        print(f"{region_of(box):<7} {' '.join(driver_args(box)):<44} {verdict:<20} {detail[-100:]}{claim}")
    print(f"STATUS {counts}")
    for name, region in REGIONS.items():
        print(f"  accepted (driver, engine, cheb3, backchain) for {name}: {region['accepted'] or 'NONE YET'}")
    return sum(nn for key, nn in counts.items() if key.endswith(" PASS")) == len(boxes())


def tiling_controls():
    """Red/green tiling controls: the cover tiles; dropped box, overlap, shifted row (large and lambda) and a broken seam link are
    caught."""
    lam = region_boxes("lambda")
    return {"cover tiles": not check_tiling(boxes()),
            "dropped box caught": bool(check_tiling(boxes()[1:])),
            "overlap caught": bool(check_tiling(boxes() + [boxes()[3]])),
            "shifted large row caught": bool(check_tiling([(bb[0], bb[1], bb[2] + (Fraction(1, 100) if bb[2] == 1 else 0), bb[3],
                                                            bb[4]) for bb in boxes()])),
            "dropped lambda box caught": bool(check_tiling([bb for bb in boxes() if bb != lam[20]])),
            "lambda gap caught": bool(check_tiling([bb if bb[3] != Fraction(-163, 100) else (bb[0], bb[1], bb[2], Fraction(-2),
                                                                                               bb[4]) for bb in boxes()])),
            "stray box caught": bool(check_tiling(boxes() + [(S_LO, S_HI, Fraction(1, 10), Fraction(1, 5), "lin")])),
            "seam link caught": bool(check_links(L_BOT, Fraction(-64, 100))),     # e^-0.64 = 0.5273 < 53/100
            "corner link caught": bool(check_links(Fraction(-1386, 100), L_TOP))}   # e^-13.86 = 9.6e-7 > 2^-20 = 9.54e-7


def parse_controls():
    """Red/green parse_log controls: PASS only under the box's OWN region's accepted quadruple, banner, rc=0 and header."""
    large_quad, lam_quad = next(iter(REGIONS["large"]["accepted"])), next(iter(REGIONS["lambda"]["accepted"]))
    box, other, lbox = region_boxes("large")[0], region_boxes("large")[1], region_boxes("lambda")[0]
    bad_backchain = large_quad[:3] + ("0123abcd",)
    result = "CHARTM RESULT: Phi_lo(e^-27/2) >= +0.01, after deep pieces +0.01, u_b = 1e-9, prefix <= 1e-4, Phi(0+) >= +0.01 -> "

    def fake(quad, banner_quad, header_box, verdict, tail):
        return (f"DEPS driver {quad[0]} engine {quad[1]} cheb3 {quad[2]} backchain {quad[3]}\nchartM v0.71 (driver md5 "
                f"{banner_quad[0]}, engine md5 {banner_quad[1]}, cheb3 md5 {banner_quad[2]}, prec 128)\n"
                f"{box_header(header_box)} rho_s 5/2\n{result}{verdict}{tail}")
    large_acc, lam_acc = REGIONS["large"]["accepted"], REGIONS["lambda"]["accepted"]
    cases = [("PASS", fake(large_quad, large_quad, box, "PASS", "\nrc=0\n"), box, large_acc),
             ("PASS-UNACCEPTED-MD5", fake(bad_backchain, bad_backchain, box, "PASS", "\nrc=0"), box, large_acc),
             ("PASS-UNACCEPTED-MD5", fake(large_quad, bad_backchain[:2] + ("0123abcd", "x"), box, "PASS", "\nrc=0"), box, large_acc),
             ("PASS-UNACCEPTED-MD5", f"{box_header(box)}\n{result}PASS\nrc=0", box, large_acc),
             ("PASS-NO-RC0", fake(large_quad, large_quad, box, "PASS", "\nrc=1"), box, large_acc),
             ("PASS-WRONG-BOX", fake(large_quad, large_quad, other, "PASS", "\nrc=0"), box, large_acc),
             ("FAIL", fake(large_quad, large_quad, box, "FAIL", "\nrc=1"), box, large_acc),
             ("running/no result", "DEPS ...\nCELL ...", box, large_acc),
             ("FAILED rc=1", "DEPS ...\nCELL ...\nFAIL: s degree > 20 needed: shrink the box or the cell\nrc=1\n", box, large_acc),
             ("running/no result", "DEPS ...\nFAIL: a line that is not the end\nCELL ...", box, large_acc),
             ("PASS", fake(lam_quad, lam_quad, lbox, "PASS", "\nrc=0"), lbox, lam_acc),
             ("PASS-UNACCEPTED-MD5", fake(large_quad, large_quad, lbox, "PASS", "\nrc=0"), lbox, lam_acc),     # v0.71 on a lambda box
             ("PASS-UNACCEPTED-MD5", fake(lam_quad, lam_quad, box, "PASS", "\nrc=0"), box, large_acc),        # v1.00 on a large box
             ("PASS-UNACCEPTED-MD5", fake(lam_quad, lam_quad, lbox, "PASS", "\nrc=0"), lbox, {}),             # corner: none accepted
             ("PASS-WRONG-BOX", fake(lam_quad, lam_quad, region_boxes("lambda")[9], "PASS", "\nrc=0"), lbox, lam_acc)]
    return {"parse_log region rule": all(parse_log(text, bb, acc)[0] == want for want, text, bb, acc in cases)}


def cli_controls():
    """Red/green CLI controls: --done words round-trip for every box, a non-cover box is refused (--done 2, --driver 2), malformed
    words give 3, each order lists EVERY box once with its regions in the ORDERS sequence, the large region keeps the v0.30
    central-first order, --driver names the region's driver."""
    v030_order = sorted(region_boxes("large"), key=lambda bb: (abs(bb[0] + bb[1]), bb[2]))
    region_runs = {order: [region_of(bb) for kk, bb in enumerate(order_boxes(order))
                           if kk == 0 or region_of(bb) != region_of(order_boxes(order)[kk - 1])] for order in ORDERS}
    return {"args round-trip": all(parse_box_args(driver_args(bb)) == bb for bb in boxes()),
            "non-cover box refused": not any(parse_box_args(["0", "1", "1", "2"]) == bb for bb in boxes()),
            "--done codes 2/3/10": (main_done(["0", "1", "1", "2"]) == 2 and main_done(["1/3", "1", "53/100", "x"]) == 3
                                    and main_done(driver_args(region_boxes("corner")[0])) == NOT_YET),
            "--driver codes 2/3": main_driver(["0", "1", "1", "2"]) == 2 and main_driver(["1/3", "1", "53/100", "x"]) == 3,
            "orders list every box once": all(sorted(order_boxes(order)) == sorted(boxes()) for order in ORDERS),
            "orders keep region sequence": all(tuple(region_runs[order]) == ORDERS[order] for order in ORDERS),
            "large order = v0.30": [bb for bb in order_boxes("large-first") if region_of(bb) == "large"] == v030_order,
            "rows-first lambda row-major (small-first is not)":
                row_major([bb for bb in order_boxes("rows-first") if region_of(bb) == "lambda"])
                and not row_major([bb for bb in order_boxes("small-first") if region_of(bb) == "lambda"]),
            "rows-first large = v0.30": [bb for bb in order_boxes("rows-first") if region_of(bb) == "large"] == v030_order,
            "tags unique": len({tag(bb) for bb in boxes()}) == len(boxes())}


def main_test():
    results = tiling_controls() | parse_controls() | cli_controls()
    print("TEST " + ", ".join(f"{name} {ok}" for name, ok in results.items()))
    return all(results.values())


def main_order(order):
    for box in order_boxes(order):
        print(f"{REGIONS[region_of(box)]['driver']} {tag(box)} {' '.join(driver_args(box))}")


def main_done(args):
    """Exit code for --done: 0 PASS, NOT_YET not (yet) PASS, 2 not a cover box (loud), 3 ANY error (loud; v0.50, R1: an
    unreadable log must never read as "not done", which would make the runner re-run an accepted box)."""
    try:
        box = parse_box_args(args)
        if box is None or box not in set(boxes()):
            print(f"--done: {' '.join(args)} is NOT a box of this cover", file=sys.stderr)
            return 2
        return 0 if box_status(box)[0] == "PASS" else NOT_YET
    except Exception as err:   # noqa: BLE001 - every failure must stop the runner
        print(f"--done: ERROR {type(err).__name__}: {err}", file=sys.stderr)
        return 3


def main_driver(args):
    """Exit code for --driver (prints the box's current driver on stdout): 0 printed, 2 not a cover box (loud), 3 ANY error (loud)."""
    try:
        box = parse_box_args(args)
        if box is None or box not in set(boxes()):
            print(f"--driver: {' '.join(args)} is NOT a box of this cover", file=sys.stderr)
            return 2
        print(REGIONS[region_of(box)]["driver"])
        return 0
    except Exception as err:   # noqa: BLE001 - every failure must stop the runner
        print(f"--driver: ERROR {type(err).__name__}: {err}", file=sys.stderr)
        return 3


def main():
    args = sys.argv[1:]
    if args == ["--check"]:
        sys.exit(0 if main_check() else 1)
    if args == ["--status"]:
        sys.exit(0 if main_status() else 1)
    if args == ["--test"]:
        sys.exit(0 if main_test() else 1)
    if len(args) == 2 and args[0] == "--order" and args[1] in ORDERS:
        main_order(args[1])
        sys.exit(0)
    if args[:1] == ["--done"]:
        sys.exit(main_done(args[1:]))
    if args[:1] == ["--driver"]:
        sys.exit(main_driver(args[1:]))
    sys.exit(__doc__)


if __name__ == "__main__":
    main()
