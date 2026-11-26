#!/usr/bin/env python3
# chartM.py - P020 P7 chart M BACKWARD certificate on a parameter box (s = log r, gamma) by 3D tensor cells
##   = the old cap exactly in its central cell v [-11/2, -7/2] (plan tune8: M_g 3.5e3, degrees (16, 20, 20)); the cap only stops a
##   cell, a higher one adds nodes only where a cell needs them. No other change.
##   (rc=1, u-cell [-15/2, -11/2], M_g) on "a partner point may touch or cross R" - the whole real s segment (a = 1/(1+e^s) varies
##   6x) widens the partner ball; its two s-halves pass (domprobe131: all 4 row-1 boxes with s >= 25/27 refused at SUB_S 1, none at
##   2). split_sup: on the M_g and M_y axes, a real s ball whose refined_sup still fails a WIDTH_ASSERTS check is re-evaluated on
##   its ball_halves, to S_SPLIT_DEPTH; at depth 0 the assert stays loud. No other change.
##   -11/2], M_s) on "contour piece ... meets the cut of point [+/- 0.321] + [+/- 0.346]j" for ONE whole s-cover ball; its 4
##   quarters all pass (g_sup <= 0.89). refined_sup now treats an engine/driver ENCLOSURE-WIDTH assert (WIDTH_ASSERTS) on a ball at
##   depth > 0 like a large value: it refines; at depth 0 the assert stays loud. No other change.
##   each y-node) + N_U_CELLS 5 (deep part from e^-19/2, not e^-27/2: measured deep pieces ~230 u at K 4)
##   (they cover it; POINTS FORM needs only some cover), to REFINE_DEPTH; value = min(whole, max of quarters); REFINE control
##   WINDOWS boxes' deep packets use the REAL-LINE zero-following frame (real_window_frame: the contour IS R) bounded with H_wc
##   (wc_majorant_on_pieces), plain contour where the frame cannot be built; corner deep gamma cuts geometric from u (deep_gamma_edges);
##   depths from ENDPOINTS (depth_of: bilinear, valid on the whole ball, no clamp); controls R1-R3 + corner packets in the verdict
##   (older version lines: versions/chartM_version_0.71.py; 0.80 line: candidates/snap_v130/chartM.py; 0.90 and
##   1.00 lines: chartM_v131.py)
"""Usage: chartM.py --test | --plan s_lo s_hi g_lo g_hi | s_lo s_hi g_lo g_hi     (exact rationals; s = log r)
CLAIM CERTIFIED (PASS, exit 0): Phi(s, gamma, u) := Def0/A^2 - k0 > 0 for EVERY s in [s_lo, s_hi], gamma in [g_lo, g_hi] and EVERY
depth u > 0, in the normalized chart M of ASSEMBLY Sec. 1 (pole 1, mass a = 1/(1 + e^s), at -i u; pole 2, mass b = 1 - a, at
cos(gamma) - i(sin(gamma) + u)). Any failed check exits 1.
1. ANCHOR. W_CELL on (default): Lemma W0 (NOTE_chartM_wcell Sec. 1): Phi(u) >= (D1 - k0) - int_u^oo f (FLUX + CLUSTER-W with
   T -> oo), so A = D1 - k0 exactly and the W-CELL (1b) covers every u >= U0 = e^V_W. W_CELL off (v0.50 path): CLUSTER-W at
   T = e^V_TOP: Phi(., T) >= A_T = (D1 - k0) - 4.05 s_T^2/(1 - s_T) (s_T <= 1/T, ab <= 1/4).
1b. W-CELL (NOTE Sec. 2-3): w = 1/u = w0 (1 - y)/2, w0 = e^-V_W; g_w(x, z, y) = (w0/2) h(w), h(w) = u^2 f(u) = f_dil(w)/w (W1:
   dilation), analytic where every point of C_dil(w) (-i, -i + w e, -i + a w e, e = e^{-i gamma}) is below R and every partner above
   (W2: |q| < 1 for each offset q); w_rhos checks the filled ellipses exactly (|q| <= W_MARGIN) and make_config re-asserts the
   domain on every evaluated ball. int_y^1 g_w = int_{u(y)}^oo f, so the suffix / G / E machinery of 2 applies unchanged. Node
   values (w0/2) u_k^2 f(u_k) by eng.flux_enclosure (u-frame, u_k = 1/w_k > 0); majorants: (w0/2) sup|f_dil| / (certified lower
   bound of |w| on the evaluated ball; must be > 0, else FAIL: the curve avoids w = 0).
2. CELLS (ASSEMBLY 10B, 10C choice (i)): v in [c - 1, c + 1], c = V_TOP - 1 - 2k (W_CELL: V_W in place of V_TOP), y = v - c
   (h = 1). g(x, z, y) = e^v f(s, gamma,
   e^v) with s = s_c + s_h x, gamma = g_c + g_h z. P = tensor interpolant at first-kind nodes of POINT flux balls (eng.flux_enclosure;
   node errors ride in the ball coefficients), cheb3 v0.20. On the real cube |g - P| <= R = R_y + L_y R_g + L_y L_g R_s
  , R_j = 4 M_j rho_j^-d_j/(rho_j - 1), L = 1 + (2/pi) log(d + 1).
   POINTS FORM (v0.60): the telescoping is (g - I_y g) + I_y (g - I_g g) + I_y I_g (g - I_s g), and I_y h = sum_k l_k(y) h(., ., y_k),
   so the 2nd and 3rd terms see g only at the y-NODES y_k. Hence M_y >= sup |g| over (y on its ellipse CURVE) x (s, gamma on their
   WHOLE real segments); M_g >= sup over (gamma curve) x (s segment) x (y in {y_k}); M_s >= sup over (s curve) x (gamma segment) x
   (y in {y_k}) (the gamma segment contains the gamma-nodes). For each fixed real value of the other axes, g is analytic on the
   FILLED ellipse (Sec. 3), so the curve bounds it there (maximum principle).
   Suffix: int_y^1 g <= S(y) + 2R, S = A(1) - A(y); full cell <= F + 2R (F = A(1) - A(-1), a 2D polynomial). G = sum of earlier
   F's stays a 2D POLYNOMIAL in the SAME scaled (x, z) for every cell, E = sum of their 2R's. CHAIN-UP floor of cell k:
   A_T - E - 2R_k - max_{x,z,y} [G + S_k] > 0 (certified branch-and-bound maximum, cheb3.poly_max_3d).
3. ANALYTIC DOMAIN on the filled ellipses (checked EXACTLY in assert_filled_domain, then again per cover ball by make_config's
   real-contour assert: every point below R, every partner above R on the whole ball). zero = a e^{-i gamma} - i u.
   s-axis (gamma, u real): |phi| <= |Im s| < g_lo with phi = arg a (adding 1 to e^s moves the argument toward 0), and
   g_hi + |Im s| < pi, so Im zero = -(|a| sin(gamma - phi) + u) < 0 and Im zero# = |a| sin(gamma + phi) + u > 0; poles do not move.
   gamma-axis (s, u real): 0 < Re gamma < pi gives Im p2 = -(sin(Re g) e^{Im g} + u) < 0, Im p2# = sin(Re g) e^{-Im g} + u > 0,
   and the zero (real a in (0, 1)) likewise. y-axis (s, gamma real): |Im y| < pi/2 gives Re u > 0.
   With all points below and partners above R, every constant-log argument (p - r#, r# - p, p# - r, r - p#) stays in its own open
   half-plane, where engine v1.20+'s fixed-branch logs are analytic: no window is needed for these boxes.
3b. MAJORANT INTEGRAND. f = (1/pi) int_R [H - 2ab D1(x; pbar, pbar#)] dx with pbar = a p1 + b p2, pbar# = a p1# + b p2# (the mass
   centre; for real parameters pbar# = conj pbar) and D1(z; p, p#) = (1/4) T_pp T#_pp - k0/((z - p)(z - p#)), the UNIT one-pole
   density (|r|^2 - k0|S|^2 of one pole: the engine's single_integrand). EXACT: int_R D1(x; p, conj p) dx = 0 for every p below R
   (one pole's Def0 is D1 at every depth: the identity behind the engine's removal of the single-pole parts), and
   (p, p#) -> int_R D1 is analytic on {Im p < 0 < Im p#} and vanishes on the totally real set p# = conj p, hence everywhere there.
   pbar below / pbar# above R on the ball: pbar = -i u + b e^{-i gamma} is the zero with a <-> b swapped (same Sec. 3 argument,
   |arg b| <= |Im s|), and every rotated log argument is asserted in rot_log anyway. At merged poles H = 2ab D1(z; pbar) exactly,
   so this removes the leading part that only cancels in the integral; f itself (node values) is unchanged.
   T's difference quotients are evaluated as E(w)/beta (dd_log) to keep their cancellation on parameter balls.
3c. MC1 (NOTE Sec. 4; v0.60). Mass-centre path p_j(t) = pbar + t d_j (d_1 = -b D, d_2 = a D, zero d_0 = (a - b) D, D = p2 - p1;
   partners with D#): H(0) = H_0 = 2ab D1(pbar), first-order H_1 = ab(a - b)(D d/dp + D# d/dp#) D1(pbar), int H_0 = int H_1 = 0. So
   sup|f| <= (1/pi)[sum_panels width (sum_{k=2}^{K-1} |H_k| + |H^(K)(t in [0,1])|/K!) + tail(H) + tail(H_0) + tail(H_1)], the
   t-series from acb_series in t (at t = 0 and at the t-ball [0, 1]: Taylor with integral remainder); tail(H_1) by Cauchy in t on
   the box |Re t|, |Im t| <= MC1_DISC: |H_1(x)| <= sup_t |H(x; t)|/MC1_DISC, and eng.tail_bound is a pointwise envelope for the
   whole ball. mc1_sup returns None (logged, counted) if any panel's series evaluation leaves the domain; sup_f_cfg takes the
   MIN of the plain and the MC1 totals (both valid upper bounds of sup|f|).
3d. S-WINDOWS (v0.80; WINDOWS boxes = lambda boxes and the corner; u-cell M_s only). Only M_s sees complex s: nodes, M_g, M_y and
   the deep pieces are at REAL s (real contour, asserted by make_config; sup_f_windowed never windows them), and the W-CELL needs
   none (|a| < 1 on the strip keeps every offset |q| < 1). |Im s| < pi/2 => a = 1/(1 + e^s) in the disc D = {|a - 1/2| < 1/2}
   (Re e^s > 0): 0 < Re a < 1, |a| < 1. At real gamma, u: zero z0 = a e^{-i gamma} - i u = sigma - i delta, partner z0# =
   a e^{i gamma} + i u = sigma + i delta, sigma = a cos(gamma), delta = nu + u, nu = a sin(gamma), Re delta = Re(a) sin(gamma) + u
   > 0. delta is COMPLEX: Re z0 = Re sigma + Im nu, Re z0# = Re sigma - Im nu.
   LEMMA A (admissible contours; fixed s in the strip). H(z) (the engine's fixed-branch integrand) is analytic off the vertical
   cuts: DOWN from each point (p1, p2, z0), UP from each partner. Admissible = equal to R outside [-X, X] (X = xcut >= 4 |points|,
   so every cut meets R inside [-X, X]) and meeting no cut. (a) All admissible contours give the same integral: the cuts are
   closed rays to infinity, so their complement Omega is simply connected, and the loop (one contour minus the other) lies in it.
   (b) Omega is connected and an admissible contour exists iff no point lies DIRECTLY ABOVE a partner (same Re, Im point >= Im
   partner). On D this never happens: z0 over p1# needs a e^{-i gamma} in iR+ with Im >= 2u (Re a <= 0; equality at gamma = 0,
   needs a = -i t e^{-i gamma}, t >= 2u (Re a <= 0); p2 over z0# needs a = e^{-2i gamma} - i t e^{-i gamma}, t >= 0 (|a| >= 1); z0 over z0# needs Im nu = 0, and then
   Im z0 < Im z0# (Re delta > 0); poles and their partners are real-parameter, fixed. The fixed-branch CONSTANT logs (c1, c2, c1s,
   c2s of every pair) reach their imaginary-axis cuts exactly in these "point over partner" cases, so they are analytic on D too.
   (c) The common value G(s) is analytic in s: near s0 freeze an admissible contour of s0 (rays move continuously), and the
   frozen integral (tails ~ log^2|x|/x^2 uniformly) is analytic. (d) G = F at real s (R admissible). Hence G is F's continuation
   to the strip, and ANY contour certified admissible on a parameter ball gives |F| bounds there.
   CONSTRUCTION (window_frame_m; u-FREE). If |Im sigma| < Re delta is certified, the real contour (v0.71). Else: CROSSING feet =
   that of z0 if Im sigma - Re nu may be > 0, that of z0# if Im sigma + Re nu may be < 0 (worst case u -> 0) - only their rays can
   reach R or the junction heights. A, B = min, max of {crossing feet, Re sigma}; gap (L, Rt) = (A (1 - r), B + r (cos gamma - B)),
   r = WINDOW_REACH; junctions L -> L + off, Rt -> Rt + off (off = sigma - m, m = Re sigma rounded, exact); window sigma + [L - m,
   Rt - m], height Im sigma (above z0 and below z0# at EVERY x). Asserted: L - |Re off| > 0, Rt + |Re off| < cos gamma (the poles'
   rays at Re 0, cos gamma), every crossing foot in (L + |Re off|, Rt - |Re off|). ADMISSIBILITY is then certified piece by piece:
   eng.branch_check on every outside, junction and window piece for the whole parameter ball (eng.majorant_on_pieces); the window
   in the sigma-translated frame (engine v1.30 shift=: zero exactly at -i delta, constants from unshifted points). Maximum
   principle: F analytic on the strip, the filled s-ellipse + squares inside |Im s| <= pi/2 - STRIP_MARGIN (assert_filled_domain).
   window_preflight (make_box): the largest rho_s whose M_s cover balls (COVER_S_WINDOW per curve, SUB_G_WINDOW gamma sub-balls)
   all have certified Re a > 0 and a constructible frame (14:38: every s-box of three lambda rows passes at rho_s 5/2 or 11/5).
   Controls (--test, can fail): W1 (real contour valid, a foot crossing as u -> 0): gap reach 1/2, 1/4 and the real contour
   53/100, u 1e-8 (complex delta moves the crossing foot): reach 1/2, 1/4 agree; W3 the mean of F over |s - 3/10| = 1 (mostly
   windowed) = F(3/10).
3e. GAMMA MAPS (v0.80). lin: gamma = g_c + g_h z (v0.71). log (--lambda, edges exact in lambda = log gamma): gamma = e^{l_c + l_h z}.
   -(u + e^{Im g} sin(Re g)) < 0 and partner/zero alike at EVERY u > 0; asserted on the filled ellipse + squares (|Im lambda|
   < pi/2, |gamma| <= e^{Re lambda} < pi). W-CELL: |Im gamma| <= e^{Re lambda max} |Im lambda| max (im_gamma_reach). CORNER
   (lin, g_lo = 0): Re gamma >= -r on the gamma-ellipse, so each u-cell needs u_lo > sin(r) e^{|Im g| max} (corner_reach, else
   FAIL); deep pieces are real. Prefix: sin(gamma) < 1/2 there, so prefix_bound uses UNIFORM-ABS only (v0.71 rule).
4. DEEP PART below V_BOT: unit pieces [e^(v-1), e^v], CELL-UP with U = V = length x max over K x K exact (s, gamma) sub-boxes
   of sup|f| on the REAL u-piece ball (v0.70: K adaptive in DEEP_SUB; real parameters satisfy the real-contour domain).  5. PREFIX (0, u_b]: min(UNIFORM-ABS, MIXED-EDGE if H >= 1/2).
Engine: F_arb.py (IMPORT ONLY, never edited here)."""
import hashlib
import json
import math
import sys
import time
from fractions import Fraction
from flint import acb, acb_series, arb, ctx

sys.dont_write_bytecode = True
import F_arb as eng  # noqa: E402
import backchain as bc  # noqa: E402
import cheb3 as c3  # noqa: E402

VERSION = "1.41"     # printed in every run header (--test too) and in the dump file name
W_CELL = True        # v0.60: W-CELL on top (anchor D1 - k0 exactly); False = v0.50 path (CLUSTER-W anchor at e^V_TOP)
V_TOP = 4
V_W = Fraction(1, 2)  # W-CELL covers u >= e^V_W (w0 = e^-V_W = 0.6065); u-cells start below it
N_U_CELLS = 5 if W_CELL else 12   # v1.30: 5 u-cells to -19/2 (v0.70: 7 to -27/2); crude sub-boxed pieces below (~230 u at K 4)
DEEP_SUB = (1, 2, 4)              # deep pieces: K x K (s, gamma) sub-boxes, first K whose decrement <= DEEP_PIECE_TARGET
DEEP_PIECE_TARGET = Fraction(1, 4000)
V_BOT = (V_W if W_CELL else V_TOP) - 2 * N_U_CELLS   # u-cells cover [V_BOT, top]; crude unit pieces below (07:53: a crude piece
                     # at e^[-14,-13] on the box s [-1/2, 1/2] x gamma [1, 3/2] has sup|f| <= 2481 -> 3.5e-3: too big above ~e^-20)
RHO_W_CHOICES = (Fraction(5), Fraction(4), Fraction(3), Fraction(5, 2), Fraction(2), Fraction(3, 2))   # largest passing w_rhos
MC1_K = 3            # MC1 t-series order: |H_2| + |H^(3)(t-ball)|/3!
MC1_DISC = Fraction(1, 2)   # Cauchy box in t for the tail of H_1
MC1_U_CELLS = False  # MC1 in the u-cells too (pays only at u >~ 5, i.e. never below V_W; ~3x cost)
RHO_Y = Fraction(5, 2)
RHO_G = Fraction(5, 2)
RHO_S_CHOICES = (Fraction(5, 2), Fraction(11, 5), Fraction(2), Fraction(9, 5), Fraction(8, 5), Fraction(3, 2))
COVER = 32
W_MARGIN = Fraction(7, 8)   # W-CELL ellipses keep every offset |q| <= W_MARGIN (W2 needs < 1; margin keeps M moderate)
CELL_TARGET = Fraction(1, 1000)
DEG_MAX = (20, 24, 32)   # v1.41: gamma 20 -> 24 (half lambda rows need 20 in a central cell)
MAX_TOL = Fraction(1, 50000)
PREFIX_TARGET = Fraction(1, 2000)
IM_S_SHARE = Fraction(4, 5)   # s-ellipse: |Im s| (with cover radius) <= IM_S_SHARE * g_lo
LOG = []


def ex(num):
    return eng.exact(num)


def fail(message):
    print(f"FAIL: {message}", flush=True)
    sys.exit(1)


STRIP_MARGIN = Fraction(1, 8)   # WINDOWS boxes: the s-ellipse (+ square covers) keeps |Im s| <= pi/2 - STRIP_MARGIN
COVER_S_WINDOW = 64   # WINDOWS boxes, u-cell M_s: cover balls on the s-ellipse curve (smaller balls keep Re sigma tight: Sec. 3d)
SUB_G_WINDOW = 4      # WINDOWS boxes, u-cell M_s: real gamma sub-balls (the cos(gamma) spread widens Re sigma)


def make_box(s_lo, s_hi, g_lo, g_hi, gmap="lin"):
    """Box record. gmap "lin": gamma = g_c + g_h z on [g_lo, g_hi]; "log" (v0.90): lambda = log gamma = l_c + l_h z on the EXACT
    lambda-edges [g_lo, g_hi] (Sec. 3e). WINDOWS (log boxes and the corner g_lo = 0): complex s uses zero-following windows (Sec. 3d),
    so rho_s only keeps the strip |Im s| < pi/2; else rho_s keeps |Im s| <= IM_S_SHARE g_lo (real contour, v0.71)."""
    box = {"map": gmap, "s": (s_lo, s_hi), "s_c": (s_lo + s_hi) / 2, "s_h": (s_hi - s_lo) / 2,
           "windows": gmap == "log" or g_lo == 0}
    key = "g" if gmap == "lin" else "l"
    box.update({key: (g_lo, g_hi), key + "_c": (g_lo + g_hi) / 2, key + "_h": (g_hi - g_lo) / 2})
    limit = arb.pi() / 2 - ex(STRIP_MARGIN) if box["windows"] else ex(IM_S_SHARE * g_lo)
    for rho in RHO_S_CHOICES:
        if ex(box["s_h"]) * (minor(rho) + SQRT2 * cover_radius(rho)) <= limit and window_preflight(box, rho):
            box["rho_s"] = rho
            return box
    fail(f"s half-width {box['s_h']} too large for its s-domain (windows {box['windows']}, g_lo = {g_lo})")


def window_preflight(box, rho):
    """WINDOWS boxes: True iff on EVERY cover ball of the s-ellipse curve (the balls M_s evaluates) Re a > 0 is certified (so Re delta
    > 0 at every u > 0) and window_frame_m succeeds for each gamma sub-ball (SUB_G; the frame depends on sigma = a cos(gamma) only,
    not on u). 14:27: far-s boxes (a ~ e^-s) fail at large |Im s|, where a turns nearly imaginary and Re sigma -> 0. Lin boxes with
    g_lo > 0 (real contour): always True."""
    if not box["windows"]:
        return True
    for zc, radius in bc.ellipse_cover(ex(rho), COVER_S_WINDOW):
        amass = 1 / (1 + s_at(box, complex_ball(zc, radius)).exp())
        if not amass.real.lower() > 0:
            return False
        for gg in gamma_segments(box, SUB_G_WINDOW):
            if not crossing_feet(amass, acb(gg))[1]:
                continue   # the real contour is valid at every u > 0 on this ball
            try:
                window_frame_m(amass, acb(gg))   # u-free by construction (crossing feet decided at the worst case u -> 0)
            except AssertionError:
                return False
    return True


def box_text(box):
    """The box's gamma range as printed in the certify header (lin boxes: exactly the v0.71 text, which cover --status parses)."""
    if box["map"] == "lin":
        return f"gamma in [{box['g'][0]}, {box['g'][1]}]"
    return f"lambda = log gamma in [{box['l'][0]}, {box['l'][1]}]"


def gamma_ends(box):
    """(gamma_lo, gamma_hi) as arb (exact for lin; exp of the exact lambda-edges for log)."""
    if box["map"] == "lin":
        return ex(box["g"][0]), ex(box["g"][1])
    return ex(box["l"][0]).exp(), ex(box["l"][1]).exp()


def gamma_segments(box, count):
    """The real gamma range in `count` real balls whose union contains it (log: exp of exact lambda sub-balls)."""
    if box["map"] == "lin":
        return sub_segments(box, "g", count)
    lo, hi = box["l"]   # exp is increasing: the image of [l_a, l_b] is [e^l_a, e^l_b], enclosed from its endpoints (v1.00; the Arb
    edges = [lo + (hi - lo) * Fraction(jj, count) for jj in range(count + 1)]   # exp of a wide ball is symmetric and went < 0)
    return [span(ex(aa).exp().lower(), ex(bb).exp().upper()) for aa, bb in zip(edges[:-1], edges[1:])]


DEEP_G_RATIO_LOG2 = 2   # v1.10: corner deep pieces cut gamma at g_hi 4^-j (pole 2's depth varies by a factor <= ~5 per cut)


def deep_gamma_edges(box, u_top):
    """Exact gamma edges of a CORNER deep piece with u <= u_top (v1.10): 0, g_hi 4^-J, ..., g_hi 4^-1, g_hi with J the largest j such
    that g_hi 4^-j >= u_top (J = 0 if g_hi < u_top). Pole 2's depth sin(gamma) + u then varies by a factor <= ~5 on each cut
    [g_hi 4^-(j+1), g_hi 4^-j] and <= ~e (4 + 1) on the bottom cut [0, g_hi 4^-J], instead of ranging over [u, g_hi + u] on one ball
    (whose integrand envelope ~ 1/x over that range inflates the bound, and whose depth cannot be certified > 0 once u < ~1e-15).
    Any edges give a valid cover (contiguous exact rationals from 0 to g_hi); the float J only places them."""
    g_hi = box["g"][1]
    ratio = 2 ** DEEP_G_RATIO_LOG2
    levels = max(0, math.floor(math.log(float(g_hi) / float(u_top.upper()), ratio)))
    return [Fraction(0)] + [g_hi / ratio ** jj for jj in range(levels, -1, -1)]


def deep_gamma_segments(box, count, u_top):
    """Real gamma balls whose union contains the box's gamma range, for a deep piece with u <= u_top: CORNER boxes (lin, g_lo = 0) cut
    geometrically (deep_gamma_edges), each cut in `count` equal exact parts; other boxes: gamma_segments (unchanged)."""
    if not (box["map"] == "lin" and box["g"][0] == 0):
        return gamma_segments(box, count)
    edges = deep_gamma_edges(box, u_top)
    return [eng.box(aa + (bb - aa) * Fraction(jj, count), aa + (bb - aa) * Fraction(jj + 1, count))
            for aa, bb in zip(edges[:-1], edges[1:]) for jj in range(count)]


def minor(rho):
    return (ex(rho) - 1 / ex(rho)) / 2


def major(rho):
    return (ex(rho) + 1 / ex(rho)) / 2


def cover_radius(rho):
    """bc.ellipse_cover radius in the scaled coordinate: (pi/COVER) * semi-major."""
    return arb.pi() / COVER * major(rho)


SQRT2 = arb(2).sqrt()   # cover balls are SQUARES of half-side cover_radius: a point moves by up to sqrt(2) cover


def assert_filled_domain(box):
    """Sec. 3 conditions on the FILLED ellipses plus square covers (exact arithmetic; strict). s-axis: real contour (|Im s| < g_lo,
    g_hi + |Im s| < pi) or, WINDOWS, the strip |Im s| < pi/2 (Sec. 3d). gamma-axis: lin with g_lo > 0: 0 < Re gamma < pi; the corner
    (lin, g_lo = 0) is checked PER u-CELL (corner_reach); log: |Im lambda| < pi/2 and |gamma| < pi (Sec. 3e)."""
    im_s = ex(box["s_h"]) * (minor(box["rho_s"]) + SQRT2 * cover_radius(box["rho_s"]))
    g_lo, g_hi = gamma_ends(box)
    s_ok = im_s < arb.pi() / 2 if box["windows"] else (im_s < g_lo and g_hi + im_s < arb.pi())
    if not s_ok:
        fail(f"s-axis domain: |Im s| <= {float(im_s.upper()):.4f} (windows {box['windows']})")
    if box["map"] == "log":
        im_l = ex(box["l_h"]) * (minor(RHO_G) + SQRT2 * cover_radius(RHO_G))
        re_l = ex(box["l_c"]) + ex(box["l_h"]) * (major(RHO_G) + SQRT2 * cover_radius(RHO_G))
        if not (im_l < arb.pi() / 2 and re_l.exp() < arb.pi()):
            fail("lambda-axis domain: need |Im lambda| < pi/2 and |gamma| < pi on the filled ellipse")
    elif box["g"][0] > 0:
        reach = ex(box["g_h"]) * (major(RHO_G) + SQRT2 * cover_radius(RHO_G))
        if not (ex(box["g_c"]) - reach > 0 and ex(box["g_c"]) + reach < arb.pi()):
            fail("gamma-axis domain: Re gamma must stay in (0, pi) on the filled ellipse")
    if not (minor(RHO_Y) + SQRT2 * cover_radius(RHO_Y) < arb.pi() / 2):
        fail("y-axis domain: |Im y| must stay below pi/2")


def corner_reach(box):
    """CORNER box (lin, g_lo = 0; Sec. 3e): on the filled gamma-ellipse + squares Re gamma >= -r, |Im gamma| <= i, so for real u
    Im p2 = -u - sin(Re g) e^{Im g} <= -u + sin(r) e^i, the zero likewise (0 < a < 1), partners mirrored. Returns sin(r) e^i: every
    u-cell needs u_lo > it (asserted in u_frame); make_config re-asserts the domain on every ball."""
    reach = ex(box["g_h"]) * (major(RHO_G) + SQRT2 * cover_radius(RHO_G)) - ex(box["g_c"])
    im_g = ex(box["g_h"]) * (minor(RHO_G) + SQRT2 * cover_radius(RHO_G))
    assert reach.upper() < arb.pi() / 2, f"corner_reach premise r <= pi/2 fails: r = {reach} (M2)"
    return reach.sin() * im_g.exp()


def real_seg(box, key):
    lo, hi = box[key]
    return eng.box(lo, hi)


def s_at(box, xx):
    return ex(box["s_c"]) + ex(box["s_h"]) * xx


def g_at(box, zz):
    if box["map"] == "lin":
        return ex(box["g_c"]) + ex(box["g_h"]) * zz
    return (ex(box["l_c"]) + ex(box["l_h"]) * zz).exp()


def u_at(centre, yy):
    return (ex(centre) + yy).exp()


NEAR_RATIO, MID_RATIO, FAR_RATIO = 1.06, 1.12, 1.25
MID_SPAN = 1000      # mid-ratio panels out to MID_SPAN * (spread + max |depth|), far-ratio panels beyond, to X


def geometric_edges(centre, start, stop, ratio):
    """Exact Fraction edges centre -+ step for step = start, start*ratio, ... < stop."""
    pts, step = set(), start
    while step < stop:
        pts |= {centre - Fraction(step), centre + Fraction(step)}
        step *= ratio
    return pts


def fine_edges(cfg):
    """Panel edges on [-X, X]: NEAR_RATIO around every point/partner real-part centre from least/4 to spread, MID_RATIO out to
    MID_SPAN * scale, FAR_RATIO to X = cfg['xcut'] (the tails beyond X: eng.tail_bound)."""
    centres = sorted({Fraction(float(eng.value(cc).real.mid())) for cc in cfg["points"] + cfg["sharp"]})
    depth = max(float(abs(eng.value(cc).imag).upper()) for cc in cfg["points"])
    spread = 4 * (max(abs(float(cc)) for cc in centres) + 1)
    xcut = Fraction(cfg["xcut"])
    pts = set(centres) | {Fraction(-spread), Fraction(spread), -xcut, xcut}
    for cc in centres:
        pts |= geometric_edges(cc, cfg["least"] / 4, spread, NEAR_RATIO)
    mid_stop = MID_SPAN * (spread + depth)
    pts |= geometric_edges(Fraction(0), spread, mid_stop, MID_RATIO) | geometric_edges(Fraction(0), mid_stop, float(xcut), FAR_RATIO)
    return sorted(pp for pp in pts if -xcut <= pp <= xcut)


SERIES_W = Fraction(1, 2)
SERIES_BITS = 34


def log1p_series_over(ww):
    """E(w) = Log(1 + w)/w for |w| < 1/2: sum_k (-w)^k/(k+1), tail <= |w|^K/(1 - |w|) added as a ball (radius ~ rad(w)/2)."""
    mag = abs(ww).upper()
    terms = max(2, math.ceil(SERIES_BITS * math.log(2) / -math.log(max(float(mag), 1e-300))) + 1)
    total = acb(0)
    for kk in reversed(range(terms)):
        total = total * (-ww) + acb(1) / (kk + 1)
    tail = mag ** terms / (1 - mag)
    return total + acb(tail * arb(0, 1), tail * arb(0, 1))


def rot_log(ww, rot):
    """The engine's fixed rotated logs: rot = +1: Log(i w) - i pi/2 (= log_above / log_dn); rot = -1: Log(-i w) + i pi/2
    (= log_below / log_up). The rotated argument rot*i*w is asserted in the OPEN right half-plane (the real-contour DOMAIN)."""
    rotated = ww * acb(0, rot)
    assert head(rotated).real.lower() > 0, f"rotated log argument {head(rotated)} not certified in the right half-plane"
    return rotated.log() - acb(0, rot * arb.pi() / 2)


def head(val):
    """Constant coefficient of an acb_series in z (for z = acb_series([ball, 1]) it encloses the value over the whole ball)."""
    return val[0] if isinstance(val, acb_series) else val


def dd_log(alpha, beta, delta, rot):
    """[L(alpha) - L(beta)]/delta with L = rot_log(., rot), delta = alpha - beta; alpha, beta, delta each computed DIRECTLY as a
    difference of inputs (z - p, z - r#, p - r#). |delta/beta| < 1/2: both rotated arguments lie in the open right half-plane, so
    L(alpha) - L(beta) = Log(alpha/beta) = Log(1 + w), w = delta/beta, and the quotient is E(w)/beta (series): this keeps the
    cancellation near a foot that two separately enclosed logs lose (rad(parameter)/depth). Else (L(alpha) - L(beta))/delta, the
    engine's own form (no cancellation issue when |delta| >= |beta|/2)."""
    l_alpha, l_beta = rot_log(alpha, rot), rot_log(beta, rot)
    ww = delta / beta
    if abs(head(ww)).upper() < eng.exact(SERIES_W):
        if isinstance(ww, acb_series):  # Taylor mode: exact E(w) = Log(1 + w)/w (1 + w in the disc |. - 1| < 1/2: off the cut)
            return ((1 + ww).log() / ww) / beta
        return log1p_series_over(ww) / beta
    return (l_alpha - l_beta) / delta


def t_pair_wc(zz, cfg, pair):
    """(t_hol, t_sharp) of the engine's pair (t_hol, t_sharp in F_arb), as difference quotients (same functions):
    t_hol = [L+(z - r#) - L+(p - r#)]/(z - p) - [L-(z - p) - L-(r# - p)]/(z - r#),
    t_sharp = [L-(z - r) - L-(p# - r)]/(z - p#) - [L+(z - p#) - L+(r - p#)]/(z - r)   (L+ = rot_log(., +1), L- = rot_log(., -1))."""
    pp, pps = cfg["points"][pair["ip"]], cfg["sharp"][pair["ip"]]
    rr, rrs = cfg["points"][pair["ir"]], cfg["sharp"][pair["ir"]]
    hol = dd_log(zz - rrs, pp - rrs, zz - pp, 1) - dd_log(zz - pp, rrs - pp, zz - rrs, -1)
    sharp = dd_log(zz - rr, pps - rr, zz - pps, -1) - dd_log(zz - pps, rr - pps, zz - rr, 1)
    return hol, sharp


def merged_density(zz, cfg):
    """2ab D1(z; pbar, pbar#) (Sec. 3b), well-conditioned T_pp, T#_pp; pbar asserted below R and pbar# above R."""
    (aa, bb), (p1, p2), (p1s, p2s) = cfg["amps"], cfg["points"][1:], cfg["sharp"][1:]
    pbar, pbar_s = aa * p1 + bb * p2, aa * p1s + bb * p2s
    assert pbar.imag.upper() < 0 and pbar_s.imag.lower() > 0, f"mass centre {pbar} / partner {pbar_s} not certified off R"
    t_hol = dd_log(zz - pbar_s, pbar - pbar_s, zz - pbar, 1) - dd_log(zz - pbar, pbar_s - pbar, zz - pbar_s, -1)
    t_sharp = dd_log(zz - pbar, pbar_s - pbar, zz - pbar_s, -1) - dd_log(zz - pbar_s, pbar - pbar_s, zz - pbar, 1)
    return 2 * aa * bb * (t_hol * t_sharp / 4 - cfg["k0"] / ((zz - pbar) * (zz - pbar_s)))


def h_integrand_wc(zz, cfg):
    """The engine's cancelled integrand H (eng.h_integrand, same pairs, coefficients and final formula) with well-conditioned T."""
    hol, sharp = {}, {}
    for key, pair in cfg["pairs"].items():
        th, ts = t_pair_wc(zz, cfg, pair)
        hol[key], sharp[key] = pair["coef"] * th, pair["coef"] * ts
    cross = [key for key in cfg["pairs"] if key not in eng.OWN]
    (r1, r2), (r1s, r2s) = [hol[key] for key in eng.OWN], [sharp[key] for key in eng.OWN]
    cc, ccs = sum(hol[key] for key in cross), sum(sharp[key] for key in cross)
    (a1, a2), (p1, p2), (p1s, p2s) = cfg["amps"], cfg["points"][1:], cfg["sharp"][1:]
    s1, s2, s1s, s2s = -a1 / (zz - p1), -a2 / (zz - p2), -a1 / (zz - p1s), -a2 / (zz - p2s)
    return r1 * r2s + r2 * r1s + (r1 + r2) * ccs + cc * (r1s + r2s) + cc * ccs - cfg["k0"] * (s1 * s2s + s2 * s1s)


def chart_m_config(s_ball, g_ball, u_ball):
    """Real-contour config of chart M with the zero given EXPLICITLY: a + b = 1 exactly, so zero = a p2 + b p1 = a e^{-i gamma} - i u
    has foot a cos(gamma) and depth a sin(gamma) + u (partner a e^{i gamma} + i u). The engine's default (a p2 + b p1)/(a + b) divides
    by the ball a + (1 - a) = [1 +- 2 rad a] and inflates the zero (07:58: on s [-1/2,1/2] x gamma [1,3/2] its foot ball reached
    x = -0.08, next to pole 1). make_config still asserts the real-contour domain on the whole ball."""
    masses, feet, depths = chart_m_parts(s_ball, g_ball, u_ball)
    cos_g = gamma_trig(g_ball)[0]
    zero = (nonneg_product(masses[0], cos_g), depth_of(masses[0], g_ball, u_ball))
    return eng.make_config(masses, feet, depths, derivative=False, zero=zero, contour="real")


def real_nonneg_ends(ball):
    """(lower, upper) of a REAL ball whose lower end is certified >= 0; None otherwise."""
    val = acb(ball)
    return (val.real.lower(), val.real.upper()) if val.imag.is_zero() and val.real.lower() >= 0 else None


def sin_ends(g_ball):
    """(lower end of sin(lo), upper end of sin(hi)) for a REAL gamma ball [lo, hi] certified inside (-pi/2, pi/2), where sine is
    increasing: sin(gamma) lies in that range for EVERY gamma of the ball (lo may be slightly negative: eng.box(0, b) has lower end
    ~ -b 2^-30). None otherwise. The ENDPOINTS keep sin(lo) ~ lo, while a sine BALL over [lo, b] has lower end ~ -b 2^-30."""
    gam = acb(g_ball)
    if not gam.imag.is_zero():
        return None
    lo, hi = arb(gam.real.lower()), arb(gam.real.upper())
    if not (lo > -arb.pi() / 2 and hi < arb.pi() / 2):
        return None
    return lo.sin().lower(), hi.sin().upper()


def depth_of(scale, g_ball, u_ball):
    """scale sin(gamma) + u: pole 2's depth (scale 1) or the zero's (scale a). v1.10: when gamma is real inside (-pi/2, pi/2) (sin_ends:
    sin(gamma) in [l, h]) and scale in [p, q], u in [u_lo, u_hi] are real with p, u_lo >= 0, from ENDPOINTS: scale x is bilinear, so
    on [p, q] x [l, h] it lies in [min(p l, q l), max(p h, q h)] (scale >= 0) - for EVERY gamma of the ball, no sign assumption on
    gamma.
    Corner deep cut [0, b] at v = -20: the ball form gave the zero depth lower end -4.7e-11 although u >= 7.6e-10. Else the v1.00
    ball form."""
    sins, scales, us = sin_ends(g_ball), real_nonneg_ends(scale), real_nonneg_ends(u_ball)
    if sins is None or scales is None or us is None:
        return nonneg_product(scale, gamma_trig(g_ball)[1]) + u_ball
    lows = [(end * sins[0]).lower() for end in scales]
    highs = [(end * sins[1]).upper() for end in scales]
    lower = (min(lows) + us[0]).lower()
    upper = (max(highs) + us[1]).upper()
    return acb(span(lower, upper))


def nonneg_product(xx, yy):
    """x y; for two REAL balls with certified lower ends >= 0 the ENDPOINT product [x_lo y_lo, x_hi y_hi] (v1.00: midpoint-radius
    multiplication of two wide positive balls loses the sign, e.g. (0.5 +- 0.216)(1.48e-4 +- 1.19e-4) has lower end -4.3e-5 while
    the true range is [8.4e-6, 1.9e-4]; that refused the deep lambda row's M_y). Else the Arb product."""
    xa, ya = acb(xx), acb(yy)
    if xa.imag.is_zero() and ya.imag.is_zero() and xa.real.lower() >= 0 and ya.real.lower() >= 0:
        lo = (arb(xa.real.lower()) * arb(ya.real.lower())).lower()
        hi = (arb(xa.real.upper()) * arb(ya.real.upper())).upper()
        return acb(span(arb(lo), arb(hi)))
    return xa * ya


def gamma_trig(g_ball):
    """(cos gamma, sin gamma). For a REAL ball inside [0, pi/2] (certified) the MONOTONE endpoint enclosures cos in [cos hi, cos lo],
    real packets refuse). Else (complex, outside, or a lower end below 0 by radius rounding) the generic Arb functions; the depths
    use depth_of's endpoint form (v1.10), not this sine ball."""
    gam = acb(g_ball)
    if gam.imag.is_zero() and gam.real.lower() >= 0 and gam.real.upper() < arb.pi() / 2:
        lo, hi = arb(gam.real.lower()), arb(gam.real.upper())
        return acb(span(hi.cos().lower(), lo.cos().upper())), acb(span(lo.sin().lower(), hi.sin().upper()))
    return gam.cos(), gam.sin()


def span(lo, hi):
    """arb ball containing the closed interval [lo, hi] (arb endpoints with lo <= hi). Its lower end may sit below lo by ~ (hi - lo)
    end -4.7e-10), so no ball with a positive radius has lower end EXACTLY 0. The corner's deep cuts (deep_gamma_edges) keep hi ~ u."""
    return (lo + hi) / 2 + (hi - lo) / 2 * arb(0, 1)


def chart_m_parts(s_ball, g_ball, u_ball):
    """eng.chart_m with gamma_trig: masses (a, 1 - a), a = 1/(1 + e^s), feet (0, cos gamma), depths (u, sin gamma + u); pole 2's
    depth by depth_of (v1.10: endpoints on real packets)."""
    amass = 1 / (1 + s_ball.exp())
    return (amass, 1 - amass), (arb(0), gamma_trig(g_ball)[0]), (u_ball, depth_of(arb(1), g_ball, u_ball))


def u_spec(cfg, g_ball, u_ball):
    """MC1 data (Sec. 3c) of the u-frame config: p1 = -iu, p1# = iu, D = p2 - p1 = e^{-i gamma}, D# = e^{i gamma} (exact forms)."""
    aa, bb = cfg["amps"]
    return aa, bb, -acb(0, 1) * u_ball, acb(0, 1) * u_ball, (-acb(0, 1) * g_ball).exp(), (acb(0, 1) * g_ball).exp()


def sup_f(s_ball, g_ball, u_ball, mc1=False):
    """Exact upper endpoint >= sup |f| over the u-frame parameter ball (REAL-contour config; make_config asserts the domain)."""
    cfg = chart_m_config(s_ball, g_ball, u_ball)
    return sup_f_cfg(cfg, u_spec(cfg, g_ball, u_ball) if mc1 else None)


WINDOW_STATS = {"real": 0, "window": 0}
GAP_REFINE = 16      # outside panels refine geometrically from the window-gap ends, first step (gap width)/GAP_REFINE (chart C)


def zero_pair(s_ball, g_ball, u_ball):
    """(sigma, delta) with zero = sigma - i delta, partner = sigma + i delta (a analytic in s, a + b = 1): sigma = a cos(gamma),
    delta = a sin(gamma) + u (Sec. 3d). v1.10: nonneg_product and depth_of (sign-safe on REAL packets; on complex s both are the
    plain Arb forms of v1.00)."""
    amass = 1 / (1 + s_ball.exp())
    return nonneg_product(amass, gamma_trig(g_ball)[0]), depth_of(amass, g_ball, u_ball)


def sup_f_windowed(s_ball, g_ball, u_ball):
    """Sec. 3d (WINDOWS boxes, u-frame): sup|f|. REAL s (the M_g and M_y axes, and node-adjacent calls): the real contour, whose
    domain make_config asserts. COMPLEX s (M_s): gamma and u must be real; the real contour if
    |Im sigma| < Re delta is certified (zero below R, partner above), else the zero-following window."""
    if acb(s_ball).imag.is_zero():
        return sup_f(s_ball, g_ball, u_ball)
    assert acb(g_ball).imag.is_zero() and acb(u_ball).imag.is_zero(), "s-window needs real gamma and u (M_s axis only)"
    assert abs(s_ball.imag).upper() < arb.pi() / 2, f"s ball leaves the strip |Im s| < pi/2: {s_ball}"
    sigma, delta = zero_pair(s_ball, g_ball, u_ball)
    assert delta.real.lower() > 0, f"Re delta = Re(a) sin(gamma) + u not certified positive: {delta}"
    if abs(sigma.imag).upper() < delta.real.lower():
        WINDOW_STATS["real"] += 1
        return sup_f(s_ball, g_ball, u_ball)
    WINDOW_STATS["window"] += 1
    return window_sup_f(s_ball, g_ball, u_ball, sigma, delta)


WINDOW_NEAR = 1.25   # geometric panel ratio inside the window (chart C's NEAR)


def window_edges_m(lo, hi, foot, least):
    """Exact window panel edges on [lo, hi] (frame translated by sigma: the zero at Im nu - i Re delta): geometric from the zero's
    x = foot (step least/4) and from both ends (step (hi - lo)/64), ratio WINDOW_NEAR (chart C's window_edges, asymmetric)."""
    span = float(hi - lo)
    pts = {lo, hi} | geometric_edges(foot, least / 4, 2 * span, WINDOW_NEAR)
    for end in (lo, hi):
        pts |= geometric_edges(end, span / 64, span / 2, WINDOW_NEAR)
    return sorted(pp for pp in pts if lo <= pp <= hi)


def junction_pieces(start, delta, scale):
    """The segment start -> start + delta (every delta in the ball), split into K pieces of length <= scale/4: [(covering acb box,
    length bound)]. Vendored from chartC v0.80 (md5 c1830fef, two reads), same logic; avoids a fifth pinned dependency."""
    length = abs(delta).upper()
    count = max(1, math.ceil(4 * float(length) / float(scale)))
    return [(ex(start) + eng.box(Fraction(kk, count), Fraction(kk + 1, count)) * delta, length / count) for kk in range(count)]


def segment_integral(cfg, start, stop):
    """CONTROL ONLY: int of H along the straight segment start -> stop (vendored from chartC v0.80, c1830fef)."""
    return acb.integral(lambda zz, an: eng.h_integrand(zz, cfg, an), acb(start), acb(stop), rel_tol=eng.TOL_REL,
                        abs_tol=eng.TOL_ABS, eval_limit=10 ** 6)


def panels_integral(cfg, edges):
    return sum((segment_integral(cfg, ex(lo), ex(hi)) for lo, hi in zip(edges[:-1], edges[1:])), acb(0))


def dyadic(value):
    """Exact Fraction of a float (a proposal only; every use is followed by certified asserts)."""
    return Fraction(float(value))


WINDOW_REACH = Fraction(1, 2)   # the gap ends sit this share of the way from the outermost foot to the pole feet 0, cos(gamma)


def crossing_feet(amass, gam):
    """(sigma, crossing): sigma = a cos(gamma) and the feet (Re sigma + Im nu for z0, Re sigma - Im nu for z0#; nu = a sin(gamma))
    of the zero-pair points that may lie on the wrong side of R for SOME u >= 0 (worst case u -> 0). Empty: the real contour is
    valid at every u > 0."""
    cos_g, sin_g = gamma_trig(gam)
    sigma, nu = amass * cos_g, amass * sin_g
    crossing = ([sigma.real + nu.imag] if (sigma.imag - nu.real).upper() > 0 else []) + \
               ([sigma.real - nu.imag] if (sigma.imag + nu.real).lower() < 0 else [])
    return sigma, crossing


def window_frame_m(amass, g_ball, reach=WINDOW_REACH):
    """Sec. 3d frame (u-FREE). sigma = a cos(gamma), nu = a sin(gamma) (delta = nu + u). z0 = sigma - i delta has foot Re sigma +
    Im nu, z0# = sigma + i delta has foot Re sigma - Im nu. A foot is CROSSING if its
    point may lie on the wrong side of R for some u >= 0 (worst case u -> 0): z0 if Im sigma - Re nu may be > 0, z0# if Im sigma +
    Re nu may be < 0. With A, B = min, max of {crossing feet, Re sigma} (balls): gap (left, right) = (A/2, (B + cos_lo)/2) on R;
    junctions left -> left + offset and right -> right + offset with offset = sigma - m (m = Re sigma rounded, exact), so nearly
    vertical; window = sigma + [left - m, right - m] (height Im sigma: above z0, below z0#, at every x). Asserted (certified on the
    whole ball): 0 < left - |Re offset|, right + |Re offset| < cos(gamma) (the poles' rays), and every crossing foot X lies in
    (left + |Re offset|, right - |Re offset|) (its ray crosses R inside the gap and misses the junctions). Returns (left, right, m,
    offset). This only CONSTRUCTS the contour; admissibility is certified piece by piece (branch_check); value: lemma of Sec. 3d."""
    gam = acb(g_ball)
    sigma, crossing = crossing_feet(amass, gam)
    cos_lo = gamma_trig(gam)[0].real.lower()
    assert crossing, "window requested where the real contour is valid for every u >= 0"
    low = min(float(xx.lower()) for xx in crossing + [sigma.real])
    high = max(float(xx.upper()) for xx in crossing + [sigma.real])
    share = float(reach)
    left, right, mid = dyadic(low * (1 - share)), dyadic(high + share * (float(cos_lo) - high)), dyadic(sigma.real.mid())
    offset = sigma - ex(mid)
    slack = abs(offset.real)
    assert ex(left) - slack > 0 and ex(right) + slack < cos_lo, f"window/junctions reach a pole foot's ray: gap ({left}, {right})"
    for foot in crossing:
        assert (foot - slack > ex(left)) and (foot + slack < ex(right)), \
            f"crossing zero foot {foot} not inside the gap ({float(left):.3e}, {float(right):.3e}) with junction slack {slack}"
    return left, right, mid, offset


def outside_edges(cfg, gap_lo, gap_hi):
    """Exact panel edges of [-X, gap_lo] and of [gap_hi, X]: fine_edges plus geometric refinement from both gap ends."""
    pts = set(fine_edges(cfg)) | {gap_lo, gap_hi}
    for end in (gap_lo, gap_hi):
        pts |= geometric_edges(end, float(gap_hi - gap_lo) / GAP_REFINE, 4.0, NEAR_RATIO)
    left = sorted(pp for pp in pts if pp <= gap_lo and abs(pp) <= cfg["xcut"])
    right = sorted(pp for pp in pts if pp >= gap_hi and abs(pp) <= cfg["xcut"])
    return left, right


def window_pieces(s_ball, g_ball, u_ball, frame):
    """The Sec. 3d contour for one parameter ball and its frame (left, right, mid, offset) (window_frame_m, or v1.10
    real_window_frame): (out, win, outside pieces, junction pieces, window pieces, outside edges, frame)."""
    sigma, delta = zero_pair(s_ball, g_ball, u_ball)
    left, right, mid, offset = frame
    out, win = window_configs(s_ball, g_ball, u_ball, sigma, delta)
    edges = outside_edges(out, left, right)
    scale = right - left
    junctions = junction_pieces(left, offset, scale) + junction_pieces(right, offset, scale)
    foot = dyadic(acb(delta).imag.mid())
    window = eng.real_pieces(window_edges_m(left - mid, right - mid, foot, win["least"]))
    return out, win, eng.real_pieces(edges[0]) + eng.real_pieces(edges[1]), junctions, window, edges, (left, right, mid, offset)


def window_configs(s_val, g_val, u_val, sigma, delta):
    """(out, win): the unshifted window-mode config (R outside the gap, junctions) and the window frame translated by sigma."""
    masses, feet, depths = chart_m_parts(s_val, g_val, u_val)
    out = eng.make_config(masses, feet, depths, False, zero=(sigma, delta), contour="window")
    win = eng.make_config(masses, feet, depths, False, zero=(acb(0), delta), contour="window", shift=sigma)
    return out, win


def window_flux_m(s_pt, g_pt, u_pt, reach):
    """CONTROL ONLY: ball for F at ONE complex s point (real gamma, u) by integrating along the Sec. 3d contour with gap reach
    `reach` (frame_flux_m on window_frame_m)."""
    return frame_flux_m(s_pt, g_pt, u_pt, window_frame_m(1 / (1 + s_pt.exp()), g_pt, reach))


def frame_flux_m(s_pt, g_pt, u_pt, frame):
    """CONTROL ONLY: ball for F at ONE parameter point by integrating along the Sec. 3d contour of `frame` (window_frame_m, or the
    v1.10 real_window_frame), oriented -X -> left -> left + offset -> (window) -> right + offset -> right -> X. Every piece is
    branch-checked first."""
    out, win, outside, junctions, window, edges, frame = window_pieces(s_pt, g_pt, u_pt, frame)
    for cfg, pieces in ((out, outside), (out, junctions), (win, window)):
        for zball, _ in pieces:
            eng.branch_check(zball, cfg)
    left, right, mid, offset = frame
    lo_end, hi_end = ex(left), ex(right)
    total = (panels_integral(out, edges[0]) + panels_integral(out, edges[1])
             + panels_integral(win, window_edges_m(left - mid, right - mid, dyadic(acb(zero_pair(s_pt, g_pt, u_pt)[1]).imag.mid()),
                                                   win["least"]))
             + segment_integral(out, lo_end, lo_end + offset) + segment_integral(out, hi_end + offset, hi_end))
    tail = eng.tail_bound(out)
    return (total + acb(tail * arb(0, 1), tail * arb(0, 1))) / arb.pi()


def window_sup_f(s_ball, g_ball, u_ball, sigma, delta):
    """sup|f| on the Sec. 3d contour (frame window_frame_m at WINDOW_REACH): every piece branch-checked by eng.majorant_on_pieces
    (out-frame for R outside the gap and the junctions, sigma-translated frame for the window); tails as on R."""
    out, win, outside, junctions, window, _, _ = window_pieces(s_ball, g_ball, u_ball,
                                                               window_frame_m(1 / (1 + s_ball.exp()), g_ball, WINDOW_REACH))
    total = (eng.majorant_on_pieces(out, outside) + eng.majorant_on_pieces(out, junctions) + eng.majorant_on_pieces(win, window)
             + eng.tail_bound(out))
    return (total / arb.pi()).upper()


def wc_majorant_on_pieces(cfg, pieces):
    """eng.majorant_on_pieces with the WELL-CONDITIONED H of sup_f_cfg (h_integrand_wc; eng.branch_check per piece, and every rot_log
    inside asserts its own rotated argument in the open right half-plane, constants included): exact upper endpoint of sum over
    pieces (zball, length) of length * sup|H|. v1.10 (probe 19:39, lambda [-10.43, -8.23], v = -25): on R outside the gap the plain
    H gave 2.8e11 (its two pole-1 terms cancel only to ~ rad/u) and H_wc 1.7e3; in the window 1.2e5 vs 3.5e2."""
    total = arb(0)
    for zball, length in pieces:
        eng.branch_check(zball, cfg)
        total += arb(length).upper() * abs(h_integrand_wc(zball, cfg)).upper()
    return total.upper()


def real_window_frame(s_ball, g_ball):
    """v1.10, DEEP pieces of WINDOWS boxes at REAL (s, gamma, u): the Sec. 3d frame around the zero's foot range itself. For real
    parameters the zero sigma - i delta lies below R and its partner above (no crossing feet); sigma and offset = sigma - m are REAL,
    so R outside the gap, both junctions and the window all lie ON R: the contour IS R, and its integral is the real-contour flux
    for every parameter of the ball. Only the panels follow the zero (window frame translated by sigma), so the zero's foot spread
    over a real s-ball no longer enters the bound. gap (left, right) = (sigma_lo (1 - WINDOW_REACH), sigma_hi + WINDOW_REACH
    (cos_lo - sigma_hi)), m = sigma rounded; asserted (certified): 0 < left - |offset| and right + |offset| < cos_lo, i.e. the pole
    feet 0 and cos(gamma) stay outside the gap and the junctions (needs a_hi < ~2 a_lo and b_hi < ~2 b_lo on the s-ball)."""
    amass = 1 / (1 + s_ball.exp())
    cos_g = gamma_trig(g_ball)[0]
    sigma = acb(nonneg_product(amass, cos_g))
    assert sigma.imag.is_zero() and acb(g_ball).imag.is_zero(), "real_window_frame needs real s and gamma"
    cos_lo = cos_g.real.lower()
    share = float(WINDOW_REACH)
    low, high = float(sigma.real.lower()), float(sigma.real.upper())
    left, right, mid = dyadic(low * (1 - share)), dyadic(high + share * (float(cos_lo) - high)), dyadic(sigma.real.mid())
    offset = sigma - ex(mid)
    slack = abs(offset.real)
    assert ex(left) - slack > 0 and ex(right) + slack < cos_lo, \
        f"deep window/junctions reach a pole foot: gap ({float(left):.3e}, {float(right):.3e}), junction slack {slack}"
    return left, right, mid, offset


DEEP_STATS = {"window": 0, "plain": 0}   # v1.10: deep packets of WINDOWS boxes by contour (real-line window / plain real contour)


def deep_sup_f(box, s_ball, g_ball, u_ball):
    """sup|f| on one deep-piece packet (REAL s, gamma, u). WINDOWS boxes (v1.10): the real-line zero-following contour of
    real_window_frame (probe 19:33: on lambda [-10.43, -8.23] at v = -15 the plain bound with K = 1 was 1.6e14 - the zero's depth
    a sin(gamma) + u is far below its foot's spread over the s-ball), every piece bounded with H_wc (wc_majorant_on_pieces), as
    sup_f's own panels are. Where that frame cannot be built (its gap would reach a pole foot: a -> 1 makes the zero's foot
    a cos(gamma) meet pole 2's foot cos(gamma), e.g. the top lambda row at s = -25/3; the zero is then DEEP, a sin(gamma) >= 0.19)
    the plain real contour, which is valid for every real packet. Other boxes: the plain real contour (sup_f, v0.71). Both are
    upper bounds for the same real-line integral; DEEP_STATS counts which one each packet used (printed with the DEEP line)."""
    if not box["windows"]:
        return sup_f(s_ball, g_ball, u_ball)
    assert acb(u_ball).imag.is_zero(), f"deep packet needs a REAL u (the contour IS R only for real s, gamma, u): {u_ball}"  # A1
    try:
        frame = real_window_frame(s_ball, g_ball)
    except AssertionError:
        DEEP_STATS["plain"] += 1
        return sup_f(s_ball, g_ball, u_ball)
    DEEP_STATS["window"] += 1
    out, win, outside, junctions, window, _, _ = window_pieces(s_ball, g_ball, u_ball, frame)
    total = (wc_majorant_on_pieces(out, outside) + wc_majorant_on_pieces(out, junctions) + wc_majorant_on_pieces(win, window)
             + eng.tail_bound(out))
    return (total / arb.pi()).upper()


MC1_STATS = {"used": 0, "fallback": 0}


def sup_f_cfg(cfg, spec):
    """Exact upper endpoint >= sup |f| over the config's parameter ball: the plain bound (1/pi)[sum over panels of width * sup|H|
    + tail(H)] (H = the engine's cancelled integrand, well-conditioned form, eng.branch_check per piece) or, given spec, the MIN of
    it and the MC1 bound (Sec. 3c) - two valid upper bounds."""
    panels, total, edges = [], arb(0), fine_edges(cfg)
    for lo, hi in zip(edges[:-1], edges[1:]):
        zball, length = eng.real_pieces([lo, hi])[0]
        eng.branch_check(zball, cfg)
        h_abs = abs(h_integrand_wc(zball, cfg)).upper()
        panels.append((zball, arb(length).upper(), h_abs))
        total += panels[-1][1] * h_abs
    plain = ((total + eng.tail_bound(cfg)) / arb.pi()).upper()
    if spec is None:
        return plain
    other = mc1_sup(cfg, panels, spec)
    return other if other is not None and other < plain else plain


def mc1_config(cfg, spec, tval):
    """Copy of cfg on the mass-centre path (Sec. 3c): points pbar + t d_j (zero, pole 1, pole 2), partners pbar# + t d_j#; t a
    scalar ball or an acb_series in t. d_0 = (a - b) D, d_1 = -b D, d_2 = a D with D = p2 - p1 given exactly in spec."""
    aa, bb, p1, p1s, dd, dds = spec
    pbar, pbar_s = p1 + bb * dd, p1s + bb * dds
    out = dict(cfg)
    out["points"] = [pbar + (aa - bb) * dd * tval, pbar - bb * dd * tval, pbar + aa * dd * tval]
    out["sharp"] = [pbar_s + (aa - bb) * dds * tval, pbar_s - bb * dds * tval, pbar_s + aa * dds * tval]
    return out


def assert_path_domain(cfg_t):
    """C1 / v0.20: on the t-ball every path point strictly below R and every partner strictly above (convexity
    covers real parameters only; complex (s, gamma) balls need this check)."""
    for cc in cfg_t["points"]:
        assert head(cc).imag.upper() < 0, f"MC1 path point may touch R: {head(cc)}"
    for cc in cfg_t["sharp"]:
        assert head(cc).imag.lower() > 0, f"MC1 path partner may touch R: {head(cc)}"


def mc1_sup(cfg, panels, spec):
    """MC1 upper bound of sup|f| (Sec. 3c), or None if a series evaluation leaves the domain (counted in MC1_STATS)."""
    saved = ctx.cap
    ctx.cap = MC1_K + 1
    try:
        at_zero = mc1_config(cfg, spec, acb_series([acb(0), acb(1)]))
        at_ball = mc1_config(cfg, spec, acb_series([acb(arb("0.5", "0.5")), acb(1)]))
        assert_path_domain(at_ball)
        total = arb(0)
        for zball, length, h_abs in panels:
            ser0, serb = h_integrand_wc(zball, at_zero), h_integrand_wc(zball, at_ball)
            rest = (sum((abs(ser0[kk]) for kk in range(2, MC1_K)), arb(0)) + abs(serb[MC1_K])).upper()
            alt = (h_abs + abs(ser0[0]) + abs(ser0[1])).upper()      # |H| + |H_0| + |H_1| >= |H - H_0 - H_1| too
            total += length * (rest if rest < alt else alt)
        tails = eng.tail_bound(cfg) + merged_tail(cfg) + h1_tail(cfg, spec)
    except (AssertionError, ValueError) as err:
        MC1_STATS["fallback"] += 1
        LOG.append(f"MC1 fallback: {str(err)[:120]}")
        return None
    finally:
        ctx.cap = saved
    MC1_STATS["used"] += 1
    return ((total + tails) / arb.pi()).upper()


def merged_tail(cfg):
    """Bound on int_{|x| > X} |2ab D1(x; pbar)|, X = cfg['xcut'] >= 4 |pbar|, |pbar#|: the engine's tail_bound argument for one pole
    of mass 1: |T| <= 4 ell/|x|, so |D1| <= (4 ell^2 + k0 * 4)/x^2 (|x - c| >= |x|/2), ell = log(1.5 X) + pi + |Log(pbar - pbar#)|
    + |Log(pbar# - pbar)|; int_X^oo (log x + c)^2/x^2 = (ell^2 + 2 ell + 2)/X. Times 2 sides and |2ab|."""
    (aa, bb), (p1, p2), (p1s, p2s) = cfg["amps"], cfg["points"][1:], cfg["sharp"][1:]
    pbar, pbar_s = aa * p1 + bb * p2, aa * p1s + bb * p2s
    xcut = arb(cfg["xcut"])
    assert abs(pbar).upper() < xcut / 4 and abs(pbar_s).upper() < xcut / 4, "merged tail premise X >= 4|pbar| fails"
    ell = xcut.log() + arb(3).log() - arb(2).log() + arb.pi() + 2 * (abs(rot_log(pbar - pbar_s, 1)) + abs(rot_log(pbar_s - pbar, -1)))
    return (2 * abs(2 * aa * bb) * (4 * (ell ** 2 + 2 * ell + 2) + 4 * eng.k0()) / xcut).upper()


def h1_tail(cfg, spec):
    """Bound on int_{|x| > X} |H_1|: the t-box [-c, c] + i[-c, c] (c = MC1_DISC)
    contains the circle |t| = c, so |H_1(x)| <= sup_{|t| = c} |H(x; t)|/c. The configuration ball over the t-box goes through
    eng.make_config (feet (p + p#)/2, depths (p# - p)/(2i): enclosures; it ASSERTS the real-contour domain on the whole ball) and
    eng.tail_bound is a pointwise envelope valid for every configuration in it, at the SAME X = cfg['xcut']."""
    cc = ex(MC1_DISC)
    disc = mc1_config(cfg, spec, acb(cc * arb(0, 1), cc * arb(0, 1)))
    feet = [(pp + ps) / 2 for pp, ps in zip(disc["points"], disc["sharp"])]
    depths = [(ps - pp) / acb(0, 2) for pp, ps in zip(disc["points"], disc["sharp"])]
    box_cfg = eng.make_config(cfg["amps"], tuple(feet[1:]), tuple(depths[1:]), derivative=False, zero=(feet[0], depths[0]),
                              contour="real")
    box_cfg["xcut"] = cfg["xcut"]
    return eng.tail_bound(box_cfg) / cc


def dil_config(s_ball, g_ball, w_ball):
    """C_dil(w) (NOTE Lemma W1): pole 1 (mass a) at -i, pole 2 (mass b) at -i + w e^{-i gamma}, zero -i + a w e^{-i gamma} given
    EXPLICITLY; REAL contour."""
    masses, _, _ = eng.chart_m(s_ball.exp(), g_ball, acb(1))
    w_cos, w_sin = w_ball * g_ball.cos(), w_ball * g_ball.sin()
    return eng.make_config(masses, (acb(0), w_cos), (acb(1), 1 + w_sin), derivative=False,
                           zero=(masses[0] * w_cos, 1 + masses[0] * w_sin), contour="real")


def w_spec(cfg, g_ball, w_ball):
    """MC1 data of the w-frame config: p1 = -i, p1# = i, D = w e^{-i gamma}, D# = w e^{i gamma}."""
    aa, bb = cfg["amps"]
    return aa, bb, -acb(0, 1), acb(0, 1), w_ball * (-acb(0, 1) * g_ball).exp(), w_ball * (acb(0, 1) * g_ball).exp()


def complex_ball(centre, radius):
    return centre + acb(radius * arb(0, 1), radius * arb(0, 1))


SUB_S, SUB_G = 1, 1   # real s- and gamma-segments split into this many sub-balls inside the majorants (07:59: on the box
                      # s [-1/2,1/2] x gamma [1,3/2] at u = e^-5 the whole-box ball costs 144x vs a point; s alone 20x, gamma alone 30x)


Y_GROUPS = 8          # v0.80: u-cell M_s, M_g over Y_GROUPS equal real y-balls covering [-1, 1] (a SUPERSET of the y-nodes: valid in
                      # the points form; u = e^(c + y) > 0 on all of it) instead of each y-node; 0 = the nodes (v0.71). W-CELL: nodes
                      # always. v1.30: 8 (was 0).


def y_majorant_points(frame, y_points):
    """The y-values for M_s and M_g (POINTS FORM): the y-nodes, or for a u-cell with Y_GROUPS > 0 the real balls of [-1, 1]."""
    if Y_GROUPS == 0 or frame["kind"].startswith("w"):
        return y_points
    edges = [Fraction(2 * jj, Y_GROUPS) - 1 for jj in range(Y_GROUPS + 1)]
    return [acb(eng.box(aa, bb)) for aa, bb in zip(edges[:-1], edges[1:])]


def sub_segments(box, key, count):
    """The real segment of `key` in `count` equal exact sub-balls (their union is the whole segment)."""
    lo, hi = box[key]
    edges = [lo + (hi - lo) * Fraction(jj, count) for jj in range(count + 1)]
    return [eng.box(aa, bb) for aa, bb in zip(edges[:-1], edges[1:])]


def u_frame(box, centre):
    """u-cell v in [centre - 1, centre + 1] (Sec. 2): g = u f(u), u = e^{centre + y}; rhos (rho_s of the box, RHO_G, RHO_Y).
    WINDOWS boxes: sup_f_windowed (Sec. 3d). CORNER box: the cell's u_lo must exceed corner_reach (Sec. 3e), else FAIL."""
    if box["map"] == "lin" and box["g"][0] == 0 and not ex(centre - 1).exp() > corner_reach(box):
        fail(f"corner box: u-cell [e^{centre - 1}, e^{centre + 1}] too deep for the gamma-ellipse reach {corner_reach(box)}")

    def g_sup(s_ball, g_ball, yy):
        uu = u_at(centre, yy)
        value = sup_f_windowed(s_ball, g_ball, acb(uu)) if box["windows"] else sup_f(s_ball, g_ball, acb(uu), MC1_U_CELLS)
        return (value * abs(uu).upper()).upper()

    def g_node(s_pt, g_pt, yy):
        uu = u_at(centre, yy)
        return eng.flux_enclosure(*eng.chart_m(s_pt.exp(), g_pt, uu)) * uu

    return {"label": f"CELL v in [{centre - 1}, {centre + 1}]", "rhos": (box["rho_s"], RHO_G, RHO_Y), "g_sup": g_sup,
            "g_node": g_node, "kind": "u: g = u f(u), u = e^(param + y)", "param": centre}


def w_frame(box):
    """W-CELL (Sec. 1b): w = w0 (1 - y)/2, g_w = (w0/2) h(w), h = u^2 f(u) = f_dil(w)/w; rhos by w_rhos (asserted domain)."""
    w0 = (-ex(V_W)).exp()

    def w_of(yy):
        return w0 * (1 - yy) / 2

    def g_sup(s_ball, g_ball, yy):
        ww = acb(w_of(yy))
        low = abs(ww).lower()
        if not low > 0:
            fail(f"w-cell majorant ball {ww} meets w = 0 (G1)")
        cfg = dil_config(s_ball, g_ball, ww)
        return (w0 / 2 * sup_f_cfg(cfg, w_spec(cfg, g_ball, ww)) / low).upper()

    def g_node(s_pt, g_pt, yy):
        ww = w_of(yy)
        if not ww.lower() > 0:
            fail(f"w-cell node {ww} meets w = 0 (G1)")
        uu = 1 / ww
        return w0 / 2 * uu ** 2 * eng.flux_enclosure(*eng.chart_m(s_pt.exp(), g_pt, uu))

    return {"label": f"W-CELL u >= e^{V_W} (w0 = {float(w0.mid()):.4f})", "rhos": w_rhos(box, w0), "g_sup": g_sup,
            "g_node": g_node, "kind": "w: g = (w0/2) u^2 f(u), u = 1/w, w = w0 (1 - y)/2, w0 = e^(-param)", "param": V_W}


def w_rhos(box, w0):
    """(rho_s, rho_g, rho_y) of the W-CELL: per axis the largest RHO_W_CHOICES entry whose FILLED ellipse (plus cover radius) keeps
    every offset |q| (W2: q in {w e, w e#, a w e, a w e#}) <= W_MARGIN < 1, the other axes real:
    y-axis (s, gamma real, 0 < a < 1): |w| <= (w0/2)(1 + major + sqrt(2) cover) (cover boxes are SQUARES of half-side cover:
    g_h (minor + cover); s-axis (w, gamma real): |Im s| <= s_h (minor + cover) < pi/2 gives |a|, |b| < 1, so |q| <= w0.
    make_config still asserts the domain on every evaluated ball."""
    margin = ex(W_MARGIN)
    tests = (lambda rr: ex(box["s_h"]) * (minor(rr) + cover_radius(rr)) < arb.pi() / 2 and w0 <= margin,
             lambda rr: w0 * im_gamma_reach(box, rr).exp() <= margin,
             lambda rr: w0 / 2 * (1 + major(rr) + arb(2).sqrt() * cover_radius(rr)) <= margin)
    out = []
    for axis, test in enumerate(tests):
        passing = [rr for rr in RHO_W_CHOICES if test(rr)]
        if not passing:
            fail(f"w-cell axis {axis}: no rho in {RHO_W_CHOICES} keeps the offsets <= {W_MARGIN} (W2)")
        out.append(max(passing))
    return tuple(out)


def im_gamma_reach(box, rho):
    """Upper bound of |Im gamma| on the filled gamma-axis ellipse of ratio rho plus its covers. lin: g_h (minor + cover) (v0.71
    form). log (gamma = e^lambda): |Im gamma| = e^{Re lambda} |sin Im lambda| <= e^{l_c + l_h (major + sqrt2 cover)} l_h (minor +
    sqrt2 cover)."""
    if box["map"] == "lin":
        return ex(box["g_h"]) * (minor(rho) + cover_radius(rho))
    im_l = ex(box["l_h"]) * (minor(rho) + SQRT2 * cover_radius(rho))
    return (ex(box["l_c"]) + ex(box["l_h"]) * (major(rho) + SQRT2 * cover_radius(rho))).exp() * im_l


DUMP = {"handle": None}   # certify mode (v0.70): one JSON line per node value, majorant call, cell and deep piece (P2-B input)


def ball_text(val):
    """[re mid, re rad, im mid, im rad] of an arb/acb ball as decimal strings: mid to 30 digits; rad as a float rounded up PLUS
    1e-29 |mid|."""
    cc = acb(val)
    out = []
    for part in (cc.real, cc.imag):
        out += [part.mid().str(30, radius=False), repr((float(part.rad()) + 1e-29 * abs(float(part.mid()))) * (1 + 1e-9))]
    return out


def dump(record):
    if DUMP["handle"] is not None:
        DUMP["handle"].write(json.dumps(record) + "\n")


REFINE_ABOVE = 20    # v1.20: a majorant cover ball whose g_sup exceeds this is re-evaluated on its quarters (00:04 Oct 30: the
REFINE_DEPTH = 2     # worst v1.10 lambda ball gave 1.1e6 whole, 5.7 on its 4 s-quarters, 0.37 at its centre: ball dependency)


def ball_halves(part):
    """Two real balls covering the real ball `part`: [lo, mid] and [mid, hi], each the union of an endpoint and the midpoint."""
    lo, hi = arb(part.lower()), arb(part.upper())
    mid = (lo + hi) / 2
    return lo.union(mid), mid.union(hi)


def quarters(zball):
    """4 complex balls whose union contains the complex ball zball (a rectangle): each part split by ball_halves."""
    return [acb(re, im) for re in ball_halves(zball.real) for im in ball_halves(zball.imag)]


WIDTH_ASSERTS = ("contour piece ", "a point may touch", "a partner point may touch", "constant log argument ",
                 "mass sum may vanish", "pole depths not certified", "mass centre ", "rotated log argument ", "Re delta ")
                     # v1.31: assert texts (engine F_arb + this driver) that say only "this enclosure is too wide to certify
                     # the domain/branch"; design premises (the |Im s| < pi/2 strip, window construction) are NOT listed: always loud


def width_assert(err):
    return str(err).startswith(WIDTH_ASSERTS)


def refined_sup(evaluate, zball, depth):
    """(value, evaluations): evaluate(zball), or, above REFINE_ABOVE with depth > 0, the smaller of it and the max over the quarters
    of zball (recursively). Valid: every point of zball lies in a quarter, so either number bounds |g| on zball.
    v1.31: if evaluate(zball) fails a WIDTH_ASSERTS check and depth > 0, the value is the max over the quarters alone (same cover
    argument); at depth 0, or for any other assert, the error propagates (loud)."""
    try:
        value = evaluate(zball)
    except AssertionError as err:
        if depth == 0 or not width_assert(err):
            raise
        value = None
    if value is not None and (depth == 0 or not value > REFINE_ABOVE):
        return value, 1
    best, count = arb(0), 1
    for quarter in quarters(zball):
        kid, used = refined_sup(evaluate, quarter, depth - 1)
        best, count = (kid if kid > best else best), count + used
    return (best if value is None or best < value else value), count


S_SPLIT_DEPTH = 2    # v1.40: on the M_g / M_y axes a REAL s ball still failing a width assert after refined_sup is halved, to this depth


def split_sup(evaluate_for, s_ball, zball, depth):
    """(value, evaluations): refined_sup(evaluate_for(s_ball), zball, REFINE_DEPTH) for a REAL s ball; v1.40: if that fails a
    WIDTH_ASSERTS check and depth > 0, the max over the two ball_halves of s_ball (recursively). Valid: every point of s_ball lies
    in a half, so the max bounds |g| over s_ball x zball. At depth 0, or for any other assert, the error propagates (loud)."""
    try:
        return refined_sup(evaluate_for(s_ball), zball, REFINE_DEPTH)
    except AssertionError as err:
        if depth == 0 or not width_assert(err):
            raise
    best, count = arb(0), 0
    for half in ball_halves(acb(s_ball).real):
        kid, used = split_sup(evaluate_for, acb(half), zball, depth - 1)
        best, count = (kid if kid > best else best), count + used
    return best, count


def axis_evaluator(box, frame, axis, others):
    """g_sup as a function of the axis ball zz (unit-ellipse coordinate); `others` = [s, gamma, y] with the axis entry unused."""
    def evaluate(zz):
        args = list(others)
        args[axis] = acb(s_at(box, zz)) if axis == 0 else acb(g_at(box, zz)) if axis == 1 else zz
        return frame["g_sup"](*args)
    return evaluate


def axis_majorant(box, frame, axis, y_points):
    """M_axis (Sec. 2, POINTS FORM): max over the COVER balls of the axis ellipse curve of frame g_sup, each ball refined by
    refined_sup (v1.20); the other axes take: s and gamma their whole real segments (SUB_S / SUB_G sub-balls), y its ellipse ball
    (axis 2) or each y-node point (axes 0, 1)."""
    worst = arb(0)
    windowed = box["windows"] and axis == 0 and frame["kind"].startswith("u")   # the only place the s-windows act (Sec. 3d)
    for zc, radius in bc.ellipse_cover(ex(frame["rhos"][axis]), COVER_S_WINDOW if windowed else COVER):
        zball = complex_ball(zc, radius)
        s_balls = [s_at(box, zball)] if axis == 0 else [acb(ss) for ss in sub_segments(box, "s", SUB_S)]
        g_balls = [g_at(box, zball)] if axis == 1 else [acb(gg) for gg in gamma_segments(box, SUB_G_WINDOW if windowed else SUB_G)]
        for yy in ([zball] if axis == 2 else y_majorant_points(frame, y_points)):
            for ss in s_balls:
                for gg in g_balls:
                    if axis == 0:   # s IS the axis ball: refined_sup quarters it
                        value, used = refined_sup(axis_evaluator(box, frame, 0, [acb(ss), acb(gg), yy]), zball, REFINE_DEPTH)
                    else:           # v1.40: s is a real segment ball: split_sup halves it on a width assert
                        value, used = split_sup(lambda part, gg=gg, yy=yy: axis_evaluator(box, frame, axis, [part, acb(gg), yy]),
                                                acb(ss), zball, S_SPLIT_DEPTH)
                    worst = value if value > worst else worst
                    dump({"k": "maj", "cell": frame["label"], "axis": axis, "s": ball_text(ss), "g": ball_text(gg),
                          "y": ball_text(yy), "bound": repr(float(value) * (1 + 1e-9)), "evals": used})
    return worst


PLAN_DEG_MAX = 60    # plan mode reports degrees up to this (a certify run still stops at DEG_MAX)
PLAN_MODE = False


def first_degree(test, cap, label):
    for degree in range(1, (PLAN_DEG_MAX if PLAN_MODE else cap) + 1):
        if test(degree):
            return degree
    fail(f"{label} degree > {PLAN_DEG_MAX if PLAN_MODE else cap} needed: shrink the box or the cell")


def cell_plan(box, frame):
    """Majorants and degrees in the POINTS FORM order: M_y -> d_y; M_g at the y-nodes -> d_g; M_s at the y-nodes -> d_s, with
    R_y, L_y R_g, L_y L_g R_s each <= CELL_TARGET/3 (y first: its Lebesgue factor multiplies)."""
    rhos, third, bern = [ex(rr) for rr in frame["rhos"]], ex(CELL_TARGET) / 3, c3.bernstein_remainder
    m_y = axis_majorant(box, frame, 2, None)
    d_y = first_degree(lambda dd: bern(m_y, rhos[2], dd) < third, DEG_MAX[2], "y")
    y_points, lam_y = c3.cheb_nodes(d_y), c3.lebesgue_bound(d_y)
    m_g = axis_majorant(box, frame, 1, y_points)
    d_g = first_degree(lambda dd: lam_y * bern(m_g, rhos[1], dd) < third, DEG_MAX[1], "gamma")
    lam_g = c3.lebesgue_bound(d_g)
    m_s = axis_majorant(box, frame, 0, y_points)
    d_s = first_degree(lambda dd: lam_y * lam_g * bern(m_s, rhos[0], dd) < third, DEG_MAX[0], "s")
    return [m_s, m_g, m_y], (d_s, d_g, d_y)


def node_tensor(box, frame, degrees):
    """values[i][j][k] = g at (s-node i, gamma-node j, y-node k) as balls, and the largest |g| (for the majorant control)."""
    nodes = [c3.cheb_nodes(dd) for dd in degrees]
    values, biggest = [], arb(0)
    for ii, xx in enumerate(nodes[0]):
        plane = []
        for jj, zz in enumerate(nodes[1]):
            row = []
            for kk, yy in enumerate(nodes[2]):
                gg = frame["g_node"](s_at(box, xx), g_at(box, zz), yy)
                dump({"k": "node", "cell": frame["label"], "ijk": [ii, jj, kk], "s": ball_text(s_at(box, xx)),
                      "g": ball_text(g_at(box, zz)), "y": ball_text(yy), "value": ball_text(gg)})
                big = abs(gg).upper()
                biggest = big if big > biggest else biggest
                row.append(gg)
            plane.append(row)
        values.append(plane)
    return values, biggest


def run_cell(box, frame, state, plan_only):
    """One tensor cell; updates state (G, E) and returns the cell floor (the node count in plan mode)."""
    start = time.perf_counter()
    sups, degrees = cell_plan(box, frame)
    rem = c3.tensor_remainder(sups, [ex(rr) for rr in frame["rhos"]], degrees)
    nodes = (degrees[0] + 1) * (degrees[1] + 1) * (degrees[2] + 1)
    head = (f"{frame['label']}: M_s {float(sups[0]):.3e} M_g {float(sups[1]):.3e} M_y {float(sups[2]):.3e} "
            f"rhos {tuple(str(rr) for rr in frame['rhos'])}, degrees {degrees}, {nodes} nodes, R <= {float(rem):.2e}")
    if plan_only:
        print(head + f" (majorants {time.perf_counter() - start:.0f} s, MC1 {MC1_STATS})", flush=True)
        return nodes
    values, biggest = node_tensor(box, frame, degrees)
    for mm in sups:
        if not biggest <= mm:
            fail(f"majorant {mm} below a node value {biggest}: BUG")
    coeffs = c3.tensor_coeffs(values, degrees)
    combined = c3.add_3d(c3.as_3d(state["G"]), c3.suffix_tensor(coeffs)) if state["G"] else c3.suffix_tensor(coeffs)
    top, gap = c3.poly_max_3d(combined, MAX_TOL)
    floor = (state["A_T"] - state["E"] - 2 * rem - top).lower()
    full = c3.full_cell_2d(coeffs)
    state["G"] = c3.add_2d(state["G"], full) if state["G"] else full
    state["E"] = state["E"] + 2 * rem
    dump({"k": "cell", "cell": frame["label"], "frame": frame["kind"], "param": str(frame["param"]), "rhos": [str(rr) for rr in
          frame["rhos"]], "degrees": list(degrees), "sups": [repr(float(mm)) for mm in sups], "R": repr(float(rem)),
          "top": ball_text(top), "floor": repr(float(floor)), "E": ball_text(state["E"])})
    print(head + f"; max(G + suffix) <= {float(top):+.6e} (gap {float(gap):.1e}), FLOOR >= {float(floor):+.6f} "
          f"({time.perf_counter() - start:.0f} s)", flush=True)
    return floor


def anchor():
    """W_CELL: A = D1 - k0 exactly (Lemma W0). Else the CLUSTER-W anchor at T = e^V_TOP (Sec. 1)."""
    if W_CELL:
        return 3 * arb(3).zeta() / 4 - eng.k0()
    s_t = 1 / ex(V_TOP).exp()
    return 3 * arb(3).zeta() / 4 - eng.k0() - ex(Fraction(81, 20)) * s_t ** 2 / (1 - s_t)


def cell_frames(box):
    """The cells from the top down: the W-CELL (W_CELL) then N_U_CELLS u-cells of length 2 below the top."""
    top = V_W if W_CELL else V_TOP
    frames = [w_frame(box)] if W_CELL else []
    return frames + [u_frame(box, Fraction(top) - 1 - 2 * kk) for kk in range(N_U_CELLS)]


def mass_floor(box):
    """Exact lower bounds (a_B, m_B) of a = 1/(1 + e^s) and min(a, b) on the box (a decreases in s, b increases)."""
    a_min = (1 / (1 + ex(box["s"][1]).exp())).lower()
    b_min = (1 / (1 + (-ex(box["s"][0])).exp())).lower()
    return a_min, (a_min if a_min < b_min else b_min)


def prefix_bound(box, u_b):
    """min over the valid accepted prefix lemmas of the bound on sup_u int_u^{u_b} f (u_b <= 1/4)."""
    a_min, m_min = mass_floor(box)
    log_term = (1 / u_b).log()
    best = (bc.ABS_CONST / m_min ** 2 * u_b * (2 + log_term)).upper()
    low_a, low_b = (end.sin().lower() for end in gamma_ends(box))  # exact points (lin) or tight balls (log): decisive
    h_min = low_a if low_a < low_b else low_b
    if h_min >= ex(Fraction(1, 2)):
        me = (u_b * (64 / h_min ** 4 * (1 + log_term) + 4096 / (a_min ** 2 * h_min ** 8))).upper()
        best = me if me < best else best
    return best


def deep_piece(box, lo, hi):
    """(bound, K): bound >= int_lo^hi |f| du for every (s, gamma) in the box = (hi - lo) * max over K x K exact (s, gamma) sub-boxes of
    sup|f| on the REAL u-piece ball (CELL-UP); K = the first of DEEP_SUB whose bound <= DEEP_PIECE_TARGET, else the last K. v1.10:
    deep_sup_f per packet; a K with a refused packet (AssertionError: a domain or branch assertion) moves on to the next K; at the
    last K the assertion stays loud."""
    u_ball = acb((lo + hi) / 2 + (hi - lo) / 2 * arb(0, 1))
    for kk in DEEP_SUB:
        try:
            worst = arb(0)
            for ss in sub_segments(box, "s", kk):
                for gg in deep_gamma_segments(box, kk, hi):
                    value = deep_sup_f(box, acb(ss), acb(gg), u_ball)
                    worst = value if value > worst else worst
        except AssertionError:
            if kk == DEEP_SUB[-1]:
                raise
            continue
        bound = ((hi - lo) * worst).upper()
        if bound <= ex(DEEP_PIECE_TARGET):
            break
    return bound, kk


def deep_part(box, b_now, plan_only):
    """Crude unit pieces from V_BOT down until a prefix bound <= PREFIX_TARGET; returns (b at u_b, u_b, ok). Each piece:
    Phi(u) >= b_now - int_u^{e^v} |f| >= b_now - deep_piece bound for every u in [e^(v-1), e^v] (CHAIN-UP), so ok needs every
    running b > 0."""
    vv, ok, pieces = V_BOT, True, []
    while not (ex(vv).exp() <= ex(Fraction(1, 4)) and prefix_bound(box, ex(vv).exp()) <= ex(PREFIX_TARGET)):
        if not plan_only:
            bound, kk = deep_piece(box, ex(vv - 1).exp(), ex(vv).exp())
            b_now = b_now - bound
            ok = ok and b_now.lower() > 0
            pieces.append(f"{float(bound):.1e}/K{kk}")
            dump({"k": "deep", "v": [str(vv - 1), str(vv)], "K": kk, "bound": repr(float(bound) * (1 + 1e-9)), "b": ball_text(b_now)})
        vv -= 1
    if pieces:
        print(f"DEEP pieces from e^{V_BOT} down: {' '.join(pieces)}"
              f"{f'; packets by contour {DEEP_STATS}' if box['windows'] else ''}", flush=True)
    return b_now, ex(vv).exp(), ok


def certify(box, plan_only):
    assert_filled_domain(box)
    a_t = anchor()
    where = f"u = oo (W-CELL to e^{V_W})" if W_CELL else f"u = e^{V_TOP}"
    print(f"CHARTM box s in [{box['s'][0]}, {box['s'][1]}], {box_text(box)}: rho_s {box['rho_s']}, windows {box['windows']}, "
          f"anchor A = {float(a_t.lower()):.6f} at {where}, u-cells v in [{V_BOT}, {V_W if W_CELL else V_TOP}]", flush=True)
    state = {"A_T": a_t, "E": arb(0), "G": None}
    if not plan_only:
        g_key = "g" if box["map"] == "lin" else "l"
        tag = ("" if box["map"] == "lin" else "L") + "_".join(str(edge).replace("/", "o") for edge in box["s"] + box[g_key])
        path = f"logs/dump_box_{tag}_v{VERSION.replace('.', '')}.jsonl"
        DUMP["handle"] = open(path, "w", encoding="utf-8")
        print(f"DUMP (P2-B input): {path}", flush=True)
        dump({"k": "box", "map": box["map"], "s": [str(edge) for edge in box["s"]], g_key: [str(edge) for edge in box[g_key]],
              "A": ball_text(a_t), "driver_md5": file_md5(__file__), "engine_md5": file_md5(eng.__file__),
              "cheb3_md5": file_md5(c3.__file__)})
    results = [run_cell(box, frame, state, plan_only) for frame in cell_frames(box)]
    if plan_only:
        print(f"PLAN total nodes {sum(results)}", flush=True)
        _, u_b, _ = deep_part(box, arb(0), True)
        print(f"PLAN prefix at u_b = e^{math.log(float(u_b.mid())):.1f}: {float(prefix_bound(box, u_b)):.2e}", flush=True)
        return True
    bottom, _ = c3.poly_max_3d(c3.as_3d(state["G"]), MAX_TOL)
    b_now = state["A_T"] - state["E"] - bottom
    b_end, u_b, deep_ok = deep_part(box, b_now, False)
    face = (b_end - prefix_bound(box, u_b)).lower()
    verdict = all(ff > 0 for ff in results) and b_now.lower() > 0 and deep_ok and face > 0
    dump({"k": "result", "b_bot": ball_text(b_now), "b_end": ball_text(b_end), "u_b": ball_text(u_b), "face": repr(float(face)),
          "verdict": "PASS" if verdict else "FAIL"})
    DUMP["handle"].close()
    DUMP["handle"] = None
    print(f"CHARTM RESULT: Phi_lo(e^{V_BOT}) >= {float(b_now.lower()):+.6f}, after deep pieces {float(b_end.lower()):+.6f}, "
          f"u_b = {float(u_b.mid()):.3e}, prefix <= {float(prefix_bound(box, u_b)):.3e}, Phi(0+) >= {float(face):+.6f} -> "
          f"{'PASS' if verdict else 'FAIL'}", flush=True)
    return verdict


def refine_control():
    """v1.20 REFINE control (CAN fail): (a) the 4 corners and the centre of a complex ball each lie in one of its quarters; (b) on
    the worst v1.10 lambda ball (row [-383/100, -163/100], s [-25/27, 25/27], cell v [-3/2, 1/2]: 1.1e6 whole, 00:04 Oct 30) the
    refined value is below 1/100 of the whole-ball value and not below the centre-point value."""
    parent = acb(arb("-0.2", 0.066), arb("0.96", 0.066))
    corners = [acb(re, im) for re in (arb(parent.real.lower()), arb(parent.real.upper()))
               for im in (arb(parent.imag.lower()), arb(parent.imag.upper()))] + [acb(parent.real.mid(), parent.imag.mid())]
    covered = all(any(qq.contains(pt) for qq in quarters(parent)) for pt in corners)
    box = make_box(Fraction(-25, 27), Fraction(25, 27), Fraction(-383, 100), Fraction(-163, 100), "log")
    frame, target = u_frame(box, Fraction(-1, 2)), acb(arb("-0.197"), arb("0.9617"))
    zball = min((complex_ball(zc, radius) for zc, radius in bc.ellipse_cover(ex(box["rho_s"]), COVER_S_WINDOW)),
                key=lambda zz: float(abs(s_at(box, zz.mid()) - target).mid()))
    gg = next(acb(seg) for seg in gamma_segments(box, SUB_G_WINDOW) if seg.contains(arb("0.1545")))
    yy = arb("-0.8526401643540922")
    whole = frame["g_sup"](acb(s_at(box, zball)), gg, yy)
    refined, used = refined_sup(axis_evaluator(box, frame, 0, [None, gg, yy]), zball, REFINE_DEPTH)
    centre = frame["g_sup"](acb(s_at(box, zball.mid())), acb(gg.real.mid()), yy)
    ok = covered and refined < whole / 100 and centre <= refined
    print(f"REFINE control (v1.20): quarters cover corners + centre {covered}; worst v1.10 lambda ball: whole {float(whole):.3e}, "
          f"refined {float(refined):.3e} ({used} evaluations), centre point {float(centre):.3e} -> {'ok' if ok else 'FAIL'}",
          flush=True)
    return ok


def raises_assert(func):
    try:
        func()
        return False
    except AssertionError:
        return True


def width_assert_control():
    """v1.31 WIDTH-ASSERT control (CAN fail): (a) the ball that stopped the first v1.30 lambda box (top row, s [-25/27, 25/27],
    cell v [-15/2, -11/2], s-cover ball 10, gamma sub-ball 2, y-group 0) fails a WIDTH assert whole, and refined_sup returns a value
    <= 1 (measured 0.888 on its quarters); (b) LOUD: a width assert that never goes away still raises at depth 0, and a non-width
    assert raises at once (one evaluation)."""
    box = make_box(Fraction(-25, 27), Fraction(25, 27), Fraction(-163, 100), Fraction(-63, 100), "log")
    frame = u_frame(box, Fraction(-13, 2))
    zc, radius = bc.ellipse_cover(ex(box["rho_s"]), COVER_S_WINDOW)[10]
    zball = complex_ball(zc, radius)
    gg, yy = acb(gamma_segments(box, SUB_G_WINDOW)[2]), y_majorant_points(frame, None)[0]
    evaluate = axis_evaluator(box, frame, 0, [None, gg, yy])
    whole_fails = raises_assert(lambda: evaluate(zball))
    refined, used = refined_sup(evaluate, zball, REFINE_DEPTH)
    calls = []

    def stub(text):
        def always(_zz):
            calls.append(1)
            raise AssertionError(text)
        return always
    stays_loud = raises_assert(lambda: refined_sup(stub("contour piece STUB meets the cut of point STUB"), zball, REFINE_DEPTH))
    calls.clear()
    other_loud = raises_assert(lambda: refined_sup(stub("s ball leaves the strip |Im s| < pi/2: STUB"), zball, REFINE_DEPTH))
    ok = whole_fails and refined <= 1 and stays_loud and other_loud and len(calls) == 1
    print(f"WIDTH-ASSERT control (v1.31): whole ball asserts {whole_fails}; refined {float(refined):.3e} ({used} evaluations); "
          f"persistent width assert loud {stays_loud}; other assert loud at once {other_loud and len(calls) == 1} "
          f"-> {'ok' if ok else 'FAIL'}", flush=True)
    return ok


def s_split_control():
    """v1.40 S-SPLIT control (CAN fail): (a) the ball that stopped lambda row 1 box s [25/9, 125/27] (cell v [-15/2, -11/2], M_g
    axis, gamma-cover ball 2, y-group 0) still fails a width assert on the WHOLE real s segment after refined_sup (v1.31), and
    split_sup returns a finite positive value; (b) LOUD: split_sup at depth 0 still raises."""
    box = make_box(Fraction(25, 9), Fraction(125, 27), Fraction(-163, 100), Fraction(-63, 100), "log")
    frame = u_frame(box, Fraction(-13, 2))
    zc, radius = bc.ellipse_cover(ex(RHO_G), COVER)[2]
    zball = complex_ball(zc, radius)
    whole, yy = acb(sub_segments(box, "s", SUB_S)[0]), y_majorant_points(frame, None)[0]

    def evaluate_for(part):
        return axis_evaluator(box, frame, 1, [part, None, yy])
    whole_loud = raises_assert(lambda: refined_sup(evaluate_for(whole), zball, REFINE_DEPTH))
    depth0_loud = raises_assert(lambda: split_sup(evaluate_for, whole, zball, 0))
    value, used = split_sup(evaluate_for, whole, zball, S_SPLIT_DEPTH)
    ok = whole_loud and depth0_loud and value.is_finite() and value > 0
    print(f"S-SPLIT control (v1.40): whole s segment asserts after refinement {whole_loud}; depth 0 loud {depth0_loud}; split "
          f"value {float(value):.3e} ({used} evaluations) -> {'ok' if ok else 'FAIL'}", flush=True)
    return ok


def main_test():
    """Smoke test (direct, a few minutes): domain checks refuse a too-wide s-box and a too-large w0 (W2 margin); integrand, merged,
    MC1 and w-frame controls; the W-CELL on a tiny box: node values at the planned y-nodes stay below its three majorants (a
    control that CAN fail)."""
    bc.apply_work_settings()
    ok = True
    try:
        make_box(Fraction(-2), Fraction(2), Fraction(1, 2), Fraction(3, 5))
        ok = False
    except SystemExit:
        print("refused wide s-box at small g_lo: ok")
    box = make_box(Fraction(-1, 8), Fraction(1, 8), Fraction(5, 4), Fraction(11, 8))
    try:
        w_rhos(box, ex(Fraction(19, 20)))
        ok = False
    except SystemExit:
        print("refused w0 = 0.95 > W_MARGIN (W2): ok")
    ok &= integrand_control()
    ok &= mc1_control()
    ok &= wframe_control()
    ok &= lambda_corner_control()
    ok &= window_control()
    ok &= real_window_control()
    ok &= refine_control()
    ok &= width_assert_control()
    ok &= s_split_control()
    assert_filled_domain(box)
    frame = w_frame(box)
    sups, degrees = cell_plan(box, frame)
    _, biggest = node_tensor(box, frame, (2, 2, degrees[2]))
    ok &= all(biggest <= mm for mm in sups)
    print(f"{frame['label']}: majorants {[f'{float(mm):.3e}' for mm in sups]}, rhos {frame['rhos']}, degrees {degrees}, "
          f"max |g(nodes)| {float(biggest):.3e}, MC1 {MC1_STATS}", flush=True)
    print("TEST", "PASS" if ok else "FAIL", flush=True)
    return ok


def real_window_control():
    """v1.10 controls that CAN fail, at REAL points (s, gamma, u) of a deep lambda row (gamma = 1e-4) and of the corner (gamma = 1e-9),
    u = 1e-9: (R1) the real-line window contour of real_window_frame integrates to the plain real-contour flux eng.flux_complex
    (both balls overlap, both narrow); (R2) the deep bound deep_sup_f on a small real packet around the point, by the WINDOW path,
    is >= |F(point)|; (R3) the plain H bound on the same packet is far larger (why H_wc: the pole-1 cancellation)."""
    ok, lines, u_pt, s_half = True, [], Fraction(1, 10 ** 9), Fraction(1, 64)
    cases = (("lambda", Fraction(3, 10), Fraction(1, 10 ** 4), (Fraction(-93, 10), Fraction(-91, 10), "log")),    # e^-9.3..e^-9.1
             ("corner", Fraction(-1, 5), Fraction(1, 10 ** 9), (Fraction(0), Fraction(1, 2 ** 28), "lin")))        # 2^-28 = 3.7e-9
    for name, s_pt, g_pt, (y_lo, y_hi, gmap) in cases:
        sb, gb, ub = acb(ex(s_pt)), acb(ex(g_pt)), acb(ex(u_pt))
        windowed = frame_flux_m(sb, gb, ub, real_window_frame(sb, gb))
        plain = eng.flux_complex(*eng.chart_m(sb.exp(), gb, ub))
        agree = windowed.overlaps(plain) and max(float(vv.real.rad()) for vv in (windowed, plain)) < 1e-6
        box = make_box(s_pt - s_half, s_pt + s_half, y_lo, y_hi, gmap)
        packet = (acb(eng.box(*box["s"])), acb(gamma_segments(box, 1)[0]), acb(span(ex(u_pt / 2), ex(u_pt * 2))))
        before = dict(DEEP_STATS)
        bound = deep_sup_f(box, *packet)
        used_window = DEEP_STATS["window"] == before["window"] + 1
        out, win, outside, junctions, window, _, _ = window_pieces(*packet, real_window_frame(*packet[:2]))
        plain_h = eng.majorant_on_pieces(out, outside)
        covers = bound >= abs(windowed).upper()
        ok = ok and agree and covers and used_window and plain_h > 100 * bound
        lines.append(f"{name}: F window {float(windowed.real.mid()):+.6e} vs real {float(plain.real.mid()):+.6e} agree {agree}; "
                     f"deep bound {float(bound):.3e} >= |F| {covers} (window path {used_window}); plain-H outside {float(plain_h):.2e}")
    print(f"REAL-WINDOW control (v1.10): {'; '.join(lines)} -> {'ok' if ok else 'FAIL'}", flush=True)
    return ok


def refused(action):
    """True iff action() FAILs (SystemExit from fail())."""
    try:
        action()
    except SystemExit:
        return True
    return False


def lambda_corner_control():
    """Sec. 3e controls that CAN fail: a lambda box passes its domain check and maps z = -1, 1 onto its gamma ends; a lambda box with
    |Im lambda| >= pi/2 is refused; the corner [0, 2^-20] admits the deepest u-cell, the corner [0, 1/100] is refused there; v1.10:
    the corner's geometric deep packets (K = 1, 2, 4) are ALL admitted at u ~ 1e-20 and at u ~ e^-60, while ONE real ball over
    [0, 2^-20] at u ~ 1e-20 is refused (radius rounding: why the cuts are needed); deep edges run exactly from 0 to g_hi."""
    lbox = make_box(Fraction(-1), Fraction(1), Fraction(-2), Fraction(-63, 100), "log")
    assert_filled_domain(lbox)
    ends = gamma_ends(lbox)
    mapped = g_at(lbox, ex(-1)).overlaps(ends[0]) and g_at(lbox, ex(1)).overlaps(ends[1])
    wide = refused(lambda: assert_filled_domain(make_box(Fraction(-1, 2), Fraction(1, 2), Fraction(-6), Fraction(0), "log")))
    deepest = V_BOT + 1
    small = make_box(Fraction(-1, 2), Fraction(1, 2), Fraction(0), Fraction(1, 2 ** 20))
    corner_ok = not refused(lambda: u_frame(small, deepest))
    corner_bad = refused(lambda: u_frame(make_box(Fraction(-1, 2), Fraction(1, 2), Fraction(0), Fraction(1, 100)), deepest))
    corner_deep, one_ball = corner_deep_controls(small)
    deep =make_box(Fraction(-25, 27), Fraction(25, 27), Fraction(-1043, 100), Fraction(-823, 100), "log")
    deep_y = all(config_admitted(acb(sub_segments(deep, "s", 1)[0]), acb(gamma_segments(deep, 1)[0]),
                                 acb(u_at(deepest, complex_ball(zc, radius))))
                 for zc, radius in bc.ellipse_cover(ex(RHO_Y), COVER))
    ok = mapped and wide and corner_ok and corner_bad and deep_y and lbox["windows"] and small["windows"] and corner_deep and one_ball
    print(f"LAMBDA/CORNER control: lambda box rho_s {lbox['rho_s']}, z = +-1 -> gamma ends {mapped}; |Im lambda| >= pi/2 refused "
          f"{wide}; corner [0, 2^-20] deepest cell admitted {corner_ok}, corner [0, 1/100] refused {corner_bad}; deep lambda row "
          f"[-10.43, -8.23]: every M_y y-ball of the deepest cell admitted {deep_y} (tune3 14:40 refusal); corner deep packets "
          f"(geometric cuts, K = 1, 2, 4, u ~ 1e-20 and e^-60) + exact edges admitted {corner_deep}; one ball over "
          f"[0, 2^-20] at u ~ 1e-20 refused {one_ball} -> {'ok' if ok else 'FAIL'}", flush=True)
    return ok


def corner_deep_controls(small):
    """(geometric packets ok, one ball refused) for the corner box `small` (v1.10): at the deep pieces u in [e^(v-1), e^v] with
    e^v ~ 1e-20 and e^v = e^-60, every packet of deep_gamma_segments (K = 1, 2, 4) is admitted; deep_gamma_edges runs exactly
    from 0 to g_hi, increasing; ONE ball over [0, 2^-20] is refused; depth_of on a genuinely negative real ball [-2^-42, 2^-20]
    still encloses the true depth at gamma = -2^-42 (no clamp)."""
    s_ball = acb(sub_segments(small, "s", 1)[0])
    packets_ok = True
    for v_top in (Fraction(-46), Fraction(-60)):     # e^-46 = 1.05e-20
        top = ex(v_top).exp()
        u_ball = acb(span(ex(v_top - 1).exp().lower(), top.upper()))
        edges = deep_gamma_edges(small, top)
        packets_ok = (packets_ok and edges[0] == 0 and edges[-1] == small["g"][1] and all(aa < bb for aa, bb in zip(edges, edges[1:]))
                      and all(config_admitted(s_ball, acb(gg), u_ball) for kk in (1, 2, 4)
                              for gg in deep_gamma_segments(small, kk, top)))
    one_ball = not config_admitted(s_ball, acb(gamma_segments(small, 1)[0]), acb(span(ex(-47).exp().lower(), ex(-46).exp().upper())))
    wrong_lo, u_wrong = Fraction(-1, 2 ** 42), Fraction(1, 2 ** 38)
    depth = acb(depth_of(arb(1), acb(eng.box(wrong_lo, Fraction(1, 2 ** 20))), acb(ex(u_wrong))))
    covers_negative = depth.real.lower() <= ex(wrong_lo).sin() + ex(u_wrong)   # the true depth at gamma = -2^-42 stays enclosed
    return packets_ok and covers_negative, one_ball


def config_admitted(s_ball, g_ball, u_ball):
    """True iff chart_m_config certifies the real-contour domain on this ball (no AssertionError)."""
    try:
        chart_m_config(s_ball, g_ball, u_ball)
    except AssertionError:
        return False
    return True


WINDOW_POINTS = 24   # Cauchy-mean nodes on the circle |s - s0| = 1 (nearest singularity of F in s at distance ~3: error ~3^-24)


def window_control():
    """Sec. 3d controls that CAN fail (chart C pattern): (W1) where the real contour is valid at a complex s but a foot crosses
    as u -> 0, the contours with gap reach 1/2 and 1/4 and the real contour agree; (W2) where it is invalid, the two contours
    the crossing foot): the two contours agree; (W3) Cauchy mean: the average of F over |s - s0| = 1 (window wherever the real
    contour is invalid) equals the REAL-contour F(s0)."""
    gam, s0, reaches = acb(ex(Fraction(1, 20))), ex(Fraction(3, 10)), (WINDOW_REACH, Fraction(1, 4))
    s_w1, g_w1, u_w1 = acb(s0, ex(Fraction(1, 20))), acb(ex(Fraction(1, 100))), acb(ex(Fraction(1, 100)))
    w1 = [window_flux_m(s_w1, g_w1, u_w1, reach) for reach in reaches]
    w1.append(eng.flux_complex(*eng.chart_m(s_w1.exp(), g_w1, u_w1)))
    s_w2, u_w2 = acb(s0, ex(Fraction(3, 5))), acb(ex(Fraction(1, 1000)))
    sigma, delta = zero_pair(s_w2, gam, u_w2)
    invalid = not abs(sigma.imag).upper() < delta.real.lower()
    w2 = [window_flux_m(s_w2, gam, u_w2, reach) for reach in reaches]
    s_w4, g_w4, u_w4 = acb(ex(Fraction(200, 27)), ex(Fraction(35, 36))), acb(ex(Fraction(53, 100))), acb(ex(Fraction(1, 10 ** 8)))
    w4 = [window_flux_m(s_w4, g_w4, u_w4, reach) for reach in reaches]
    agree4 = w4[0].overlaps(w4[1]) and max(float(vv.real.rad()) for vv in w4) < 1e-6
    total, windows = acb(0), 0
    for kk in range(WINDOW_POINTS):
        s_k = acb(s0) + (acb(0, 2 * arb.pi() * kk / WINDOW_POINTS)).exp()
        sigma_k, delta_k = zero_pair(s_k, gam, u_w2)
        if abs(sigma_k.imag).upper() < delta_k.real.lower():
            total += eng.flux_complex(*eng.chart_m(s_k.exp(), gam, u_w2))
        else:
            total += window_flux_m(s_k, gam, u_w2, WINDOW_REACH)
            windows += 1
    mean = total / WINDOW_POINTS
    centre = eng.flux_enclosure(*eng.chart_m(acb(s0).real.exp(), gam.real, u_w2.real))
    agree1 = all(vv.overlaps(w1[0]) for vv in w1)
    agree2 = invalid and w2[0].overlaps(w2[1])
    agree3 = windows > 0 and abs(mean - centre).upper() < 1e-8
    ok = agree1 and agree2 and agree3 and agree4
    print(f"WINDOW control: (W1) s = 3/10 + i/20, gamma 1/100, u 1/100: reach 1/2, 1/4, real F = {w1[0].real.mid().str(10)} agree "
          f"{agree1}; (W2) s = 3/10 + 3i/5, gamma 1/20, u 1/1000: real contour invalid {invalid}, reach 1/2, 1/4 agree {agree2}; "
          f"(W4) s = 200/27 + 35i/36, gamma 53/100, u 1e-8: F = {w4[0].real.mid().str(10)} + {w4[0].imag.mid().str(6)} i, reach "
          f"1/2, 1/4 agree {agree4}; (W3) mean over |s - 3/10| = 1 ({windows}/{WINDOW_POINTS} windows) {mean.real.mid().str(10)} "
          f"vs F(3/10) {centre.mid().str(10)}, |diff| {float(abs(mean - centre).upper()):.1e} -> {'ok' if ok else 'FAIL'}",
          flush=True)
    return ok


def path_flux(masses, spec, tval):
    """f of the REAL configuration at real t on the mass-centre path, by the engine alone (its own zero (a p2 + b p1)/(a + b) =
    pbar + t d_0): feet Re p_j(t), depths -Im p_j(t). Independent of mc1_config and of the t-series."""
    aa, bb, p1, _, dd, _ = spec
    pbar = p1 + bb * dd
    pts = (pbar - bb * dd * tval, pbar + aa * dd * tval)
    return eng.flux_enclosure(masses, tuple(pp.real for pp in pts), tuple(-pp.imag for pp in pts))


def mc1_control():
    """Controls that CAN fail for Sec. 3c at point parameters: (i) t-series coefficient 0 overlaps merged_density (H_0 = 2ab D1) and
    the path config at t = 1 overlaps the configuration's H; (ii) f(t) = O(t^2) on the path (int H_0 = int H_1 = 0) by the ENGINE:
    f(1/10)/f(1/100) in [60, 140] (a nonzero int H_1 would give ~10); (iii) at u = 20 the MC1 bound is >= |f| and below the plain
    bound (so MC1 is really used)."""
    ok = True
    for s_txt, g_txt, u_txt in (("0", "13/10", "20"), ("1/2", "13/10", "20"), ("1/2", "1", "3")):
        s_pt, g_pt, u_pt = acb(ex(s_txt)), acb(ex(g_txt)), acb(ex(u_txt))
        cfg = chart_m_config(s_pt, g_pt, u_pt)
        spec = u_spec(cfg, g_pt, u_pt)
        saved = ctx.cap
        ctx.cap = MC1_K + 1
        try:
            at_zero, at_one = mc1_config(cfg, spec, acb_series([acb(0), acb(1)])), mc1_config(cfg, spec, acb(1))
            for zz in (-30.0, -0.7, 0.0, 0.4, 2.0, 25.0):
                ok &= bool(h_integrand_wc(acb(zz), at_zero)[0].overlaps(merged_density(acb(zz), cfg)))
                ok &= bool(h_integrand_wc(acb(zz), at_one).overlaps(h_integrand_wc(acb(zz), cfg)))
        finally:
            ctx.cap = saved
        masses = tuple(aa.real for aa in cfg["amps"])
        ratio = path_flux(masses, spec, ex(Fraction(1, 10))) / path_flux(masses, spec, ex(Fraction(1, 100)))
        ok &= bool(60 < ratio.mid() < 140)
        flux = eng.flux_enclosure(*eng.chart_m(s_pt.real.exp(), g_pt.real, u_pt.real))
        plain, both = sup_f(s_pt, g_pt, u_pt), sup_f(s_pt, g_pt, u_pt, True)
        ok &= abs(flux).upper() <= both
        if u_txt == "20":
            ok &= both < plain
        print(f"MC1 control (s, gamma, u) = ({s_txt}, {g_txt}, {u_txt}): f(1/10)/f(1/100) = {float(ratio.mid()):.2f}; |f| "
              f"{float(abs(flux).upper()):.3e} <= MC1 {float(both):.3e} (plain {float(plain):.3e})", flush=True)
    return ok


def wframe_control():
    """Controls that CAN fail for Sec. 1b on box s [-1/8, 1/8] x gamma [5/4, 11/8]: (i) W1 dilation: g_node = (w0/2) u^2 f(u)
    overlaps (w0/2) f_dil(w)/w from the engine on the DILATED configuration (masses, feet (0, w cos g), depths (1, 1 + w sin g));
    (ii) g_sup at that real node (point s, gamma) >= |g_node|."""
    ok = True
    box = make_box(Fraction(-1, 8), Fraction(1, 8), Fraction(5, 4), Fraction(11, 8))
    frame, w0 = w_frame(box), (-ex(V_W)).exp()
    for s_pt, g_pt, yy in ((ex(0), ex(Fraction(13, 10)), ex(Fraction(1, 3))),
                           (ex(Fraction(1, 8)), ex(Fraction(5, 4)), ex(Fraction(1, 2 ** 20) - 1))):
        node = frame["g_node"](s_pt, g_pt, yy)
        ww = w0 * (1 - yy) / 2
        masses, _, _ = eng.chart_m(s_pt.exp(), g_pt, ww)
        dil = w0 / 2 * eng.flux_enclosure(masses, (arb(0), ww * g_pt.cos()), (arb(1), 1 + ww * g_pt.sin())) / ww
        bound = frame["g_sup"](acb(s_pt), acb(g_pt), yy)
        ok &= bool(node.overlaps(dil)) and abs(node).upper() <= bound
        print(f"w-frame control w = {float(ww.mid()):.4f}: g_node {float(node.mid()):+.6e}, dilated {float(dil.mid()):+.6e}, "
              f"g_sup {float(bound):.3e}", flush=True)
    return ok


def integrand_control():
    """Control that CAN fail: h_integrand_wc must overlap eng.h_integrand at real points z near and far from every foot, for
    point parameters (depths 1e-6 .. 20, complex gamma and complex s inside the domain), and be much narrower on parameter balls."""
    ok = True
    cases = ((ex(0), ex("13/10"), ex("1/1000000")), (ex("1/3"), ex("1/2"), ex(20)),
             (ex(0) + acb(0, ex("1/5")), ex("13/10"), ex("1/100")), (ex(1), ex("13/10") + acb(0, ex("1/4")), ex("1/10")))
    for s_pt, g_pt, u_pt in cases:
        cfg = eng.make_config(*eng.chart_m(acb(s_pt).exp(), acb(g_pt), acb(u_pt)), derivative=False)
        feet = sorted({float(eng.value(cc).real.mid()) for cc in cfg["points"]})
        for zz in [ff + dd for ff in feet for dd in (0.0, 1e-7, 3e-3, -0.2, 5.0)] + [-40.0, 1e4]:
            old, new = eng.h_integrand(acb(zz), cfg, False), h_integrand_wc(acb(zz), cfg)
            ok &= bool(old.overlaps(new))
    wide = eng.make_config(*eng.chart_m(eng.box("-1/8", "1/8").exp(), acb(eng.box("5/4", "11/8")), acb(ex(-6).exp())), False)
    zz = acb(eng.box("1/2000", "1/1000"))
    old, new = abs(eng.h_integrand(zz, wide, False)).upper(), abs(h_integrand_wc(zz, wide)).upper()
    print(f"integrand control: point overlaps {'ok' if ok else 'FAIL'}; parameter-ball |H| near pole 1: engine {float(old):.3e}, "
          f"well-conditioned {float(new):.3e}", flush=True)
    return ok and merged_control()


def merged_control():
    """Controls that CAN fail for Sec. 3b: (i) merged_density = 2ab * eng.single_integrand of a unit pole at pbar (overlap at real
    points); (ii) eng.single_control at that pole: int_{-X}^{X} D1 = -(its tails) (the identity int_R D1 = 0); (iii) sup_f (the
    subtracted majorant) >= |f| at the point."""
    ok = True
    for s_pt, g_pt, u_pt in ((ex(0), ex("13/10"), ex(20)), (ex("1/2"), ex("3/4"), ex("1/1000"))):
        masses, feet, depths = eng.chart_m(s_pt.exp(), g_pt, u_pt)
        cfg = eng.make_config(masses, feet, depths, derivative=False)
        pbar = masses[0] * cfg["points"][1] + masses[1] * cfg["points"][2]
        unit = ((arb(1), arb(1)), (pbar.real, pbar.real + 3), (-pbar.imag, -pbar.imag))
        cfg1 = eng.make_config(*unit, derivative=False)
        for zz in (float(pbar.real.mid()) + dd for dd in (0.0, 1e-4, -0.3, 2.0, -50.0)):
            want = 2 * masses[0] * masses[1] * eng.single_integrand(acb(zz), cfg1, False)
            ok &= bool(merged_density(acb(zz), cfg).overlaps(want))
        core, expected = eng.single_control(*unit)
        ok &= abs(core - expected).upper() < 1e-8
        flux = eng.flux_enclosure(masses, feet, depths)
        bound = sup_f(acb(s_pt), acb(g_pt), acb(u_pt))
        ok &= abs(flux).upper() <= bound
        print(f"merged control u = {float(u_pt.mid()):.0e}: |f| = {float(abs(flux).upper()):.3e} <= subtracted majorant "
              f"{float(bound):.3e}; int D1 control {float(core.mid()):+.2e} vs {float(expected.mid()):+.2e}", flush=True)
    return ok


def main():
    args = sys.argv[1:]
    print(f"chartM v{VERSION} (driver md5 {file_md5(__file__)}, engine md5 {file_md5(eng.__file__)}, cheb3 md5 "
          f"{file_md5(c3.__file__)}, prec {bc.WORK_PREC})", flush=True)
    if args == ["--test"]:
        sys.exit(0 if main_test() else 1)
    gmap = "log" if "--lambda" in args else "lin"
    args = [aa for aa in args if aa != "--lambda"]
    plan_only = len(args) == 5 and args[0] == "--plan"
    global PLAN_MODE
    PLAN_MODE = plan_only
    if len(args) != 4 and not plan_only:
        sys.exit(__doc__)
    bc.apply_work_settings()
    box = make_box(*(Fraction(aa) for aa in args[-4:]), gmap)
    sys.exit(0 if certify(box, plan_only) else 1)


def file_md5(path):
    """House hash: md5, first 8 hex digits."""
    with open(path, "rb") as handle:
        return hashlib.md5(handle.read()).hexdigest()[:8]


if __name__ == "__main__":
    main()
