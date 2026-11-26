#!/usr/bin/env python3
# chartM.py - P020 P7 chart M BACKWARD certificate on a parameter box (s = log r, gamma) by 3D tensor cells
##   (deep_piece; 09:23 [-14,-13] K = 4 -> 1.8e-4); DUMP (certify mode): every node, majorant call, cell, deep piece as JSON lines
##  ; RHO_W_CHOICES + 3/2 as v0.61
##   Lemmas W0-W2); MC1 majorant (min with the plain one); POINTS FORM (M_g, M_s at the y-nodes); SUBTRACTED_TAYLOR code removed
##   an inconclusive comparison of two sine balls could pick the wrong one). No other change.
##   the engine's /(a+b) inflated it); SUB_S/SUB_G sub-balls in axis_parameter_balls (default 1 = unchanged balls). No other change.
##   (older version lines: versions/chartM_version_0.50.py)
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

W_CELL = True        # v0.60: W-CELL on top (anchor D1 - k0 exactly); False = v0.50 path (CLUSTER-W anchor at e^V_TOP)
V_TOP = 4
V_W = Fraction(1, 2)  # W-CELL covers u >= e^V_W (w0 = e^-V_W = 0.6065); u-cells start below it
N_U_CELLS = 7 if W_CELL else 12   # v0.70: 7 u-cells to -27/2; crude sub-boxed pieces below (09:23: [-14,-13] K = 4 -> 1.8e-4)
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
DEG_MAX = (20, 20, 32)
MAX_TOL = Fraction(1, 50000)
PREFIX_TARGET = Fraction(1, 2000)
IM_S_SHARE = Fraction(4, 5)   # s-ellipse: |Im s| (with cover radius) <= IM_S_SHARE * g_lo
LOG = []


def ex(num):
    return eng.exact(num)


def fail(message):
    print(f"FAIL: {message}", flush=True)
    sys.exit(1)


def make_box(s_lo, s_hi, g_lo, g_hi):
    """Box record; rho_s is the largest choice whose s-ellipse (plus cover radius) keeps |Im s| <= IM_S_SHARE g_lo."""
    box = {"s": (s_lo, s_hi), "g": (g_lo, g_hi), "s_c": (s_lo + s_hi) / 2, "s_h": (s_hi - s_lo) / 2,
           "g_c": (g_lo + g_hi) / 2, "g_h": (g_hi - g_lo) / 2}
    for rho in RHO_S_CHOICES:
        if ex(box["s_h"]) * (minor(rho) + cover_radius(rho)) <= ex(IM_S_SHARE * g_lo):
            box["rho_s"] = rho
            return box
    fail(f"s half-width {box['s_h']} too large for g_lo = {g_lo} on the real contour (needs a window)")


def minor(rho):
    return (ex(rho) - 1 / ex(rho)) / 2


def major(rho):
    return (ex(rho) + 1 / ex(rho)) / 2


def cover_radius(rho):
    """bc.ellipse_cover radius in the scaled coordinate: (pi/COVER) * semi-major."""
    return arb.pi() / COVER * major(rho)


def assert_filled_domain(box):
    """Sec. 3 conditions on the FILLED ellipses (exact arithmetic; strict)."""
    g_lo, g_hi = ex(box["g"][0]), ex(box["g"][1])
    im_s = ex(box["s_h"]) * (minor(box["rho_s"]) + cover_radius(box["rho_s"]))
    if not (im_s < g_lo and g_hi + im_s < arb.pi()):
        fail(f"s-axis domain: |Im s| <= {float(im_s.upper()):.4f} vs g_lo, pi - g_hi")
    reach = ex(box["g_h"]) * (major(RHO_G) + cover_radius(RHO_G))
    if not (ex(box["g_c"]) - reach > 0 and ex(box["g_c"]) + reach < arb.pi()):
        fail("gamma-axis domain: Re gamma must stay in (0, pi) on the filled ellipse")
    if not (minor(RHO_Y) + cover_radius(RHO_Y) < arb.pi() / 2):
        fail("y-axis domain: |Im y| must stay below pi/2")


def real_seg(box, key):
    lo, hi = box[key]
    return eng.box(lo, hi)


def s_at(box, xx):
    return ex(box["s_c"]) + ex(box["s_h"]) * xx


def g_at(box, zz):
    return ex(box["g_c"]) + ex(box["g_h"]) * zz


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
    masses, feet, depths = eng.chart_m(s_ball.exp(), g_ball, u_ball)
    zero = (masses[0] * g_ball.cos(), masses[0] * g_ball.sin() + u_ball)
    return eng.make_config(masses, feet, depths, derivative=False, zero=zero, contour="real")


def u_spec(cfg, g_ball, u_ball):
    """MC1 data (Sec. 3c) of the u-frame config: p1 = -iu, p1# = iu, D = p2 - p1 = e^{-i gamma}, D# = e^{i gamma} (exact forms)."""
    aa, bb = cfg["amps"]
    return aa, bb, -acb(0, 1) * u_ball, acb(0, 1) * u_ball, (-acb(0, 1) * g_ball).exp(), (acb(0, 1) * g_ball).exp()


def sup_f(s_ball, g_ball, u_ball, mc1=False):
    """Exact upper endpoint >= sup |f| over the u-frame parameter ball (REAL-contour config; make_config asserts the domain)."""
    cfg = chart_m_config(s_ball, g_ball, u_ball)
    return sup_f_cfg(cfg, u_spec(cfg, g_ball, u_ball) if mc1 else None)


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


def sub_segments(box, key, count):
    """The real segment of `key` in `count` equal exact sub-balls (their union is the whole segment)."""
    lo, hi = box[key]
    edges = [lo + (hi - lo) * Fraction(jj, count) for jj in range(count + 1)]
    return [eng.box(aa, bb) for aa, bb in zip(edges[:-1], edges[1:])]


def u_frame(box, centre):
    """u-cell v in [centre - 1, centre + 1] (Sec. 2): g = u f(u), u = e^{centre + y}; rhos (rho_s of the box, RHO_G, RHO_Y)."""
    def g_sup(s_ball, g_ball, yy):
        uu = u_at(centre, yy)
        return (sup_f(s_ball, g_ball, acb(uu), MC1_U_CELLS) * abs(uu).upper()).upper()

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
             lambda rr: w0 * (ex(box["g_h"]) * (minor(rr) + cover_radius(rr))).exp() <= margin,
             lambda rr: w0 / 2 * (1 + major(rr) + arb(2).sqrt() * cover_radius(rr)) <= margin)
    out = []
    for axis, test in enumerate(tests):
        passing = [rr for rr in RHO_W_CHOICES if test(rr)]
        if not passing:
            fail(f"w-cell axis {axis}: no rho in {RHO_W_CHOICES} keeps the offsets <= {W_MARGIN} (W2)")
        out.append(max(passing))
    return tuple(out)


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


def axis_majorant(box, frame, axis, y_points):
    """M_axis (Sec. 2, POINTS FORM): max over the COVER balls of the axis ellipse curve of frame g_sup; the other axes take: s and
    gamma their whole real segments (SUB_S / SUB_G sub-balls), y its ellipse ball (axis 2) or each y-node point (axes 0, 1)."""
    worst = arb(0)
    for zc, radius in bc.ellipse_cover(ex(frame["rhos"][axis]), COVER):
        zball = complex_ball(zc, radius)
        s_balls = [s_at(box, zball)] if axis == 0 else [acb(ss) for ss in sub_segments(box, "s", SUB_S)]
        g_balls = [g_at(box, zball)] if axis == 1 else [acb(gg) for gg in sub_segments(box, "g", SUB_G)]
        for yy in ([zball] if axis == 2 else y_points):
            for ss in s_balls:
                for gg in g_balls:
                    value = frame["g_sup"](acb(ss), acb(gg), yy)
                    worst = value if value > worst else worst
                    dump({"k": "maj", "cell": frame["label"], "axis": axis, "s": ball_text(ss), "g": ball_text(gg),
                          "y": ball_text(yy), "bound": repr(float(value) * (1 + 1e-9))})
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
    low_a, low_b = ex(box["g"][0]).sin().lower(), ex(box["g"][1]).sin().lower()  # exact points: the comparison is decisive
    h_min = low_a if low_a < low_b else low_b
    if h_min >= ex(Fraction(1, 2)):
        me = (u_b * (64 / h_min ** 4 * (1 + log_term) + 4096 / (a_min ** 2 * h_min ** 8))).upper()
        best = me if me < best else best
    return best


def deep_piece(box, lo, hi):
    """(bound, K): bound >= int_lo^hi |f| du for every (s, gamma) in the box = (hi - lo) * max over K x K exact (s, gamma) sub-boxes of
    sup|f| on the REAL u-piece ball (CELL-UP); K = the first of DEEP_SUB whose bound <= DEEP_PIECE_TARGET, else the last K."""
    u_ball = acb((lo + hi) / 2 + (hi - lo) / 2 * arb(0, 1))
    for kk in DEEP_SUB:
        worst = arb(0)
        for ss in sub_segments(box, "s", kk):
            for gg in sub_segments(box, "g", kk):
                value = sup_f(acb(ss), acb(gg), u_ball)
                worst = value if value > worst else worst
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
        print(f"DEEP pieces from e^{V_BOT} down: {' '.join(pieces)}", flush=True)
    return b_now, ex(vv).exp(), ok


def certify(box, plan_only):
    assert_filled_domain(box)
    a_t = anchor()
    where = f"u = oo (W-CELL to e^{V_W})" if W_CELL else f"u = e^{V_TOP}"
    print(f"CHARTM box s in [{box['s'][0]}, {box['s'][1]}], gamma in [{box['g'][0]}, {box['g'][1]}]: rho_s {box['rho_s']}, "
          f"anchor A = {float(a_t.lower()):.6f} at {where}, u-cells v in [{V_BOT}, {V_W if W_CELL else V_TOP}]", flush=True)
    state = {"A_T": a_t, "E": arb(0), "G": None}
    if not plan_only:
        tag = "_".join(str(edge).replace("/", "o") for edge in box["s"] + box["g"])
        path = f"logs/dump_box_{tag}_v070.jsonl"
        DUMP["handle"] = open(path, "w", encoding="utf-8")
        print(f"DUMP (P2-B input): {path}", flush=True)
        dump({"k": "box", "s": [str(edge) for edge in box["s"]], "g": [str(edge) for edge in box["g"]], "A": ball_text(a_t),
              "driver_md5": file_md5(__file__), "engine_md5": file_md5(eng.__file__), "cheb3_md5": file_md5(c3.__file__)})
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
    assert_filled_domain(box)
    frame = w_frame(box)
    sups, degrees = cell_plan(box, frame)
    _, biggest = node_tensor(box, frame, (2, 2, degrees[2]))
    ok &= all(biggest <= mm for mm in sups)
    print(f"{frame['label']}: majorants {[f'{float(mm):.3e}' for mm in sups]}, rhos {frame['rhos']}, degrees {degrees}, "
          f"max |g(nodes)| {float(biggest):.3e}, MC1 {MC1_STATS}", flush=True)
    print("TEST", "PASS" if ok else "FAIL", flush=True)
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
    if args == ["--test"]:
        sys.exit(0 if main_test() else 1)
    plan_only = len(args) == 5 and args[0] == "--plan"
    global PLAN_MODE
    PLAN_MODE = plan_only
    if len(args) != 4 and not plan_only:
        sys.exit(__doc__)
    bc.apply_work_settings()
    box = make_box(*(Fraction(aa) for aa in args[-4:]))
    print(f"chartM v0.71 (driver md5 {file_md5(__file__)}, engine md5 {file_md5(eng.__file__)}, cheb3 md5 "
          f"{file_md5(c3.__file__)}, prec {bc.WORK_PREC})", flush=True)
    sys.exit(0 if certify(box, plan_only) else 1)


def file_md5(path):
    """House hash: md5, first 8 hex digits."""
    with open(path, "rb") as handle:
        return hashlib.md5(handle.read()).hexdigest()[:8]


if __name__ == "__main__":
    main()
