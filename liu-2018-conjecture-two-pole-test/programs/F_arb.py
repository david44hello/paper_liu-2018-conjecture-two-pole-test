#!/usr/bin/env python3
# F_arb.py - P020 rung [1] INTEGRAL-BUDGET engine: rigorous arb enclosures of the boundary flux F and of dF/dt (common shift t)
# F = (1/pi) int_R (|r_S|^2 - k0 |S|^2) dx (FLUX, accepted); r_S = (1/2) sum_{j,k} (-a_j) eps_k T_{p_j,r_k} (RATLOG (7)), log points
# r_k = zero (eps = +1) and poles (eps = -1), T_{p,r}(z) = [conj Log(z - r) - conj Log(conj p - r)]/(z - p) - [Log(z - p) - Log(conj r - p)]/(z - conj r).
# SINGLE-POLE PARTS REMOVED EXACTLY: r_j := (a_j/2) T_{p_j,p_j} is r of pole j alone, c := r - r_1 - r_2, and
#   H := |r|^2 - k0|S|^2 - sum_j (|r_j|^2 - k0|S_j|^2) = 2Re[r_1 conj r_2] + 2Re[(r_1 + r_2) conj c] + |c|^2 - 2 k0 Re[S_1 conj S_2].
# int_R (|r_j|^2 - k0|S_j|^2) = 0 (one pole's Def0 is D1 a_j^2 at every depth), so F = (1/pi) int_R H; H has no 1/h cancellation.
# HOLOMORPHIC FORM: on R, conj Log(x - c) = Log(x - conj c) (c off R), so |w|^2 = w(x) w#(x), w#(x) := conj w(conj x); all factors are
# holomorphic in |Im x| < (least depth of a pole or the zero). Logs use analytic=True (cut touched => NaN => acb.integral splits).
# VERTICAL CUTS (v0.60): the principal Log(z - c) has its cut running LEFT from c, parallel to R at distance h, so every panel on
# x < min Re c needs ~ length/h subdivisions. On R, Im(z - c) > 0 for points c (Im c < 0) and < 0 for partners c#, so exactly
#   Log(z - c) = Log(-i (z - c)) + i pi/2,   Log(z - c#) = Log(i (z - c#)) - i pi/2,
# whose cuts run vertically AWAY from R (down from c, up from c#): the integrand is analytic off those rays and the poles.
# DERIVATIVE: along the common shift every pole and the zero move by -i dt (t real), so Dual(value, d/dt) arithmetic on the same code
# gives dH/dt. Masses, feet and depths may be arb BALLS (a parameter box): acb.integral then encloses int H dx for EVERY point of the box.
# RANGE: geometric panels on [-X, X]; the tails |x| > X use the explicit majorants of tail_bound() / tail_bound_deriv().
# COMPLEX PARAMETERS: every conj point is replaced by its analytic
# partner p# = f + i h (p = f - i h; f, h, masses real-analytic in the parameters), and conj Log(conj p - r) = Log(p - r#) etc.
# (arguments never on the cut: Im(p - r#) = -(h_p + h_r) < 0). For real parameters this is exactly the old conj() form.
# DOMAIN: every point (zero, poles) has Im < 0 and every partner
# Im > 0, and m1 + m2 != 0. Then on R every -i(x - c) and i(x - c#) has positive real part (vertical-cut logs analytic), the four
# constant logs have arguments off R, and no denominator vanishes: the integrand is analytic in the parameters along all of R.
# (For complex masses the zero is NOT a convex combination of the poles, so this must be checked, not inferred.)
#   c1 = Log(p - r#), c2s = Log(r - p#) (argument in the LOWER half-plane at real parameters) and c2 = Log(r# - p), c1s = Log(p# - r)
#   (UPPER) is continued from that half-plane by a FIXED rotated branch (log_dn: cut up the positive imaginary axis; log_up: cut down
#   the negative imaginary axis), certified off its cut on the whole ball. Equal to the principal values at real parameters. Whether
#   the cut is avoided along a whole path from the real parameters is the chart caller's continuation argument.
# CHARTS: normalized masses a = 1/(1+r), b = 1 - a;
#   C: feet -1, +1, common depth t;  M: pole 1 (mass a, shallower) at -i tau, pole 2 (mass b) at cos(gamma) - i(sin(gamma) + tau).
import math
import sys
import time
from fractions import Fraction
from flint import acb, arb, ctx

sys.dont_write_bytecode = True
PREC = 128
X_BASE = 10**18
RATIO = 4
TOL_REL, TOL_ABS = arb(2) ** -50, arb(2) ** -70
OWN = ((0, 1), (1, 2))
IMAG = acb(0, 1)


def half_pi_i():
    """i pi/2 at the CURRENT working precision (a module constant would be fixed at import-time precision)."""
    return acb(0, arb.pi() / 2)


class Dual:
    """value v and derivative d along the common depth shift; t is real, so conjugation acts on both parts."""
    __slots__ = ("v", "d")

    def __init__(self, vv, dd):
        self.v, self.d = acb(vv), acb(dd)

    def __add__(self, oo):
        oo = lift(oo)
        return Dual(self.v + oo.v, self.d + oo.d)

    __radd__ = __add__

    def __sub__(self, oo):
        oo = lift(oo)
        return Dual(self.v - oo.v, self.d - oo.d)

    def __rsub__(self, oo):
        return lift(oo) - self

    def __neg__(self):
        return Dual(-self.v, -self.d)

    def __mul__(self, oo):
        oo = lift(oo)
        return Dual(self.v * oo.v, self.d * oo.v + self.v * oo.d)

    __rmul__ = __mul__

    def __truediv__(self, oo):
        oo = lift(oo)
        return Dual(self.v / oo.v, (self.d * oo.v - self.v * oo.d) / (oo.v * oo.v))

    def log(self, analytic=False):
        return Dual(self.v.log(analytic=analytic), self.d / self.v)

    def conjugate(self):
        return Dual(self.v.conjugate(), self.d.conjugate())


def lift(obj):
    return obj if isinstance(obj, Dual) else Dual(obj, 0)


def value(obj):
    return obj.v if isinstance(obj, Dual) else obj


def k0():
    return arb.pi() ** 2 / 12


def exact(num):
    frac = Fraction(num)
    return arb(frac.numerator) / frac.denominator


def exact_pair(nums):
    return tuple(exact(nn) for nn in nums)


def box(lo, hi):
    """arb ball containing the closed interval [lo, hi] (exact endpoints)."""
    return (exact(lo) + exact(hi)) / 2 + (exact(hi) - exact(lo)) / 2 * arb(0, 1)


def chart_c(ratio, depth):
    """ASSEMBLY chart C: feet -1, +1, common depth t; normalized masses (r, t: arb points or balls)."""
    amass = 1 / (1 + ratio)
    return (amass, 1 - amass), (arb(-1), arb(1)), (depth, depth)


def chart_m(ratio, gamma, tau):
    """ASSEMBLY chart M: pole 1 (mass a) at -i tau, pole 2 (mass b) at cos(gamma) - i(sin(gamma) + tau); unit pole distance."""
    amass = 1 / (1 + ratio)
    return (amass, 1 - amass), (arb(0), gamma.cos()), (tau, gamma.sin() + tau)


def log_up(ww):
    """Log w continued from the UPPER half-plane: cut DOWN the negative imaginary axis; principal Log wherever Im w >= 0."""
    return (ww * (-IMAG)).log() + half_pi_i()


def log_dn(ww):
    """Log w continued from the LOWER half-plane: cut UP the positive imaginary axis; principal Log wherever Im w <= 0 (w != neg. R)."""
    return (ww * IMAG).log() - half_pi_i()


def const_log(ww, upper):
    """Constant (parameter-only) log on its fixed rotated branch, certified off that branch's cut on the whole ball (v1.20)."""
    rot = ww * (-IMAG if upper else IMAG)
    assert off_cut(value(rot)), f"constant log argument {value(ww)} may meet its {'log_up' if upper else 'log_dn'} cut"
    return log_up(ww) if upper else log_dn(ww)


def make_pair(coef, points, sharp, ip, ir):
    """c1 = conj Log(conj p - r) = Log(p - r#), c2 = Log(r# - p) and their partners c1# = Log(p# - r), c2# = Log(r - p#);
    fixed rotated branches from the physical half-planes (lower: c1, c2#; upper: c2, c1#), see CONSTANT LOGS."""
    pp, rr, pps, rrs = points[ip], points[ir], sharp[ip], sharp[ir]
    return {"coef": coef, "ip": ip, "ir": ir, "c1": const_log(pp - rrs, False), "c2": const_log(rrs - pp, True),
            "c1s": const_log(pps - rr, True), "c2s": const_log(rr - pps, False)}


def is_real(params):
    return all(acb(xx).imag.is_zero() for xx in params)


def assert_domain(points, sharp):
    """Certified on the whole ball: every point strictly below R, every analytic partner strictly above R (see DOMAIN above)."""
    for cc in points:
        assert value(cc).imag.upper() < 0, f"a point may touch or cross R: {value(cc)}"
    for cc in sharp:
        assert value(cc).imag.lower() > 0, f"a partner point may touch or cross R: {value(cc)}"


def frame_points(poles, poles_sharp, zero_pt, zero_sharp, shift):
    """(integrand points, integrand partners, constant points, constant partners). shift None: one frame. shift sigma (WINDOW frame,
    v1.30): the integrand uses poles - sigma and the zero as given (already in the shifted frame); the constants use the UNSHIFTED
    poles and zero + sigma. Pair differences are translation invariant, and the unshifted ones keep exact cancellations (own pairs
    p - p# = -2i depth): shifting both feet by a ball sigma first would add 2 rad(sigma) to every pole-pole difference."""
    if shift is None:
        points, sharp = [zero_pt, *poles], [zero_sharp, *poles_sharp]
        return points, sharp, points, sharp
    sig = acb(shift)
    return ([zero_pt, poles[0] - sig, poles[1] - sig], [zero_sharp, poles_sharp[0] - sig, poles_sharp[1] - sig],
            [zero_pt + sig, *poles], [zero_sharp + sig, *poles_sharp])


def make_config(masses, feet, depths, derivative, zero=None, contour="real", shift=None):
    """masses, feet, depths: PAIRS of arb or acb (points or BALLS = a parameter box; acb = complexified parameters). Pole
    p_j = feet[j] - i depths[j] with analytic partner p_j# = feet[j] + i depths[j] (= conj p_j for real parameters; never a conj()
    of a complex ball); each depth includes the common shift t; derivative: Dual mode (dp/dt = -i, dp#/dt = +i).
    zero: optional (foot, depth): the zero of S given EXPLICITLY as foot - i depth (partner foot + i depth). For WINDOW frames, where
    the caller has translated so that the zero sits exactly at -i u: then no ball cancellation is needed (the caller guarantees it
    IS the zero of S for every parameter in the ball). contour: "real" asserts the real-contour DOMAIN; "window" does not, and every
    piece used with such a config must pass branch_check().
    shift (v1.30, needs zero): feet are given UNSHIFTED; the config's integrand frame is z' = z - shift (see frame_points)."""
    assert all(acb(dd).real.lower() > 0 for dd in depths), f"pole depths not certified positive: {depths}"
    assert contour in ("real", "window"), f"unknown contour mode {contour}"
    wrap = (lambda vv, dd: Dual(vv, dd)) if derivative else (lambda vv, dd: vv)
    amps = [wrap(acb(mm), 0) for mm in masses]
    poles = [wrap(acb(ff) - IMAG * acb(dd), -IMAG) for ff, dd in zip(feet, depths)]
    poles_sharp = [wrap(acb(ff) + IMAG * acb(dd), IMAG) for ff, dd in zip(feet, depths)]
    total = amps[0] + amps[1]
    assert not value(total).contains(0), f"mass sum may vanish: {value(total)}"
    if zero is None:
        zero_pt = (amps[0] * poles[1] + amps[1] * poles[0]) / total
        zero_sharp = (amps[0] * poles_sharp[1] + amps[1] * poles_sharp[0]) / total
    else:
        zero_pt = wrap(acb(zero[0]) - IMAG * acb(zero[1]), -IMAG)
        zero_sharp = wrap(acb(zero[0]) + IMAG * acb(zero[1]), IMAG)
    assert shift is None or zero is not None, "shift needs the zero given explicitly in the shifted frame"
    points, sharp, c_points, c_sharp = frame_points(poles, poles_sharp, zero_pt, zero_sharp, shift)
    if contour == "real":
        assert_domain(points, sharp)
    eps = [1, -1, -1]
    pairs = {(jj, kk): make_pair(-amps[jj] * eps[kk] / 2, c_points, c_sharp, jj + 1, kk) for jj in range(2) for kk in range(3)}
    if contour == "real":
        least = min(float((-value(cc).imag).lower()) for cc in points)  # certified positive by assert_domain; panel scale only
    else:
        least = min(float(acb(dd).real.lower()) for dd in depths + ((zero[1],) if zero is not None else ()))
    xcut = X_BASE * max(1, math.ceil(1 / least))
    return {"amps": amps, "points": points, "sharp": sharp, "pairs": pairs, "k0": wrap(k0(), 0),
            "lift": lift if derivative else acb, "xcut": xcut, "least": least, "real": is_real((*masses, *feet, *depths))}


def t_hol(zz, logs, logs_sharp, cfg, pair):
    pp, rrs = cfg["points"][pair["ip"]], cfg["sharp"][pair["ir"]]
    return (logs_sharp[pair["ir"]] - pair["c1"]) / (zz - pp) - (logs[pair["ip"]] - pair["c2"]) / (zz - rrs)


def t_sharp(zz, logs, logs_sharp, cfg, pair):
    pps, rr = cfg["sharp"][pair["ip"]], cfg["points"][pair["ir"]]
    return (logs[pair["ir"]] - pair["c1s"]) / (zz - pps) - (logs_sharp[pair["ip"]] - pair["c2s"]) / (zz - rr)


def log_below(zz, cc, analytic):
    """Log(z - c) for c below R (Im c < 0), cut vertically DOWN from c; equals the principal Log wherever Im(z - c) >= 0.
    (= log_up(z - c), with the analytic flag acb.integral needs.)"""
    return ((zz - cc) * (-IMAG)).log(analytic=analytic) + half_pi_i()


def log_above(zz, cc, analytic):
    """Log(z - c#) for c# above R (Im c# > 0), cut vertically UP from c#; equals the principal Log wherever Im(z - c#) <= 0.
    (= log_dn(z - c#), with the analytic flag acb.integral needs.)"""
    return ((zz - cc) * IMAG).log(analytic=analytic) - half_pi_i()


def r_parts(zz, cfg, analytic):
    logs = [log_below(zz, cc, analytic) for cc in cfg["points"]]
    logs_sharp = [log_above(zz, cc, analytic) for cc in cfg["sharp"]]
    hol = {key: pair["coef"] * t_hol(zz, logs, logs_sharp, cfg, pair) for key, pair in cfg["pairs"].items()}
    sharp = {key: pair["coef"] * t_sharp(zz, logs, logs_sharp, cfg, pair) for key, pair in cfg["pairs"].items()}
    cross = [key for key in cfg["pairs"] if key not in OWN]
    return [hol[key] for key in OWN], [sharp[key] for key in OWN], sum(hol[key] for key in cross), sum(sharp[key] for key in cross)


def h_integrand(zz, cfg, analytic):
    (r1, r2), (r1s, r2s), cc, ccs = r_parts(zz, cfg, analytic)
    (a1, a2), (p1, p2), (p1s, p2s) = cfg["amps"], cfg["points"][1:], cfg["sharp"][1:]
    s1, s2 = -a1 / (zz - p1), -a2 / (zz - p2)
    s1s, s2s = -a1 / (zz - p1s), -a2 / (zz - p2s)
    return r1 * r2s + r2 * r1s + (r1 + r2) * ccs + cc * (r1s + r2s) + cc * ccs - cfg["k0"] * (s1 * s2s + s2 * s1s)


def single_integrand(zz, cfg, analytic):
    (r1, _), (r1s, _), _, _ = r_parts(zz, cfg, analytic)
    a1, p1, p1s = cfg["amps"][0], cfg["points"][1], cfg["sharp"][1]
    return r1 * r1s - cfg["k0"] * (a1 * a1) / ((zz - p1) * (zz - p1s))


def breakpoints(cfg):
    centres = sorted({float(value(cc).real.mid()) for cc in cfg["points"]})
    spread = 4 * (max(abs(cc) for cc in centres) + 1)
    pts = set(centres) | {-spread, spread, -cfg["xcut"], cfg["xcut"]}
    for cc in centres:
        step = cfg["least"]
        while step < spread:
            pts |= {cc - step, cc + step}
            step *= RATIO
    step = spread
    while step < cfg["xcut"]:
        pts |= {-step, step}
        step *= RATIO
    return sorted(pp for pp in pts if -cfg["xcut"] <= pp <= cfg["xcut"])


def tail_constants(cfg):
    """Shared constants for |x| >= X >= 4 max|points|: |x - c| in [|x|/2, 3|x|/2]; |Log w| <= log|w| + pi (|w| >= 1);
    Lc = sum |c1| + |c2| + |c1#| + |c2#| >= max; ell(X) = log(1.5 X) + pi + Lc; C = 4 sum_cross |coef| (so |c| <= C ell/|x|);
    masses enter as |a_j| (complex parameters allowed)."""
    for cc in cfg["points"] + cfg["sharp"]:  # full ball radii, certified comparison
        assert abs(value(cc)).upper() < arb(cfg["xcut"]) / 4, f"tail premise X >= 4|c| not certified for {value(cc)}"
    pairs = cfg["pairs"].values()
    lc = sum(abs(value(pp[name])) for pp in pairs for name in ("c1", "c2", "c1s", "c2s"))
    ccross = 4 * sum(abs(value(pp["coef"])) for key, pp in cfg["pairs"].items() if key not in OWN)
    ell = arb(cfg["xcut"]).log() + arb(3).log() - arb(2).log() + arb.pi() + lc
    a1, a2 = (abs(value(aa)) for aa in cfg["amps"])
    return a1, a2, ccross, ell


def tail_bound(cfg):
    """|T| <= 4 ell(x)/|x|, |r_j| <= 2 a_j ell/|x|, |c| <= C ell/|x|, |S_j| <= 2 a_j/|x|, so |H| <= (8 a1 a2 + 4 A C + C^2) ell^2/x^2
    + 8 k0 a1 a2/x^2; int_X^oo (log x + c0)^2/x^2 = ((ell)^2 + 2 ell + 2)/X. Returns the bound on int_{|x|>X} |H| dx."""
    a1, a2, ccross, ell = tail_constants(cfg)
    lead = 8 * a1 * a2 + 4 * (a1 + a2) * ccross + ccross ** 2
    return 2 * (lead * (ell ** 2 + 2 * ell + 2) + 8 * k0() * a1 * a2) / cfg["xcut"]


def tail_bound_deriv(cfg):
    """d/dt: |T'| <= (8 m + 8 (1 + ell(X))/X)/|x| =: D_T/|x| with m = sum 1/|p - r#| + 1/|p# - r| >= max; |r_j'| <= (a_j/2) D_T/|x|,
    |c'| <= (C/4) D_T/|x|, |S_j'| <= 4 a_j/(X |x|). |H'| <= [(4 a1 a2 + 2 A C + C^2/2) D_T ell(x) + 32 k0 a1 a2/X]/x^2 and
    int_X^oo ell(x)/x^2 = (ell(X) + 1)/X. Returns the bound on int_{|x|>X} |H'| dx."""
    a1, a2, ccross, ell = tail_constants(cfg)
    points, sharp = [value(cc) for cc in cfg["points"]], [value(cc) for cc in cfg["sharp"]]
    mm = sum(1 / abs(points[pp["ip"]] - sharp[pp["ir"]]) + 1 / abs(sharp[pp["ip"]] - points[pp["ir"]])
             for pp in cfg["pairs"].values())
    xcut = cfg["xcut"]
    d_t = 8 * mm + 8 * (1 + ell) / xcut
    lead = 4 * a1 * a2 + 2 * (a1 + a2) * ccross + ccross ** 2 / 2
    return 2 * (lead * d_t * (ell + 1) / xcut + 32 * k0() * a1 * a2 / arb(xcut) ** 2)


def integrate(func, cfg, part):
    total = acb(0)
    pts = breakpoints(cfg)
    for lo, hi in zip(pts[:-1], pts[1:]):
        total += acb.integral(lambda zz, an: part(func(cfg["lift"](zz), cfg, an)), exact(lo), exact(hi), rel_tol=TOL_REL,
                              abs_tol=TOL_ABS, eval_limit=10**6)
    return total


def flux_enclosure(masses, feet, depths):
    """Ball containing F for every point of the REAL (masses, feet, depths) box."""
    cfg = make_config(masses, feet, depths, derivative=False)
    assert cfg["real"], "flux_enclosure needs real parameters: use flux_complex"
    core = integrate(h_integrand, cfg, lambda ww: ww)
    assert core.imag.contains(0), f"core integral not real: {core}"
    return (core.real + tail_bound(cfg) * arb(0, 1)) / arb.pi()


def flux_complex(masses, feet, depths):
    """acb ball containing the analytic continuation of F for every point of a COMPLEX parameter box (|F| bounds on ellipses)."""
    cfg = make_config(masses, feet, depths, derivative=False)
    core = integrate(h_integrand, cfg, lambda ww: ww)
    tail = tail_bound(cfg)
    return (core + acb(tail * arb(0, 1), tail * arb(0, 1))) / arb.pi()


def flux_derivative_enclosure(masses, feet, depths):
    """Ball containing dF/dt for every point of the REAL (masses, feet, depths) box."""
    cfg = make_config(masses, feet, depths, derivative=True)
    assert cfg["real"], "flux_derivative_enclosure needs real parameters"
    core = integrate(h_integrand, cfg, lambda ww: ww.d)
    assert core.imag.contains(0), f"derivative integral not real: {core}"
    return (core.real + tail_bound_deriv(cfg) * arb(0, 1)) / arb.pi()


MAJ_RATIO = 1.25  # geometric growth of the majorant panels (relative panel width ~ 25% of the distance to the nearest centre)


def majorant_points(cfg):
    """Fixed panel edges for majorant_bound: around every point/partner centre from least/4 outward, then out to +-X. EXACT
    Fractions (v1.10): float edges cc -+ step collapse onto cc once step < 1e-16 |cc| (depths ~1e-22 next to feet +-1)."""
    centres = sorted({Fraction(float(value(cc).real.mid())) for cc in cfg["points"] + cfg["sharp"]})
    spread = 4 * (max(abs(cc) for cc in centres) + 1)
    pts = set(centres) | {-spread, spread, Fraction(-cfg["xcut"]), Fraction(cfg["xcut"])}
    for cc in centres:
        step = cfg["least"] / 4
        while step < spread:
            pts |= {cc - Fraction(step), cc + Fraction(step)}
            step *= MAJ_RATIO
    step = float(spread)
    while step < cfg["xcut"]:
        pts |= {-Fraction(step), Fraction(step)}
        step *= 2 * MAJ_RATIO  # far field: H ~ log^2/x^2 is smooth on [x, 2.5x]
    return sorted(pp for pp in pts if -cfg["xcut"] <= pp <= cfg["xcut"])


def majorant_bound(masses, feet, depths):
    """Exact upper endpoint >= sup |F| over the WHOLE (complex) parameter ball: (1/pi)[sum over panels of width * sup|H| + tail].
    H is the cancelled integrand (single-pole parts removed) evaluated on (real panel ball) x (parameter ball): crude, since no
    cancellation between panels is used, but non-adaptive (~1e3 ball evaluations) and valid wherever the DOMAIN holds. For M bounds."""
    cfg = make_config(masses, feet, depths, derivative=False)
    pts = majorant_points(cfg)
    total = arb(0)
    for lo, hi in zip(pts[:-1], pts[1:]):
        total += (exact(hi) - exact(lo)) * abs(h_integrand(acb(box(lo, hi)), cfg, False)).upper()
    return ((total + tail_bound(cfg)) / arb.pi()).upper()


def off_cut(ww):
    """Certified: the ball ww avoids the closed negative real axis (the principal Log cut, and 0)."""
    return ww.real.lower() > 0 or ww.imag.lower() > 0 or ww.imag.upper() < 0


def branch_check(zz, cfg):
    """Certified on the contour piece zz (an acb ball): for every point c, -i(z - c) avoids the cut, and for every partner c#,
    i(z - c#) avoids it. Then the vertical-cut logs are analytic on the piece and no denominator 1/(z - c), 1/(z - c#) vanishes.
    (That the PRINCIPAL values are the analytic continuation along the chosen contour is the caller's contour argument.)"""
    for cc in cfg["points"]:
        assert off_cut((zz - value(cc)) * (-IMAG)), f"contour piece {zz} meets the cut of point {value(cc)}"
    for cc in cfg["sharp"]:
        assert off_cut((zz - value(cc)) * IMAG), f"contour piece {zz} meets the cut of partner {value(cc)}"


def majorant_on_pieces(cfg, pieces):
    """Exact upper endpoint of sum over contour pieces (zball, length) of length * sup|H| on the piece; every piece branch-checked.
    Shared tool for window/junction contours (zero-following frames) in complex-parameter M bounds."""
    total = arb(0)
    for zball, length in pieces:
        branch_check(zball, cfg)
        total += arb(length).upper() * abs(h_integrand(zball, cfg, False)).upper()
    return total.upper()


def real_pieces(edges):
    """Contour pieces (real panel ball, length) from sorted exact-convertible panel edges."""
    return [(acb(box(lo, hi)), exact(hi) - exact(lo)) for lo, hi in zip(edges[:-1], edges[1:])]


def single_control(masses, feet, depths):
    """int_{-X}^{X} (|r_1|^2 - k0|S_1|^2) must equal -(its tails) = -pi^2 a1^2/(3X) + O(log X/X^2): a control that CAN fail."""
    cfg = make_config(masses, feet, depths, derivative=False)
    core = integrate(single_integrand, cfg, lambda ww: ww)
    return core.real, -arb.pi() ** 2 * value(cfg["amps"][0]).real ** 2 / (3 * cfg["xcut"])


VALIDATION = ((("1", "1"), "1"), (("4/3", "2/3"), "3/10"), (("1", "1"), "1/1000000"), (("1", "1"), "10"),
              (("19/10", "1/10"), "1/20"))
DERIV_TESTS = ((("1", "1"), "3/10", "1/1000"), (("4/3", "2/3"), "1/100", "1/100000"))
BOX_TESTS = ((("1", "1"), "3/10", "31/100"), (("1", "1"), "1/1000", "2/1000"), (("1", "1"), "1/1000000", "2/1000000"))
FEET = (-1, 1)
# chart tests: (ratio lo, hi), (gamma lo, hi) or None for chart C, (depth lo, hi)
CHART_TESTS = ((("15/16", "1"), None, ("1/4", "17/64")), (("1", "1"), ("1/2", "1/2"), ("1/1048576", "1/1048576")),
               (("1", "9/8"), ("1/2", "33/64"), ("1/1048576", "1/524288")), (("1", "1"), ("1/8", "1/8"), (Fraction(1, 2**37),) * 2))
SCALING_CONTROL = ("1/3", "1/8")  # ratio, tau: chart M at gamma = 0 is chart C rescaled, so F_M(tau) = 2 F_C(2 tau)


def common(masses, depth):
    """VALIDATION configs (same as F_float_ref.py): exact masses, feet -1, +1, common depth."""
    return exact_pair(masses), exact_pair(FEET), (depth, depth)


def chart_spec(ratio, gamma, depth):
    ratio_ball, depth_ball = box(*ratio), box(*depth)
    return chart_c(ratio_ball, depth_ball) if gamma is None else chart_m(ratio_ball, box(*gamma), depth_ball)


def report_point(masses, depth):
    start = time.perf_counter()
    flux = flux_enclosure(*common(masses, exact(depth)))
    secs = time.perf_counter() - start
    single, expected = single_control(*common(masses, exact(depth)))
    print(f"POINT masses {masses[0]}, {masses[1]} depth {depth}: F in {flux.str(12, radius=True)} ({secs:.1f} s)  "
          f"single-pole control {single.str(8, radius=True)} vs {expected.str(8)}", flush=True)


def report_derivative(masses, depth, delta):
    start = time.perf_counter()
    deriv = flux_derivative_enclosure(*common(masses, exact(depth)))
    secs = time.perf_counter() - start
    upper = flux_enclosure(*common(masses, exact(depth) + exact(delta)))
    lower = flux_enclosure(*common(masses, exact(depth) - exact(delta)))
    print(f"DERIV masses {masses[0]}, {masses[1]} depth {depth}: dF/dt in {deriv.str(10, radius=True)} ({secs:.1f} s)  "
          f"central difference (delta {delta}) {((upper - lower) / (2 * exact(delta))).str(10, radius=True)}", flush=True)


def report_box(masses, lo, hi):
    start = time.perf_counter()
    flux_box = flux_enclosure(*common(masses, box(lo, hi)))
    mid = time.perf_counter()
    deriv_box = flux_derivative_enclosure(*common(masses, box(lo, hi)))
    end = time.perf_counter()
    print(f"BOX masses {masses[0]}, {masses[1]} t in [{lo}, {hi}]: F in {flux_box.str(8, radius=True)} ({mid - start:.1f} s)  "
          f"dF/dt in {deriv_box.str(8, radius=True)} ({end - mid:.1f} s)", flush=True)


def report_chart(ratio, gamma, depth):
    start = time.perf_counter()
    flux_box = flux_enclosure(*chart_spec(ratio, gamma, depth))
    mid = time.perf_counter()
    deriv_box = flux_derivative_enclosure(*chart_spec(ratio, gamma, depth))
    end = time.perf_counter()
    name = "C" if gamma is None else f"M gamma in [{gamma[0]}, {gamma[1]}]"
    print(f"CHART {name} r in [{ratio[0]}, {ratio[1]}] depth in [{depth[0]}, {depth[1]}]: F in {flux_box.str(8, radius=True)} "
          f"({mid - start:.1f} s)  dF/dt in {deriv_box.str(8, radius=True)} ({end - mid:.1f} s)", flush=True)


def report_scaling_control(ratio, tau):
    flux_m = flux_enclosure(*chart_m(exact(ratio), arb(0), exact(tau)))
    flux_c = flux_enclosure(*chart_c(exact(ratio), 2 * exact(tau)))
    verdict = "overlap" if flux_m.overlaps(2 * flux_c) else "DISJOINT (FAIL)"
    print(f"SCALING CONTROL r = {ratio} tau = {tau}: F_M = {flux_m.str(10, radius=True)}  2 F_C(2 tau) = "
          f"{(2 * flux_c).str(10, radius=True)} -> {verdict}", flush=True)


def main_prototype():
    ctx.prec = PREC
    print(f"F_arb v0.70 prec {PREC}, X = {X_BASE:.0e} * max(1, 1/least depth), panel ratio {RATIO}", flush=True)
    for masses, depth in VALIDATION:
        report_point(masses, depth)
    for masses, depth, delta in DERIV_TESTS:
        report_derivative(masses, depth, delta)
    for masses, lo, hi in BOX_TESTS:
        report_box(masses, lo, hi)
    report_scaling_control(*SCALING_CONTROL)
    for ratio, gamma, depth in CHART_TESTS:
        report_chart(ratio, gamma, depth)
    print("F ARB PROTOTYPE DONE", flush=True)


if __name__ == "__main__":
    main_prototype()
