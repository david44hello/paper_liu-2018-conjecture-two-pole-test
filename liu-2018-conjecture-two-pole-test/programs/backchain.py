#!/usr/bin/env python3
# backchain.py - P020 P7: BACKWARD path certificate at one exact parameter point, from POINT flux values only (no ball derivatives)
# Phi(u) := Def0/A^2 - k0 (normalized). FLUX: Phi(u) = Phi(T) - int_u^T f (0 < u <= T). CLUSTER-W (accepted, repaired):
#   Phi(T) >= D1 - k0 - 16.2 a b s^2/(1 - s), s = separation/mean depth <= 2/T (C) or 1/T (M), valid for s <= 1/4.
#   So Phi(u) >= Phi_lo(T) - G(u), G(u) := int_u^T f; we certify UPPER bounds on G.
# Interval [alpha, beta] in v = log u, v = mid + h y, y in [-1, 1]: int_v^beta f(e^v') e^v' dv' = int_y^1 g, g(y) := f(e^{mid+hy}) e^{mid+hy} h.
#   p = interpolant of g at d + 1 first-kind Chebyshev points from POINT values (ball coefficients carry node errors), kept in the
#   Chebyshev basis (coefficients decay like rho^-k: no monomial conversion, no factorial growth of ball radii).
#   |g - p| <= R = 4 M_g rho^-d/(rho - 1) on [-1, 1], M_g = M h e^{mid + h a_rho} >= sup |g| on E_rho (a_rho = semi-major axis),
#   M >= sup |f| on the ellipse curve from eng.majorant_bound on COVER complex boxes (maximum principle; f analytic for Re u > 0).
#   P = exact Chebyshev primitive of p (int T_0 = T_1, int T_1 = T_2/4, int T_k = T_{k+1}/(2(k+1)) - T_{k-1}/(2(k-1))).
#   int_y^1 g <= P(1) - P(y) + R (1 - y). P is evaluated only at EXACT points as sum a_k cos(k acos y) (|T_k| <= 1, so radii just add;
#   a ball Clenshaw recurrence inflates radii like (1 + sqrt 2)^k). On a piece |y - y_c| <= delta: |P(y) - P(y_c)| <= delta sup|p|,
#   sup_[-1,1] |p| <= sum |c_k| (mean value theorem, P' = p). Full interval: P(1) - P(-1) + 2R.
# PREFIX (0, u_b] (u_b = bottom of the last interval), from TWO-SIDED small-depth lemmas:
#   C: |F_h - E| <= 2^32 m^-4 h (1 + log 1/h)^3 (ER2, normalized, h <= m^2/64), so E <= E_up := F(h_E) + rate(h_E) with h_E = 2^-k
#      sized to rate <= EDGE_RATE, and sup_u int_u^{u_b} f <= u_b max(E_up, 0) + 2^32 m^-4 I3(u_b) (IB: I3 = (u^2/2)(U^3+1.5U^2+1.5U+.75)).
#   M (H = sin gamma >= 1/2): |F - c log(1/t)| <= 4096/(a^2 H^8), |c| <= 64/H^4 (MIXED-EDGE), so sup int <= u_b (|c|(1 + log 1/u_b) + C).
#   BOTH charts, every angle: int_0^u |f| <= 2^34 m^-2 u (2 + log 1/u),
#      u <= 1/4. The smallest valid prefix bound is used; each one is printed.
# PASS on (0, T] iff every interval floor > 0 and Phi_lo(u_b) - prefix > 0 (certified exact comparisons). Phi(0+) >= the last value.
import math
import sys
import time
from fractions import Fraction
from flint import acb, arb, ctx

sys.dont_write_bytecode = True
import F_arb as eng  # noqa: E402

WORK_PREC, WORK_TOL = 96, 30  # f_tune_v010.log: prec 96, tol 2^-30 stays inside the prec-128 balls (1e-11) at ~3x the speed
RHO = Fraction(5, 2)
HALF = Fraction(1)  # interval half-length h in v (length 2)
COVER = 32  # complex boxes on the ellipse curve
PIECES = 128  # y-subdivision for the partial-integral maximum
TARGET = Fraction(1, 100000)  # allowed integrated remainder per interval: 2R <= TARGET (v0.30 run: 1/5000 dominated small-u intervals)
DEGREE_MAX = 48
CLUSTER_CONST = Fraction(162, 10)
ER2_CONST = 2 ** 32
ABS_CONST = 2 ** 34
EDGE_RATE = Fraction(1, 10**9)
USAGE = "usage: backchain.py C r u0 T  |  backchain.py M r gamma u0 T   (exact rationals)"


def cheb_angles(degree):
    return [arb.pi() * (2 * ii + 1) / (2 * (degree + 1)) for ii in range(degree + 1)]


def cheb_coefficients(values, degree):
    """p = sum_k c_k T_k interpolating values at the first-kind points (c_0 already halved)."""
    angles = cheb_angles(degree)
    coeffs = [2 * sum(ff * (kk * th).cos() for ff, th in zip(values, angles)) / (degree + 1) for kk in range(degree + 1)]
    coeffs[0] = coeffs[0] / 2
    return coeffs


def cheb_primitive(coeffs):
    """Chebyshev coefficients of a primitive of sum_k c_k T_k (constant term 0)."""
    prim = [arb(0)] * (len(coeffs) + 1)
    for kk, ck in enumerate(coeffs):
        if kk == 0:
            prim[1] += ck
        elif kk == 1:
            prim[2] += ck / 4
        else:
            prim[kk + 1] += ck / (2 * (kk + 1))
            prim[kk - 1] -= ck / (2 * (kk - 1))
    return prim


def cheb_value(coeffs, yy):
    """sum_k a_k T_k(y) at an EXACT y in [-1, 1], as sum a_k cos(k acos y): radii add (no recurrence inflation)."""
    angle = yy.acos()
    return sum((ak * (kk * angle).cos() for kk, ak in enumerate(coeffs)), arb(0))


def cheb_sup(coeffs):
    """sup_[-1,1] |sum c_k T_k| <= sum |c_k| (exact upper endpoint)."""
    return sum((abs(ck) for ck in coeffs), arb(0)).upper()


def ellipse_cover(rho, count):
    """Complex boxes (centre in the y-plane, radius) whose union contains the curve y = (rho e^{i th} + e^{-i th}/rho)/2."""
    semi_major, semi_minor = (rho + 1 / rho) / 2, (rho - 1 / rho) / 2
    step = 2 * arb.pi() / count
    radius = step / 2 * semi_major  # an arc of angle `step` has length <= step * max|y'(th)| <= step * semi_major
    return [(acb((step * (mm + arb(1) / 2)).cos() * semi_major, (step * (mm + arb(1) / 2)).sin() * semi_minor), radius)
            for mm in range(count)]


def ellipse_bound(spec, mid, half, rho):
    """M >= sup |f| on the Bernstein ellipse curve of [mid - h, mid + h] in v (u = e^v): eng.majorant_bound on every cover box."""
    bound = arb(0)
    for centre, radius in ellipse_cover(eng.exact(rho), COVER):
        uball = (eng.exact(mid) + eng.exact(half) * (centre + acb(radius * arb(0, 1), radius * arb(0, 1)))).exp()
        value = eng.majorant_bound(*spec(uball))
        bound = value if value > bound else bound  # exact upper endpoints: certified comparison
    return bound


def g_bound(bound, mid, half, rho):
    """M_g >= sup |f e^v h| on E_rho: |e^v| <= e^{mid + h a_rho}."""
    rr = eng.exact(rho)
    return (bound * eng.exact(half) * (eng.exact(mid) + eng.exact(half) * (rr + 1 / rr) / 2).exp()).upper()


def choose_degree(g_max, rho):
    for degree in range(4, DEGREE_MAX + 1):
        if 8 * g_max * eng.exact(rho) ** -degree / (eng.exact(rho) - 1) < eng.exact(TARGET):
            return degree
    sys.exit(f"degree > {DEGREE_MAX} needed (M_g = {g_max}); shorten the interval")


def node_values(spec, mid, half, degree):
    """f at the nodes (for the majorant check) and g = f e^v h at the nodes."""
    flux, gvals = [], []
    for th in cheb_angles(degree):
        vv = eng.exact(mid) + eng.exact(half) * th.cos()
        ff = eng.flux_enclosure(*spec(vv.exp()))
        flux.append(ff)
        gvals.append(ff * vv.exp() * eng.exact(half))
    return flux, gvals


def check_majorant(bound, values):
    """A control that CAN fail: the majorant on the ellipse curve dominates sup|f| on [-1, 1] (maximum principle)."""
    for vv in values:
        assert abs(vv).upper() <= bound, f"majorant {bound} below a node value {vv}: BUG"


def partial_max(coeffs, prim, remainder):
    """Upper bounds of max_{y in [-1, 1]} int_y^1 g and of int_{-1}^1 g, from P(1) - P(y) + R (1 - y); on the piece around y_c
    (half-width delta) P(y) >= P(y_c) - delta sup|p| and 1 - y <= 1 - y_c + delta."""
    top = cheb_value(prim, arb(1))
    delta, slope = eng.exact(Fraction(1, PIECES)), cheb_sup(coeffs)
    worst = arb(0)
    for kk in range(PIECES):
        y_c = eng.exact(Fraction(2 * kk + 1, PIECES) - 1)
        value = (top - cheb_value(prim, y_c) + delta * slope + remainder * (1 - y_c + delta)).upper()
        worst = value if value > worst else worst
    full = (top - cheb_value(prim, arb(-1)) + 2 * remainder).upper()
    return worst, full


def interval_step(spec, mid, half):
    start = time.perf_counter()
    bound = ellipse_bound(spec, mid, half, RHO)
    g_max = g_bound(bound, mid, half, RHO)
    degree = choose_degree(g_max, RHO)
    flux, gvals = node_values(spec, mid, half, degree)
    check_majorant(bound, flux)
    remainder = 4 * g_max * eng.exact(RHO) ** -degree / (eng.exact(RHO) - 1)
    coeffs = cheb_coefficients(gvals, degree)
    worst, full = partial_max(coeffs, cheb_primitive(coeffs), remainder)
    return worst, full, bound, degree, flux, time.perf_counter() - start


def cluster_floor(ab, separation, v_top):
    """CLUSTER-W at depth T_eff = e^{v_top}: s = separation/mean depth <= separation/T_eff."""
    ss = eng.exact(separation) / eng.exact(v_top).exp()
    assert ss < eng.exact(Fraction(1, 4)), "CLUSTER-W needs s <= 1/4"
    d1 = 3 * arb(3).zeta() / 4
    return d1 - eng.k0() - eng.exact(CLUSTER_CONST) * ab * ss ** 2 / (1 - ss)


def er2_rate(m_min, hh):
    return ER2_CONST / m_min ** 4 * hh * (1 + (1 / hh).log()) ** 3


def edge_upper(job):
    """E_up >= E_edge: F(h_E) + ER2 rate at the largest dyadic h_E <= m^2/64 with rate <= EDGE_RATE."""
    m_min = eng.exact(job["m"])
    kk = 6
    while not (eng.exact(Fraction(1, 2 ** kk)) <= m_min ** 2 / 64 and er2_rate(m_min, eng.exact(Fraction(1, 2 ** kk))) < eng.exact(EDGE_RATE)):
        kk += 1
    saved = ctx.prec
    ctx.prec = max(saved, kk + 96)  # depth 2^-k next to feet at distance 1: keep ~96 bits beyond the depth scale
    depth = eng.exact(Fraction(1, 2 ** kk))
    edge = eng.flux_enclosure(*job["spec"](depth)) + er2_rate(m_min, depth)
    ctx.prec = saved
    return edge.upper(), kk


def prefix_c(job, u_b):
    m_min = eng.exact(job["m"])
    assert u_b.upper() <= m_min ** 2 / 64, "ER2 range h <= m^2/64 fails at u_b"
    e_up, kk = edge_upper(job)
    big_u = 1 + (1 / u_b).log()
    i3 = u_b ** 2 / 2 * (big_u ** 3 + 3 * big_u ** 2 / 2 + 3 * big_u / 2 + arb(3) / 4)
    bound = (u_b * (e_up if e_up > 0 else arb(0)) + ER2_CONST / m_min ** 4 * i3).upper()
    return bound, f"ER2 two-sided: E_up = {float(e_up):.9f} (h_E = 2^-{kk}), prefix int <= {float(bound):.3e}"


def prefix_m(job, u_b):
    h_low = eng.exact(job["gamma"]).sin().lower()
    if not h_low >= eng.exact(Fraction(1, 2)):
        return None, "MIXED-EDGE not applicable (H < 1/2)"
    amass = eng.exact(job["a"])
    cabs, cerr = 64 / h_low ** 4, 4096 / (amass ** 2 * h_low ** 8)
    bound = (u_b * (cabs * (1 + (1 / u_b).log()) + cerr)).upper()
    return bound, f"MIXED-EDGE two-sided (H >= 1/2): prefix int <= {float(bound):.3e}"


def prefix_abs(job, u_b):
    assert u_b.upper() <= eng.exact(Fraction(1, 4)), "UNIFORM-ABS needs u <= 1/4"
    bound = (ABS_CONST / eng.exact(job["m"]) ** 2 * u_b * (2 + (1 / u_b).log())).upper()
    return bound, f"UNIFORM-ABS (both charts, every angle): int |f| <= {float(bound):.3e}"


def best_prefix(job, u_b):
    """The smallest valid prefix bound over the applicable rules (exact upper endpoints: certified comparison)."""
    rules = (prefix_c if job["chart"] == "C" else prefix_m, prefix_abs)
    best, notes = None, []
    for rule in rules:
        bound, note = rule(job, u_b)
        notes.append(note)
        if bound is not None and (best is None or bound < best):
            best = bound
    return best, "; ".join(notes)


def run_chain(job):
    v_top = Fraction(math.ceil(math.log(job["T"])))  # integer v_top >= log T: the chain starts at T_eff = e^{v_top} >= T
    phi_t = cluster_floor(eng.exact(job["ab"]), job["sep"], v_top)
    count = math.ceil((float(v_top) - math.log(job["u0"])) / float(2 * HALF))
    print(f"BACKCHAIN {job['label']}: T_eff = e^{v_top}, Phi_lo(T_eff) = {float(phi_t.lower()):.6f} (CLUSTER-W), "
          f"u0 = {float(job['u0']):.3e}, {count} intervals of length {2 * HALF} in v, rho = {RHO}", flush=True)
    g_up, chain_ok = arb(0), True
    for jj in range(count):
        mid = v_top - (2 * jj + 1) * HALF
        worst, full, bound, degree, flux, secs = interval_step(job["spec"], mid, HALF)
        floor = (phi_t - g_up - worst).lower()
        chain_ok = chain_ok and floor > 0
        g_up = g_up + full
        print(f"INTERVAL v in [{float(mid - HALF):.1f}, {float(mid + HALF):.1f}]: M = {float(bound):.3e}, degree {degree}, "
              f"f(nodes) in [{min(float(vv.lower()) for vv in flux):+.4e}, {max(float(vv.upper()) for vv in flux):+.4e}], "
              f"int f <= {float(full):+.6e}, Phi floor >= {float(floor):+.6f} ({secs:.1f} s)", flush=True)
    v_bottom = v_top - 2 * count * HALF
    return chain_ok, (phi_t - g_up).lower(), eng.exact(v_bottom).exp()


def run_backchain(job):
    chain_ok, phi_bottom, u_b = run_chain(job)
    prefix, note = best_prefix(job, u_b)
    print(f"PREFIX (0, u_b = {float(u_b.mid()):.3e}]: {note}", flush=True)
    face = None if prefix is None else (phi_bottom - prefix).lower()
    verdict = chain_ok and face is not None and face > 0
    face_text = "n/a" if face is None else f"{float(face):+.6f}"
    print(f"BACKCHAIN RESULT {job['label']}: chain on [u_b, T] {'PASS' if chain_ok else 'FAIL'}, Phi_lo(u_b) = {float(phi_bottom):+.6f}, "
          f"Phi(0+) >= {face_text} -> {'PASS on (0, T]' if verdict else 'NOT CERTIFIED on (0, T]'}", flush=True)


def parse_job(args):
    if len(args) == 4 and args[0] == "C":
        ratio, u0, big_t = Fraction(args[1]), Fraction(args[2]), Fraction(args[3])
        amass = 1 / (1 + ratio)
        return {"chart": "C", "label": f"C r = {args[1]}", "spec": lambda uu: eng.chart_c(eng.exact(ratio), uu),
                "ab": amass * (1 - amass), "sep": 2, "u0": u0, "T": big_t, "m": min(amass, 1 - amass), "a": amass}
    if len(args) == 5 and args[0] == "M":
        ratio, gamma, u0, big_t = Fraction(args[1]), Fraction(args[2]), Fraction(args[3]), Fraction(args[4])
        amass = 1 / (1 + ratio)
        return {"chart": "M", "label": f"M r = {args[1]}, gamma = {args[2]}", "gamma": gamma,
                "spec": lambda uu: eng.chart_m(eng.exact(ratio), eng.exact(gamma), uu),
                "ab": amass * (1 - amass), "sep": 1, "u0": u0, "T": big_t, "m": min(amass, 1 - amass), "a": amass}
    sys.exit(USAGE)


def apply_work_settings():
    ctx.prec = WORK_PREC
    eng.TOL_REL, eng.TOL_ABS = arb(2) ** -WORK_TOL, arb(2) ** -(WORK_TOL + 20)


def main_backchain():
    apply_work_settings()
    print(f"backchain v0.50 (prec {WORK_PREC}, tol 2^-{WORK_TOL}, engine X_BASE {eng.X_BASE:.0e})", flush=True)
    run_backchain(parse_job(sys.argv[1:]))
    print("BACKCHAIN DONE", flush=True)


if __name__ == "__main__":
    main_backchain()
