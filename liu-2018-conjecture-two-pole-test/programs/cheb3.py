#!/usr/bin/env python3
# cheb3.py - P020 P7 chart M: 3D tensor Chebyshev cells (s, gamma-coordinate, y) for the backward chain (CELL-UP/CHAIN-UP)
"""Usage: cheb3.py --test
A cell = parameter box B (axes 0, 1: scaled sigma, eta in [-1, 1]) x one v-interval (axis 2: y in [-1, 1], v = c + h y).
P = tensor interpolant at first-kind nodes (point values as balls: node errors carried in the coefficients).
|g - P| <= R_2 + L_2 R_1 + L_2 L_1 R_0 on the real box, R_j = 4 M_j rho_j^-d_j/(rho_j - 1), L_j = Lebesgue bound of axis j, and
M_j >= sup |g| over (axis j on the Bernstein ellipse E_rho_j) x (the other axes on their REAL segments) (I = I_0 I_1 I_2 telescoping).
Suffix for every (sigma, eta) and y: int_y^1 g <= A(sigma, eta, 1) - A(sigma, eta, y) + R (1 - y), A = exact y-primitive of P.
The chain keeps G(sigma, eta) = sum of full-cell integrals as a 2D Chebyshev polynomial (+ a scalar remainder), so the floor is
Phi_lo(T) - max_{sigma, eta, y} [G(sigma, eta) + A(., ., 1) - A(., ., y)] - (remainders) > 0: no sum of separate per-cell sups."""
import heapq
import itertools
import math
import sys
from fractions import Fraction
from flint import arb, ctx

sys.dont_write_bytecode = True


def cheb_angles(degree):
    return [arb.pi() * (2 * ii + 1) / (2 * (degree + 1)) for ii in range(degree + 1)]


def cheb_nodes(degree):
    return [th.cos() for th in cheb_angles(degree)]


def lebesgue_bound(degree):
    """First-kind Chebyshev interpolation: Lambda_n <= (2/pi) log(n + 1) + 1 (Rivlin)."""
    return 2 / arb.pi() * arb(degree + 1).log() + 1


def axis_transform(values, axis, degree):
    """Discrete Chebyshev transform along one axis of a nested-list tensor (c_0 halved)."""
    angles = cheb_angles(degree)
    cos_table = [[(kk * th).cos() for th in angles] for kk in range(degree + 1)]

    def transform(vec):
        out = [2 * sum((vv * cc for vv, cc in zip(vec, cos_table[kk])), arb(0)) / (degree + 1) for kk in range(degree + 1)]
        out[0] = out[0] / 2
        return out

    return map_axis(values, axis, transform)


def map_axis(tensor, axis, func):
    """Apply func to every 1D fibre of a 3D nested list along `axis` (0, 1 or 2)."""
    n0, n1, n2 = len(tensor), len(tensor[0]), len(tensor[0][0])
    shape = [n0, n1, n2]
    fibres = {}
    for idx in itertools.product(*(range(nn) for nn in shape[:axis] + shape[axis + 1:])):
        fibre = [tensor_get(tensor, idx[:axis] + (kk,) + idx[axis:]) for kk in range(shape[axis])]
        fibres[idx] = func(fibre)
    new_len = len(next(iter(fibres.values())))
    shape[axis] = new_len
    out = [[[None] * shape[2] for _ in range(shape[1])] for _ in range(shape[0])]
    for idx, fibre in fibres.items():
        for kk, val in enumerate(fibre):
            pos = idx[:axis] + (kk,) + idx[axis:]
            out[pos[0]][pos[1]][pos[2]] = val
    return out


def tensor_get(tensor, idx):
    return tensor[idx[0]][idx[1]][idx[2]]


def tensor_coeffs(values, degrees):
    """values[i][j][k] at (node_i, node_j, node_k) -> coefficients c[a][b][k] of sum c T_a T_b T_k."""
    coeffs = values
    for axis in range(3):
        coeffs = axis_transform(coeffs, axis, degrees[axis])
    return coeffs


def primitive_1d(coeffs):
    """Chebyshev coefficients of a primitive of sum c_k T_k (int T0 = T1, int T1 = T2/4, int Tk = T_{k+1}/(2(k+1)) - T_{k-1}/(2(k-1)))."""
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


def suffix_tensor(coeffs):
    """Coefficients (axis 2 in y) of S(sigma, eta, y) = A(sigma, eta, 1) - A(sigma, eta, y), A = y-primitive of P."""
    def suffix(vec):
        prim = primitive_1d(vec)
        at_one = sum(prim, arb(0))                    # T_k(1) = 1
        out = [-pp for pp in prim]
        out[0] += at_one
        return out

    return map_axis(coeffs, 2, suffix)


def full_cell_2d(coeffs):
    """2D coefficients (sigma, eta) of A(., ., 1) - A(., ., -1) = int_{-1}^1 P dy."""
    out = []
    for row in coeffs:
        out.append([])
        for vec in row:
            prim = primitive_1d(vec)
            out[-1].append(sum((pp * (1 - (-1) ** kk) for kk, pp in enumerate(prim)), arb(0)))
    return out


def angle_pieces(count):
    """Angle balls covering [0, pi]: piece m is the ball (m + 1/2) pi/count +- pi/(2 count)."""
    half = arb.pi() / (2 * count)
    return [(2 * mm + 1) * half + arb(0, 1) * half for mm in range(count)]


def cos_vectors(pieces, degree):
    """For every angle ball: [cos(k theta) for k <= degree] (T_k(cos theta) = cos k theta: every x in [-1, 1] is covered)."""
    return [[(kk * th).cos() for kk in range(degree + 1)] for th in pieces]


def box_max_3d(coeffs, pieces_per_axis):
    """Certified upper bound of max over [-1, 1]^3 of sum c[a][b][k] T_a T_b T_k (angle subdivision; exact upper endpoint)."""
    dims = (len(coeffs), len(coeffs[0]), len(coeffs[0][0]))
    vecs = [cos_vectors(angle_pieces(pieces_per_axis), dim - 1) for dim in dims]
    best = None
    for vz in vecs[2]:
        plane = [[sum((ck * tk for ck, tk in zip(coeffs[aa][bb], vz)), arb(0)) for bb in range(dims[1])] for aa in range(dims[0])]
        for vy in vecs[1]:
            line = [sum((plane[aa][bb] * vy[bb] for bb in range(dims[1])), arb(0)) for aa in range(dims[0])]
            for vx in vecs[0]:
                upper = sum((line[aa] * vx[aa] for aa in range(dims[0])), arb(0)).upper()
                best = upper if best is None or upper > best else best
    return best


def frac_ball(lo, hi):
    """arb ball containing the closed interval [lo, hi] (exact Fraction endpoints)."""
    lo_b, hi_b = arb(lo.numerator) / lo.denominator, arb(hi.numerator) / hi.denominator
    return (lo_b + hi_b) / 2 + (hi_b - lo_b) / 2 * arb(0, 1)


def cos_row(theta, degree):
    return [(kk * theta).cos() for kk in range(degree + 1)]


def contract(coeffs, rows):
    """sum_{a,b,k} c[a][b][k] rows[0][a] rows[1][b] rows[2][k] in ball arithmetic."""
    total = arb(0)
    for aa, plane in enumerate(coeffs):
        line = arb(0)
        for bb, fibre in enumerate(plane):
            line += rows[1][bb] * sum((ck * tk for ck, tk in zip(fibre, rows[2])), arb(0))
        total += rows[0][aa] * line
    return total


def dsin_row(theta, degree):
    """d/dtheta cos(k theta) = -k sin(k theta)."""
    return [-kk * (kk * theta).sin() for kk in range(degree + 1)]


def piece_bounds(coeffs, piece, dims):
    """piece = 3 theta/pi intervals (lo, hi). Returns (certified upper bound of P on the piece, certified LOWER bound of P at the
    piece centre). T_k(cos theta) = cos(k theta), so theta-ball rows enclose every T_k(x) with x in the piece. Upper bound = min of
    (i) the direct ball enclosure and (ii) the MEAN-VALUE form P(c) + sum_i sup|dP/dtheta_i| (half-width_i): (ii) is second order
    at a maximum (every endpoint x = +-1 is a critical point in theta), (i) first order."""
    thetas = [arb.pi() * frac_ball(lo, hi) for lo, hi in piece]
    balls = [cos_row(th, dim - 1) for th, dim in zip(thetas, dims)]
    points = [cos_row(arb.pi() * frac_ball((lo + hi) / 2, (lo + hi) / 2), dim - 1) for (lo, hi), dim in zip(piece, dims)]
    centre = contract(coeffs, points)
    mean_value = centre
    for axis, ((lo, hi), dim) in enumerate(zip(piece, dims)):
        if dim > 1:
            rows = balls[:axis] + [dsin_row(thetas[axis], dim - 1)] + balls[axis + 1:]
            mean_value += abs(contract(coeffs, rows)) * arb.pi() * frac_ball((hi - lo) / 2, (hi - lo) / 2)
    direct = contract(coeffs, balls).upper()
    mv_up = mean_value.upper()
    return (mv_up if mv_up < direct else direct), centre.lower()


def split_piece(piece, dims):
    """Halve every axis of degree >= 1 (an axis of degree 0 is constant: never split)."""
    halves = []
    for (lo, hi), dim in zip(piece, dims):
        mid = (lo + hi) / 2
        halves.append([(lo, mid), (mid, hi)] if dim > 1 else [(lo, hi)])
    return list(itertools.product(*halves))


def poly_max_3d(coeffs, tol, start=6, budget=20000):
    """Certified U >= max over [-1, 1]^3 of sum c T_a T_b T_k, by branch and bound in theta = acos x. Returns (U, gap) where some
    point value is >= U - gap; gap <= tol unless the evaluation budget ran out (then U is still a valid, looser upper bound).
    Pruned pieces have upper < best lower <= true max, so the max lies in a kept piece and U = max of the kept uppers."""
    dims = (len(coeffs), len(coeffs[0]), len(coeffs[0][0]))
    tol = frac_ball(Fraction(tol), Fraction(tol))  # arb, never compare arb with Fraction directly
    grid = [[(Fraction(jj, start if dim > 1 else 1), Fraction(jj + 1, start if dim > 1 else 1))
             for jj in range(start if dim > 1 else 1)] for dim in dims]
    heap, best_low, count = [], None, 0
    for piece in itertools.product(*grid):
        upper, lower = piece_bounds(coeffs, piece, dims)
        best_low = lower if best_low is None or lower > best_low else best_low
        heapq.heappush(heap, (-float(upper), count, upper, piece))
        count += 1
    while count < budget:
        _, _, upper, piece = heap[0]
        if not upper - best_low > tol:
            break
        heapq.heappop(heap)
        for child in split_piece(piece, dims):
            c_up, c_low = piece_bounds(coeffs, child, dims)
            count += 1
            best_low = c_low if c_low > best_low else best_low
            if not c_up < best_low:
                heapq.heappush(heap, (-float(c_up), count, c_up, child))
    top = heap[0][2]
    for entry in heap:  # float heap keys may misorder near-ties: take the exact maximum of all kept uppers
        top = entry[2] if entry[2] > top else top
    return top, (top - best_low).upper()


def as_3d(coeffs_2d):
    """Embed 2D (sigma, eta) coefficients as a 3D tensor with a single y-coefficient (constant in y)."""
    return [[[cc] for cc in row] for row in coeffs_2d]


def add_3d(left, right):
    """Sum of two coefficient tensors of possibly different shapes (zero padding)."""
    dims = [max(len(left), len(right)), max(len(left[0]), len(right[0])), max(len(left[0][0]), len(right[0][0]))]
    out = [[[arb(0)] * dims[2] for _ in range(dims[1])] for _ in range(dims[0])]
    for tensor in (left, right):
        for aa, row in enumerate(tensor):
            for bb, vec in enumerate(row):
                for kk, cc in enumerate(vec):
                    out[aa][bb][kk] += cc
    return out


def add_2d(left, right):
    dims = [max(len(left), len(right)), max(len(left[0]), len(right[0]))]
    out = [[arb(0)] * dims[1] for _ in range(dims[0])]
    for tensor in (left, right):
        for aa, row in enumerate(tensor):
            for bb, cc in enumerate(row):
                out[aa][bb] += cc
    return out


def bernstein_remainder(sup_bound, rho, degree):
    """Interpolation error at d + 1 first-kind points for |g| <= M on E_rho: 4 M rho^-d/(rho - 1) (Trefethen ATAP Thm 8.2)."""
    rr = arb(rho)
    return 4 * arb(sup_bound) * rr ** -degree / (rr - 1)


def tensor_remainder(sups, rhos, degrees):
    """R_2 + L_2 R_1 + L_2 L_1 R_0 (axes 0, 1, 2 = sigma, eta, y; I = I_0 I_1 I_2, so the y-axis error enters first)."""
    rem = [bernstein_remainder(mm, rr, dd) for mm, rr, dd in zip(sups, rhos, degrees)]
    lam = [lebesgue_bound(dd) for dd in degrees]
    return (rem[2] + lam[2] * rem[1] + lam[2] * lam[1] * rem[0]).upper()


def main_test():
    """Synthetic check, g = e^{0.3 sigma} / (3 - eta) * cos(0.7 y + 0.2 sigma): coefficients reproduce g at a random point; the
    suffix polynomial equals the exact y-integral; box_max_3d bounds the true maximum of the suffix from above, closely."""
    ctx.prec = 96
    degrees = (8, 8, 10)

    def gfun(sg, et, yy):
        return (sg * arb("0.3")).exp() / (3 - et) * (arb("0.7") * yy + arb("0.2") * sg).cos()

    nodes = [cheb_nodes(dd) for dd in degrees]
    values = [[[gfun(xx, ee, yy) for yy in nodes[2]] for ee in nodes[1]] for xx in nodes[0]]
    coeffs = tensor_coeffs(values, degrees)
    ok = True
    pt = (arb("0.37"), arb("-0.61"), arb("0.15"))
    approx = sum(coeffs[aa][bb][kk] * (aa * pt[0].acos()).cos() * (bb * pt[1].acos()).cos() * (kk * pt[2].acos()).cos()
                 for aa in range(9) for bb in range(9) for kk in range(11))
    err = abs(approx - gfun(*pt)).upper()
    ok &= err < 1e-6
    print(f"interpolation error at a test point: {float(err):.2e}")
    suffix = suffix_tensor(coeffs)

    def exact_suffix(sg, et, yy):
        cc = arb("0.2") * sg
        return (sg * arb("0.3")).exp() / (3 - et) * (((arb("0.7") + cc).sin() - (arb("0.7") * yy + cc).sin()) / arb("0.7"))

    s_approx = sum(suffix[aa][bb][kk] * (aa * pt[0].acos()).cos() * (bb * pt[1].acos()).cos() * (kk * pt[2].acos()).cos()
                   for aa in range(9) for bb in range(9) for kk in range(12))
    s_err = abs(s_approx - exact_suffix(*pt)).upper()
    ok &= s_err < 1e-6
    print(f"suffix error at the test point: {float(s_err):.2e}")
    upper = box_max_3d(suffix, 16)
    true_max = max(float(exact_suffix(arb(xx), arb(ee), arb(yy)).mid()) for xx in (1.0,) for ee in (1.0,) for yy in [-1 + 0.01 * jj for jj in range(201)])
    ok &= float(upper) >= true_max - 1e-6 and float(upper) < true_max * 1.25 + 0.05
    print(f"box max upper {float(upper):.5f} vs true max (sigma = eta = 1 line) {true_max:.5f}")
    full = full_cell_2d(coeffs)
    f_approx = sum(full[aa][bb] * (aa * pt[0].acos()).cos() * (bb * pt[1].acos()).cos() for aa in range(9) for bb in range(9))
    f_err = abs(f_approx - exact_suffix(pt[0], pt[1], arb(-1))).upper()
    ok &= f_err < 1e-6
    print(f"full-cell error: {float(f_err):.2e}; tensor remainder demo {float(tensor_remainder((2, 2, 2), (3, 3, 3), degrees)):.2e}")
    ok &= max_test(suffix, exact_suffix)
    print("TEST", "PASS" if ok else "FAIL", flush=True)


def max_test(suffix, exact_suffix):
    """poly_max_3d: U must be >= the dense-sample max of the polynomial, within tol + 1e-6 of it, and the gap must be <= tol.
    Second, a polynomial whose max is interior (P = -(x - 0.3)^2 - (y + 0.2)^2 - (z - 0.1)^2, max 0): U in [0, tol]."""
    tol = Fraction(1, 10**5)
    upper, gap = poly_max_3d(suffix, tol)
    grid = [-1 + jj / 20 for jj in range(41)]
    sample = max(float(exact_suffix(arb(xx), arb(ee), arb(yy)).mid()) for xx in grid for ee in grid for yy in grid)
    ok = float(upper) >= sample - 1e-6 and float(upper) <= sample + 1e-5 + 1e-6 and float(gap) <= 1e-5
    bowl = [[[arb(0)] * 3 for _ in range(3)] for _ in range(3)]  # -(x-a)^2 = -(T2/2 + 1/2) + 2a T1 - a^2
    for axis, centre in enumerate((arb("0.3"), arb("-0.2"), arb("0.1"))):
        idx = [[0, 0, 0], [0, 0, 0], [0, 0, 0]]
        for kk, val in ((0, -arb(1) / 2 - centre * centre), (1, 2 * centre), (2, -arb(1) / 2)):
            pos = [0, 0, 0]
            pos[axis] = kk
            bowl[pos[0]][pos[1]][pos[2]] += val
    b_up, b_gap = poly_max_3d(bowl, tol)
    ok &= -1e-12 <= float(b_up) <= 1e-5 + 1e-12
    print(f"poly_max_3d: suffix U = {float(upper):.7f} (dense sample {sample:.7f}, gap {float(gap):.1e}); bowl U = {float(b_up):.2e}")
    return ok


def main():
    if sys.argv[1:] == ["--test"]:
        main_test()
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
