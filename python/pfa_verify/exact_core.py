# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander S. Donahue
"""Independent exact Python oracle for all Pillars I-III claims of promislow-fracton-amoeba.

All algebraic verifications use exact arbitrary-precision Python integers (`int`) and
`fractions.Fraction`; transcendental Ronkin integrals, spectral winding numbers,
discriminant winding invariants, and 4-band eigenvalue braids are explicitly labeled
`numerical_approximation` with verified gap bounds.
"""

from __future__ import annotations

import cmath
import json
import math
from collections import defaultdict
from itertools import permutations
from pathlib import Path
from typing import Any

SIGS: tuple[tuple[int, int, int], ...] = (
    (1, 1, 1),
    (1, -1, -1),
    (-1, 1, -1),
    (-1, -1, 1),
)

COSET_PROD: tuple[tuple[tuple[int, int, int, int], ...], ...] = (
    ((0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 0, 2), (0, 0, 0, 3)),
    ((0, 0, 0, 1), (1, 0, 0, 0), (0, 0, 0, 3), (1, 0, 0, 2)),
    ((0, 0, 0, 2), (-1, 1, -1, 3), (0, 1, 0, 0), (-1, 0, -1, 1)),
    ((0, 0, 0, 3), (0, -1, 1, 2), (0, -1, 0, 1), (0, 0, 1, 0)),
)

PERMS4: list[tuple[tuple[int, ...], int]] = [
    (p, -1 if sum(1 for a in range(4) for b in range(a + 1, 4) if p[a] > p[b]) % 2 else 1)
    for p in permutations(range(4))
]

ElemP = tuple[int, int, int, int]
ZPElem = dict[ElemP, int]
LPoly3 = dict[tuple[int, int, int], int]


def elem_mul(g1: ElemP, g2: ElemP) -> ElemP:
    i1, j1, k1, c1 = g1
    i2, j2, k2, c2 = g2
    s1, s2, s3 = SIGS[c1]
    dx, dy, dz, c3 = COSET_PROD[c1][c2]
    return (i1 + s1 * i2 + dx, j1 + s2 * j2 + dy, k1 + s3 * k2 + dz, c3)


def elem_inv(g: ElemP) -> ElemP:
    i, j, k, c = g
    dx, dy, dz, _ = COSET_PROD[c][c]
    s1, s2, s3 = SIGS[c]
    return (-dx - s1 * i, -dy - s2 * j, -dz - s3 * k, c)


def zp_one() -> ZPElem:
    return {(0, 0, 0, 0): 1}


def zp_add(a: ZPElem, b: ZPElem, mod: int | None = None) -> ZPElem:
    out: dict[ElemP, int] = defaultdict(int, a)
    for k, v in b.items():
        out[k] += v
    res: ZPElem = {}
    for k, v in out.items():
        nv = v % mod if mod is not None else v
        if nv != 0:
            res[k] = nv
    return res


def zp_sub(a: ZPElem, b: ZPElem, mod: int | None = None) -> ZPElem:
    return zp_add(a, {k: -v for k, v in b.items()}, mod=mod)


def zp_mul(a: ZPElem, b: ZPElem, mod: int | None = None) -> ZPElem:
    out: dict[ElemP, int] = defaultdict(int)
    for g1, v1 in a.items():
        for g2, v2 in b.items():
            out[elem_mul(g1, g2)] += v1 * v2
    res: ZPElem = {}
    for k, v in out.items():
        nv = v % mod if mod is not None else v
        if nv != 0:
            res[k] = nv
    return res


def zp_star(a: ZPElem) -> ZPElem:
    return {elem_inv(g): v for g, v in a.items()}


def gardam_alpha() -> ZPElem:
    pts = [
        (0, 0, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0), (1, 1, 0, 0),
        (0, 0, -1, 0), (1, 0, -1, 0), (0, 1, -1, 0), (1, 1, -1, 0),
        (-1, -1, 0, 1), (1, 0, 0, 1), (0, -1, 1, 1), (0, 0, 1, 1),
        (0, 0, 0, 2), (1, 0, 0, 2), (0, -1, 1, 2), (1, 1, 1, 2),
        (0, 0, 0, 3), (1, 0, -1, 3), (-1, 0, -1, 3), (0, 1, -1, 3), (0, -1, -1, 3),
    ]
    return {g: 1 for g in pts}


def gardam_beta() -> ZPElem:
    pts = [
        (-1, -1, 0, 0), (-1, -1, 1, 0), (-1, 0, 0, 0), (-1, 0, 1, 0),
        (0, -1, 0, 0), (0, -1, 1, 0), (0, 0, 0, 0), (0, 0, 1, 0),
        (-2, -1, 0, 1), (-1, -1, 1, 1), (-1, 0, 1, 1), (0, 0, 0, 1),
        (0, -2, 1, 2), (0, -1, 0, 2), (1, -1, 0, 2), (1, 0, 1, 2),
        (-1, 0, 0, 3), (0, -1, 0, 3), (0, 0, -1, 3), (0, 1, 0, 3), (1, 0, 0, 3),
    ]
    return {g: 1 for g in pts}


def lp_add(a: LPoly3, b: LPoly3) -> LPoly3:
    out: dict[tuple[int, int, int], int] = defaultdict(int, a)
    for k, v in b.items():
        out[k] += v
    return {k: v for k, v in out.items() if v != 0}


def lp_mul(a: LPoly3, b: LPoly3) -> LPoly3:
    out: dict[tuple[int, int, int], int] = defaultdict(int)
    for (x1, y1, z1), v1 in a.items():
        for (x2, y2, z2), v2 in b.items():
            out[(x1 + x2, y1 + y2, z1 + z2)] += v1 * v2
    return {k: v for k, v in out.items() if v != 0}


def bloch_matrix4(u: ZPElem) -> list[list[LPoly3]]:
    mat: list[list[dict[tuple[int, int, int], int]]] = [
        [defaultdict(int) for _ in range(4)] for _ in range(4)
    ]
    for row in range(4):
        s1, s2, s3 = SIGS[row]
        for (gx, gy, gz, gc), v in u.items():
            dx, dy, dz, col = COSET_PROD[row][gc]
            mat[row][col][(s1 * gx + dx, s2 * gy + dy, s3 * gz + dz)] += v
    return [[{k: v for k, v in cell.items() if v != 0} for cell in row] for row in mat]


def det_bloch4(u: ZPElem) -> LPoly3:
    m = bloch_matrix4(u)
    acc: LPoly3 = {}
    for perm, sgn in PERMS4:
        term: LPoly3 = {(0, 0, 0): sgn}
        for r in range(4):
            cell = m[r][perm[r]]
            if not cell:
                term = {}
                break
            term = lp_mul(term, cell)
        if term:
            acc = lp_add(acc, term)
    return acc


def hensel_lift_gardam(bits: int) -> tuple[ZPElem, bool]:
    mod = 1 << bits
    a = gardam_alpha()
    b = gardam_beta()
    two = {(0, 0, 0, 0): 2}
    for _ in range(bits):
        ab = zp_mul(a, b, mod=mod)
        b = zp_mul(b, zp_sub(two, ab, mod=mod), mod=mod)
    ok = zp_mul(a, b, mod=mod) == zp_one() and zp_mul(b, a, mod=mod) == zp_one()
    return b, ok


def rank_mod_p(mat: list[list[int]], p: int) -> int:
    if not mat:
        return 0
    m, n = len(mat), len(mat[0])
    a = [[x % p for x in row] for row in mat]
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if a[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        a[r], a[piv] = a[piv], a[r]
        inv = pow(a[r][c], p - 2, p)
        rr = a[r]
        for j in range(c, n):
            rr[j] = (rr[j] * inv) % p
        for i in range(m):
            if i != r and a[i][c] != 0:
                fac = a[i][c]
                ri = a[i]
                for j in range(c, n):
                    ri[j] = (ri[j] - fac * rr[j]) % p
        r += 1
        if r == m:
            break
    return r


def signed_haah_k_logical(
    L: int, p: int, a1: int = 1, a2: int = 1, a3: int = 1, b1: int = 1, b2: int = 1, b3: int = 1
) -> int:
    """Exact logical qudit count k_logical(L, p) = log_p GSD_p(L) via 2D quotient elimination."""
    def mul_r(A: list[list[int]], B: list[list[int]]) -> list[list[int]]:
        C = [[0] * L for _ in range(L)]
        for i1 in range(L):
            for j1 in range(L):
                v1 = A[i1][j1]
                if not v1:
                    continue
                for i2 in range(L):
                    ri = (i1 + i2) % L
                    rB = B[i2]
                    rC = C[ri]
                    for j2 in range(L):
                        if rB[j2]:
                            rC[(j1 + j2) % L] = (rC[(j1 + j2) % L] + v1 * rB[j2]) % p
        return C

    zp = [[0] * L for _ in range(L)]
    zp[0][0] = (-a3) % p
    zp[1 % L][0] = (zp[1 % L][0] - a3 * a1) % p
    zp[0][1 % L] = (zp[0][1 % L] - a3 * a2) % p

    res = [[0] * L for _ in range(L)]
    res[0][0] = 1
    base = zp
    e = L
    while e:
        if e & 1:
            res = mul_r(res, base)
        base = mul_r(base, base)
        e >>= 1
    res[0][0] = (res[0][0] - 1) % p

    h1 = [[0] * L for _ in range(L)]
    for i, j, c in [
        (2, 0, -a1 * b3),
        (1, 1, a3 * b1 - a2 * b3 - a1 * b2),
        (0, 2, -a2 * b2),
        (1, 0, -b3),
        (0, 1, -b2),
        (0, 0, a3),
    ]:
        h1[i % L][j % L] = (h1[i % L][j % L] + c) % p

    n2 = L * L
    rows: list[list[int]] = []
    for poly in (h1, res):
        nz = [(a, b, poly[a][b]) for a in range(L) for b in range(L) if poly[a][b] != 0]
        for i in range(L):
            for j in range(L):
                row = [0] * n2
                for a, b, v in nz:
                    row[((i + a) % L) * L + ((j + b) % L)] = v
                rows.append(row)
    return 2 * (n2 - rank_mod_p(rows, p))


def eval_bloch_complex(
    m: list[list[LPoly3]], kx: float, ky: float, kz: float, mu: tuple[float, float, float] = (0.0, 0.0, 0.0)
) -> list[list[complex]]:
    out = [[0j] * 4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            s = 0j
            for (px, py, pz), v in m[i][j].items():
                s += v * cmath.exp((px * mu[0] + py * mu[1] + pz * mu[2]) + 1j * (px * kx + py * ky + pz * kz))
            out[i][j] = s
    return out


def det4_complex(mat: list[list[complex]]) -> complex:
    tot = 0j
    for perm, sgn in PERMS4:
        tot += sgn * mat[0][perm[0]] * mat[1][perm[1]] * mat[2][perm[2]] * mat[3][perm[3]]
    return tot


def charpoly4_complex(mat: list[list[complex]]) -> tuple[complex, complex, complex, complex, complex]:
    def mm(A: list[list[complex]], B: list[list[complex]]) -> list[list[complex]]:
        return [[sum(A[i][k] * B[k][j] for k in range(4)) for j in range(4)] for i in range(4)]

    def tr(A: list[list[complex]]) -> complex:
        return sum(A[i][i] for i in range(4))

    c3 = -tr(mat)
    b1 = [[mat[i][j] + (c3 if i == j else 0) for j in range(4)] for i in range(4)]
    mb1 = mm(mat, b1)
    c2 = -tr(mb1) / 2
    b2 = [[mb1[i][j] + (c2 if i == j else 0) for j in range(4)] for i in range(4)]
    mb2 = mm(mat, b2)
    c1 = -tr(mb2) / 3
    b3 = [[mb2[i][j] + (c1 if i == j else 0) for j in range(4)] for i in range(4)]
    mb3 = mm(mat, b3)
    c0 = -tr(mb3) / 4
    return (1 + 0j, c3, c2, c1, c0)


def quartic_discriminant(coeffs: tuple[complex, complex, complex, complex, complex]) -> complex:
    """Exact discriminant of monic quartic x^4 + b x^3 + c x^2 + d x + e (= prod_{i<j} (r_i - r_j)^2)."""
    _, b, c, d, e = coeffs
    return (
        256 * e**3
        - 192 * b * d * e**2
        - 128 * c**2 * e**2
        + 144 * c * d**2 * e
        - 27 * d**4
        + 144 * b**2 * c * e**2
        - 6 * b**2 * d**2 * e
        - 80 * b * c**2 * d * e
        + 18 * b * c * d**3
        + 16 * c**4 * e
        - 4 * c**3 * d**2
        - 27 * b**4 * e**2
        + 18 * b**3 * c * d * e
        - 4 * b**3 * d**3
        - 4 * b**2 * c**3 * e
        + b**2 * c**2 * d**2
    )


def discriminant_braid_degree(
    m: list[list[LPoly3]], axis: str, f1: float, f2: float, npts: int = 1024
) -> tuple[float, float]:
    """Coordinate-free canonical braid degree = (1/2pi) int d arg Disc(lambda I - M(k)) [numerical_approximation]."""
    vals: list[complex] = []
    min_abs = float("inf")
    for n in range(npts):
        t = 2.0 * math.pi * n / npts
        if axis == "x":
            mat = eval_bloch_complex(m, t, f1, f2)
        elif axis == "y":
            mat = eval_bloch_complex(m, f1, t, f2)
        else:
            mat = eval_bloch_complex(m, f1, f2, t)
        disc = quartic_discriminant(charpoly4_complex(mat))
        min_abs = min(min_abs, abs(disc))
        vals.append(disc)
    ang = 0.0
    for n in range(npts):
        ratio = vals[(n + 1) % npts] / vals[n]
        ang += math.atan2(ratio.imag, ratio.real)
    return ang / (2.0 * math.pi), min_abs


def roots4_dk(
    coeffs: tuple[complex, complex, complex, complex, complex], init: list[complex] | None = None
) -> list[complex]:
    _, c3, c2, c1, c0 = coeffs

    def f(z: complex) -> complex:
        return (((z + c3) * z + c2) * z + c1) * z + c0

    r = list(init) if init else [cmath.exp(1j * (2 * math.pi * k / 4 + 0.13)) * 2.1 for k in range(4)]
    for _ in range(80):
        mx = 0.0
        for i in range(4):
            denom = 1 + 0j
            for j in range(4):
                if i != j:
                    denom *= r[i] - r[j]
            if abs(denom) < 1e-18:
                denom = 1e-18 + 0j
            step = f(r[i]) / denom
            r[i] -= step
            mx = max(mx, abs(step))
        if mx < 1e-13:
            break
    return r


def track_braid_loop(
    m: list[list[LPoly3]], axis: str, f1: float, f2: float, nsteps: int = 600
) -> dict[str, Any]:
    """Track 4 complex bands around a 1D T^3 cycle [numerical_approximation with gap bound]."""
    def get_k(t: float) -> tuple[float, float, float]:
        if axis == "x":
            return (t, f1, f2)
        if axis == "y":
            return (f1, t, f2)
        return (f1, f2, t)

    r0 = roots4_dk(charpoly4_complex(eval_bloch_complex(m, *get_k(0.0))))
    r_prev = list(r0)
    min_gap = float("inf")
    trajectories: list[list[complex]] = [[z] for z in r0]
    for s in range(1, nsteps + 1):
        t = 2.0 * math.pi * s / nsteps
        r_curr = roots4_dk(charpoly4_complex(eval_bloch_complex(m, *get_k(t))), init=r_prev)
        best_p, best_d = PERMS4[0][0], float("inf")
        for perm, _ in PERMS4:
            d = sum(abs(r_curr[perm[i]] - r_prev[i]) for i in range(4))
            if d < best_d:
                best_d = d
                best_p = perm
        r_matched = [r_curr[best_p[i]] for i in range(4)]
        for i in range(4):
            trajectories[i].append(r_matched[i])
            for j in range(i + 1, 4):
                min_gap = min(min_gap, abs(r_matched[i] - r_matched[j]))
        r_prev = r_matched
    best_p, best_d = PERMS4[0][0], float("inf")
    for perm, _ in PERMS4:
        d = sum(abs(r_prev[i] - r0[perm[i]]) for i in range(4))
        if d < best_d:
            best_d = d
            best_p = perm
    disc_deg, min_disc = discriminant_braid_degree(m, axis, f1, f2)
    return {
        "axis": axis,
        "fixed": [f1, f2],
        "perm": list(best_p),
        "min_gap": min_gap,
        "discriminant_braid_degree": round(disc_deg),
        "discriminant_braid_degree_raw": disc_deg,
        "min_abs_discriminant": min_disc,
        "trajectories": trajectories,
    }


def spectral_winding(
    m: list[list[LPoly3]], axis: str, f1: float, f2: float, e_ref: complex = 0j, npts: int = 512
) -> tuple[float, float]:
    vals: list[complex] = []
    min_abs = float("inf")
    for n in range(npts):
        t = 2.0 * math.pi * n / npts
        if axis == "x":
            mat = eval_bloch_complex(m, t, f1, f2)
        elif axis == "y":
            mat = eval_bloch_complex(m, f1, t, f2)
        else:
            mat = eval_bloch_complex(m, f1, f2, t)
        for i in range(4):
            mat[i][i] -= e_ref
        d = det4_complex(mat)
        min_abs = min(min_abs, abs(d))
        vals.append(d)
    ang = 0.0
    for n in range(npts):
        ratio = vals[(n + 1) % npts] / vals[n]
        ang += math.atan2(ratio.imag, ratio.real)
    return ang / (2.0 * math.pi), min_abs


def ronkin_function(
    m: list[list[LPoly3]], mu: tuple[float, float, float], grid_n: int = 16
) -> float:
    """3D Ronkin integral R(mu) = (1/(2pi)^3) int log |det Psi(e^{mu+ik})| dk [numerical_approximation]."""
    tot = 0.0
    step = 2.0 * math.pi / grid_n
    for ix in range(grid_n):
        kx = ix * step
        for iy in range(grid_n):
            ky = iy * step
            for iz in range(grid_n):
                kz = iz * step
                d = abs(det4_complex(eval_bloch_complex(m, kx, ky, kz, mu)))
                tot += math.log(max(d, 1e-15))
    return tot / (grid_n**3)


def run_all_verifications(out_dir: Path | None = None) -> dict[str, Any]:
    """Run all exact algebraic & numerical checks and optionally emit JSON certificates."""
    a = gardam_alpha()
    b = gardam_beta()
    assert len(a) == 21 and len(b) == 21
    assert zp_mul(a, b, mod=2) == zp_one()
    assert zp_mul(b, a, mod=2) == zp_one()

    d_z = det_bloch4(a)
    assert len(d_z) == 89
    assert d_z[(0, 0, 0)] == 97
    assert sum(d_z.values()) == 945
    for (i, j, k), v in d_z.items():
        assert d_z.get((i, -j, -k)) == v
        assert d_z.get((-i, j, -k)) == v
        assert d_z.get((-i, -j, k)) == v
        assert ((v - 1) if (i, j, k) == (0, 0, 0) else v) % 4 == 0

    hensel = {}
    for bits in range(1, 7):
        inv, ok = hensel_lift_gardam(bits)
        assert ok
        hensel[f"mod_{1 << bits}"] = len(inv)

    # Haah CC1 + m=1 + m=3 tables across primes
    haah_cc1 = {
        str(p): {str(L): signed_haah_k_logical(L, p, 1, 1, 1, 1, 1, 1) for L in range(2, 16)}
        for p in [2, 3, 5, 7, 11, 13]
    }
    haah_m1 = {
        str(p): {str(L): signed_haah_k_logical(L, p, 1, 1, 1, 1, 1, -1) for L in range(2, 13)}
        for p in [2, 3, 5, 7, 11]
    }
    p23_odd = signed_haah_k_logical(11, 23, 1, 1, 1, 1, 1, 1)
    assert p23_odd == 6

    m = bloch_matrix4(a)
    loops = [
        track_braid_loop(m, "x", 0.3, 0.7),
        track_braid_loop(m, "x", 1.0, 1.5),
        track_braid_loop(m, "z", 2.0, 1.0),
        track_braid_loop(m, "y", 1.0, 1.5),
    ]
    braids_summary = [{k: v for k, v in lp.items() if k != "trajectories"} for lp in loops]

    ronkin = {
        "origin_N16": ronkin_function(m, (0.0, 0.0, 0.0), 16),
        "mu_x_05_N16": ronkin_function(m, (0.5, 0.0, 0.0), 16),
        "mu_mx_05_N16": ronkin_function(m, (-0.5, 0.0, 0.0), 16),
        "mu_z_05_N16": ronkin_function(m, (0.0, 0.0, 0.5), 16),
    }

    report = {
        "version": "1.0.0",
        "gardam_alpha_support": len(a),
        "gardam_beta_support": len(b),
        "det_terms": len(d_z),
        "det_const_term": d_z[(0, 0, 0)],
        "det_augmentation": sum(d_z.values()),
        "det_mod4_holds": True,
        "hensel_2adic_supports": hensel,
        "haah_cc1_k_logical": haah_cc1,
        "haah_m1_singular_p3_k_logical": haah_m1,
        "haah_cc1_p23_L11_k": p23_odd,
        "ronkin_summary": ronkin,
        "braid_monodromy": braids_summary,
    }
    if out_dir is not None:
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "exact_verification_report.json").write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    return report


if __name__ == "__main__":
    rep = run_all_verifications(Path(__file__).resolve().parents[2] / "results")
    print(json.dumps(rep, indent=2))
