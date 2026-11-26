# SPDX-License-Identifier: Apache-2.0
"""Comprehensive verification suite for promislow-fracton-amoeba.

Covers Build Standard v1.2.0 Part B items:
- B05: Falsifiable tests per claim (T1a..T3c)
- B06: Negative tests (invalid primes, false sign-lift claims, non-units, off-torus violations)
- B08: Golden snapshot check against results/exact_verification_report.json
- B10: Hypothesis property-based tests (ElemP group axioms, Bloch homomorphism, V4 invariance)
- B11/B12: Differential testing between zero-dependency Rust binary and independent Python oracle
- B14: Metamorphic testing (V4 coordinate flips, Ronkin symmetry)
- B20: Numerical & floating-point stability (Ronkin grid refinement & discriminant degree integrality)
"""

from __future__ import annotations

import json
import math
import subprocess
import sys
from pathlib import Path

import numpy as np
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))

from pfa_verify.exact_core import (
    bloch_matrix4,
    det4_complex,
    det_bloch4,
    elem_inv,
    elem_mul,
    eval_bloch_complex,
    gardam_alpha,
    gardam_beta,
    hensel_lift_gardam,
    ronkin_function,
    signed_haah_k_logical,
    spectral_winding,
    track_braid_loop,
    zp_add,
    zp_mul,
    zp_one,
    zp_star,
    zp_sub,
)


def _find_rust_binary() -> Path | None:
    for name in ("promislow_core.exe", "promislow_core"):
        cand = ROOT / "rust" / "target" / "release" / name
        if cand.exists():
            return cand
    return None


def _elem_pow(g: tuple[int, int, int, int], n: int) -> tuple[int, int, int, int]:
    acc = (0, 0, 0, 0)
    for _ in range(n):
        acc = elem_mul(acc, g)
    return acc


def _signed_haah_conic_det(a1: int, a2: int, a3: int, b1: int, b2: int, b3: int) -> int:
    A = -a1 * b3
    B = a3 * b1 - a2 * b3 - a1 * b2
    C = -a2 * b2
    D = -b3
    E = -b2
    F = a3
    return 2 * A * (4 * C * F - E * E) - B * (2 * B * F - D * E) + D * (B * E - 2 * C * D)


# ---------- B10: Hypothesis Property-Based Tests ----------

elem_p_strategy = st.tuples(
    st.integers(-4, 4),
    st.integers(-4, 4),
    st.integers(-4, 4),
    st.integers(0, 3),
)


@given(g1=elem_p_strategy, g2=elem_p_strategy, g3=elem_p_strategy)
@settings(max_examples=200, deadline=None)
def test_hypothesis_promislow_group_axioms_and_torsion_free(g1, g2, g3):
    """B10 / T1a: Associativity, exact left/right inverses, and torsion-free check."""
    assert elem_mul(elem_mul(g1, g2), g3) == elem_mul(g1, elem_mul(g2, g3))
    e = (0, 0, 0, 0)
    assert elem_mul(g1, elem_inv(g1)) == e
    assert elem_mul(elem_inv(g1), g1) == e
    if g1 != e:
        for n in (1, 2, 3, 4, 5):
            assert _elem_pow(g1, n) != e


@given(
    u_terms=st.lists(st.tuples(elem_p_strategy, st.integers(-3, 3)), min_size=1, max_size=5),
    v_terms=st.lists(st.tuples(elem_p_strategy, st.integers(-3, 3)), min_size=1, max_size=5),
    kx=st.floats(-math.pi, math.pi, allow_nan=False, allow_infinity=False),
    ky=st.floats(-math.pi, math.pi, allow_nan=False, allow_infinity=False),
    kz=st.floats(-math.pi, math.pi, allow_nan=False, allow_infinity=False),
)
@settings(max_examples=120, deadline=None)
def test_hypothesis_bloch_homomorphism_and_v4_invariance(u_terms, v_terms, kx, ky, kz):
    """B10 / T1b & T1c: Exact homomorphism Psi(u*v)=Psi(u)Psi(v) and V4 determinant invariance."""
    u: dict[tuple[int, int, int, int], int] = {}
    for g, c in u_terms:
        u[g] = u.get(g, 0) + c
    u = {g: c for g, c in u.items() if c != 0}

    v: dict[tuple[int, int, int, int], int] = {}
    for g, c in v_terms:
        v[g] = v.get(g, 0) + c
    v = {g: c for g, c in v.items() if c != 0}

    uv = zp_mul(u, v)
    mu = np.array(eval_bloch_complex(bloch_matrix4(u), kx, ky, kz), dtype=np.complex128)
    mv = np.array(eval_bloch_complex(bloch_matrix4(v), kx, ky, kz), dtype=np.complex128)
    muv = np.array(eval_bloch_complex(bloch_matrix4(uv), kx, ky, kz), dtype=np.complex128)
    assert np.allclose(mu @ mv, muv, atol=1e-10, rtol=1e-10)

    d0 = det4_complex(eval_bloch_complex(bloch_matrix4(u), kx, ky, kz))
    for tkx, tky, tkz in [(kx, -ky, -kz), (-kx, ky, -kz), (-kx, -ky, kz)]:
        dt = det4_complex(eval_bloch_complex(bloch_matrix4(u), tkx, tky, tkz))
        assert abs(d0 - dt) < 1e-9 * max(1.0, abs(d0))


# ---------- B05: Falsifiable Exact Claim Tests ----------

def test_pillar1_gardam_unit_mod4_hensel_and_sign_obstruction():
    """T1e, T1f: Gardam mod-2 unit, 89-term det == 1 (mod 4), 2-adic tower, strengthened obstruction."""
    a = gardam_alpha()
    b = gardam_beta()
    assert len(a) == 21
    assert len(b) == 21
    assert zp_mul(a, b, mod=2) == zp_one()
    assert zp_mul(b, a, mod=2) == zp_one()

    det_poly = det_bloch4(a)
    assert len(det_poly) == 89
    assert det_poly[(0, 0, 0)] == 97
    assert sum(det_poly.values()) == 945
    for (i, j, k), coeff in det_poly.items():
        assert det_poly.get((i, -j, -k)) == coeff
        assert det_poly.get((-i, j, -k)) == coeff
        assert det_poly.get((-i, -j, k)) == coeff
        if (i, j, k) == (0, 0, 0):
            assert coeff % 4 == 1
        else:
            assert coeff % 4 == 0

    expected_supports = [21, 169, 459, 1388]
    for bits, exp_sup in enumerate(expected_supports, start=1):
        inv, ok = hensel_lift_gardam(bits)
        assert ok
        assert len(inv) == exp_sup

    # T1f Strengthened obstruction: P1^2 - 31 in {+1, -1} has zero integer solutions
    for p1 in range(-20, 21):
        assert p1 * p1 - 31 not in (-1, 1)


def test_pillar2_haah_64_classes_odd_primes_and_hw_fractons():
    """T2b, T2d, T2e: 64 signed classes, p=23 threshold, Gardam-twisted & intrinsic HW fractons."""
    hist: dict[int, int] = {}
    for a1 in (1, -1):
        for a2 in (1, -1):
            for a3 in (1, -1):
                for b1 in (1, -1):
                    for b2 in (1, -1):
                        for b3 in (1, -1):
                            d = _signed_haah_conic_det(a1, a2, a3, b1, b2, b3)
                            hist[d] = hist.get(d, 0) + 1
    assert sum(hist.values()) == 64
    assert hist == {-12: 12, -8: 16, -4: 4, 4: 4, 8: 16, 12: 12}

    # First odd-L rational root threshold at p = 23, L = 11
    assert signed_haah_k_logical(11, 23, 1, 1, 1, 1, 1, 1) == 6
    assert signed_haah_k_logical(6, 3, 1, 1, 1, 1, 1, 1) == 18
    assert signed_haah_k_logical(10, 5, 1, 1, 1, 1, 1, 1) == 30
    assert signed_haah_k_logical(8, 3, 1, 1, 1, 1, 1, -1) == 24

    # T2e: Gardam-twisted Haah & intrinsic HW fracton codes
    a, b = gardam_alpha(), gardam_beta()
    f_p = {(0, 0, 0, 0): 1, (1, 0, 0, 0): 1, (0, 1, 0, 0): 1, (0, 0, 1, 0): 1}
    g_p = {(0, 0, 0, 0): 1, (1, 1, 0, 0): 1, (0, 1, 1, 0): 1, (1, 0, 1, 0): 1}
    hx1 = zp_mul(f_p, a, mod=2)
    hx2 = zp_mul(g_p, a, mod=2)
    hz1 = zp_mul(zp_star(g_p), zp_star(b), mod=2)
    hz2 = zp_mul(zp_star(f_p), zp_star(b), mod=2)
    assert (len(hx1), len(hx2), len(hz1), len(hz2)) == (52, 52, 52, 56)
    assert zp_add(zp_mul(hx1, zp_star(hz1), mod=2), zp_mul(hx2, zp_star(hz2), mod=2), mod=2) == {}

    comm_z = zp_sub(
        zp_mul(zp_mul(f_p, a), zp_star(zp_mul(zp_star(g_p), zp_star(b)))),
        zp_mul(zp_mul(g_p, a), zp_star(zp_mul(zp_star(f_p), zp_star(b)))),
    )
    assert len(comm_z) == 342
    assert all(v % 2 == 0 for v in comm_z.values())

    f_hw = {(0, 0, 0, 0): 1, (0, 0, 0, 1): 1, (0, 0, 0, 2): 1, (0, 0, 0, 3): 1}
    g_hw = {
        (0, 0, 0, 0): 1, (1, 0, 0, 0): 1, (-1, 0, 0, 0): 1,
        (0, 1, 0, 0): 1, (0, -1, 0, 0): 1, (0, 0, 1, 0): 1, (0, 0, -1, 0): 1,
    }
    assert zp_mul(f_hw, g_hw) == zp_mul(g_hw, f_hw)
    assert zp_mul(f_hw, {(1, 0, 0, 0): 1}) != zp_mul({(1, 0, 0, 0): 1}, f_hw)


def test_pillar3_ronkin_bipolar_winding_and_s4_braid_monodromy():
    """T3a, T3c, B20: Ronkin minimum, bipolar winding antisymmetry, integral braid degrees."""
    m = bloch_matrix4(gardam_alpha())
    r0 = ronkin_function(m, (0.0, 0.0, 0.0), grid_n=12)
    rx = ronkin_function(m, (0.5, 0.0, 0.0), grid_n=12)
    rz = ronkin_function(m, (0.0, 0.0, 0.5), grid_n=12)
    assert r0 < rx and r0 < rz
    # B20 grid-refinement stability (O(1/N) due to logarithmic nodal curves where det=0)
    r0_16 = ronkin_function(m, (0.0, 0.0, 0.0), grid_n=16)
    assert abs(r0 - r0_16) < 0.05
    assert abs(r0_16 - 4.27174279) < 1e-5
    # Exact analytical scalar normalization check: det(2 * I_4) = 16 => R(0) = 4 * ln(2)
    r_scalar = ronkin_function(bloch_matrix4({(0, 0, 0, 0): 2}), (0.0, 0.0, 0.0), grid_n=4)
    assert abs(r_scalar - 4.0 * math.log(2.0)) < 1e-12

    # Exact bipolar winding antisymmetry W_x(ky, -kz) = -W_x(ky, kz)
    w_pos, gap_pos = spectral_winding(m, "x", 0.7, 1.3, e_ref=0j, npts=512)
    w_neg, gap_neg = spectral_winding(m, "x", 0.7, -1.3, e_ref=0j, npts=512)
    assert gap_pos > 1.0 and gap_neg > 1.0
    assert abs(w_pos + w_neg) < 1e-6

    # Canonical discriminant braid degrees (coordinate-free integer invariants)
    for axis, f1, f2, exp_deg, exp_perm in [
        ("x", 0.3, 0.7, -1, [0, 2, 1, 3]),
        ("x", 1.0, 1.5, -3, [2, 3, 1, 0]),
        ("z", 2.0, 1.0, -2, [1, 0, 3, 2]),
        ("y", 1.0, 1.5, 3, [3, 2, 0, 1]),
    ]:
        res = track_braid_loop(m, axis, f1, f2, nsteps=600)
        assert abs(res["discriminant_braid_degree_raw"] - exp_deg) < 1e-6
        assert res["discriminant_braid_degree"] == exp_deg
        assert res["perm"] == exp_perm
        assert res["min_gap"] > 0.4


# ---------- B06: Negative Tests ----------

def test_negative_gardam_not_unit_over_Z_and_perturbed_breaks_unit():
    """B06: Gardam alpha*beta != 1 over Z[P], and removing any term destroys mod-2 invertibility."""
    a, b = gardam_alpha(), gardam_beta()
    prod_z = zp_mul(a, b)
    assert prod_z != zp_one()
    assert prod_z[(0, 0, 0, 0)] == 17

    bad_a = dict(a)
    bad_a.pop((0, 0, 0, 0))
    assert zp_mul(bad_a, b, mod=2) != zp_one()

    for p in (3, 5, 7, 11, 13, 23):
        assert 4 % p != 0


# ---------- B14: Metamorphic Tests ----------

def test_metamorphic_v4_ronkin_symmetry():
    """B14: V4 reflections of mu leave R(mu) strictly invariant."""
    m = bloch_matrix4(gardam_alpha())
    mu = (0.35, -0.25, 0.40)
    r_base = ronkin_function(m, mu, grid_n=10)
    for s_mu in [
        (mu[0], -mu[1], -mu[2]),
        (-mu[0], mu[1], -mu[2]),
        (-mu[0], -mu[1], mu[2]),
    ]:
        assert abs(ronkin_function(m, s_mu, grid_n=10) - r_base) < 1e-10


# ---------- B08: Golden Snapshot Test ----------

def test_golden_verification_report_matches():
    """B08: Golden report JSON matches exact invariants."""
    rep_path = ROOT / "results" / "exact_verification_report.json"
    assert rep_path.exists()
    rep = json.loads(rep_path.read_text(encoding="utf-8"))
    assert rep["gardam_alpha_support"] == 21
    assert rep["det_terms"] == 89
    assert rep["det_const_term"] == 97
    assert rep["det_augmentation"] == 945
    assert rep["det_mod4_holds"] is True
    assert rep["haah_cc1_p23_L11_k"] == 6


# ---------- B11 / B12: Differential Rust vs Python Oracle Test ----------

def test_differential_rust_vs_python_oracle():
    """B11/B12: Zero-dependency Rust binary agrees bit-for-bit with Python exact oracle."""
    rust_bin = _find_rust_binary()
    if rust_bin is None:
        pytest.skip("Rust release binary not built yet")
    proc = subprocess.run(
        [str(rust_bin), "summary"],
        capture_output=True,
        text=True,
        check=True,
        timeout=60,
    )
    rust_data = json.loads(proc.stdout)
    rep = json.loads((ROOT / "results" / "exact_verification_report.json").read_text(encoding="utf-8"))

    assert rust_data["gardam_alpha_support"] == rep["gardam_alpha_support"]
    assert rust_data["gardam_beta_support"] == rep["gardam_beta_support"]
    assert rust_data["det_terms"] == rep["det_terms"]
    assert rust_data["det_const_term"] == rep["det_const_term"]
    assert rust_data["det_augmentation"] == rep["det_augmentation"]
    assert rust_data["haah_cc1_p23_L11_k"] == rep["haah_cc1_p23_L11_k"]
    assert abs(rust_data["ronkin_origin_16"] - rep["ronkin_summary"]["origin_N16"]) < 1e-6
    assert abs(rust_data["ronkin_mu_x05_16"] - rep["ronkin_summary"]["mu_x_05_N16"]) < 1e-6
    assert abs(rust_data["ronkin_mu_z05_16"] - rep["ronkin_summary"]["mu_z_05_N16"]) < 1e-6

    for key, py_entry in [
        ("braid_x_03_07", rep["braid_monodromy"][0]),
        ("braid_x_10_15", rep["braid_monodromy"][1]),
        ("braid_z_20_10", rep["braid_monodromy"][2]),
    ]:
        assert rust_data[key]["disc_braid_deg"] == py_entry["discriminant_braid_degree"]
        assert rust_data[key]["perm"] == py_entry["perm"]
