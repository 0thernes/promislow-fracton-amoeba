module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import PromislowFracton.HaahFractons

/-!
# 3D Non-Hermitian Amoeba Skin Effect, `V₄`-Convex Ronkin Origin-Minimum Law,
# Haah Fracton Quadrilateral Double-Amoeba, Algebraic EP2 Jordan Nilpotency,
# and Exact `B₄` Artin Braid Group / `S₄` Monodromy Generation (`CM-018`, `FLD-060`)
# (Theorems `T3a`, `T3b`, `T3c`)

Zero `sorry`, zero `native_decide`, zero Mathlib.
-/

@[expose] public section

namespace PromislowFracton

/-! ### Theorem `T3a`: Universal `V₄`-Convex Ronkin Origin-Minimum Law (`CM-018`) -/

/-- A function `R : ℚ³ → ℚ` is midpoint-convex if `R((u + v)/2) ≤ (R(u) + R(v))/2` for all `u, v`.
    (Equivalently, `2·R((u+v)/2) ≤ R(u) + R(v)`.) -/
def IsMidpointConvex3 (R : RatQ → RatQ → RatQ → RatQ) : Prop :=
  ∀ x1 y1 z1 x2 y2 z2 : RatQ,
    RatQ.le
      (R (RatQ.mul RatQ.half (RatQ.add x1 x2))
         (RatQ.mul RatQ.half (RatQ.add y1 y2))
         (RatQ.mul RatQ.half (RatQ.add z1 z2)))
      (RatQ.mul RatQ.half (RatQ.add (R x1 y1 z1) (R x2 y2 z2)))

/-- A function `R : ℚ³ → ℚ` is `V₄`-symmetric (forced on EVERY Hantzsche–Wendt Ronkin function
    by Theorem `T1c`) if it is invariant under `(x, y, z) ↦ (x, -y, -z), (-x, y, -z), (-x, -y, z)`
    and respects `RatQ.eqv` on arguments. -/
def IsV4Symmetric3 (R : RatQ → RatQ → RatQ → RatQ) : Prop :=
  (∀ x1 y1 z1 x2 y2 z2,
    RatQ.eqv x1 x2 → RatQ.eqv y1 y2 → RatQ.eqv z1 z2 →
    RatQ.eqv (R x1 y1 z1) (R x2 y2 z2)) ∧
  (∀ x y z, RatQ.eqv (R x (RatQ.neg y) (RatQ.neg z)) (R x y z)) ∧
  (∀ x y z, RatQ.eqv (R (RatQ.neg x) y (RatQ.neg z)) (R x y z)) ∧
  (∀ x y z, RatQ.eqv (R (RatQ.neg x) (RatQ.neg y) z) (R x y z))

private theorem ratq_half_add_self (a : RatQ) :
    RatQ.eqv (RatQ.mul RatQ.half (RatQ.add a a)) a := by
  unfold RatQ.eqv RatQ.mul RatQ.add RatQ.half
  simp only [Int.natCast_mul]; grind

private theorem ratq_half_add_neg (a : RatQ) :
    RatQ.eqv (RatQ.mul RatQ.half (RatQ.add a (RatQ.neg a))) (RatQ.ofInt 0) := by
  unfold RatQ.eqv RatQ.mul RatQ.add RatQ.neg RatQ.half RatQ.ofInt
  simp only [Int.natCast_mul]; grind

private theorem ratq_eqv_symm {a b : RatQ} (h : RatQ.eqv a b) : RatQ.eqv b a := h.symm

private theorem ratq_le_of_eqv_left {a b c : RatQ} (hab : RatQ.eqv a b) (hbc : RatQ.le b c) :
    RatQ.le a c :=
  RatQ.le_trans (RatQ.le_of_eqv hab) hbc

private theorem ratq_le_of_eqv_right {a b c : RatQ} (hab : RatQ.le a b) (hbc : RatQ.eqv b c) :
    RatQ.le a c :=
  RatQ.le_trans hab (RatQ.le_of_eqv hbc)

/-- **Theorem `T3a` (Universal `V₄`-Convex Ronkin Origin-Minimum Law — NEW):**
    For EVERY midpoint-convex, `V₄`-symmetric Ronkin function `R : ℚ³ → ℚ` (which holds
    for EVERY Hantzsche–Wendt Bloch operator `Ψ(u)` by Theorem `T1c`!), the global minimum
    of `R` is ALWAYS attained at the origin `(0, 0, 0)`:
      `∀ μ_x, μ_y, μ_z ∈ ℚ,   R(0, 0, 0) ≤ R(μ_x, μ_y, μ_z)`.
    Proof applies midpoint convexity twice across the 4-element `V₄`-orbit
    `{(x, y, z), (x, -y, -z), (-x, y, -z), (-x, -y, z)}`:
      1. `R(x, 0, 0) ≤ ½(R(x, y, z) + R(x, -y, -z)) = R(x, y, z)`
      2. `R(-x, 0, 0) ≤ ½(R(-x, y, -z) + R(-x, -y, z)) = R(x, y, z)`
      3. `R(0, 0, 0) ≤ ½(R(x, 0, 0) + R(-x, 0, 0)) ≤ R(x, y, z)`! -/
theorem v4_convex_ronkin_origin_minimum (R : RatQ → RatQ → RatQ → RatQ)
    (hconv : IsMidpointConvex3 R) (hsym : IsV4Symmetric3 R) :
    ∀ x y z : RatQ, RatQ.le (R (RatQ.ofInt 0) (RatQ.ofInt 0) (RatQ.ofInt 0)) (R x y z) := by
  intro x y z
  obtain ⟨hcong, hVa, hVb, hVab⟩ := hsym
  have hz : RatQ.eqv (RatQ.ofInt 0) (RatQ.ofInt 0) := rfl
  -- Step 1: R(x, 0, 0) ≤ R(x, y, z)
  have h1_raw := hconv x y z x (RatQ.neg y) (RatQ.neg z)
  have h1_lhs : RatQ.eqv (R x (RatQ.ofInt 0) (RatQ.ofInt 0))
      (R (RatQ.mul RatQ.half (RatQ.add x x))
         (RatQ.mul RatQ.half (RatQ.add y (RatQ.neg y)))
         (RatQ.mul RatQ.half (RatQ.add z (RatQ.neg z)))) :=
    hcong _ _ _ _ _ _ (ratq_eqv_symm (ratq_half_add_self x))
      (ratq_eqv_symm (ratq_half_add_neg y)) (ratq_eqv_symm (ratq_half_add_neg z))
  have h1_rhs : RatQ.le (RatQ.mul RatQ.half (RatQ.add (R x y z) (R x (RatQ.neg y) (RatQ.neg z)))) (R x y z) := by
    have hadd := RatQ.add_le_add (RatQ.le_refl (R x y z)) (RatQ.le_of_eqv (hVa x y z))
    have hmul := RatQ.mul_nonneg_le (k := RatQ.half) (by decide) hadd
    exact ratq_le_of_eqv_right hmul (ratq_half_add_self (R x y z))
  have hstep1 : RatQ.le (R x (RatQ.ofInt 0) (RatQ.ofInt 0)) (R x y z) :=
    RatQ.le_trans (ratq_le_of_eqv_left h1_lhs h1_raw) h1_rhs
  -- Step 2: R(-x, 0, 0) ≤ R(x, y, z)
  have h2_raw := hconv (RatQ.neg x) y (RatQ.neg z) (RatQ.neg x) (RatQ.neg y) z
  have hneg_z_add : RatQ.eqv (RatQ.mul RatQ.half (RatQ.add (RatQ.neg z) z)) (RatQ.ofInt 0) := by
    unfold RatQ.eqv RatQ.mul RatQ.add RatQ.neg RatQ.half RatQ.ofInt
    simp only [Int.natCast_mul]; grind
  have h2_lhs : RatQ.eqv (R (RatQ.neg x) (RatQ.ofInt 0) (RatQ.ofInt 0))
      (R (RatQ.mul RatQ.half (RatQ.add (RatQ.neg x) (RatQ.neg x)))
         (RatQ.mul RatQ.half (RatQ.add y (RatQ.neg y)))
         (RatQ.mul RatQ.half (RatQ.add (RatQ.neg z) z))) :=
    hcong _ _ _ _ _ _ (ratq_eqv_symm (ratq_half_add_self (RatQ.neg x)))
      (ratq_eqv_symm (ratq_half_add_neg y)) (ratq_eqv_symm hneg_z_add)
  have h2_rhs : RatQ.le
      (RatQ.mul RatQ.half (RatQ.add (R (RatQ.neg x) y (RatQ.neg z)) (R (RatQ.neg x) (RatQ.neg y) z)))
      (R x y z) := by
    have hadd := RatQ.add_le_add (RatQ.le_of_eqv (hVb x y z)) (RatQ.le_of_eqv (hVab x y z))
    have hmul := RatQ.mul_nonneg_le (k := RatQ.half) (by decide) hadd
    exact ratq_le_of_eqv_right hmul (ratq_half_add_self (R x y z))
  have hstep2 : RatQ.le (R (RatQ.neg x) (RatQ.ofInt 0) (RatQ.ofInt 0)) (R x y z) :=
    RatQ.le_trans (ratq_le_of_eqv_left h2_lhs h2_raw) h2_rhs
  -- Step 3: R(0, 0, 0) ≤ ½(R(x, 0, 0) + R(-x, 0, 0)) ≤ R(x, y, z)
  have h3_raw := hconv x (RatQ.ofInt 0) (RatQ.ofInt 0) (RatQ.neg x) (RatQ.ofInt 0) (RatQ.ofInt 0)
  have h3_lhs : RatQ.eqv (R (RatQ.ofInt 0) (RatQ.ofInt 0) (RatQ.ofInt 0))
      (R (RatQ.mul RatQ.half (RatQ.add x (RatQ.neg x)))
         (RatQ.mul RatQ.half (RatQ.add (RatQ.ofInt 0) (RatQ.ofInt 0)))
         (RatQ.mul RatQ.half (RatQ.add (RatQ.ofInt 0) (RatQ.ofInt 0)))) :=
    hcong _ _ _ _ _ _ (ratq_eqv_symm (ratq_half_add_neg x))
      (ratq_eqv_symm (ratq_half_add_self (RatQ.ofInt 0)))
      (ratq_eqv_symm (ratq_half_add_self (RatQ.ofInt 0)))
  have h3_rhs : RatQ.le
      (RatQ.mul RatQ.half (RatQ.add (R x (RatQ.ofInt 0) (RatQ.ofInt 0)) (R (RatQ.neg x) (RatQ.ofInt 0) (RatQ.ofInt 0))))
      (R x y z) := by
    have hadd := RatQ.add_le_add hstep1 hstep2
    have hmul := RatQ.mul_nonneg_le (k := RatQ.half) (by decide) hadd
    exact ratq_le_of_eqv_right hmul (ratq_half_add_self (R x y z))
  exact RatQ.le_trans (ratq_le_of_eqv_left h3_lhs h3_raw) h3_rhs

/-! ### Theorem `T3b`: Exact 3D Haah Fracton Amoeba Quadrilateral Inequality & EP2 Jordan Nilpotency -/

/-- Exact quadrilateral predicate characterizing the 3D Amoeba `𝒜(1 + x + y + z)` in radius
    coordinates `(r_x, r_y, r_z) = (e^{μ_x}, e^{μ_y}, e^{μ_z}) > 0`! -/
def InLinearAmoeba (rx ry rz : Int) : Prop :=
  0 < rx ∧ 0 < ry ∧ 0 < rz ∧
  1 ≤ rx + ry + rz ∧ rx ≤ 1 + ry + rz ∧ ry ≤ 1 + rx + rz ∧ rz ≤ 1 + rx + ry

/-- Exact quadrilateral predicate characterizing the 3D Amoeba `𝒜(1 + xy + yz + zx)` in
    scaled radius coordinates `(r_x, r_y, r_z) > 0`! -/
def InQuadAmoeba (rx ry rz : Int) : Prop :=
  0 < rx ∧ 0 < ry ∧ 0 < rz ∧
  1 ≤ rx * ry + ry * rz + rz * rx ∧
  rx * ry ≤ 1 + ry * rz + rz * rx ∧
  ry * rz ≤ 1 + rx * ry + rz * rx ∧
  rz * rx ≤ 1 + rx * ry + ry * rz

/-- Exact `2 × 2` off-diagonal non-Hermitian Haah fracton Dirac matrix `[[0, a], [b, 0]]`. -/
structure Mat2 (R : Type) where
  a00 : R
  a01 : R
  a10 : R
  a11 : R
  deriving DecidableEq, Repr

def Mat2.mul {R : Type} [SimpleCommRing R] (A B : Mat2 R) : Mat2 R :=
  let m := SimpleCommRing.mul; let a := SimpleCommRing.add
  ⟨a (m A.a00 B.a00) (m A.a01 B.a10), a (m A.a00 B.a01) (m A.a01 B.a11),
   a (m A.a10 B.a00) (m A.a11 B.a10), a (m A.a10 B.a01) (m A.a11 B.a11)⟩

def Mat2.zero {R : Type} [SimpleCommRing R] : Mat2 R :=
  ⟨SimpleCommRing.zero, SimpleCommRing.zero, SimpleCommRing.zero, SimpleCommRing.zero⟩

def haahDirac2 {R : Type} [SimpleCommRing R] (fval gval : R) : Mat2 R :=
  ⟨SimpleCommRing.zero, fval, gval, SimpleCommRing.zero⟩

/-- **Theorem `T3b` (3D Non-Hermitian Haah Double-Amoeba & Algebraic EP2 Jordan Coalescence):**
    1. **Double-Amoeba Non-Emptiness & Symmetrical Origin Inclusion:**
       The unit 3-torus `(r_x, r_y, r_z) = (1, 1, 1)` (i.e. `μ = (0, 0, 0)`) lies strictly inside
       the intersection `𝒜(f) ∩ 𝒜(g)` of BOTH 3D Haah fracton amoebas, and every diagonal point
       `(r, r, r)` with `r ≥ 1` lies in `𝒜(f) ∩ 𝒜(g)`, while `(r, 1, 1)` exits `𝒜(f)` for `r ≥ 4`!
    2. **Exact Algebraic EP2 Jordan-Block Nilpotency & Eigenvector Coalescence:**
       Over ANY integral domain `R`, if `fval = 0` and `gval ≠ 0` (a single-generator Exceptional Point),
       then `H = [[0, 0], [gval, 0]]` satisfies:
       - `H ≠ 0`,
       - `H² = 0` (strict Jordan nilpotency of order 2 — non-diagonalizable!),
       - EVERY zero-eigenvector `(v₀, v₁)` (`H · v = 0`) is forced to have `v₀ = 0` (1D eigenspace coalescence!). -/
theorem haah_amoeba_and_ep2_jordan :
    (InLinearAmoeba 1 1 1 ∧ InQuadAmoeba 1 1 1) ∧
    (∀ r : Int, 1 ≤ r → InLinearAmoeba r r r ∧ InQuadAmoeba r r r) ∧
    (∀ r : Int, 4 ≤ r → ¬ InLinearAmoeba r 1 1) ∧
    (∀ (R : Type) [SimpleIntegralDomain R] (gval : R),
      gval ≠ SimpleCommRing.zero →
      let H := haahDirac2 (R := R) SimpleCommRing.zero gval
      H ≠ Mat2.zero ∧
      Mat2.mul H H = Mat2.zero ∧
      (∀ v0 v1 : R,
        SimpleCommRing.add (SimpleCommRing.mul H.a10 v0) (SimpleCommRing.mul H.a11 v1) = SimpleCommRing.zero →
        v0 = SimpleCommRing.zero)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨by unfold InLinearAmoeba; omega, by unfold InQuadAmoeba; omega⟩
  · intro r hr
    constructor
    · unfold InLinearAmoeba; omega
    · unfold InQuadAmoeba
      have hrr : 1 ≤ r * r := Int.mul_le_mul hr hr (by omega) (by omega)
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro r hr h
    unfold InLinearAmoeba at h; omega
  · intro R _ gval hgnz
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      have h10 : gval = SimpleCommRing.zero := congrArg Mat2.a10 heq
      exact hgnz h10
    · unfold haahDirac2 Mat2.mul Mat2.zero
      simp [SimpleCommRing.mul_zero, SimpleCommRing.zero_mul, SimpleCommRing.add_zero]
    · intro v0 v1 hv
      simp only [haahDirac2, SimpleCommRing.zero_mul, SimpleCommRing.add_zero] at hv
      rcases SimpleIntegralDomain.mul_eq_zero gval v0 hv with hg0 | hv0
      · exact absurd hg0 hgnz
      · exact hv0

/-! ### Theorem `T3c`: Artin Braid Group `B₄` Relations & Full `S₄` Monodromy Generation (`CM-018`) -/

/-- Elements of the symmetric group `S₄` acting on 4 complex Bloch bands `{0, 1, 2, 3}`,
    represented as bijections `Fin 4 → Fin 4` via 4-tuples `(p0, p1, p2, p3)`. -/
structure Perm4 where
  p0 : Fin 4
  p1 : Fin 4
  p2 : Fin 4
  p3 : Fin 4
  deriving DecidableEq, Repr

namespace Perm4

def apply (π : Perm4) (i : Fin 4) : Fin 4 :=
  match i with
  | ⟨0, _⟩ => π.p0
  | ⟨1, _⟩ => π.p1
  | ⟨2, _⟩ => π.p2
  | ⟨3, _⟩ => π.p3

def comp (π σ : Perm4) : Perm4 :=
  ⟨π.apply σ.p0, π.apply σ.p1, π.apply σ.p2, π.apply σ.p3⟩

def id : Perm4 := ⟨0, 1, 2, 3⟩

/-- Artin braid generators `σ₁, σ₂, σ₃` projected to `S₄` (adjacent band swaps). -/
def s1 : Perm4 := ⟨1, 0, 2, 3⟩
def s2 : Perm4 := ⟨0, 2, 1, 3⟩
def s3 : Perm4 := ⟨0, 1, 3, 2⟩

/-- The concrete monodromy permutations discovered on Gardam's 4-band Hantzsche–Wendt crystal
    `Ψ(α̃)(k)` around fundamental cycles of `𝕋³`:
    - `g_x1 = (0, 2, 1, 3)` (transposition `(1 2)` at `loop x (0.3, 0.7)`, gap `0.4841`)
    - `g_x2 = (2, 3, 1, 0)` (4-cycle `(0 2 1 3)` at `loop x (1.0, 1.5)`, gap `1.5925`)
    - `g_z2 = (1, 0, 3, 2)` (double transposition `(0 1)(2 3)` at `loop z (2.0, 1.0)`, gap `1.4901`) -/
def gardamLoopX1 : Perm4 := ⟨0, 2, 1, 3⟩
def gardamLoopX2 : Perm4 := ⟨2, 3, 1, 0⟩
def gardamLoopZ2 : Perm4 := ⟨1, 0, 3, 2⟩

/-- BFS closure of a generator set in `S₄` (bounded fuel 30 > |S₄| = 24). -/
def closeStep (gens cur : List Perm4) : List Perm4 :=
  cur.foldl (fun acc x =>
    gens.foldl (fun acc2 g =>
      let y := comp g x
      if acc2.contains y then acc2 else y :: acc2) acc) cur

def subgroupOrderLoop (gens : List Perm4) : Nat → List Perm4 → List Perm4
  | 0, cur => cur
  | n + 1, cur =>
    let nxt := closeStep gens cur
    if nxt.length == cur.length then cur else subgroupOrderLoop gens n nxt

def subgroupOrder (gens : List Perm4) : Nat :=
  (subgroupOrderLoop gens 30 [id]).length

end Perm4

/-- **Theorem `T3c` (Artin Braid `B₄` Relations & Full Non-Abelian `S₄` Monodromy Generation):**
    1. The three adjacent-band crossing generators `σ₁, σ₂, σ₃` satisfy all three Artin braid
       relations (`σ₁σ₂σ₁ = σ₂σ₁σ₂`, `σ₂σ₃σ₂ = σ₃σ₂σ₃`, `σ₁σ₃ = σ₃σ₁`).
    2. The observed Gardam crystal monodromy loops `g_x1 = (1 2)` and `g_x2 = (0 2 1 3)` are
       non-commuting (`g_x1 ∘ g_x2 ≠ g_x2 ∘ g_x1`), have exact orders `2` and `4`, and
       **generate the ENTIRE non-Abelian symmetric group `S₄` of order `24`**! -/
theorem artin_b4_relations_and_s4_monodromy_generation :
    (Perm4.comp (Perm4.comp Perm4.s1 Perm4.s2) Perm4.s1 =
      Perm4.comp (Perm4.comp Perm4.s2 Perm4.s1) Perm4.s2) ∧
    (Perm4.comp (Perm4.comp Perm4.s2 Perm4.s3) Perm4.s2 =
      Perm4.comp (Perm4.comp Perm4.s3 Perm4.s2) Perm4.s3) ∧
    (Perm4.comp Perm4.s1 Perm4.s3 = Perm4.comp Perm4.s3 Perm4.s1) ∧
    (Perm4.comp Perm4.gardamLoopX1 Perm4.gardamLoopX2 ≠
      Perm4.comp Perm4.gardamLoopX2 Perm4.gardamLoopX1) ∧
    (Perm4.comp Perm4.gardamLoopX1 Perm4.gardamLoopX1 = Perm4.id) ∧
    (Perm4.comp (Perm4.comp Perm4.gardamLoopX2 Perm4.gardamLoopX2)
      (Perm4.comp Perm4.gardamLoopX2 Perm4.gardamLoopX2) = Perm4.id) ∧
    (Perm4.subgroupOrder [Perm4.gardamLoopX1, Perm4.gardamLoopX2] = 24) := by
  decide +kernel

end PromislowFracton
