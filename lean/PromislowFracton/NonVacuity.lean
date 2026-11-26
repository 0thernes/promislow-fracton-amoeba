module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import PromislowFracton.NonHermitianAmoeba

/-!
# Concrete Non-Vacuity Witnesses (`NonVacuity.lean`)

Proves that EVERY hypothesis bundle across Theorems `T1a`–`T3c` is strictly NON-VACUOUS by
exhibiting explicit, concrete inhabitants checked directly by the Lean 4.35.0 kernel:
- `ZMod 11`: concrete `SimpleIntegralDomain` of characteristic `11 ≠ 2` in which ALL THREE
  parametrisation quadratics `cc1Px, cc1Py, cc1Pz` have explicit roots (`4`, `8`, `7`)!
- `sampleTorusPtInt`: concrete `TorusPt Int` inhabitant `(1, 1, -1, -1, 1, 1)`.
- `quadraticRonkin`: concrete midpoint-convex `V₄`-symmetric Ronkin function `x² + y² + z²` on `ℚ³`.
- Concrete EP2 Jordan-block witness `haahDirac2 0 1` over `Int` and primes `5, 23`.
-/

@[expose] public section

namespace PromislowFracton.NonVacuity

instance instSimpleCommRingZMod11 : SimpleCommRing (ZMod 11) :=
  ZMod.mkSimpleCommRing 11 (by decide)

private theorem zmod11_mul_zero_aux (av bv : Nat) (ha : av < 11) (hb : bv < 11)
    (h : (av * bv) % 11 = 0) : av = 0 ∨ bv = 0 := by
  revert h hb ha
  match av with
  | 0 => intro _ _ _; left; rfl
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 =>
    match bv with
    | 0 => intro _ _ _; right; rfl
    | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => intro _ _ h; exact absurd h (by decide)
    | _ + 11 => intro _ hb _; omega
  | _ + 11 => intro ha _ _; omega

instance instSimpleIntegralDomainZMod11 : SimpleIntegralDomain (ZMod 11) where
  one_ne_zero := by decide
  mul_eq_zero := by
    intro a b h
    cases a with | mk av alt =>
    cases b with | mk bv blt =>
    have hmul : (av * bv) % 11 = 0 := congrArg ZMod.val h
    rcases zmod11_mul_zero_aux av bv alt blt hmul with rfl | rfl
    · left; apply ZMod.ext; rfl
    · right; apply ZMod.ext; rfl

/-- Witness 1: Concrete `TorusPt Int` inhabitant for Theorems `T1b` and `T1c`. -/
def sampleTorusPtInt : TorusPt Int :=
  ⟨1, 1, -1, -1, 1, 1, rfl, rfl, rfl⟩

/-- Witness 2: Concrete midpoint-convex `V₄`-symmetric Ronkin function `R(x, y, z) = x² + y² + z²` on `ℚ³`. -/
def quadraticRonkin (x y z : RatQ) : RatQ :=
  RatQ.add (RatQ.add (RatQ.mul x x) (RatQ.mul y y)) (RatQ.mul z z)

/-- Exact 1D rational midpoint convexity of `u ↦ u²`: `((a+b)/2)² ≤ (a² + b²)/2`
    (equivalent to `(a - b)² ≥ 0` after clearing positive denominators). -/
private theorem ratq_sq_midpoint_le (a b : RatQ) :
    RatQ.le
      (RatQ.mul (RatQ.mul RatQ.half (RatQ.add a b)) (RatQ.mul RatQ.half (RatQ.add a b)))
      (RatQ.mul RatQ.half (RatQ.add (RatQ.mul a a) (RatQ.mul b b))) := by
  unfold RatQ.le RatQ.mul RatQ.add RatQ.half
  simp only [Int.natCast_mul]
  change (1 * (a.num * (b.den : Int) + b.num * (a.den : Int))) *
           (1 * (a.num * (b.den : Int) + b.num * (a.den : Int))) *
           (2 * ((a.den : Int) * (a.den : Int) * ((b.den : Int) * (b.den : Int)))) ≤
         1 * (a.num * a.num * ((b.den : Int) * (b.den : Int)) + b.num * b.num * ((a.den : Int) * (a.den : Int))) *
           (2 * ((a.den : Int) * (b.den : Int)) * (2 * ((a.den : Int) * (b.den : Int))))
  have hsq : 0 ≤ (a.num * (b.den : Int) - b.num * (a.den : Int)) *
                 (a.num * (b.den : Int) - b.num * (a.den : Int)) := int_sq_nonneg _
  have hden : (0 : Int) ≤ (a.den : Int) * (a.den : Int) * ((b.den : Int) * (b.den : Int)) :=
    Int.mul_nonneg (int_sq_nonneg _) (int_sq_nonneg _)
  have hdiff :
      (a.num * a.num * ((b.den : Int) * (b.den : Int)) + b.num * b.num * ((a.den : Int) * (a.den : Int))) *
        (2 * ((a.den : Int) * (b.den : Int)) * (2 * ((a.den : Int) * (b.den : Int)))) -
      (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.num * (b.den : Int) + b.num * (a.den : Int)) *
        (2 * ((a.den : Int) * (a.den : Int) * ((b.den : Int) * (b.den : Int)))) =
      2 * ((a.num * (b.den : Int) - b.num * (a.den : Int)) *
           (a.num * (b.den : Int) - b.num * (a.den : Int))) *
          ((a.den : Int) * (a.den : Int) * ((b.den : Int) * (b.den : Int))) := by
    grind
  have hprod_nn : 0 ≤ 2 * ((a.num * (b.den : Int) - b.num * (a.den : Int)) *
      (a.num * (b.den : Int) - b.num * (a.den : Int))) *
      ((a.den : Int) * (a.den : Int) * ((b.den : Int) * (b.den : Int))) :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) hsq) hden
  have h1 : (1 * (a.num * (b.den : Int) + b.num * (a.den : Int))) *
        (1 * (a.num * (b.den : Int) + b.num * (a.den : Int))) *
        (2 * ((a.den : Int) * (a.den : Int) * ((b.den : Int) * (b.den : Int)))) =
      (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.num * (b.den : Int) + b.num * (a.den : Int)) *
        (2 * ((a.den : Int) * (a.den : Int) * ((b.den : Int) * (b.den : Int)))) := by grind
  have h2 : 1 * (a.num * a.num * ((b.den : Int) * (b.den : Int)) + b.num * b.num * ((a.den : Int) * (a.den : Int))) *
        (2 * ((a.den : Int) * (b.den : Int)) * (2 * ((a.den : Int) * (b.den : Int)))) =
      (a.num * a.num * ((b.den : Int) * (b.den : Int)) + b.num * b.num * ((a.den : Int) * (a.den : Int))) *
        (2 * ((a.den : Int) * (b.den : Int)) * (2 * ((a.den : Int) * (b.den : Int)))) := by grind
  omega

/-- Half distributes over addition on `RatQ` up to `RatQ.eqv`. -/
private theorem ratq_half_add_distrib (u v : RatQ) :
    RatQ.eqv (RatQ.add (RatQ.mul RatQ.half u) (RatQ.mul RatQ.half v))
             (RatQ.mul RatQ.half (RatQ.add u v)) := by
  unfold RatQ.eqv RatQ.add RatQ.mul RatQ.half
  simp only [Int.natCast_mul]; grind

/-- Addition of 3 pairs rearranges `(a1+a2)+(b1+b2) ≈ (a1+b1)+(a2+b2)`. -/
private theorem ratq_add_swap (a1 a2 b1 b2 : RatQ) :
    RatQ.eqv (RatQ.add (RatQ.add a1 a2) (RatQ.add b1 b2))
             (RatQ.add (RatQ.add a1 b1) (RatQ.add a2 b2)) := by
  unfold RatQ.eqv RatQ.add
  simp only [Int.natCast_mul]; grind

private theorem ratq_mul_eqv_right {k a b : RatQ} (h : RatQ.eqv a b) :
    RatQ.eqv (RatQ.mul k a) (RatQ.mul k b) := by
  unfold RatQ.eqv RatQ.mul at *
  simp only [Int.natCast_mul]
  have h1 : k.num * a.num * ((k.den : Int) * (b.den : Int)) = (k.num * (k.den : Int)) * (a.num * (b.den : Int)) := by grind
  have h2 : k.num * b.num * ((k.den : Int) * (a.den : Int)) = (k.num * (k.den : Int)) * (b.num * (a.den : Int)) := by grind
  rw [h1, h2, h]

private theorem ratq_add_eqv {a1 a2 b1 b2 : RatQ} (ha : RatQ.eqv a1 a2) (hb : RatQ.eqv b1 b2) :
    RatQ.eqv (RatQ.add a1 b1) (RatQ.add a2 b2) := by
  unfold RatQ.eqv RatQ.add at *
  simp only [Int.natCast_mul]
  have h1 : (a1.num * (b1.den : Int) + b1.num * (a1.den : Int)) * ((a2.den : Int) * (b2.den : Int)) =
      (a1.num * (a2.den : Int)) * ((b1.den : Int) * (b2.den : Int)) +
      (b1.num * (b2.den : Int)) * ((a1.den : Int) * (a2.den : Int)) := by grind
  have h2 : (a2.num * (b2.den : Int) + b2.num * (a2.den : Int)) * ((a1.den : Int) * (b1.den : Int)) =
      (a2.num * (a1.den : Int)) * ((b1.den : Int) * (b2.den : Int)) +
      (b2.num * (b1.den : Int)) * ((a1.den : Int) * (a2.den : Int)) := by grind
  rw [h1, h2, ha, hb]

private theorem ratq_sq_eqv {a b : RatQ} (h : RatQ.eqv a b) :
    RatQ.eqv (RatQ.mul a a) (RatQ.mul b b) := by
  unfold RatQ.eqv RatQ.mul at *
  simp only [Int.natCast_mul]
  have h1 : a.num * a.num * ((b.den : Int) * (b.den : Int)) = (a.num * (b.den : Int)) * (a.num * (b.den : Int)) := by grind
  have h2 : b.num * b.num * ((a.den : Int) * (a.den : Int)) = (b.num * (a.den : Int)) * (b.num * (a.den : Int)) := by grind
  rw [h1, h2, h]

private theorem ratq_eqv_trans {a b c : RatQ} (hab : RatQ.eqv a b) (hbc : RatQ.eqv b c) :
    RatQ.eqv a c := by
  unfold RatQ.eqv at *
  have hpos : (b.den : Int) ≠ 0 := by have := b.den_pos; omega
  apply Int.eq_of_mul_eq_mul_right hpos
  have hm1 := congrArg (fun t => t * (c.den : Int)) hab
  have hm2 := congrArg (fun t => t * (a.den : Int)) hbc
  grind

theorem quadraticRonkin_is_convex : IsMidpointConvex3 quadraticRonkin := by
  intro x1 y1 z1 x2 y2 z2
  unfold quadraticRonkin
  have hx := ratq_sq_midpoint_le x1 x2
  have hy := ratq_sq_midpoint_le y1 y2
  have hz := ratq_sq_midpoint_le z1 z2
  have hxy := RatQ.add_le_add hx hy
  have hxyz := RatQ.add_le_add hxy hz
  -- Combine the 3 half-sums into `½((x1²+y1²+z1²) + (x2²+y2²+z2²))`
  have hr1 : RatQ.eqv
      (RatQ.add (RatQ.mul RatQ.half (RatQ.add (RatQ.mul x1 x1) (RatQ.mul x2 x2)))
                (RatQ.mul RatQ.half (RatQ.add (RatQ.mul y1 y1) (RatQ.mul y2 y2))))
      (RatQ.mul RatQ.half (RatQ.add (RatQ.add (RatQ.mul x1 x1) (RatQ.mul x2 x2))
                                    (RatQ.add (RatQ.mul y1 y1) (RatQ.mul y2 y2)))) :=
    ratq_half_add_distrib _ _
  have hr2 : RatQ.eqv
      (RatQ.add (RatQ.add (RatQ.mul RatQ.half (RatQ.add (RatQ.mul x1 x1) (RatQ.mul x2 x2)))
                          (RatQ.mul RatQ.half (RatQ.add (RatQ.mul y1 y1) (RatQ.mul y2 y2))))
                (RatQ.mul RatQ.half (RatQ.add (RatQ.mul z1 z1) (RatQ.mul z2 z2))))
      (RatQ.add (RatQ.mul RatQ.half (RatQ.add (RatQ.add (RatQ.mul x1 x1) (RatQ.mul x2 x2))
                                              (RatQ.add (RatQ.mul y1 y1) (RatQ.mul y2 y2))))
                (RatQ.mul RatQ.half (RatQ.add (RatQ.mul z1 z1) (RatQ.mul z2 z2)))) :=
    ratq_add_eqv hr1 rfl
  have hr3 : RatQ.eqv
      (RatQ.add (RatQ.mul RatQ.half (RatQ.add (RatQ.add (RatQ.mul x1 x1) (RatQ.mul x2 x2))
                                              (RatQ.add (RatQ.mul y1 y1) (RatQ.mul y2 y2))))
                (RatQ.mul RatQ.half (RatQ.add (RatQ.mul z1 z1) (RatQ.mul z2 z2))))
      (RatQ.mul RatQ.half (RatQ.add (RatQ.add (RatQ.add (RatQ.mul x1 x1) (RatQ.mul x2 x2))
                                              (RatQ.add (RatQ.mul y1 y1) (RatQ.mul y2 y2)))
                                    (RatQ.add (RatQ.mul z1 z1) (RatQ.mul z2 z2)))) :=
    ratq_half_add_distrib _ _
  have hr4 : RatQ.eqv
      (RatQ.add (RatQ.add (RatQ.add (RatQ.mul x1 x1) (RatQ.mul x2 x2))
                          (RatQ.add (RatQ.mul y1 y1) (RatQ.mul y2 y2)))
                (RatQ.add (RatQ.mul z1 z1) (RatQ.mul z2 z2)))
      (RatQ.add (RatQ.add (RatQ.add (RatQ.mul x1 x1) (RatQ.mul y1 y1)) (RatQ.mul z1 z1))
                (RatQ.add (RatQ.add (RatQ.mul x2 x2) (RatQ.mul y2 y2)) (RatQ.mul z2 z2))) := by
    have hswap1 := ratq_add_eqv (ratq_add_swap (RatQ.mul x1 x1) (RatQ.mul x2 x2) (RatQ.mul y1 y1) (RatQ.mul y2 y2))
      (rfl : RatQ.eqv (RatQ.add (RatQ.mul z1 z1) (RatQ.mul z2 z2)) (RatQ.add (RatQ.mul z1 z1) (RatQ.mul z2 z2)))
    have hswap2 := ratq_add_swap (RatQ.add (RatQ.mul x1 x1) (RatQ.mul y1 y1))
      (RatQ.add (RatQ.mul x2 x2) (RatQ.mul y2 y2)) (RatQ.mul z1 z1) (RatQ.mul z2 z2)
    exact ratq_eqv_trans hswap1 hswap2
  exact RatQ.le_trans hxyz
    (RatQ.le_trans (RatQ.le_of_eqv hr2)
      (RatQ.le_trans (RatQ.le_of_eqv hr3) (RatQ.le_of_eqv (ratq_mul_eqv_right hr4))))

theorem quadraticRonkin_is_v4_sym : IsV4Symmetric3 quadraticRonkin := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x1 y1 z1 x2 y2 z2 hx hy hz
    unfold quadraticRonkin
    exact ratq_add_eqv (ratq_add_eqv (ratq_sq_eqv hx) (ratq_sq_eqv hy)) (ratq_sq_eqv hz)
  · intro x y z; unfold quadraticRonkin RatQ.eqv RatQ.add RatQ.mul RatQ.neg; simp only [Int.natCast_mul]; grind
  · intro x y z; unfold quadraticRonkin RatQ.eqv RatQ.add RatQ.mul RatQ.neg; simp only [Int.natCast_mul]; grind
  · intro x y z; unfold quadraticRonkin RatQ.eqv RatQ.add RatQ.mul RatQ.neg; simp only [Int.natCast_mul]; grind

/-- Witness 3: Concrete roots of `cc1Px, cc1Py, cc1Pz` in `ZMod 11` (`2`, `4`, `3`). -/
theorem zmod11_cc1_roots_nonvac :
    SimpleCommRing.ofNat (R := ZMod 11) 2 ≠ SimpleCommRing.zero ∧
    (∃ rx : ZMod 11, cc1Px rx = SimpleCommRing.zero) ∧
    (∃ ry : ZMod 11, cc1Py ry = SimpleCommRing.zero) ∧
    (∃ rz : ZMod 11, cc1Pz rz = SimpleCommRing.zero) := by
  refine ⟨by decide, ⟨⟨2, by decide⟩, by decide⟩, ⟨⟨4, by decide⟩, by decide⟩, ⟨⟨3, by decide⟩, by decide⟩⟩

private theorem isPrimeNat_of_check (p : Nat) (hp : 2 ≤ p)
    (hcheck : (List.range (p + 1)).all (fun d => !(d ∣ p) || d == 1 || d == p) = true) :
    IsPrimeNat p := by
  refine ⟨hp, ?_⟩
  intro d hd
  have hle : d ≤ p := Nat.le_of_dvd (by omega) hd
  have hmem : d ∈ List.range (p + 1) := List.mem_range.mpr (by omega)
  have hall := List.all_eq_true.mp hcheck d hmem
  have hdvd : decide (d ∣ p) = true := decide_eq_true hd
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_false_iff_not] at hall
  rcases hall with (hnd | h1) | hp'
  · exact absurd hd hnd
  · exact Or.inl h1
  · exact Or.inr hp'

/-- Master Non-Vacuity Certificate aggregating concrete inhabitants of every hypothesis bundle. -/
theorem nonvac_all_hypotheses :
    (ElemP.genA ≠ ElemP.one) ∧
    (sampleTorusPtInt.x * sampleTorusPtInt.xi = 1) ∧
    (SimpleCommRing.ofNat (R := ZMod 11) 2 ≠ SimpleCommRing.zero) ∧
    (∃ rx : ZMod 11, cc1Px rx = SimpleCommRing.zero) ∧
    (∃ ry : ZMod 11, cc1Py ry = SimpleCommRing.zero) ∧
    (∃ rz : ZMod 11, cc1Pz rz = SimpleCommRing.zero) ∧
    (IsMidpointConvex3 quadraticRonkin ∧ IsV4Symmetric3 quadraticRonkin) ∧
    ((1 : Int) ≠ 0 ∧ haahDirac2 (R := Int) 0 1 ≠ Mat2.zero) ∧
    (IsPrimeNat 5 ∧ IsPrimeNat 23) :=
  ⟨by decide, rfl, zmod11_cc1_roots_nonvac.1, zmod11_cc1_roots_nonvac.2.1,
   zmod11_cc1_roots_nonvac.2.2.1, zmod11_cc1_roots_nonvac.2.2.2,
   ⟨quadraticRonkin_is_convex, quadraticRonkin_is_v4_sym⟩,
   ⟨by decide, by decide⟩,
   ⟨isPrimeNat_of_check 5 (by decide) (by decide),
    isPrimeNat_of_check 23 (by decide) (by decide)⟩⟩

end PromislowFracton.NonVacuity
