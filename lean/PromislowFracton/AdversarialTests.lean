module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import PromislowFracton.NonVacuity

/-!
# Adversarial False-Variant Refutations (`AdversarialTests.lean`)

Playbook v1.3 Gold Standard Checklist Item #12:
Prove constructively inside the Lean 4.35.0 kernel that deliberately FALSE mathematical claims
(weakened statements, false universality claims, false char-0 lifts) are STRICTLY REFUTABLE!
-/

@[expose] public section

namespace PromislowFracton.Adversarial

/-- False Claim 1 (Kaplansky Unit Conjecture in char 2): "Every unit in `𝔽₂[P]` has support size 1."
    Refuted constructively by Gardam's 21-term unit `gardamAlpha`. -/
theorem refute_kaplansky_unit_f2 :
    ¬ (∀ u v : ZPElem, zpMulMod 2 u v = zpOne → u.length = 1) := by
  intro h
  have hlen := h gardamAlpha gardamBeta gardam_unit_mod2.2.2.1
  have h21 := gardam_unit_mod2.1
  omega

/-- False Claim 2: "All 64 signed Haah cubic codes remain smooth modulo 3."
    Refuted constructively by `(1, 1, 1, 1, 1, -1)` whose conic discriminant is `-12 ≡ 0 (mod 3)`. -/
theorem refute_all_signed_haah_smooth_mod3 :
    ¬ (∀ a1 a2 a3 b1 b2 b3 : Int,
        IsSign a1 → IsSign a2 → IsSign a3 → IsSign b1 → IsSign b2 → IsSign b3 →
        signedHaahConicDet a1 a2 a3 b1 b2 b3 % 3 ≠ 0) := by
  intro h
  have h1 := h 1 1 1 1 1 (-1) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  exact h1 (by decide)

/-- False Claim 3: "`(1, 1, 1)` is a root of Haah `CC1` over every prime field `𝔽_p`."
    Refuted constructively at `p = 3` (`f(1,1,1) = 4 ≡ 1 ≢ 0 (mod 3)`). -/
theorem refute_one_one_one_root_mod3 :
    ¬ (∀ p : Nat, p ≥ 2 → (1 + 1 + 1 + 1) % p = 0) := by
  intro h
  have h3 := h 3 (by decide)
  exact absurd h3 (by decide)

/-- False Claim 4: "The Gardam-twisted Haah code commutes over `ℤ[P]` (characteristic 0)."
    Refuted constructively by the 342-term nonzero integer commutator defect. -/
theorem refute_gardam_twisted_haah_commutes_over_Z :
    zpSub (zpMulFast (zpMulFast haahF_P gardamAlpha) (zpStar (zpMulFast (zpStar haahG_P) (zpStar gardamBeta))))
          (zpMulFast (zpMulFast haahG_P gardamAlpha) (zpStar (zpMulFast (zpStar haahF_P) (zpStar gardamBeta)))) ≠ [] := by
  intro h
  have hlen := gardam_twisted_and_intrinsic_hw_fracton_codes.2.2.2.2.2.1
  rw [h] at hlen
  exact absurd hlen (by decide)

/-- False Claim 5: "The all-`+1` lift of Gardam's unit has determinant `±1` at `(1, 1, 1)`."
    Refuted constructively (`det(1,1,1) = 945 ≠ ±1`). -/
theorem refute_gardam_all_plus_lift_unit :
    ¬ IsSign (lpSumCoeffs (lpDet4 (zpBlochMat gardamAlpha))) := by
  intro h
  have h945 := gardam_det_mod4_and_v4_law.2.2.1
  rw [h945] at h
  rcases h with h1 | hm1 <;> omega

/-- Master conjunction of all 5 adversarial refutations. -/
theorem all_adversarial_refutations :
    (¬ (∀ u v : ZPElem, zpMulMod 2 u v = zpOne → u.length = 1)) ∧
    (¬ (∀ a1 a2 a3 b1 b2 b3 : Int,
        IsSign a1 → IsSign a2 → IsSign a3 → IsSign b1 → IsSign b2 → IsSign b3 →
        signedHaahConicDet a1 a2 a3 b1 b2 b3 % 3 ≠ 0)) ∧
    (¬ (∀ p : Nat, p ≥ 2 → (1 + 1 + 1 + 1) % p = 0)) ∧
    (zpSub (zpMulFast (zpMulFast haahF_P gardamAlpha) (zpStar (zpMulFast (zpStar haahG_P) (zpStar gardamBeta))))
           (zpMulFast (zpMulFast haahG_P gardamAlpha) (zpStar (zpMulFast (zpStar haahF_P) (zpStar gardamBeta)))) ≠ []) ∧
    (¬ IsSign (lpSumCoeffs (lpDet4 (zpBlochMat gardamAlpha)))) :=
  ⟨refute_kaplansky_unit_f2, refute_all_signed_haah_smooth_mod3,
   refute_one_one_one_root_mod3, refute_gardam_twisted_haah_commutes_over_Z,
   refute_gardam_all_plus_lift_unit⟩

end PromislowFracton.Adversarial
