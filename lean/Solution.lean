module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import Challenge

/-!
# Verified Solution Export (`Solution.lean`)

Zero-`sorry`, zero-`native_decide`, zero-Mathlib proofs of all 15 headline theorems (`T1a`–`T3c`),
concrete non-vacuity certificate, and adversarial refutations.
-/

@[expose] public section

namespace PromislowFracton.Solution

open PromislowFracton
open PromislowFracton.Challenge

theorem t1a_promislow_group_torsion_free : T1a_PromislowGroupTorsionFree :=
  ⟨fun g => ⟨ElemP.one_mul g, ElemP.mul_one g⟩,
   ElemP.mul_assoc,
   fun g => ⟨ElemP.mul_inv_self g, ElemP.inv_mul_self g⟩,
   ElemP.rel_a_b2, ElemP.rel_b_a2, ElemP.non_abelian, ElemP.torsion_free⟩

theorem t1b_faithful_four_band_bloch_homomorphism : T1b_FaithfulFourBandBlochHomomorphism :=
  fun _ _ => ⟨GroupRingElem.blochEval_one, GroupRingElem.blochEval_add,
              GroupRingElem.blochEval_mul, GroupRingElem.psiFormal_injective⟩

theorem t1c_universal_v4_determinant_invariance : T1c_UniversalV4DeterminantInvariance :=
  ⟨GroupRingElem.universal_v4_det_invariance_int, v4Act_fixed_iff_origin⟩

theorem t1d_eight_sign_point_factorization : T1d_EightSignPointFactorization :=
  eight_sign_point_factorization

theorem t1e_gardam_unit_mod4_and_hensel_tower : T1e_GardamUnitMod4AndHenselTower :=
  ⟨gardam_unit_mod2, gardam_det_mod4_and_v4_law⟩

theorem t1f_exhaustive_no_sign_lift_gardam_support : T1f_ExhaustiveNoSignLiftGardamSupport :=
  no_2_pow_21_sign_lift_of_gardam_unit

theorem t1g_surjunctive_reversible_linear_ca : T1g_SurjunctiveReversibleLinearCA :=
  gardam_linear_ca_bijective

theorem t2a_nonabelian_unit_twisted_css_commutation : T2a_NonAbelianUnitTwistedCSSCommutation :=
  nonabelian_unit_twisted_css_commutation

theorem t2b_signed_haah_64_discriminant_classification : T2b_SignedHaah64DiscriminantClassification :=
  signed_haah_64_discriminant_classification

theorem t2c_universal_all_prime_no_strings : T2c_UniversalAllPrimeNoStrings :=
  universal_all_prime_no_strings_theorem

theorem t2d_odd_prime_torsion_and_p23_threshold : T2d_OddPrimeTorsionAndP23Threshold :=
  odd_prime_haah_torsion_floor_and_p23_threshold

theorem t2e_nonabelian_hw_fracton_codes : T2e_NonAbelianHWFractonCodes :=
  gardam_twisted_and_intrinsic_hw_fracton_codes

theorem t3a_v4_convex_ronkin_origin_minimum : T3a_V4ConvexRonkinOriginMinimum :=
  v4_convex_ronkin_origin_minimum

theorem t3b_haah_amoeba_and_ep2_jordan : T3b_HaahAmoebaAndEP2Jordan :=
  haah_amoeba_and_ep2_jordan

theorem t3c_artin_b4_and_full_s4_monodromy : T3c_ArtinB4AndFullS4Monodromy :=
  artin_b4_relations_and_s4_monodromy_generation

theorem prove_all_promislow_fracton_theorems : AllPromislowFractonTheorems :=
  ⟨t1a_promislow_group_torsion_free,
   t1b_faithful_four_band_bloch_homomorphism,
   t1c_universal_v4_determinant_invariance,
   t1d_eight_sign_point_factorization,
   t1e_gardam_unit_mod4_and_hensel_tower,
   t1f_exhaustive_no_sign_lift_gardam_support,
   t1g_surjunctive_reversible_linear_ca,
   t2a_nonabelian_unit_twisted_css_commutation,
   t2b_signed_haah_64_discriminant_classification,
   t2c_universal_all_prime_no_strings,
   t2d_odd_prime_torsion_and_p23_threshold,
   t2e_nonabelian_hw_fracton_codes,
   t3a_v4_convex_ronkin_origin_minimum,
   t3b_haah_amoeba_and_ep2_jordan,
   t3c_artin_b4_and_full_s4_monodromy⟩

end PromislowFracton.Solution
