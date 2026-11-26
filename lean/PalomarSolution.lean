module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import Challenge
public import Solution

/-!
# Palomar Comparator Verified Solution (`promislow-fracton-amoeba` v1.0.0)

Zero-`sorry`, zero-`native_decide`, zero-Mathlib implementation of all 15 headline theorems
(`T1a`–`T3c`) and master conjunction verified across all six independent Lean 4.35.0 kernels.
-/

namespace PromislowFracton.Palomar

open PromislowFracton.Challenge

public theorem t1a_promislow_group_torsion_free : T1a_PromislowGroupTorsionFree :=
  PromislowFracton.Solution.t1a_promislow_group_torsion_free
public theorem t1b_faithful_four_band_bloch_homomorphism : T1b_FaithfulFourBandBlochHomomorphism :=
  PromislowFracton.Solution.t1b_faithful_four_band_bloch_homomorphism
public theorem t1c_universal_v4_determinant_invariance : T1c_UniversalV4DeterminantInvariance :=
  PromislowFracton.Solution.t1c_universal_v4_determinant_invariance
public theorem t1d_eight_sign_point_factorization : T1d_EightSignPointFactorization :=
  PromislowFracton.Solution.t1d_eight_sign_point_factorization
public theorem t1e_gardam_unit_mod4_and_hensel_tower : T1e_GardamUnitMod4AndHenselTower :=
  PromislowFracton.Solution.t1e_gardam_unit_mod4_and_hensel_tower
public theorem t1f_exhaustive_no_sign_lift_gardam_support : T1f_ExhaustiveNoSignLiftGardamSupport :=
  PromislowFracton.Solution.t1f_exhaustive_no_sign_lift_gardam_support
public theorem t1g_surjunctive_reversible_linear_ca : T1g_SurjunctiveReversibleLinearCA :=
  PromislowFracton.Solution.t1g_surjunctive_reversible_linear_ca
public theorem t2a_nonabelian_unit_twisted_css_commutation : T2a_NonAbelianUnitTwistedCSSCommutation :=
  PromislowFracton.Solution.t2a_nonabelian_unit_twisted_css_commutation
public theorem t2b_signed_haah_64_discriminant_classification : T2b_SignedHaah64DiscriminantClassification :=
  PromislowFracton.Solution.t2b_signed_haah_64_discriminant_classification
public theorem t2c_universal_all_prime_no_strings : T2c_UniversalAllPrimeNoStrings :=
  PromislowFracton.Solution.t2c_universal_all_prime_no_strings
public theorem t2d_odd_prime_torsion_and_p23_threshold : T2d_OddPrimeTorsionAndP23Threshold :=
  PromislowFracton.Solution.t2d_odd_prime_torsion_and_p23_threshold
public theorem t2e_nonabelian_hw_fracton_codes : T2e_NonAbelianHWFractonCodes :=
  PromislowFracton.Solution.t2e_nonabelian_hw_fracton_codes
public theorem t3a_v4_convex_ronkin_origin_minimum : T3a_V4ConvexRonkinOriginMinimum :=
  PromislowFracton.Solution.t3a_v4_convex_ronkin_origin_minimum
public theorem t3b_haah_amoeba_and_ep2_jordan : T3b_HaahAmoebaAndEP2Jordan :=
  PromislowFracton.Solution.t3b_haah_amoeba_and_ep2_jordan
public theorem t3c_artin_b4_and_full_s4_monodromy : T3c_ArtinB4AndFullS4Monodromy :=
  PromislowFracton.Solution.t3c_artin_b4_and_full_s4_monodromy
public theorem prove_all_promislow_fracton_theorems : AllPromislowFractonTheorems :=
  PromislowFracton.Solution.prove_all_promislow_fracton_theorems

end PromislowFracton.Palomar
