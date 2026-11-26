module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

import Solution
import PalomarSolution

/-!
# Strict Axiom Allowlist Audit (`PromislowFracton` v1.0.0)

Every exported headline theorem (`T1a`–`T3c`), the Hensel geometric tower, the strengthened
infinite-family no-sign-lift theorem, the master conjunction, the concrete non-vacuity
certificate, and all 5 adversarial false-variant refutations (20 audited declarations) must
depend strictly on a subset of `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms PromislowFracton.Palomar.t1a_promislow_group_torsion_free
#print axioms PromislowFracton.Palomar.t1b_faithful_four_band_bloch_homomorphism
#print axioms PromislowFracton.Palomar.t1c_universal_v4_determinant_invariance
#print axioms PromislowFracton.Palomar.t1d_eight_sign_point_factorization
#print axioms PromislowFracton.Palomar.t1e_gardam_unit_mod4_and_hensel_tower
#print axioms PromislowFracton.Palomar.t1f_exhaustive_no_sign_lift_gardam_support
#print axioms PromislowFracton.Palomar.t1g_surjunctive_reversible_linear_ca
#print axioms PromislowFracton.Palomar.t2a_nonabelian_unit_twisted_css_commutation
#print axioms PromislowFracton.Palomar.t2b_signed_haah_64_discriminant_classification
#print axioms PromislowFracton.Palomar.t2c_universal_all_prime_no_strings
#print axioms PromislowFracton.Palomar.t2d_odd_prime_torsion_and_p23_threshold
#print axioms PromislowFracton.Palomar.t2e_nonabelian_hw_fracton_codes
#print axioms PromislowFracton.Palomar.t3a_v4_convex_ronkin_origin_minimum
#print axioms PromislowFracton.Palomar.t3b_haah_amoeba_and_ep2_jordan
#print axioms PromislowFracton.Palomar.t3c_artin_b4_and_full_s4_monodromy
#print axioms PromislowFracton.Palomar.prove_all_promislow_fracton_theorems
#print axioms PromislowFracton.hensel_geometric_identity
#print axioms PromislowFracton.strengthened_no_sign_lift_of_gardam_support
#print axioms PromislowFracton.NonVacuity.nonvac_all_hypotheses
#print axioms PromislowFracton.Adversarial.all_adversarial_refutations
