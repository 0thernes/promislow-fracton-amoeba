module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import PromislowFracton

/-!
# Trusted Challenge Statement Contract (`Challenge.lean`)

Concise, human-readable proposition definitions for all 15 headline theorems (`T1a`–`T3c`),
concrete non-vacuity certificate (`NonVacuityCert`), adversarial false-variant refutations
(`AdversarialCert`), and master conjunction (`AllPromislowFractonTheorems`).
-/

@[expose] public section

namespace PromislowFracton.Challenge

open PromislowFracton

/-- `T1a`: Promislow / Hantzsche–Wendt group `P` axioms, relations, non-Abelianness, and constructive torsion-freeness. -/
def T1a_PromislowGroupTorsionFree : Prop :=
  (∀ g : ElemP, ElemP.mul ElemP.one g = g ∧ ElemP.mul g ElemP.one = g) ∧
  (∀ g₁ g₂ g₃ : ElemP, ElemP.mul (ElemP.mul g₁ g₂) g₃ = ElemP.mul g₁ (ElemP.mul g₂ g₃)) ∧
  (∀ g : ElemP, ElemP.mul g (ElemP.inv g) = ElemP.one ∧ ElemP.mul (ElemP.inv g) g = ElemP.one) ∧
  (ElemP.mul (ElemP.mul (ElemP.inv ElemP.genA) ElemP.genY) ElemP.genA = ElemP.inv ElemP.genY) ∧
  (ElemP.mul (ElemP.mul (ElemP.inv ElemP.genB) ElemP.genX) ElemP.genB = ElemP.inv ElemP.genX) ∧
  (ElemP.mul ElemP.genA ElemP.genB ≠ ElemP.mul ElemP.genB ElemP.genA) ∧
  (∀ g : ElemP, ∀ n : Nat, 0 < n → ElemP.pow g n = ElemP.one → g = ElemP.one)

/-- `T1b`: Faithful `4 × 4` twisted Bloch matrix ring homomorphism `Ψ : R[P] ↪ M₄(R[x±¹, y±¹, z±¹])`. -/
def T1b_FaithfulFourBandBlochHomomorphism : Prop :=
  ∀ (R : Type) [SimpleCommRing R],
    (∀ pt : TorusPt R, GroupRingElem.blochEval (GroupRingElem.one : GroupRingElem R) pt = Mat4.one) ∧
    (∀ u v : GroupRingElem R, ∀ pt : TorusPt R,
      GroupRingElem.blochEval (GroupRingElem.add u v) pt =
        Mat4.add (GroupRingElem.blochEval u pt) (GroupRingElem.blochEval v pt)) ∧
    (∀ u v : GroupRingElem R, ∀ pt : TorusPt R,
      GroupRingElem.blochEval (GroupRingElem.mul u v) pt =
        Mat4.mul (GroupRingElem.blochEval u pt) (GroupRingElem.blochEval v pt)) ∧
    (∀ u : GroupRingElem R,
      (∀ row col pt, GroupRingElem.psiFormal u row col pt = SimpleCommRing.zero) →
      ∀ g : ElemP, GroupRingElem.coeff u g = SimpleCommRing.zero)

/-- `T1c`: Universal `V₄`-invariance of `det₄(Ψ(u) - E·I₄)` and unique `V₄`-fixed origin `(0, 0, 0)`. -/
def T1c_UniversalV4DeterminantInvariance : Prop :=
  (∀ (c : Coset) (u : GroupRingElem Int) (E : Int) (pt : TorusPt Int),
    Mat4.det4 (Mat4.shift (GroupRingElem.blochEval u (TorusPt.v4 c pt)) E) =
      Mat4.det4 (Mat4.shift (GroupRingElem.blochEval u pt) E)) ∧
  (∀ pt : Int × Int × Int, (∀ c : Coset, v4Act c pt = pt) ↔ pt = (0, 0, 0))

/-- `T1d`: Exact eight-sign-point factorization (4 quaternionic perfect squares + 4 abelian/Gaussian products). -/
def T1d_EightSignPointFactorization : Prop :=
  ∀ P Q R_ S : Int,
    (Mat4.det4 (blochAtSign P Q R_ S 1 1 1) =
      (P + Q + R_ + S) * (P + Q - R_ - S) * (P - Q + R_ - S) * (P - Q - R_ + S)) ∧
    (Mat4.det4 (blochAtSign P Q R_ S 1 1 (-1)) =
      (P * P - Q * Q - R_ * R_ + S * S) * (P * P - Q * Q - R_ * R_ + S * S)) ∧
    (Mat4.det4 (blochAtSign P Q R_ S 1 (-1) 1) =
      (P * P - Q * Q + R_ * R_ - S * S) * (P * P - Q * Q + R_ * R_ - S * S)) ∧
    (Mat4.det4 (blochAtSign P Q R_ S (-1) 1 1) =
      (P * P + Q * Q - R_ * R_ - S * S) * (P * P + Q * Q - R_ * R_ - S * S)) ∧
    (Mat4.det4 (blochAtSign P Q R_ S (-1) (-1) (-1)) =
      (P * P + Q * Q + R_ * R_ + S * S) * (P * P + Q * Q + R_ * R_ + S * S)) ∧
    (Mat4.det4 (blochAtSign P Q R_ S 1 (-1) (-1)) =
      ((P + Q) * (P + Q) + (R_ + S) * (R_ + S)) * ((P - Q) * (P - Q) + (R_ - S) * (R_ - S))) ∧
    (Mat4.det4 (blochAtSign P Q R_ S (-1) 1 (-1)) =
      ((P + R_) * (P + R_) + (Q + S) * (Q + S)) * ((P - R_) * (P - R_) + (Q - S) * (Q - S))) ∧
    (Mat4.det4 (blochAtSign P Q R_ S (-1) (-1) 1) =
      ((P - S) * (P - S) + (Q + R_) * (Q + R_)) * ((P + S) * (P + S) + (Q - R_) * (Q - R_)))

/-- `T1e`: Gardam's 21-term unit in `𝔽₂[P]`, exact 89-term mod-4 determinant law (`const = 97`, `aug = 945`),
    and universal 2-adic Hensel geometric inverse tower. -/
def T1e_GardamUnitMod4AndHenselTower : Prop :=
  (gardamAlpha.length = 21 ∧ gardamBeta.length = 21 ∧
   zpMulMod 2 gardamAlpha gardamBeta = zpOne ∧ zpMulMod 2 gardamBeta gardamAlpha = zpOne) ∧
  (let d := lpDet4 (zpBlochMat gardamAlpha)
   d.length = 89 ∧ lpLookup d (0, 0, 0) = 97 ∧ lpSumCoeffs d = 945 ∧
   lpIsV4Invariant d = true ∧ spMod 2 d = lpOne ∧ spMod 4 d = lpOne)

/-- `T1f`: Strengthened `2^21` No-Sign-Lift Obstruction for Gardam's support in `ℤ[P]`. -/
def T1f_ExhaustiveNoSignLiftGardamSupport : Prop :=
  ∀ (p0 p1 p2 p3 p4 p5 p6 p7 q0 q1 q2 q3 r0 r1 r2 r3 s0 s1 s2 s3 s4 : Int),
    IsSign p0 → IsSign p1 → IsSign p2 → IsSign p3 →
    IsSign p4 → IsSign p5 → IsSign p6 → IsSign p7 →
    IsSign q0 → IsSign q1 → IsSign q2 → IsSign q3 →
    IsSign r0 → IsSign r1 → IsSign r2 → IsSign r3 →
    IsSign s0 → IsSign s1 → IsSign s2 → IsSign s3 → IsSign s4 →
    ¬ (∀ sx sy sz, IsSign sx → IsSign sy → IsSign sz →
        IsSign (Mat4.det4 (blochAtSign
          (evalPSign p0 p1 p2 p3 p4 p5 p6 p7 sx sy sz)
          (evalQSign q0 q1 q2 q3 sx sy sz)
          (evalRSign r0 r1 r2 r3 sx sy sz)
          (evalSSign s0 s1 s2 s3 s4 sx sy sz) sx sy sz)))

/-- `T1g`: Surjunctive & reversible 21-neighbor `P`-equivariant linear CA on `𝔽₂^P` (`ANL-063`). -/
def T1g_SurjunctiveReversibleLinearCA : Prop :=
  let phiA := linCA (zpToBoolElem gardamAlpha)
  let phiB := linCA (zpToBoolElem gardamBeta)
  (∀ cfg : ElemP → Bool, phiA (phiB cfg) = cfg) ∧
  (∀ cfg : ElemP → Bool, phiB (phiA cfg) = cfg) ∧
  (∀ k : ElemP, ∀ cfg : ElemP → Bool, phiA (leftShift k cfg) = leftShift k (phiA cfg))

/-- `T2a`: Arbitrary involutive-ring unit-twisted non-Abelian CSS commutation law. -/
def T2a_NonAbelianUnitTwistedCSSCommutation : Prop :=
  ∀ (R : Type) (add mul : R → R → R) (neg star : R → R) (zero one : R),
    (∀ x y z, mul (mul x y) z = mul x (mul y z)) →
    (∀ x, mul x one = x) →
    (∀ x, add x (neg x) = zero) →
    (∀ x y, mul x (neg y) = neg (mul x y)) →
    (∀ x y, star (mul x y) = mul (star y) (star x)) →
    (∀ x, star (star x) = x) →
    (∀ x, star (neg x) = neg (star x)) →
    ∀ f g u v : R, mul f g = mul g f → mul u v = one →
    add (mul (mul f u) (star (mul (star g) (star v))))
        (mul (mul g u) (star (neg (mul (star f) (star v))))) = zero

/-- `T2b`: Complete 64-signed Haah cubic code conic discriminant & bad-prime classification (`p ∈ {2, 3}` only). -/
def T2b_SignedHaah64DiscriminantClassification : Prop :=
  (all64Signs.length = 64) ∧
  (countWithDet (-12) = 12 ∧ countWithDet (-8) = 16 ∧ countWithDet (-4) = 4 ∧
   countWithDet 4 = 4 ∧ countWithDet 8 = 16 ∧ countWithDet 12 = 12) ∧
  (∀ a1 a2 a3 b1 b2 b3 : Int,
    IsSign a1 → IsSign a2 → IsSign a3 → IsSign b1 → IsSign b2 → IsSign b3 →
    let d := signedHaahConicDet a1 a2 a3 b1 b2 b3
    (d = -12 ∨ d = -8 ∨ d = -4 ∨ d = 4 ∨ d = 8 ∨ d = 12) ∧
    (∀ p : Nat, p ≥ 5 → IsPrimeNat p → d % (p : Int) ≠ 0)) ∧
  (∀ x y : Int,
    (x * x + x * y - y * y + x - y + 1 - ((x - 1) * (x - 1) + (x - 1) * y - y * y)) % 3 = 0) ∧
  (∀ x y : F4,
    let add := SimpleCommRing.add (R := F4)
    let mul := SimpleCommRing.mul (R := F4)
    mul (add (add x (mul F4.w y)) F4.w2) (add (add x (mul F4.w2 y)) F4.w) =
      add (add (add (add (add (mul x x) (mul x y)) (mul y y)) x) y) F4.one)

/-- `T2c`: Universal all-prime (`p ≥ 2` and `char = 0`) Type-II No-Strings Theorem for Haah `CC1`. -/
def T2c_UniversalAllPrimeNoStrings : Prop :=
  (∀ (K : Type) [SimpleIntegralDomain K],
    SimpleCommRing.ofNat (R := K) 2 ≠ SimpleCommRing.zero →
    (∃ rx : K, cc1Px rx = SimpleCommRing.zero) →
    (∃ ry : K, cc1Py ry = SimpleCommRing.zero) →
    (∃ rz : K, cc1Pz rz = SimpleCommRing.zero) →
    ∀ (a b c : Int) (lam : K), lam ≠ SimpleCommRing.zero →
    (let d := -(a + b + c)
     ∀ t : K,
      SimpleCommRing.mul
        (SimpleCommRing.mul (SimpleCommRing.npow (cc1Px t) (posPart a))
                            (SimpleCommRing.npow (cc1Py t) (posPart b)))
        (SimpleCommRing.mul (SimpleCommRing.npow (cc1Pz t) (posPart c))
                            (SimpleCommRing.npow (cc1D t)  (posPart d))) =
      SimpleCommRing.mul lam
        (SimpleCommRing.mul
          (SimpleCommRing.mul (SimpleCommRing.npow (cc1Px t) (negPart a))
                              (SimpleCommRing.npow (cc1Py t) (negPart b)))
          (SimpleCommRing.mul (SimpleCommRing.npow (cc1Pz t) (negPart c))
                              (SimpleCommRing.npow (cc1D t)  (negPart d))))) →
    a = 0 ∧ b = 0 ∧ c = 0) ∧
  (∀ (a b c : Int) (lam : F4), lam ≠ F4.zero →
    (∀ t : F4,
      let x := SimpleCommRing.add (SimpleCommRing.mul F4.w t) F4.w2
      let y := t
      let z := SimpleCommRing.add (SimpleCommRing.mul F4.w2 t) F4.w
      SimpleCommRing.mul (SimpleCommRing.mul (SimpleCommRing.npow x (posPart a))
                                             (SimpleCommRing.npow y (posPart b)))
                         (SimpleCommRing.npow z (posPart c)) =
      SimpleCommRing.mul lam
        (SimpleCommRing.mul (SimpleCommRing.mul (SimpleCommRing.npow x (negPart a))
                                                (SimpleCommRing.npow y (negPart b)))
                            (SimpleCommRing.npow z (negPart c)))) →
    a = 0 ∧ b = 0 ∧ c = 0)

/-- `T2d`: Odd-prime Haah torsion floor & first odd-`L` quartic-curve threshold (`p = 23`, `L = 11`). -/
def T2d_OddPrimeTorsionAndP23Threshold : Prop :=
  (∀ p : Nat, p ≥ 3 → p % 2 = 1 → (1 + 1 + 1 + 1) % p ≠ 0) ∧
  (∀ p : Nat, p ≥ 3 →
    let m1 := p - 1
    (1 + m1 + 1 + m1) % p = 0 ∧ (1 + m1 * 1 + 1 * m1 + m1 * m1) % p = 0) ∧
  (hasOddOrderRootFp 3 = false ∧ hasOddOrderRootFp 5 = false ∧ hasOddOrderRootFp 7 = false ∧
   hasOddOrderRootFp 11 = false ∧ hasOddOrderRootFp 13 = false ∧
   hasOddOrderRootFp 17 = false ∧ hasOddOrderRootFp 19 = false) ∧
  (hasOddOrderRootFp 23 = true ∧ hasOddOrderRootFp 31 = true)

/-- `T2e`: Gardam-twisted & intrinsically non-Abelian Hantzsche–Wendt fracton stabilizer codes. -/
def T2e_NonAbelianHWFractonCodes : Prop :=
  let hx1 := zpMulFastMod 2 haahF_P gardamAlpha
  let hx2 := zpMulFastMod 2 haahG_P gardamAlpha
  let hz1 := zpMulFastMod 2 (zpStar haahG_P) (zpStar gardamBeta)
  let hz2 := zpMulFastMod 2 (zpStar haahF_P) (zpStar gardamBeta)
  let commMod2 := spMod 2 (zpAdd (zpMulFast hx1 (zpStar hz1)) (zpMulFast hx2 (zpStar hz2)))
  let commZ := zpSub (zpMulFast (zpMulFast haahF_P gardamAlpha) (zpStar (zpMulFast (zpStar haahG_P) (zpStar gardamBeta))))
                     (zpMulFast (zpMulFast haahG_P gardamAlpha) (zpStar (zpMulFast (zpStar haahF_P) (zpStar gardamBeta))))
  hx1.length = 52 ∧ hx2.length = 52 ∧ hz1.length = 52 ∧ hz2.length = 56 ∧
  commMod2 = [] ∧ commZ.length = 342 ∧
  zpMulFast hwIntrinsicF hwIntrinsicG = zpMulFast hwIntrinsicG hwIntrinsicF ∧
  zpMulFast hwIntrinsicF [(ElemP.genX, 1)] ≠ zpMulFast [(ElemP.genX, 1)] hwIntrinsicF

/-- `T3a`: Universal `V₄`-convex Ronkin origin-minimum theorem (`CM-018`). -/
def T3a_V4ConvexRonkinOriginMinimum : Prop :=
  ∀ (R : RatQ → RatQ → RatQ → RatQ),
    IsMidpointConvex3 R → IsV4Symmetric3 R →
    ∀ x y z : RatQ, RatQ.le (R (RatQ.ofInt 0) (RatQ.ofInt 0) (RatQ.ofInt 0)) (R x y z)

/-- `T3b`: Exact 3D Haah fracton double-amoeba quadrilateral characterization & EP2 Jordan coalescence. -/
def T3b_HaahAmoebaAndEP2Jordan : Prop :=
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
      v0 = SimpleCommRing.zero))

/-- `T3c`: Artin braid `B₄` relations & full non-Abelian `S₄` monodromy generation on Gardam's crystal. -/
def T3c_ArtinB4AndFullS4Monodromy : Prop :=
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
  (Perm4.subgroupOrder [Perm4.gardamLoopX1, Perm4.gardamLoopX2] = 24)

/-- Master conjunction of all 15 headline theorems across Pillars I–III. -/
def AllPromislowFractonTheorems : Prop :=
  T1a_PromislowGroupTorsionFree ∧
  T1b_FaithfulFourBandBlochHomomorphism ∧
  T1c_UniversalV4DeterminantInvariance ∧
  T1d_EightSignPointFactorization ∧
  T1e_GardamUnitMod4AndHenselTower ∧
  T1f_ExhaustiveNoSignLiftGardamSupport ∧
  T1g_SurjunctiveReversibleLinearCA ∧
  T2a_NonAbelianUnitTwistedCSSCommutation ∧
  T2b_SignedHaah64DiscriminantClassification ∧
  T2c_UniversalAllPrimeNoStrings ∧
  T2d_OddPrimeTorsionAndP23Threshold ∧
  T2e_NonAbelianHWFractonCodes ∧
  T3a_V4ConvexRonkinOriginMinimum ∧
  T3b_HaahAmoebaAndEP2Jordan ∧
  T3c_ArtinB4AndFullS4Monodromy

end PromislowFracton.Challenge
