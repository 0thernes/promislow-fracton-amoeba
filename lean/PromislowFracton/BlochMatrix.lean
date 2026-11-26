module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

public import PromislowFracton.PromislowGroup

/-!
# Faithful 4×4 Twisted Bloch Representation, Universal `V₄`-Determinant Invariance,
# and Exact Eight-Sign-Point Factorization (Theorems `T1b`, `T1c`, `T1d`)

Zero `sorry`, zero `native_decide`, zero Mathlib.
-/

@[expose] public section

namespace PromislowFracton

/-- An invertible point `(x, y, z) ∈ (Rˣ)³` with explicit multiplicative inverses. -/
structure TorusPt (R : Type) [SimpleCommRing R] where
  x  : R
  xi : R
  y  : R
  yi : R
  z  : R
  zi : R
  hx : SimpleCommRing.mul x xi = SimpleCommRing.one
  hy : SimpleCommRing.mul y yi = SimpleCommRing.one
  hz : SimpleCommRing.mul z zi = SimpleCommRing.one

namespace TorusPt

variable {R : Type} [SimpleCommRing R]

/-- Integer power `a^k` given `a` and its inverse `ai`. -/
def zpow (a ai : R) (k : Int) : R :=
  match k with
  | Int.ofNat n => SimpleCommRing.npow a n
  | Int.negSucc n => SimpleCommRing.npow ai (n + 1)

theorem zpow_zero (a ai : R) : zpow a ai 0 = SimpleCommRing.one := rfl

private theorem npow_mul_inv_cancel {a ai : R} (h : SimpleCommRing.mul a ai = SimpleCommRing.one)
    (n : Nat) :
    SimpleCommRing.mul (SimpleCommRing.npow a n) (SimpleCommRing.npow ai n) = SimpleCommRing.one := by
  induction n with
  | zero => simp [SimpleCommRing.npow, SimpleCommRing.one_mul]
  | succ k ih =>
    rw [SimpleCommRing.npow_succ, SimpleCommRing.npow_succ]
    calc SimpleCommRing.mul (SimpleCommRing.mul a (SimpleCommRing.npow a k))
            (SimpleCommRing.mul ai (SimpleCommRing.npow ai k))
        = SimpleCommRing.mul (SimpleCommRing.mul a ai)
            (SimpleCommRing.mul (SimpleCommRing.npow a k) (SimpleCommRing.npow ai k)) := by
          rw [SimpleCommRing.mul_assoc a, ← SimpleCommRing.mul_assoc (SimpleCommRing.npow a k),
              SimpleCommRing.mul_comm (SimpleCommRing.npow a k) ai,
              SimpleCommRing.mul_assoc ai, ← SimpleCommRing.mul_assoc a]
      _ = SimpleCommRing.mul SimpleCommRing.one SimpleCommRing.one := by rw [h, ih]
      _ = SimpleCommRing.one := SimpleCommRing.one_mul _

private theorem npow_add_neg {a ai : R} (h : SimpleCommRing.mul a ai = SimpleCommRing.one)
    (m n : Nat) :
    SimpleCommRing.mul (SimpleCommRing.npow a m) (SimpleCommRing.npow ai n) =
      zpow a ai ((m : Int) - (n : Int)) := by
  by_cases hmn : n ≤ m
  · have hsub : (m : Int) - (n : Int) = Int.ofNat (m - n) := by
      rw [Int.ofNat_eq_natCast]; omega
    rw [hsub, zpow]
    have hm : SimpleCommRing.npow a m = SimpleCommRing.mul (SimpleCommRing.npow a (m - n)) (SimpleCommRing.npow a n) := by
      rw [← SimpleCommRing.npow_add, Nat.sub_add_cancel hmn]
    rw [hm, SimpleCommRing.mul_assoc, npow_mul_inv_cancel h, SimpleCommRing.mul_one]
  · have hlt : m < n := Nat.lt_of_not_le hmn
    have hsub : (m : Int) - (n : Int) = Int.negSucc (n - m - 1) := by
      rw [Int.negSucc_eq]; omega
    rw [hsub, zpow]
    have hn : SimpleCommRing.npow ai n =
        SimpleCommRing.mul (SimpleCommRing.npow ai m) (SimpleCommRing.npow ai (n - m - 1 + 1)) := by
      rw [← SimpleCommRing.npow_add, show m + (n - m - 1 + 1) = n by omega]
    rw [hn, ← SimpleCommRing.mul_assoc, npow_mul_inv_cancel h, SimpleCommRing.one_mul]

theorem zpow_add {a ai : R} (h : SimpleCommRing.mul a ai = SimpleCommRing.one) (p q : Int) :
    SimpleCommRing.mul (zpow a ai p) (zpow a ai q) = zpow a ai (p + q) := by
  cases p with
  | ofNat m =>
    cases q with
    | ofNat n =>
      have h1 : Int.ofNat m + Int.ofNat n = Int.ofNat (m + n) := rfl
      rw [h1]; exact (SimpleCommRing.npow_add a m n).symm
    | negSucc n =>
      have h1 : Int.ofNat m + Int.negSucc n = (m : Int) - ((n + 1 : Nat) : Int) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      rw [h1]; exact npow_add_neg h m (n + 1)
  | negSucc m =>
    cases q with
    | ofNat n =>
      have h1 : Int.negSucc m + Int.ofNat n = (n : Int) - ((m + 1 : Nat) : Int) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      rw [h1, SimpleCommRing.mul_comm]
      exact npow_add_neg h n (m + 1)
    | negSucc n =>
      have h1 : Int.negSucc m + Int.negSucc n = Int.negSucc (m + n + 1) := by
        rw [Int.negSucc_eq, Int.negSucc_eq, Int.negSucc_eq]; omega
      rw [h1, zpow, zpow, zpow]
      rw [show m + n + 1 + 1 = (m + 1) + (n + 1) by omega]
      exact (SimpleCommRing.npow_add ai (m + 1) (n + 1)).symm

theorem zpow_neg {a ai : R} (k : Int) : zpow ai a k = zpow a ai (-k) := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ m => rfl
  | negSucc n => rfl

/-- Evaluate Laurent monomial `x^i y^j z^k` at `pt`. -/
def mon (pt : TorusPt R) (i j k : Int) : R :=
  SimpleCommRing.mul (SimpleCommRing.mul (zpow pt.x pt.xi i) (zpow pt.y pt.yi j)) (zpow pt.z pt.zi k)

theorem mon_zero (pt : TorusPt R) : mon pt 0 0 0 = SimpleCommRing.one := by
  simp [mon, zpow, SimpleCommRing.npow, SimpleCommRing.one_mul]

theorem mon_mul (pt : TorusPt R) (i1 j1 k1 i2 j2 k2 : Int) :
    SimpleCommRing.mul (mon pt i1 j1 k1) (mon pt i2 j2 k2) =
      mon pt (i1 + i2) (j1 + j2) (k1 + k2) := by
  unfold mon
  rw [← zpow_add pt.hx i1 i2, ← zpow_add pt.hy j1 j2, ← zpow_add pt.hz k1 k2]
  have h4 : ∀ u v w t : R,
      SimpleCommRing.mul (SimpleCommRing.mul u v) (SimpleCommRing.mul w t) =
      SimpleCommRing.mul (SimpleCommRing.mul u w) (SimpleCommRing.mul v t) := by
    intro u v w t
    rw [SimpleCommRing.mul_assoc u v, ← SimpleCommRing.mul_assoc v w,
        SimpleCommRing.mul_comm v w, SimpleCommRing.mul_assoc w v, ← SimpleCommRing.mul_assoc u]
  rw [h4 (SimpleCommRing.mul (zpow pt.x pt.xi i1) (zpow pt.y pt.yi j1)) (zpow pt.z pt.zi k1)
         (SimpleCommRing.mul (zpow pt.x pt.xi i2) (zpow pt.y pt.yi j2)) (zpow pt.z pt.zi k2),
      h4 (zpow pt.x pt.xi i1) (zpow pt.y pt.yi j1) (zpow pt.x pt.xi i2) (zpow pt.y pt.yi j2)]

/-- Klein four-group `V₄` action on `TorusPt R`. -/
def v4 (c : Coset) (pt : TorusPt R) : TorusPt R :=
  match c with
  | Coset.e  => pt
  | Coset.a  => ⟨pt.x, pt.xi, pt.yi, pt.y, pt.zi, pt.z,
                 pt.hx, SimpleCommRing.mul_comm pt.y pt.yi ▸ pt.hy,
                 SimpleCommRing.mul_comm pt.z pt.zi ▸ pt.hz⟩
  | Coset.b  => ⟨pt.xi, pt.x, pt.y, pt.yi, pt.zi, pt.z,
                 SimpleCommRing.mul_comm pt.x pt.xi ▸ pt.hx, pt.hy,
                 SimpleCommRing.mul_comm pt.z pt.zi ▸ pt.hz⟩
  | Coset.ab => ⟨pt.xi, pt.x, pt.yi, pt.y, pt.z, pt.zi,
                 SimpleCommRing.mul_comm pt.x pt.xi ▸ pt.hx,
                 SimpleCommRing.mul_comm pt.y pt.yi ▸ pt.hy, pt.hz⟩

theorem mon_v4 (c : Coset) (pt : TorusPt R) (i j k : Int) :
    mon (v4 c pt) i j k = mon pt (Coset.signX c * i) (Coset.signY c * j) (Coset.signZ c * k) := by
  cases c <;>
    simp only [v4, mon, Coset.signX, Coset.signY, Coset.signZ, Int.one_mul, Int.neg_mul]
  · rw [zpow_neg j, zpow_neg k]
  · rw [zpow_neg i, zpow_neg k]
  · rw [zpow_neg i, zpow_neg j]

end TorusPt

/-- `4 × 4` matrix over `R` indexed by `Coset`. -/
abbrev Mat4 (R : Type) := Coset → Coset → R

namespace Mat4

variable {R : Type} [SimpleCommRing R]

def zero : Mat4 R := fun _ _ => SimpleCommRing.zero
def one : Mat4 R := fun i j => if i = j then SimpleCommRing.one else SimpleCommRing.zero
def add (A B : Mat4 R) : Mat4 R := fun i j => SimpleCommRing.add (A i j) (B i j)
def shift (A : Mat4 R) (E : R) : Mat4 R :=
  fun i j => if i = j then SimpleCommRing.sub (A i j) E else A i j

def mul (A B : Mat4 R) : Mat4 R := fun i j =>
  SimpleCommRing.add
    (SimpleCommRing.add (SimpleCommRing.mul (A i Coset.e) (B Coset.e j))
                        (SimpleCommRing.mul (A i Coset.a) (B Coset.a j)))
    (SimpleCommRing.add (SimpleCommRing.mul (A i Coset.b) (B Coset.b j))
                        (SimpleCommRing.mul (A i Coset.ab) (B Coset.ab j)))

def det3 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : R) : R :=
  let m := SimpleCommRing.mul; let a := SimpleCommRing.add; let s := SimpleCommRing.sub
  a (s (m a00 (s (m a11 a22) (m a12 a21)))
       (m a01 (s (m a10 a22) (m a12 a20))))
    (m a02 (s (m a10 a21) (m a11 a20)))

def det4 (M : Mat4 R) : R :=
  let m := SimpleCommRing.mul; let s := SimpleCommRing.sub; let a := SimpleCommRing.add
  let c0 := det3 (M .a .a) (M .a .b) (M .a .ab) (M .b .a) (M .b .b) (M .b .ab) (M .ab .a) (M .ab .b) (M .ab .ab)
  let c1 := det3 (M .a .e) (M .a .b) (M .a .ab) (M .b .e) (M .b .b) (M .b .ab) (M .ab .e) (M .ab .b) (M .ab .ab)
  let c2 := det3 (M .a .e) (M .a .a) (M .a .ab) (M .b .e) (M .b .a) (M .b .ab) (M .ab .e) (M .ab .a) (M .ab .ab)
  let c3 := det3 (M .a .e) (M .a .a) (M .a .b) (M .b .e) (M .b .a) (M .b .b) (M .ab .e) (M .ab .a) (M .ab .b)
  s (a (s (m (M .e .e) c0) (m (M .e .a) c1)) (m (M .e .b) c2)) (m (M .e .ab) c3)

def allPerms4 : List (Int × Coset × Coset × Coset × Coset) :=
  [ ( 1, .e, .a, .b, .ab), (-1, .e, .a, .ab, .b), (-1, .e, .b, .a, .ab),
    ( 1, .e, .b, .ab, .a), ( 1, .e, .ab, .a, .b), (-1, .e, .ab, .b, .a),
    (-1, .a, .e, .b, .ab), ( 1, .a, .e, .ab, .b), ( 1, .a, .b, .e, .ab),
    (-1, .a, .b, .ab, .e), (-1, .a, .ab, .e, .b), ( 1, .a, .ab, .b, .e),
    ( 1, .b, .e, .a, .ab), (-1, .b, .e, .ab, .a), (-1, .b, .a, .e, .ab),
    ( 1, .b, .a, .ab, .e), ( 1, .b, .ab, .e, .a), (-1, .b, .ab, .a, .e),
    (-1, .ab, .e, .a, .b), ( 1, .ab, .e, .b, .a), ( 1, .ab, .a, .e, .b),
    (-1, .ab, .a, .b, .e), (-1, .ab, .b, .e, .a), ( 1, .ab, .b, .a, .e) ]

def leibniz4 (M : Mat4 Int) : Int :=
  allPerms4.foldl (fun acc (sgn, p0, p1, p2, p3) =>
    acc + sgn * M .e p0 * M .a p1 * M .b p2 * M .ab p3) 0

def permConj (c : Coset) (M : Mat4 R) : Mat4 R :=
  fun i j => M (Coset.mulV4 c i) (Coset.mulV4 c j)

def diagPermConj (c : Coset) (u ui : Coset → R) (M : Mat4 R) : Mat4 R :=
  fun i j =>
    SimpleCommRing.mul (SimpleCommRing.mul (u i) (M (Coset.mulV4 c i) (Coset.mulV4 c j))) (ui j)

theorem det4_eq_leibniz4 (M : Mat4 Int) : det4 M = leibniz4 M := by
  simp only [det4, det3, leibniz4, allPerms4, List.foldl,
    SimpleCommRing.add, SimpleCommRing.sub, SimpleCommRing.mul, SimpleCommRing.neg]
  grind

theorem det4_permConj_int (c : Coset) (M : Mat4 Int) :
    det4 (permConj c M) = det4 M := by
  rw [det4_eq_leibniz4, det4_eq_leibniz4]
  cases c <;>
    simp only [permConj, Coset.mulV4, Coset.mulCocycle, leibniz4, allPerms4, List.foldl] <;>
    grind

/-- Exact diagonal-conjugation invariance of `det4` over `Int`. -/
theorem det4_diag_conj_int (u ui : Coset → Int) (hu : ∀ k : Coset, u k * ui k = 1) (M : Mat4 Int) :
    det4 (fun i j => u i * M i j * ui j) = det4 M := by
  rw [det4_eq_leibniz4, det4_eq_leibniz4]
  have he := hu .e; have ha := hu .a; have hb := hu .b; have hab := hu .ab
  have h1prod : (u .e * ui .e) * (u .a * ui .a) * (u .b * ui .b) * (u .ab * ui .ab) = 1 := by
    rw [he, ha, hb, hab]; rfl
  have hgen : ∀ (p0 p1 p2 p3 : Coset) (m0 m1 m2 m3 : Int),
      (p0, p1, p2, p3) ∈ allPerms4.map (fun t => t.2) →
      (u .e * m0 * ui p0) * (u .a * m1 * ui p1) * (u .b * m2 * ui p2) * (u .ab * m3 * ui p3) =
      m0 * m1 * m2 * m3 := by
    intro p0 p1 p2 p3 m0 m1 m2 m3 hp
    simp only [allPerms4, List.map, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    all_goals
      apply Eq.trans (b := ((u .e * ui .e) * (u .a * ui .a) * (u .b * ui .b) * (u .ab * ui .ab)) *
          (m0 * m1 * m2 * m3))
      · grind
      · rw [h1prod, Int.one_mul]
  unfold leibniz4
  suffices hf : ∀ (l : List (Int × Coset × Coset × Coset × Coset)) (acc : Int),
      (∀ t ∈ l, t.2 ∈ allPerms4.map (fun x => x.2)) →
      l.foldl (fun acc (sgn, p0, p1, p2, p3) =>
        acc + sgn * (u .e * M .e p0 * ui p0) * (u .a * M .a p1 * ui p1) *
          (u .b * M .b p2 * ui p2) * (u .ab * M .ab p3 * ui p3)) acc =
      l.foldl (fun acc (sgn, p0, p1, p2, p3) =>
        acc + sgn * M .e p0 * M .a p1 * M .b p2 * M .ab p3) acc by
    exact hf allPerms4 0 (fun t ht => List.mem_map.mpr ⟨t, ht, rfl⟩)
  intro l
  induction l with
  | nil => intro acc _; rfl
  | cons hd tl ih =>
    intro acc hmem
    rcases hd with ⟨sgn, p0, p1, p2, p3⟩
    have hhd := hgen p0 p1 p2 p3 (M .e p0) (M .a p1) (M .b p2) (M .ab p3)
      (hmem (sgn, p0, p1, p2, p3) (List.mem_cons_self ..))
    have hstep :
        sgn * (u .e * M .e p0 * ui p0) * (u .a * M .a p1 * ui p1) *
          (u .b * M .b p2 * ui p2) * (u .ab * M .ab p3 * ui p3) =
        sgn * M .e p0 * M .a p1 * M .b p2 * M .ab p3 := by
      have hl : sgn * (u .e * M .e p0 * ui p0) * (u .a * M .a p1 * ui p1) *
          (u .b * M .b p2 * ui p2) * (u .ab * M .ab p3 * ui p3) =
          sgn * ((u .e * M .e p0 * ui p0) * (u .a * M .a p1 * ui p1) *
            (u .b * M .b p2 * ui p2) * (u .ab * M .ab p3 * ui p3)) := by grind
      rw [hl, hhd]; grind
    simp only [List.foldl, hstep]
    exact ih _ (fun t ht => hmem t (List.mem_cons_of_mem _ ht))

end Mat4

/-- Finite-support element of the group ring `R[P]` represented as an association list. -/
abbrev GroupRingElem (R : Type) := List (ElemP × R)

namespace GroupRingElem

variable {R : Type} [SimpleCommRing R]

def one : GroupRingElem R := [(ElemP.one, SimpleCommRing.one)]
def add (u v : GroupRingElem R) : GroupRingElem R := u ++ v
def mul (u v : GroupRingElem R) : GroupRingElem R :=
  u.flatMap (fun (g1, c1) => v.map (fun (g2, c2) => (ElemP.mul g1 g2, SimpleCommRing.mul c1 c2)))

def coeff (u : GroupRingElem R) (g : ElemP) : R :=
  u.foldl (fun acc (h, c) => if h = g then SimpleCommRing.add acc c else acc) SimpleCommRing.zero

def blochSingle (g : ElemP) (c : R) (pt : TorusPt R) : Mat4 R :=
  fun row col =>
    let (dx, dy, dz, col') := Coset.mulCocycle row g.c
    if col = col' then
      SimpleCommRing.mul c
        (TorusPt.mon pt
          (Coset.signX row * g.ix + dx)
          (Coset.signY row * g.iy + dy)
          (Coset.signZ row * g.iz + dz))
    else
      SimpleCommRing.zero

def blochEval (u : GroupRingElem R) (pt : TorusPt R) : Mat4 R :=
  u.foldl (fun acc (g, c) => Mat4.add acc (blochSingle g c pt)) Mat4.zero

private theorem blochEval_foldl_add (u : GroupRingElem R) (init : Mat4 R) (pt : TorusPt R) :
    u.foldl (fun acc (g, c) => Mat4.add acc (blochSingle g c pt)) init =
      Mat4.add init (blochEval u pt) := by
  induction u generalizing init with
  | nil =>
    funext i j; simp [blochEval, Mat4.add, Mat4.zero, SimpleCommRing.add_zero]
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    simp only [blochEval, List.foldl]
    rw [ih, ih (Mat4.add Mat4.zero (blochSingle g c pt))]
    funext i j
    simp only [Mat4.add, Mat4.zero, SimpleCommRing.zero_add, SimpleCommRing.add_assoc]

private theorem blochEval_cons (g : ElemP) (c : R) (tl : GroupRingElem R) (pt : TorusPt R) :
    blochEval ((g, c) :: tl) pt = Mat4.add (blochSingle g c pt) (blochEval tl pt) := by
  unfold blochEval
  simp only [List.foldl]
  rw [blochEval_foldl_add]
  funext i j
  simp only [Mat4.add, Mat4.zero, SimpleCommRing.zero_add]
  rfl

theorem blochEval_one (pt : TorusPt R) : blochEval (one : GroupRingElem R) pt = Mat4.one := by
  funext i j
  cases i <;> cases j <;>
    simp [blochEval, one, blochSingle, ElemP.one, Coset.mulCocycle, Coset.signX, Coset.signY,
          Coset.signZ, TorusPt.mon_zero, Mat4.add, Mat4.zero, Mat4.one,
          SimpleCommRing.zero_add, SimpleCommRing.one_mul]

theorem blochEval_add (u v : GroupRingElem R) (pt : TorusPt R) :
    blochEval (add u v) pt = Mat4.add (blochEval u pt) (blochEval v pt) := by
  unfold blochEval add
  rw [List.foldl_append, blochEval_foldl_add]
  rfl

theorem blochSingle_mul (g1 g2 : ElemP) (c1 c2 : R) (pt : TorusPt R) :
    Mat4.mul (blochSingle g1 c1 pt) (blochSingle g2 c2 pt) =
      blochSingle (ElemP.mul g1 g2) (SimpleCommRing.mul c1 c2) pt := by
  funext row col
  cases g1 with | mk x1 y1 z1 k1 =>
  cases g2 with | mk x2 y2 z2 k2 =>
  cases row <;> cases col <;> cases k1 <;> cases k2 <;>
    simp only [Mat4.mul, blochSingle, ElemP.mul, Coset.mulCocycle, Coset.signX, Coset.signY,
               Coset.signZ, ite_true, ite_false, reduceCtorEq,
               SimpleCommRing.zero_mul, SimpleCommRing.mul_zero,
               SimpleCommRing.zero_add, SimpleCommRing.add_zero]
  all_goals
    have hswap : ∀ a b c d : R,
        SimpleCommRing.mul (SimpleCommRing.mul a b) (SimpleCommRing.mul c d) =
        SimpleCommRing.mul (SimpleCommRing.mul a c) (SimpleCommRing.mul b d) := fun a b c d => by
      rw [SimpleCommRing.mul_assoc a b, ← SimpleCommRing.mul_assoc b c,
          SimpleCommRing.mul_comm b c, SimpleCommRing.mul_assoc c b, ← SimpleCommRing.mul_assoc a]
    rw [hswap, TorusPt.mon_mul]
    congr 1; congr 1 <;> omega

private theorem mat4_mul_add_right (A B C : Mat4 R) :
    Mat4.mul A (Mat4.add B C) = Mat4.add (Mat4.mul A B) (Mat4.mul A C) := by
  funext i j
  simp only [Mat4.mul, Mat4.add, SimpleCommRing.left_distrib]
  have h4 : ∀ x1 y1 x2 y2 : R,
      SimpleCommRing.add (SimpleCommRing.add x1 y1) (SimpleCommRing.add x2 y2) =
      SimpleCommRing.add (SimpleCommRing.add x1 x2) (SimpleCommRing.add y1 y2) := fun x1 y1 x2 y2 => by
    rw [SimpleCommRing.add_assoc x1 y1, ← SimpleCommRing.add_assoc y1 x2,
        SimpleCommRing.add_comm y1 x2, SimpleCommRing.add_assoc x2 y1, ← SimpleCommRing.add_assoc x1]
  rw [h4 (SimpleCommRing.mul (A i Coset.e) (B Coset.e j)) (SimpleCommRing.mul (A i Coset.e) (C Coset.e j)),
      h4 (SimpleCommRing.mul (A i Coset.b) (B Coset.b j)) (SimpleCommRing.mul (A i Coset.b) (C Coset.b j)),
      h4]

private theorem mat4_mul_add_left (A B C : Mat4 R) :
    Mat4.mul (Mat4.add A B) C = Mat4.add (Mat4.mul A C) (Mat4.mul B C) := by
  funext i j
  simp only [Mat4.mul, Mat4.add, SimpleCommRing.right_distrib]
  have h4 : ∀ x1 y1 x2 y2 : R,
      SimpleCommRing.add (SimpleCommRing.add x1 y1) (SimpleCommRing.add x2 y2) =
      SimpleCommRing.add (SimpleCommRing.add x1 x2) (SimpleCommRing.add y1 y2) := fun x1 y1 x2 y2 => by
    rw [SimpleCommRing.add_assoc x1 y1, ← SimpleCommRing.add_assoc y1 x2,
        SimpleCommRing.add_comm y1 x2, SimpleCommRing.add_assoc x2 y1, ← SimpleCommRing.add_assoc x1]
  rw [h4 (SimpleCommRing.mul (A i Coset.e) (C Coset.e j)) (SimpleCommRing.mul (B i Coset.e) (C Coset.e j)),
      h4 (SimpleCommRing.mul (A i Coset.b) (C Coset.b j)) (SimpleCommRing.mul (B i Coset.b) (C Coset.b j)),
      h4]

private theorem mat4_mul_zero_right (A : Mat4 R) : Mat4.mul A Mat4.zero = Mat4.zero := by
  funext i j; simp [Mat4.mul, Mat4.zero, SimpleCommRing.mul_zero, SimpleCommRing.add_zero]

private theorem mat4_mul_zero_left (A : Mat4 R) : Mat4.mul Mat4.zero A = Mat4.zero := by
  funext i j; simp [Mat4.mul, Mat4.zero, SimpleCommRing.zero_mul, SimpleCommRing.add_zero]

/-- **Theorem `T1b` (Part 1 — Multiplicative Homomorphism of the 4-Band Bloch Representation).** -/
theorem blochEval_mul (u v : GroupRingElem R) (pt : TorusPt R) :
    blochEval (mul u v) pt = Mat4.mul (blochEval u pt) (blochEval v pt) := by
  induction u with
  | nil => simp [mul, blochEval, mat4_mul_zero_left]
  | cons hd tl ih =>
    rcases hd with ⟨g1, c1⟩
    have hmap : ∀ (w : GroupRingElem R),
        blochEval (w.map (fun (g2, c2) => (ElemP.mul g1 g2, SimpleCommRing.mul c1 c2))) pt =
          Mat4.mul (blochSingle g1 c1 pt) (blochEval w pt) := by
      intro w
      induction w with
      | nil => simp [blochEval, mat4_mul_zero_right]
      | cons wh wt wih =>
        rcases wh with ⟨g2, c2⟩
        simp only [List.map]
        rw [blochEval_cons, blochEval_cons, mat4_mul_add_right, blochSingle_mul, wih]
    show blochEval (v.map (fun (g2, c2) => (ElemP.mul g1 g2, SimpleCommRing.mul c1 c2)) ++ mul tl v) pt = _
    rw [show v.map (fun (g2, c2) => (ElemP.mul g1 g2, SimpleCommRing.mul c1 c2)) ++ mul tl v =
          add (v.map (fun (g2, c2) => (ElemP.mul g1 g2, SimpleCommRing.mul c1 c2))) (mul tl v) from rfl]
    rw [blochEval_add, hmap, ih, blochEval_cons, mat4_mul_add_left]

def psiFormal (u : GroupRingElem R) (row col : Coset) (pt : Int × Int × Int) : R :=
  u.foldl (fun acc (g, c) =>
    let (dx, dy, dz, col') := Coset.mulCocycle row g.c
    if col = col' ∧ pt = (Coset.signX row * g.ix + dx, Coset.signY row * g.iy + dy, Coset.signZ row * g.iz + dz)
    then SimpleCommRing.add acc c
    else acc) SimpleCommRing.zero

/-- **Theorem `T1b` (Part 2 — Exact Faithfulness / Injectivity of `Ψ`).** -/
theorem psiFormal_row_e_eq_coeff (u : GroupRingElem R) (g : ElemP) :
    psiFormal u Coset.e g.c (g.ix, g.iy, g.iz) = coeff u g := by
  unfold psiFormal coeff
  have hfn :
      (fun (acc : R) (x : ElemP × R) =>
        let (dx, dy, dz, col') := Coset.mulCocycle Coset.e x.1.c
        if g.c = col' ∧ (g.ix, g.iy, g.iz) =
            (Coset.signX Coset.e * x.1.ix + dx, Coset.signY Coset.e * x.1.iy + dy, Coset.signZ Coset.e * x.1.iz + dz)
        then SimpleCommRing.add acc x.2 else acc) =
      (fun (acc : R) (x : ElemP × R) =>
        if x.1 = g then SimpleCommRing.add acc x.2 else acc) := by
    funext acc x
    rcases x with ⟨h, c⟩
    simp only [Coset.mulCocycle, Coset.signX, Coset.signY, Coset.signZ, Int.one_mul, Int.add_zero]
    have hiff : (g.c = h.c ∧ (g.ix, g.iy, g.iz) = (h.ix, h.iy, h.iz)) ↔ h = g := by
      constructor
      · cases g; cases h; intro ⟨hc, hxyz⟩; simp only [Prod.mk.injEq] at hxyz
        rcases hxyz with ⟨hx, hy, hz⟩; subst hc; subst hx; subst hy; subst hz; rfl
      · intro heq; subst heq; exact ⟨rfl, rfl⟩
    simp only [propext hiff]
  exact congrArg (fun f => u.foldl f SimpleCommRing.zero) hfn

theorem psiFormal_injective (u : GroupRingElem R)
    (h : ∀ row col pt, psiFormal u row col pt = SimpleCommRing.zero) :
    ∀ g : ElemP, coeff u g = SimpleCommRing.zero := by
  intro g
  rw [← psiFormal_row_e_eq_coeff]
  exact h Coset.e g.c (g.ix, g.iy, g.iz)

def simScale (c : Coset) (pt : TorusPt R) (row : Coset) : R :=
  let (dx, dy, dz, _) := Coset.mulCocycle c row
  TorusPt.mon pt dx dy dz

def simScaleInv (c : Coset) (pt : TorusPt R) (row : Coset) : R :=
  let (dx, dy, dz, _) := Coset.mulCocycle c row
  TorusPt.mon pt (-dx) (-dy) (-dz)

theorem simScale_mul_inv (c : Coset) (pt : TorusPt R) (row : Coset) :
    SimpleCommRing.mul (simScale c pt row) (simScaleInv c pt row) = SimpleCommRing.one := by
  unfold simScale simScaleInv
  cases c <;> cases row <;>
    simp only [Coset.mulCocycle, TorusPt.mon_mul] <;>
    exact TorusPt.mon_zero pt

theorem blochSingle_v4_conj (c : Coset) (g : ElemP) (coeff : R) (pt : TorusPt R) (row col : Coset) :
    blochSingle g coeff (TorusPt.v4 c pt) row col =
      SimpleCommRing.mul
        (SimpleCommRing.mul (simScale c pt row)
          (blochSingle g coeff pt (Coset.mulV4 c row) (Coset.mulV4 c col)))
        (simScaleInv c pt col) := by
  cases g with | mk gx gy gz gc =>
  cases c <;> cases row <;> cases col <;> cases gc <;>
    simp only [blochSingle, simScale, simScaleInv, Coset.mulV4, Coset.mulCocycle,
               Coset.signX, Coset.signY, Coset.signZ, TorusPt.mon_v4,
               ite_true, ite_false, reduceCtorEq,
               SimpleCommRing.mul_zero, SimpleCommRing.zero_mul]
  all_goals
    have hmove : ∀ s1 c0 m s2 : R,
        SimpleCommRing.mul (SimpleCommRing.mul s1 (SimpleCommRing.mul c0 m)) s2 =
        SimpleCommRing.mul c0 (SimpleCommRing.mul (SimpleCommRing.mul s1 m) s2) := fun s1 c0 m s2 => by
      rw [← SimpleCommRing.mul_assoc s1 c0 m, SimpleCommRing.mul_comm s1 c0,
          SimpleCommRing.mul_assoc c0 s1 m, SimpleCommRing.mul_assoc c0]
    rw [hmove, TorusPt.mon_mul, TorusPt.mon_mul]
    congr 1; congr 1 <;> omega

theorem blochEval_shift_v4_conj (c : Coset) (u : GroupRingElem R) (E : R) (pt : TorusPt R) :
    Mat4.shift (blochEval u (TorusPt.v4 c pt)) E =
      Mat4.diagPermConj c (simScale c pt) (simScaleInv c pt) (Mat4.shift (blochEval u pt) E) := by
  have hbase : ∀ (w : GroupRingElem R) (row col : Coset),
      blochEval w (TorusPt.v4 c pt) row col =
        SimpleCommRing.mul
          (SimpleCommRing.mul (simScale c pt row)
            (blochEval w pt (Coset.mulV4 c row) (Coset.mulV4 c col)))
          (simScaleInv c pt col) := by
    intro w
    induction w with
    | nil =>
      intro row col
      simp [blochEval, Mat4.zero, SimpleCommRing.mul_zero, SimpleCommRing.zero_mul]
    | cons hd tl ih =>
      intro row col
      rcases hd with ⟨g, cf⟩
      rw [blochEval_cons, blochEval_cons]
      simp only [Mat4.add]
      rw [blochSingle_v4_conj c g cf pt row col, ih row col]
      rw [SimpleCommRing.left_distrib, SimpleCommRing.right_distrib]
  funext row col
  unfold Mat4.shift Mat4.diagPermConj
  have hmulV4_eq : (Coset.mulV4 c row = Coset.mulV4 c col) ↔ (row = col) := by
    cases c <;> cases row <;> cases col <;> decide
  by_cases hrc : row = col
  · subst hrc
    simp only [ite_true, hbase u row row, SimpleCommRing.sub]
    rw [SimpleCommRing.left_distrib, SimpleCommRing.right_distrib]
    congr 1
    rw [SimpleCommRing.mul_neg, SimpleCommRing.neg_mul,
        SimpleCommRing.mul_comm (simScale c pt row) E,
        SimpleCommRing.mul_assoc E, simScale_mul_inv c pt row, SimpleCommRing.mul_one]
  · have hmul : Coset.mulV4 c row ≠ Coset.mulV4 c col := mt hmulV4_eq.mp hrc
    simp only [hrc, hmul, ite_false, hbase u row col]

/-- **Theorem `T1c` (Universal `V₄`-Invariance of `det₄(Ψ(u) - E·I₄)`):**
    For EVERY `c ∈ V₄`, `u ∈ ℤ[P]`, `E ∈ ℤ`, and `pt ∈ TorusPt ℤ`,
      `det₄(Ψ(u)(v₄(c, pt)) - E·I₄) = det₄(Ψ(u)(pt) - E·I₄)`. -/
theorem universal_v4_det_invariance_int (c : Coset) (u : GroupRingElem Int) (E : Int)
    (pt : TorusPt Int) :
    Mat4.det4 (Mat4.shift (blochEval u (TorusPt.v4 c pt)) E) =
      Mat4.det4 (Mat4.shift (blochEval u pt) E) := by
  rw [blochEval_shift_v4_conj c u E pt]
  have h1 : Mat4.det4 (Mat4.diagPermConj c (simScale c pt) (simScaleInv c pt)
      (Mat4.shift (blochEval u pt) E)) =
    Mat4.det4 (Mat4.permConj c (Mat4.shift (blochEval u pt) E)) := by
    exact Mat4.det4_diag_conj_int (simScale c pt) (simScaleInv c pt) (simScale_mul_inv c pt)
      (Mat4.permConj c (Mat4.shift (blochEval u pt) E))
  rw [h1]
  exact Mat4.det4_permConj_int c (Mat4.shift (blochEval u pt) E)

end GroupRingElem

def blochAtSign (P Q R_ S sx sy sz : Int) : Mat4 Int :=
  fun row col =>
    let spow (s : Int) (e : Int) : Int := if e % 2 = 0 then 1 else s
    let term (c : Coset) (v : Int) : Int :=
      let (dx, dy, dz, col') := Coset.mulCocycle row c
      if col = col' then v * spow sx dx * spow sy dy * spow sz dz else 0
    term .e P + term .a Q + term .b R_ + term .ab S

/-- **Theorem `T1d` (Exact Eight-Sign-Point Factorization Theorem).** -/
theorem eight_sign_point_factorization (P Q R_ S : Int) :
    (Mat4.det4 (blochAtSign P Q R_ S   1   1   1) =
      (P + Q + R_ + S) * (P + Q - R_ - S) * (P - Q + R_ - S) * (P - Q - R_ + S)) ∧
    (Mat4.det4 (blochAtSign P Q R_ S   1   1 (-1)) =
      (P * P - Q * Q - R_ * R_ + S * S) * (P * P - Q * Q - R_ * R_ + S * S)) ∧
    (Mat4.det4 (blochAtSign P Q R_ S   1 (-1)  1) =
      (P * P - Q * Q + R_ * R_ - S * S) * (P * P - Q * Q + R_ * R_ - S * S)) ∧
    (Mat4.det4 (blochAtSign P Q R_ S (-1)  1   1) =
      (P * P + Q * Q - R_ * R_ - S * S) * (P * P + Q * Q - R_ * R_ - S * S)) ∧
    (Mat4.det4 (blochAtSign P Q R_ S (-1) (-1) (-1)) =
      (P * P + Q * Q + R_ * R_ + S * S) * (P * P + Q * Q + R_ * R_ + S * S)) ∧
    (Mat4.det4 (blochAtSign P Q R_ S   1 (-1) (-1)) =
      ((P + Q) * (P + Q) + (R_ + S) * (R_ + S)) * ((P - Q) * (P - Q) + (R_ - S) * (R_ - S))) ∧
    (Mat4.det4 (blochAtSign P Q R_ S (-1)  1 (-1)) =
      ((P + R_) * (P + R_) + (Q + S) * (Q + S)) * ((P - R_) * (P - R_) + (Q - S) * (Q - S))) ∧
    (Mat4.det4 (blochAtSign P Q R_ S (-1) (-1)  1) =
      ((P - S) * (P - S) + (Q + R_) * (Q + R_)) * ((P + S) * (P + S) + (Q - R_) * (Q - R_))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Mat4.det4, Mat4.det3, blochAtSign, Coset.mulCocycle,
      SimpleCommRing.add, SimpleCommRing.sub, SimpleCommRing.mul, SimpleCommRing.neg] <;>
    grind

end PromislowFracton
