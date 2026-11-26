module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue

/-!
# Zero-Mathlib Commutative Ring, Finite Field, and Univariate Polynomial Core

Self-contained algebraic structures for `promislow-fracton-amoeba` (`v1.0.0`) with zero
external dependencies:
- `SimpleCommRing`: commutative unital rings (with constructive instances `Int`, `Bool` as `F_2`,
  `ZMod3`, `ZMod5`, `F4`, and `RatQ`).
- `SimpleIntegralDomain`: commutative ring with `1 ≠ 0` and no nonzero zero divisors.
- `SimpleField`: constructive field with explicit multiplicative inverse.
- `UPoly R`: univariate polynomials over a commutative ring `R`, with polynomial multiplication,
  evaluation, degree, and Bézout coprimality machinery used in Theorem `T2c` (Universal All-Prime
  Type-II No-Strings Theorem for Haah's Cubic Code).
-/

@[expose] public section

namespace PromislowFracton

/-- Minimal self-contained commutative ring with `1` (zero Mathlib). -/
class SimpleCommRing (R : Type) where
  zero : R
  one : R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  zero_add : ∀ a : R, add zero a = a
  add_zero : ∀ a : R, add a zero = a
  add_comm : ∀ a b : R, add a b = add b a
  add_neg : ∀ a : R, add a (neg a) = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : R, mul one a = a
  mul_one : ∀ a : R, mul a one = a
  mul_comm : ∀ a b : R, mul a b = mul b a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)

namespace SimpleCommRing

variable {R : Type} [SimpleCommRing R]

def sub (a b : R) : R := add a (neg b)

theorem right_distrib (a b c : R) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem neg_add (a : R) : add (neg a) a = zero := by
  rw [add_comm, add_neg]

theorem add_left_cancel {a b c : R} (h : add a b = add a c) : b = c := by
  have h1 : add (neg a) (add a b) = add (neg a) (add a c) := congrArg (add (neg a)) h
  rw [← add_assoc, ← add_assoc, neg_add, zero_add, zero_add] at h1
  exact h1

theorem mul_zero (a : R) : mul a zero = zero := by
  have h : add (mul a zero) (mul a zero) = add (mul a zero) zero := by
    rw [← left_distrib, add_zero, add_zero]
  exact add_left_cancel h

theorem zero_mul (a : R) : mul zero a = zero := by
  rw [mul_comm, mul_zero]

theorem neg_eq_of_add_eq_zero {a b : R} (h : add a b = zero) : b = neg a := by
  have h1 : add a b = add a (neg a) := by rw [h, add_neg]
  exact add_left_cancel h1

theorem neg_zero : neg (zero : R) = zero := by
  symm
  exact neg_eq_of_add_eq_zero (add_zero zero)

theorem neg_neg (a : R) : neg (neg a) = a := by
  symm
  exact neg_eq_of_add_eq_zero (neg_add a)

theorem neg_add_distrib (a b : R) : neg (add a b) = add (neg a) (neg b) := by
  symm
  apply neg_eq_of_add_eq_zero
  calc add (add a b) (add (neg a) (neg b))
      = add a (add b (add (neg a) (neg b))) := add_assoc _ _ _
    _ = add a (add (neg a) (add b (neg b))) := by
        rw [← add_assoc b, add_comm b (neg a), add_assoc]
    _ = add a (add (neg a) zero) := by rw [add_neg]
    _ = add a (neg a) := by rw [add_zero]
    _ = zero := add_neg a

theorem mul_neg (a b : R) : mul a (neg b) = neg (mul a b) := by
  apply neg_eq_of_add_eq_zero
  rw [← left_distrib, add_neg, mul_zero]

theorem neg_mul (a b : R) : mul (neg a) b = neg (mul a b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem neg_mul_neg (a b : R) : mul (neg a) (neg b) = mul a b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem sub_self (a : R) : sub a a = zero := add_neg a

theorem sub_eq_zero_iff (a b : R) : sub a b = zero ↔ a = b := by
  constructor
  · intro h
    have h1 : add (sub a b) b = add zero b := congrArg (fun x => add x b) h
    unfold sub at h1
    rw [add_assoc, neg_add, add_zero, zero_add] at h1
    exact h1
  · intro h
    subst h
    exact sub_self a

/-- Natural-number scalar embedding `n ↦ n · 1` into any commutative ring. -/
def ofNat (n : Nat) : R :=
  match n with
  | 0 => zero
  | k + 1 => add (ofNat k) one

/-- Integer embedding `z ↦ z · 1` into any commutative ring. -/
def ofInt (z : Int) : R :=
  match z with
  | Int.ofNat n => ofNat n
  | Int.negSucc n => neg (ofNat (n + 1))

/-- Natural-number power in any commutative ring. -/
def npow (a : R) : Nat → R
  | 0 => one
  | k + 1 => mul a (npow a k)

theorem npow_zero (a : R) : npow a 0 = one := rfl
theorem npow_succ (a : R) (n : Nat) : npow a (n + 1) = mul a (npow a n) := rfl

theorem npow_add (a : R) (m n : Nat) : npow a (m + n) = mul (npow a m) (npow a n) := by
  induction m with
  | zero => simp [npow, one_mul]
  | succ k ih =>
    rw [Nat.succ_add, npow_succ, npow_succ, ih, mul_assoc]

theorem mul_npow (a b : R) (n : Nat) : npow (mul a b) n = mul (npow a n) (npow b n) := by
  induction n with
  | zero => simp [npow, one_mul]
  | succ k ih =>
    rw [npow_succ, npow_succ, npow_succ, ih]
    calc mul (mul a b) (mul (npow a k) (npow b k))
        = mul a (mul b (mul (npow a k) (npow b k))) := mul_assoc _ _ _
      _ = mul a (mul (npow a k) (mul b (npow b k))) := by
          rw [← mul_assoc b, mul_comm b (npow a k), mul_assoc]
      _ = mul (mul a (npow a k)) (mul b (npow b k)) := (mul_assoc _ _ _).symm

end SimpleCommRing

/-- Commutative integral domain (nontrivial, no nonzero zero divisors). -/
class SimpleIntegralDomain (R : Type) extends SimpleCommRing R where
  one_ne_zero : one ≠ zero
  mul_eq_zero : ∀ a b : R, mul a b = zero → a = zero ∨ b = zero

/-- Constructive field (integral domain with explicit multiplicative inverse). -/
class SimpleField (K : Type) extends SimpleIntegralDomain K where
  inv : K → K
  mul_inv_cancel : ∀ a : K, a ≠ zero → mul a (inv a) = one

/-- Concrete `SimpleIntegralDomain` instance on `Int`. -/
instance instSimpleCommRingInt : SimpleCommRing Int where
  zero := 0
  one := 1
  add := Int.add
  neg := Int.neg
  mul := Int.mul
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  add_comm := Int.add_comm
  add_neg := Int.add_right_neg
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  mul_comm := Int.mul_comm
  left_distrib := Int.mul_add

instance instSimpleIntegralDomainInt : SimpleIntegralDomain Int where
  one_ne_zero := by decide
  mul_eq_zero := fun a b h => Int.mul_eq_zero.mp h

/-- Concrete finite field `F_2` represented as `Bool` (`false = 0`, `true = 1`). -/
instance instSimpleCommRingF2 : SimpleCommRing Bool where
  zero := false
  one := true
  add := xor
  neg := id
  mul := and
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  add_neg := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  left_distrib := by decide

instance instSimpleIntegralDomainF2 : SimpleIntegralDomain Bool where
  one_ne_zero := by decide
  mul_eq_zero := by decide

instance instSimpleFieldF2 : SimpleField Bool where
  inv := id
  mul_inv_cancel := by decide

/-- Finite field `F_4 = F_2[ω] / (ω^2 + ω + 1)` represented by 4 elements. -/
inductive F4 where
  | zero : F4
  | one : F4
  | w : F4
  | w2 : F4
  deriving DecidableEq, Repr

namespace F4

def add : F4 → F4 → F4
  | zero, x => x
  | x, zero => x
  | one, one => zero
  | w, w => zero
  | w2, w2 => zero
  | one, w => w2
  | w, one => w2
  | one, w2 => w
  | w2, one => w
  | w, w2 => one
  | w2, w => one

def mul : F4 → F4 → F4
  | zero, _ => zero
  | _, zero => zero
  | one, x => x
  | x, one => x
  | w, w => w2
  | w2, w2 => w
  | w, w2 => one
  | w2, w => one

def inv : F4 → F4
  | zero => zero
  | one => one
  | w => w2
  | w2 => w

instance instSimpleCommRingF4 : SimpleCommRing F4 where
  zero := F4.zero
  one := F4.one
  add := F4.add
  neg := id
  mul := F4.mul
  add_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  zero_add := fun a => by cases a <;> rfl
  add_zero := fun a => by cases a <;> rfl
  add_comm := fun a b => by cases a <;> cases b <;> rfl
  add_neg := fun a => by cases a <;> rfl
  mul_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  one_mul := fun a => by cases a <;> rfl
  mul_one := fun a => by cases a <;> rfl
  mul_comm := fun a b => by cases a <;> cases b <;> rfl
  left_distrib := fun a b c => by cases a <;> cases b <;> cases c <;> rfl

instance instSimpleIntegralDomainF4 : SimpleIntegralDomain F4 where
  one_ne_zero := by decide
  mul_eq_zero := fun a b h => by cases a <;> cases b <;> simp_all [SimpleCommRing.mul, SimpleCommRing.zero, F4.mul]

instance instSimpleFieldF4 : SimpleField F4 where
  inv := F4.inv
  mul_inv_cancel := fun a h => by cases a <;> simp_all [SimpleCommRing.mul, SimpleCommRing.zero, SimpleCommRing.one, F4.mul, F4.inv]

end F4

/-- Exact `Z / nZ` represented as `Fin n` for small prime moduli (`p = 3, 5, 7, 23, 31`). -/
structure ZMod (n : Nat) where
  val : Nat
  lt : val < n
  deriving DecidableEq, Repr

namespace ZMod

def add {n : Nat} (a b : ZMod n) : ZMod n :=
  ⟨(a.val + b.val) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) a.lt)⟩

def mul {n : Nat} (a b : ZMod n) : ZMod n :=
  ⟨(a.val * b.val) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) a.lt)⟩

def neg {n : Nat} (a : ZMod n) : ZMod n :=
  ⟨(n - a.val % n) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) a.lt)⟩

def ofNat (n : Nat) (hn : 0 < n) (k : Nat) : ZMod n :=
  ⟨k % n, Nat.mod_lt k hn⟩

theorem ext {n : Nat} {a b : ZMod n} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

@[instance_reducible]
def mkSimpleCommRing (n : Nat) (hn : 1 < n) : SimpleCommRing (ZMod n) where
  zero := ⟨0, Nat.lt_trans Nat.zero_lt_one hn⟩
  one := ⟨1, hn⟩
  add := ZMod.add
  neg := ZMod.neg
  mul := ZMod.mul
  add_assoc := fun a b c => by
    apply ext; simp [ZMod.add, Nat.add_assoc]
  zero_add := fun a => by
    apply ext; simp [ZMod.add, Nat.mod_eq_of_lt a.lt]
  add_zero := fun a => by
    apply ext; simp [ZMod.add, Nat.mod_eq_of_lt a.lt]
  add_comm := fun a b => by
    apply ext; simp [ZMod.add, Nat.add_comm]
  add_neg := fun a => by
    apply ext
    simp only [ZMod.add, ZMod.neg, Nat.mod_eq_of_lt a.lt]
    by_cases h0 : a.val = 0
    · simp [h0]
    · have hlt : n - a.val < n := Nat.sub_lt (Nat.lt_trans Nat.zero_lt_one hn) (Nat.pos_of_ne_zero h0)
      rw [Nat.mod_eq_of_lt hlt, Nat.add_sub_of_le (Nat.le_of_lt a.lt), Nat.mod_self]
  mul_assoc := fun a b c => by
    apply ext; simp [ZMod.mul, Nat.mul_assoc]
  one_mul := fun a => by
    apply ext; simp [ZMod.mul, Nat.mod_eq_of_lt a.lt]
  mul_one := fun a => by
    apply ext; simp [ZMod.mul, Nat.mod_eq_of_lt a.lt]
  mul_comm := fun a b => by
    apply ext; simp [ZMod.mul, Nat.mul_comm]
  left_distrib := fun a b c => by
    apply ext
    simp only [ZMod.mul, ZMod.add]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_add, Nat.add_mod]

end ZMod

/-- Exact rational numbers `num / den` (`den > 0`), used for ordered-field convexity (`T3a`)
    and amoeba inequalities (`T3b`) without requiring Mathlib or real-number axioms. -/
structure RatQ where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving Repr

namespace RatQ

def add (a b : RatQ) : RatQ :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def neg (a : RatQ) : RatQ :=
  ⟨-a.num, a.den, a.den_pos⟩

def mul (a b : RatQ) : RatQ :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def ofInt (z : Int) : RatQ := ⟨z, 1, Nat.zero_lt_one⟩

def half : RatQ := ⟨1, 2, by decide⟩
def quarter : RatQ := ⟨1, 4, by decide⟩

/-- Cross-multiplied exact ordering `a ≤ b` on `RatQ`. -/
def le (a b : RatQ) : Prop :=
  a.num * (b.den : Int) ≤ b.num * (a.den : Int)

/-- Cross-multiplied exact equality `a ≈ b` on `RatQ`. -/
def eqv (a b : RatQ) : Prop :=
  a.num * (b.den : Int) = b.num * (a.den : Int)

theorem le_refl (a : RatQ) : le a a := Int.le_refl _

theorem le_trans {a b c : RatQ} (hab : le a b) (hbc : le b c) : le a c := by
  unfold le at *
  have hb : (0 : Int) < (b.den : Int) := by have := b.den_pos; omega
  have ha : (0 : Int) < (a.den : Int) := by have := a.den_pos; omega
  have hc : (0 : Int) < (c.den : Int) := by have := c.den_pos; omega
  have h1 : a.num * b.den * c.den ≤ b.num * a.den * c.den :=
    Int.mul_le_mul_of_nonneg_right hab (Int.le_of_lt hc)
  have h2 : b.num * c.den * a.den ≤ c.num * b.den * a.den :=
    Int.mul_le_mul_of_nonneg_right hbc (Int.le_of_lt ha)
  have hmid : b.num * a.den * c.den = b.num * c.den * a.den := by
    rw [Int.mul_assoc, Int.mul_comm (a.den : Int), ← Int.mul_assoc]
  have h3 : a.num * c.den * b.den ≤ c.num * a.den * b.den := by
    have h4 : a.num * b.den * c.den ≤ c.num * b.den * a.den := Int.le_trans h1 (hmid ▸ h2)
    have hl : a.num * b.den * c.den = a.num * c.den * b.den := by
      rw [Int.mul_assoc, Int.mul_comm (b.den : Int), ← Int.mul_assoc]
    have hr : c.num * b.den * a.den = c.num * a.den * b.den := by
      rw [Int.mul_assoc, Int.mul_comm (b.den : Int), ← Int.mul_assoc]
    rw [← hl, ← hr]; exact h4
  exact Int.le_of_mul_le_mul_right h3 hb

theorem le_of_eqv {a b : RatQ} (h : eqv a b) : le a b := Int.le_of_eq h

theorem add_le_add {a b c d : RatQ} (hab : le a b) (hcd : le c d) :
    le (add a c) (add b d) := by
  unfold le add at *
  have ha : (0 : Int) ≤ (a.den : Int) := Int.natCast_nonneg _
  have hb : (0 : Int) ≤ (b.den : Int) := Int.natCast_nonneg _
  have hc : (0 : Int) ≤ (c.den : Int) := Int.natCast_nonneg _
  have hd : (0 : Int) ≤ (d.den : Int) := Int.natCast_nonneg _
  have h1 : a.num * b.den * (c.den * d.den) ≤ b.num * a.den * (c.den * d.den) :=
    Int.mul_le_mul_of_nonneg_right hab (Int.mul_nonneg hc hd)
  have h2 : c.num * d.den * (a.den * b.den) ≤ d.num * c.den * (a.den * b.den) :=
    Int.mul_le_mul_of_nonneg_right hcd (Int.mul_nonneg ha hb)
  have hsum := Int.add_le_add h1 h2
  have hl : (a.num * (c.den : Int) + c.num * (a.den : Int)) * ((b.den * d.den : Nat) : Int) =
      a.num * b.den * (c.den * d.den) + c.num * d.den * (a.den * b.den) := by
    rw [Int.natCast_mul]; grind
  have hr : (b.num * (d.den : Int) + d.num * (b.den : Int)) * ((a.den * c.den : Nat) : Int) =
      b.num * a.den * (c.den * d.den) + d.num * c.den * (a.den * b.den) := by
    rw [Int.natCast_mul]; grind
  rw [hl, hr]; exact hsum

theorem mul_nonneg_le {k a b : RatQ} (hk : 0 ≤ k.num) (hab : le a b) :
    le (mul k a) (mul k b) := by
  unfold le mul at *
  have hkden : (0 : Int) ≤ (k.den : Int) := Int.natCast_nonneg _
  have h1 : a.num * b.den * (k.num * k.den) ≤ b.num * a.den * (k.num * k.den) :=
    Int.mul_le_mul_of_nonneg_right hab (Int.mul_nonneg hk hkden)
  have hl : k.num * a.num * ((k.den * b.den : Nat) : Int) = a.num * b.den * (k.num * k.den) := by
    rw [Int.natCast_mul]; grind
  have hr : k.num * b.num * ((k.den * a.den : Nat) : Int) = b.num * a.den * (k.num * k.den) := by
    rw [Int.natCast_mul]; grind
  rw [hl, hr]; exact h1

end RatQ

/-- Univariate polynomials over a commutative ring `R`, represented as coefficient lists
    `[c₀, c₁, ..., c_d]` (little-endian). -/
abbrev UPoly (R : Type) := List R

namespace UPoly

variable {R : Type} [SimpleCommRing R]

def eval (p : UPoly R) (x : R) : R :=
  match p with
  | [] => SimpleCommRing.zero
  | c :: cs => SimpleCommRing.add c (SimpleCommRing.mul x (eval cs x))

def add : UPoly R → UPoly R → UPoly R
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => SimpleCommRing.add a b :: add as bs

def scale (c : R) : UPoly R → UPoly R
  | [] => []
  | a :: as => SimpleCommRing.mul c a :: scale c as

def mul : UPoly R → UPoly R → UPoly R
  | [], _ => []
  | a :: as, q => add (scale a q) (SimpleCommRing.zero :: mul as q)

def const (c : R) : UPoly R := [c]

theorem eval_add (p q : UPoly R) (x : R) :
    eval (add p q) x = SimpleCommRing.add (eval p x) (eval q x) := by
  induction p generalizing q with
  | nil => simp [add, eval, SimpleCommRing.zero_add]
  | cons a as ih =>
    cases q with
    | nil => simp [add, eval, SimpleCommRing.add_zero]
    | cons b bs =>
      simp only [add, eval, ih, SimpleCommRing.left_distrib]
      calc SimpleCommRing.add (SimpleCommRing.add a b)
            (SimpleCommRing.add (SimpleCommRing.mul x (eval as x)) (SimpleCommRing.mul x (eval bs x)))
          = SimpleCommRing.add a (SimpleCommRing.add b
              (SimpleCommRing.add (SimpleCommRing.mul x (eval as x)) (SimpleCommRing.mul x (eval bs x)))) :=
            SimpleCommRing.add_assoc _ _ _
        _ = SimpleCommRing.add a (SimpleCommRing.add (SimpleCommRing.mul x (eval as x))
              (SimpleCommRing.add b (SimpleCommRing.mul x (eval bs x)))) := by
            rw [← SimpleCommRing.add_assoc b, SimpleCommRing.add_comm b (SimpleCommRing.mul x (eval as x)),
                SimpleCommRing.add_assoc]
        _ = SimpleCommRing.add (SimpleCommRing.add a (SimpleCommRing.mul x (eval as x)))
              (SimpleCommRing.add b (SimpleCommRing.mul x (eval bs x))) :=
            (SimpleCommRing.add_assoc _ _ _).symm

theorem eval_scale (c : R) (p : UPoly R) (x : R) :
    eval (scale c p) x = SimpleCommRing.mul c (eval p x) := by
  induction p with
  | nil => simp [scale, eval, SimpleCommRing.mul_zero]
  | cons a as ih =>
    simp only [scale, eval, ih, SimpleCommRing.left_distrib]
    congr 1
    rw [← SimpleCommRing.mul_assoc, SimpleCommRing.mul_comm x c, SimpleCommRing.mul_assoc]

theorem eval_mul (p q : UPoly R) (x : R) :
    eval (mul p q) x = SimpleCommRing.mul (eval p x) (eval q x) := by
  induction p with
  | nil => simp [mul, eval, SimpleCommRing.zero_mul]
  | cons a as ih =>
    simp only [mul, eval_add, eval_scale, eval, SimpleCommRing.zero_add, ih,
      SimpleCommRing.right_distrib, SimpleCommRing.mul_assoc]

/-- Polynomial power `p^n`. -/
def pow (p : UPoly R) : Nat → UPoly R
  | 0 => [SimpleCommRing.one]
  | k + 1 => mul p (pow p k)

theorem eval_pow (p : UPoly R) (n : Nat) (x : R) :
    eval (pow p n) x = SimpleCommRing.npow (eval p x) n := by
  induction n with
  | zero => simp [pow, eval, SimpleCommRing.mul_zero, SimpleCommRing.add_zero, SimpleCommRing.npow]
  | succ k ih =>
    simp only [pow, eval_mul, ih, SimpleCommRing.npow]

end UPoly

end PromislowFracton
