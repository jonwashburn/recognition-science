import Mathlib
import RecognitionScience.Core.LogicNat

/-!
  RecognitionScience.Core.Bridge.MathlibNat

  Mathlib bridge for the Mathlib-free `Core.LogicNat` kernel.

  The kernel itself is in `RecognitionScience/Core/LogicNat.lean` and
  imports nothing beyond Lean's `Init`. This bridge proves the carrier
  equivalence with Mathlib's `Nat` and shows that addition, multiplication,
  and the Peano order on `Core.LogicNat` agree with the corresponding
  operations on `Nat` under the equivalence.
-/

namespace RecognitionScience
namespace Core
namespace LogicNat

/-- Forget a recovered natural number to Lean's `Nat`. -/
def toNat : LogicNat → Nat
  | .identity => 0
  | .step n   => Nat.succ (toNat n)

/-- Build a recovered natural number from Lean's `Nat`. -/
def fromNat : Nat → LogicNat
  | 0          => .identity
  | Nat.succ n => .step (fromNat n)

@[simp] theorem toNat_zero : toNat zero = 0 := rfl
@[simp] theorem toNat_succ (n : LogicNat) : toNat (succ n) = Nat.succ (toNat n) := rfl
@[simp] theorem fromNat_zero : fromNat 0 = zero := rfl
@[simp] theorem fromNat_succ (n : Nat) : fromNat (Nat.succ n) = succ (fromNat n) := rfl

theorem fromNat_toNat : ∀ n : LogicNat, fromNat (toNat n) = n := by
  intro n
  induction n with
  | identity => rfl
  | step n ih =>
    show fromNat (toNat (succ n)) = succ n
    rw [toNat_succ, fromNat_succ, ih]

theorem toNat_fromNat : ∀ n : Nat, toNat (fromNat n) = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show toNat (fromNat (Nat.succ n)) = Nat.succ n
    rw [fromNat_succ, toNat_succ, ih]

/-- Carrier equivalence between recovered naturals and Mathlib `Nat`. -/
def equivNat : LogicNat ≃ Nat where
  toFun := toNat
  invFun := fromNat
  left_inv := fromNat_toNat
  right_inv := toNat_fromNat

theorem toNat_add (a b : LogicNat) :
    toNat (a + b) = toNat a + toNat b := by
  induction b with
  | identity =>
    show toNat (a + zero) = toNat a + toNat zero
    rw [add_zero, toNat_zero, Nat.add_zero]
  | step b ih =>
    show toNat (a + succ b) = toNat a + toNat (succ b)
    rw [add_succ, toNat_succ, toNat_succ, ih, Nat.add_succ]

theorem toNat_mul (a b : LogicNat) :
    toNat (a * b) = toNat a * toNat b := by
  induction b with
  | identity =>
    show toNat (a * zero) = toNat a * toNat zero
    rw [mul_zero, toNat_zero, Nat.mul_zero]
  | step b ih =>
    show toNat (a * succ b) = toNat a * toNat (succ b)
    rw [mul_succ, toNat_succ, toNat_add, ih, Nat.mul_succ]

theorem toNat_le (a b : LogicNat) : a ≤ b ↔ toNat a ≤ toNat b := by
  constructor
  · rintro ⟨k, hk⟩
    have := congrArg toNat hk
    rw [toNat_add] at this
    omega
  · intro h
    refine ⟨fromNat (toNat b - toNat a), ?_⟩
    have hadd : toNat (a + fromNat (toNat b - toNat a)) = toNat b := by
      rw [toNat_add, toNat_fromNat]
      omega
    have h1 := congrArg fromNat hadd
    rw [fromNat_toNat, fromNat_toNat] at h1
    exact h1

theorem toNat_lt (a b : LogicNat) : a < b ↔ toNat a < toNat b := by
  rw [lt_iff_succ_le, toNat_le]
  constructor
  · intro h
    rw [toNat_succ] at h
    omega
  · intro h
    rw [toNat_succ]
    omega

end LogicNat
end Core
end RecognitionScience
