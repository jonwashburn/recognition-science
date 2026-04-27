import Mathlib
import RecognitionScience.Core.LogicInt
import RecognitionScience.Core.Bridge.MathlibNat

/-!
  RecognitionScience.Core.Bridge.MathlibInt

  Mathlib bridge for the Mathlib-free `Core.LogicInt` kernel.

  The kernel itself only provides the carrier and the additive
  abelian-group structure. This bridge transports a recovered integer
  to Mathlib's `Int` via the `Core.LogicNat`-to-`Nat` bridge, and
  proves the basic transport equalities for zero, one, addition, and
  negation.
-/

namespace RecognitionScience
namespace Core
namespace LogicInt

open LogicNat

/-- Map a pre-integer pair to its Mathlib `Int` value. -/
def toIntCore : LogicNat × LogicNat → Int :=
  fun p => (toNat p.1 : Int) - (toNat p.2 : Int)

theorem toIntCore_respects :
    ∀ p q : LogicNat × LogicNat, p ≈ q → toIntCore p = toIntCore q := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  show (toNat a : Int) - toNat b = (toNat c : Int) - toNat d
  have hcast := congrArg toNat (show a + d = c + b from h)
  rw [toNat_add, toNat_add] at hcast
  have : (toNat a : Int) + toNat d = (toNat c : Int) + toNat b := by exact_mod_cast hcast
  linarith

/-- Forget a recovered integer to Lean's `Int`. -/
def toInt : LogicInt → Int := Quotient.lift toIntCore toIntCore_respects

/-- Lift a Lean `Int` into the recovered integers. -/
def fromInt : Int → LogicInt
  | Int.ofNat n   => mk (LogicNat.fromNat n) LogicNat.zero
  | Int.negSucc n => mk LogicNat.zero (LogicNat.fromNat (Nat.succ n))

@[simp] theorem toInt_mk (a b : LogicNat) :
    toInt (mk a b) = (toNat a : Int) - toNat b := rfl

theorem toInt_zero : toInt (0 : LogicInt) = 0 := by
  show toInt (mk LogicNat.zero LogicNat.zero) = 0
  rw [toInt_mk]
  simp [toNat_zero]

theorem toInt_one : toInt (1 : LogicInt) = 1 := by
  show toInt (mk (LogicNat.succ LogicNat.zero) LogicNat.zero) = 1
  rw [toInt_mk, toNat_succ, toNat_zero]
  norm_num

theorem toInt_add (a b : LogicInt) : toInt (a + b) = toInt a + toInt b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      rcases p with ⟨a, b⟩
      rcases q with ⟨c, d⟩
      show toInt (mk (a + c) (b + d)) = toInt (mk a b) + toInt (mk c d)
      rw [toInt_mk, toInt_mk, toInt_mk]
      rw [toNat_add, toNat_add]
      push_cast
      ring

theorem toInt_neg (a : LogicInt) : toInt (-a) = -toInt a := by
  induction a using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨a, b⟩
    show toInt (mk b a) = -toInt (mk a b)
    rw [toInt_mk, toInt_mk]
    ring

theorem toInt_fromInt : ∀ n : Int, toInt (fromInt n) = n := by
  intro n
  cases n with
  | ofNat n =>
    show toInt (mk (LogicNat.fromNat n) LogicNat.zero) = (Int.ofNat n)
    rw [toInt_mk, toNat_fromNat, toNat_zero]
    simp [Int.ofNat]
  | negSucc n =>
    show toInt (mk LogicNat.zero (LogicNat.fromNat (Nat.succ n))) = Int.negSucc n
    rw [toInt_mk, toNat_zero, toNat_fromNat]
    simp [Int.negSucc_eq]

end LogicInt
end Core
end RecognitionScience
