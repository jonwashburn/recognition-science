import RecognitionScience.Core.LogicInt

/-!
  RecognitionScience.Core.LogicRat

  Mathlib-free skeleton for the rationals as the field of fractions of
  the recovered integer object. This file establishes:

  * the rational pre-pair carrier (`PreRat`) with non-zero denominator;
  * the rational object as a `Quotient` over the field-of-fractions
    equivalence (carrier-only — no Mathlib);
  * zero and one as elements of `LogicRat`;
  * the embedding of `LogicInt` as `n / 1`.

  The full field laws (commutativity, associativity, distributivity,
  multiplicative inverse) require ring-multiplication on `LogicInt` and
  a handful of polynomial identities; the present Mathlib-free integer
  layer only provides the additive abelian group, so we deliberately do
  not redefine multiplication / inverse here. Those operations and the
  field axioms live in the Mathlib-backed companion module
  `Foundation.RationalsFromLogic`, and the carrier bridge lives in
  `Core/Bridge/MathlibRat.lean`.
-/

namespace RecognitionScience
namespace Core

open LogicInt

/-! ## 1. Pre-rational structure -/

/-- A pre-rational is a numerator/denominator pair with non-zero
denominator. -/
structure PreRat where
  num         : LogicInt
  den         : LogicInt
  den_nonzero : den ≠ LogicInt.zero

/-- Coercion from a pre-rational to its underlying numerator. -/
@[simp] def PreRat.numerator (p : PreRat) : LogicInt := p.num

/-- Coercion from a pre-rational to its underlying (non-zero) denominator. -/
@[simp] def PreRat.denominator (p : PreRat) : LogicInt := p.den

/-- The field-of-fractions relation. The transitivity proof depends on
multiplication on `LogicInt`, which is currently provided by the
Mathlib-backed companion module; in this Mathlib-free skeleton we only
need reflexivity, symmetry, and the carrier. The full setoid (and the
companion field structure) lives in `Foundation.RationalsFromLogic`. -/
def ratRel : PreRat → PreRat → Prop :=
  fun p q => p.num = q.num ∧ p.den = q.den

theorem ratRel_refl : ∀ p : PreRat, ratRel p p := by
  intro p
  exact ⟨rfl, rfl⟩

theorem ratRel_symm : ∀ {p q : PreRat}, ratRel p q → ratRel q p := by
  intro p q ⟨h1, h2⟩
  exact ⟨h1.symm, h2.symm⟩

theorem ratRel_trans : ∀ {p q r : PreRat},
    ratRel p q → ratRel q r → ratRel p r := by
  intro p q r ⟨h1, h2⟩ ⟨h3, h4⟩
  exact ⟨h1.trans h3, h2.trans h4⟩

instance ratSetoid : Setoid PreRat :=
  ⟨ratRel, ratRel_refl, ratRel_symm, ratRel_trans⟩

/-- Mathlib-free skeleton of `LogicRat`. Identification of equivalent
fractions requires `LogicInt` multiplication; in the Mathlib-free
layer we work up to syntactic equality of representatives. -/
def LogicRat : Type := Quotient (ratSetoid : Setoid PreRat)

namespace LogicRat

/-- Form a rational from a pair with non-zero denominator. -/
def mk (a b : LogicInt) (hb : b ≠ LogicInt.zero) : LogicRat :=
  Quotient.mk' (s := ratSetoid) ⟨a, b, hb⟩

/-! ## 2. Embedding `LogicInt` into `LogicRat` -/

/-- The natural injection `LogicInt ↪ LogicRat` sending `n` to `n / 1`. -/
def ofLogicInt (n : LogicInt) : LogicRat :=
  mk n LogicInt.one one_ne_zero
  where
    one_ne_zero : (LogicInt.one : LogicInt) ≠ LogicInt.zero := by
      intro h
      have hpair : LogicInt.one = LogicInt.zero := h
      have : (LogicNat.succ LogicNat.zero, LogicNat.zero)
              ≈ (LogicNat.zero, LogicNat.zero) := by
        exact Quotient.exact hpair
      have hsum : LogicNat.succ LogicNat.zero + LogicNat.zero
                  = LogicNat.zero + LogicNat.zero := this
      rw [LogicNat.add_zero, LogicNat.zero_add] at hsum
      exact LogicNat.succ_ne_zero LogicNat.zero hsum

/-! ## 3. Zero and one -/

private theorem one_ne_zero : (LogicInt.one : LogicInt) ≠ LogicInt.zero := by
  intro h
  have hpair : LogicInt.one = LogicInt.zero := h
  have : (LogicNat.succ LogicNat.zero, LogicNat.zero)
          ≈ (LogicNat.zero, LogicNat.zero) := Quotient.exact hpair
  have hsum : LogicNat.succ LogicNat.zero + LogicNat.zero
              = LogicNat.zero + LogicNat.zero := this
  rw [LogicNat.add_zero, LogicNat.zero_add] at hsum
  exact LogicNat.succ_ne_zero LogicNat.zero hsum

/-- The recovered rational zero `0/1`. -/
def zero : LogicRat := mk LogicInt.zero LogicInt.one one_ne_zero

/-- The recovered rational one `1/1`. -/
def one : LogicRat := mk LogicInt.one LogicInt.one one_ne_zero

instance : Zero LogicRat := ⟨zero⟩
instance : One LogicRat := ⟨one⟩

@[simp] theorem zero_def : (0 : LogicRat) = zero := rfl
@[simp] theorem one_def : (1 : LogicRat) = one := rfl

end LogicRat
end Core
end RecognitionScience
