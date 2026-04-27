import RecognitionScience.Core.LogicNat

/-!
  RecognitionScience.Core.LogicInt

  Mathlib-free additive kernel for the integers as the Grothendieck
  completion of the recovered natural-number object.  This file
  establishes the integer carrier and the additive abelian-group
  structure (zero, addition, negation) by induction on `LogicNat`,
  using only Lean's `Init`-level quotient machinery.  No Mathlib
  import.

  Multiplicative ring structure and the equivalence with Lean's `Int`
  live in companion modules: `Foundation/IntegersFromLogic.lean` (full
  ring through Mathlib) and `Core/Bridge/MathlibInt.lean` (carrier
  bridge to Mathlib's `Int`).

  Keeping the additive layer separate means the Grothendieck step is
  Mathlib-free; the field-level proof obligations of multiplication
  (well-definedness up to the Grothendieck equivalence) can stay in
  the bridge layer until we add a manual ring-law normalizer for
  `LogicNat`.
-/

namespace RecognitionScience
namespace Core

open LogicNat

/-! ## 1. The Grothendieck equivalence -/

def intRel : (LogicNat × LogicNat) → (LogicNat × LogicNat) → Prop :=
  fun p q => p.1 + q.2 = q.1 + p.2

theorem intRel_refl : ∀ p : LogicNat × LogicNat, intRel p p := by
  intro p
  show p.1 + p.2 = p.1 + p.2
  rfl

theorem intRel_symm : ∀ {p q : LogicNat × LogicNat},
    intRel p q → intRel q p := by
  intro p q h
  show q.1 + p.2 = p.1 + q.2
  exact h.symm

theorem intRel_trans : ∀ {p q r : LogicNat × LogicNat},
    intRel p q → intRel q r → intRel p r := by
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ hpq hqr
  show a + f = e + b
  have key : (a + f) + d = (e + b) + d := by
    rw [add_assoc, add_comm f d, ← add_assoc, hpq]
    rw [add_assoc, add_comm b f, ← add_assoc, hqr]
    rw [add_assoc, add_comm d b, ← add_assoc]
  exact add_right_cancel key

instance setoid : Setoid (LogicNat × LogicNat) :=
  ⟨intRel, intRel_refl, intRel_symm, intRel_trans⟩

/-! ## 2. The integer object -/

def LogicInt : Type := Quotient (setoid : Setoid (LogicNat × LogicNat))

namespace LogicInt

def mk (a b : LogicNat) : LogicInt := Quotient.mk' (a, b)

theorem sound (a b c d : LogicNat) (h : a + d = c + b) :
    mk a b = mk c d := by
  apply Quotient.sound
  show a + d = c + b
  exact h

/-! ## 3. Embedding LogicNat into LogicInt -/

def ofLogicNat (n : LogicNat) : LogicInt := mk n LogicNat.zero

@[simp] theorem ofLogicNat_zero :
    ofLogicNat LogicNat.zero = mk LogicNat.zero LogicNat.zero := rfl

/-! ## 4. Zero, one, negation, addition -/

def zero : LogicInt := mk LogicNat.zero LogicNat.zero
def one : LogicInt := mk (LogicNat.succ LogicNat.zero) LogicNat.zero

instance : Zero LogicInt := ⟨zero⟩
instance : One LogicInt := ⟨one⟩

def neg : LogicInt → LogicInt :=
  Quotient.lift (fun (p : LogicNat × LogicNat) => mk p.2 p.1) (by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    show mk b a = mk d c
    apply sound
    show b + c = d + a
    have h1 : b + c = c + b := add_comm b c
    have h2 : c + b = a + d := h.symm
    have h3 : a + d = d + a := add_comm a d
    exact h1.trans (h2.trans h3))

instance : Neg LogicInt := ⟨neg⟩

/-- Helper: rearrangement of four sums used for addition well-definedness. -/
private theorem four_swap (a b c d : LogicNat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [add_assoc, ← add_assoc b c d, add_comm b c, add_assoc c b d]
  exact (add_assoc a c (b + d)).symm

def add : LogicInt → LogicInt → LogicInt :=
  Quotient.lift₂
    (fun (p q : LogicNat × LogicNat) => mk (p.1 + q.1) (p.2 + q.2))
    (by
      rintro ⟨a, b⟩ ⟨c, d⟩ ⟨a', b'⟩ ⟨c', d'⟩ hab hcd
      -- hab : a + b' = a' + b
      -- hcd : c + d' = c' + d
      show mk (a + c) (b + d) = mk (a' + c') (b' + d')
      apply sound
      show (a + c) + (b' + d') = (a' + c') + (b + d)
      -- Rearrange both sides to (a + b') + (c + d') vs (a' + b) + (c' + d).
      have lhs_eq : (a + c) + (b' + d') = (a + b') + (c + d') := four_swap a c b' d'
      have rhs_eq : (a' + c') + (b + d) = (a' + b) + (c' + d) := four_swap a' c' b d
      rw [lhs_eq, rhs_eq, hab, hcd])

instance : Add LogicInt := ⟨add⟩

@[simp] theorem add_def (x y : LogicInt) : x + y = add x y := rfl
@[simp] theorem zero_def : (0 : LogicInt) = zero := rfl
@[simp] theorem one_def : (1 : LogicInt) = one := rfl

@[simp] theorem mk_add (a b c d : LogicNat) :
    mk a b + mk c d = mk (a + c) (b + d) := rfl

@[simp] theorem mk_neg (a b : LogicNat) :
    -(mk a b) = mk b a := rfl

/-! ## 5. Additive abelian-group laws on `LogicInt` -/

theorem add_comm' (x y : LogicInt) : x + y = y + x := by
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      rcases p with ⟨a, b⟩
      rcases q with ⟨c, d⟩
      show mk (a + c) (b + d) = mk (c + a) (d + b)
      apply sound
      show (a + c) + (d + b) = (c + a) + (b + d)
      rw [add_comm a c, add_comm d b, add_comm b d]

theorem add_assoc' (x y z : LogicInt) : (x + y) + z = x + (y + z) := by
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      induction z using Quotient.inductionOn with
      | h r =>
        rcases p with ⟨a, b⟩
        rcases q with ⟨c, d⟩
        rcases r with ⟨e, f⟩
        show mk ((a + c) + e) ((b + d) + f) = mk (a + (c + e)) (b + (d + f))
        apply sound
        show ((a + c) + e) + (b + (d + f)) = (a + (c + e)) + ((b + d) + f)
        rw [add_assoc a c e, add_assoc b d f]

theorem zero_add' (x : LogicInt) : (0 : LogicInt) + x = x := by
  induction x using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨a, b⟩
    show mk (LogicNat.zero + a) (LogicNat.zero + b) = mk a b
    apply sound
    show (LogicNat.zero + a) + b = a + (LogicNat.zero + b)
    rw [zero_add, zero_add]

theorem add_zero' (x : LogicInt) : x + (0 : LogicInt) = x := by
  rw [add_comm', zero_add']

theorem add_left_neg' (x : LogicInt) : -x + x = 0 := by
  induction x using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨a, b⟩
    show mk (b + a) (a + b) = mk LogicNat.zero LogicNat.zero
    apply sound
    show (b + a) + LogicNat.zero = LogicNat.zero + (a + b)
    rw [add_zero, zero_add, add_comm]

theorem add_right_neg' (x : LogicInt) : x + (-x) = 0 := by
  rw [add_comm', add_left_neg']

theorem neg_zero' : -(0 : LogicInt) = 0 := by
  show mk LogicNat.zero LogicNat.zero = mk LogicNat.zero LogicNat.zero
  rfl

theorem neg_neg' (x : LogicInt) : -(-x) = x := by
  induction x using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨a, b⟩
    show mk a b = mk a b
    rfl

end LogicInt
end Core
end RecognitionScience
