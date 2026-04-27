/-
  RecognitionScience.Core.LogicNat

  Mathlib-free kernel for the natural numbers recovered from the Law of
  Logic. The only primitives are an identity element and a step operator.
  Peano's axioms, addition, multiplication, the linear order, and
  well-foundedness are theorems on the inductive structure. This file
  imports nothing beyond Lean's built-in `Init` library.

  The Mathlib bridge (showing `LogicNat ≃ Nat` and that the operations
  agree) lives in a separate companion file so this kernel can be
  inspected and depended on without pulling Mathlib.
-/

namespace RecognitionScience
namespace Core

/-- The recovered natural-number object. Two constructors:
`identity` (the zero of the orbit) and `step` (one application of a
non-trivial generator). -/
inductive LogicNat : Type
  | identity : LogicNat
  | step     : LogicNat → LogicNat
  deriving DecidableEq, Repr

namespace LogicNat

/-! ## 1. Peano primitives -/

@[simp] def zero : LogicNat := .identity
@[simp] def succ (n : LogicNat) : LogicNat := .step n

/-! ## 2. Peano axioms as theorems -/

theorem zero_ne_succ (n : LogicNat) : zero ≠ succ n := by
  intro h
  cases h

theorem succ_ne_zero (n : LogicNat) : succ n ≠ zero := by
  intro h
  cases h

theorem succ_injective : Function.Injective succ := by
  intro a b h
  cases h
  rfl

theorem induction
    {motive : LogicNat → Prop}
    (h0 : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) :
    ∀ n, motive n := by
  intro n
  induction n with
  | identity => exact h0
  | step n ih => exact hs n ih

/-! ## 3. Addition -/

def add : LogicNat → LogicNat → LogicNat
  | n, .identity => n
  | n, .step m   => .step (add n m)

instance : Add LogicNat := ⟨add⟩
instance : Zero LogicNat := ⟨zero⟩
instance : One LogicNat := ⟨succ zero⟩

@[simp] theorem add_def (n m : LogicNat) : n + m = add n m := rfl
@[simp] theorem zero_def : (0 : LogicNat) = zero := rfl
@[simp] theorem one_def : (1 : LogicNat) = succ zero := rfl

@[simp] theorem add_zero (n : LogicNat) : n + zero = n := rfl

@[simp] theorem add_succ (n m : LogicNat) : n + succ m = succ (n + m) := rfl

theorem zero_add (n : LogicNat) : zero + n = n := by
  induction n with
  | identity => rfl
  | step n ih =>
    show zero + succ n = succ n
    rw [add_succ, ih]

theorem succ_add (n m : LogicNat) : succ n + m = succ (n + m) := by
  induction m with
  | identity => rfl
  | step m ih =>
    show succ n + succ m = succ (n + succ m)
    rw [add_succ, add_succ, ih]

theorem add_assoc (a b c : LogicNat) : (a + b) + c = a + (b + c) := by
  induction c with
  | identity => rfl
  | step c ih =>
    show (a + b) + succ c = a + (b + succ c)
    rw [add_succ, add_succ, add_succ, ih]

theorem add_comm (a b : LogicNat) : a + b = b + a := by
  induction b with
  | identity =>
    show a + zero = zero + a
    rw [add_zero, zero_add]
  | step b ih =>
    show a + succ b = succ b + a
    rw [add_succ, succ_add, ih]

/-! ## 4. Cancellation -/

theorem add_left_cancel {a b c : LogicNat} (h : a + b = a + c) : b = c := by
  induction a with
  | identity =>
    have h0 : zero + b = zero + c := h
    rw [zero_add, zero_add] at h0
    exact h0
  | step a ih =>
    apply ih
    have h1 : succ a + b = succ a + c := h
    rw [succ_add, succ_add] at h1
    exact succ_injective h1

theorem add_right_cancel {a b c : LogicNat} (h : a + c = b + c) : a = b := by
  rw [add_comm a c, add_comm b c] at h
  exact add_left_cancel h

/-! ## 5. Multiplication -/

def mul : LogicNat → LogicNat → LogicNat
  | _, .identity => zero
  | n, .step m   => mul n m + n

instance : Mul LogicNat := ⟨mul⟩

@[simp] theorem mul_def (n m : LogicNat) : n * m = mul n m := rfl

@[simp] theorem mul_zero (n : LogicNat) : n * zero = zero := rfl

@[simp] theorem mul_succ (n m : LogicNat) : n * succ m = n * m + n := rfl

theorem zero_mul (n : LogicNat) : zero * n = zero := by
  induction n with
  | identity => rfl
  | step n ih =>
    show zero * succ n = zero
    rw [mul_succ, ih, zero_add]

theorem mul_one (n : LogicNat) : n * succ zero = n := by
  show n * succ zero = n
  rw [mul_succ, mul_zero, zero_add]

theorem one_mul (n : LogicNat) : succ zero * n = n := by
  induction n with
  | identity => rfl
  | step n ih =>
    show succ zero * succ n = succ n
    rw [mul_succ, ih]
    show n + succ zero = succ n
    rw [add_succ, add_zero]

theorem mul_add (a b c : LogicNat) : a * (b + c) = a * b + a * c := by
  induction c with
  | identity =>
    show a * (b + zero) = a * b + a * zero
    rw [add_zero, mul_zero, add_zero]
  | step c ih =>
    show a * (b + succ c) = a * b + a * succ c
    rw [add_succ, mul_succ, mul_succ, ih, add_assoc]

theorem succ_mul (n m : LogicNat) : succ n * m = n * m + m := by
  induction m with
  | identity =>
    show succ n * zero = n * zero + zero
    rw [mul_zero, mul_zero, add_zero]
  | step m ih =>
    show succ n * succ m = n * succ m + succ m
    rw [mul_succ, mul_succ, ih, add_succ, add_succ]
    apply congrArg succ
    rw [add_assoc, add_comm m n, ← add_assoc]

theorem add_mul (a b c : LogicNat) : (a + b) * c = a * c + b * c := by
  induction c with
  | identity =>
    show (a + b) * zero = a * zero + b * zero
    rw [mul_zero, mul_zero, mul_zero, add_zero]
  | step c ih =>
    show (a + b) * succ c = a * succ c + b * succ c
    rw [mul_succ, mul_succ, mul_succ, ih, add_assoc, add_assoc]
    have : b * c + (a + b) = a + (b * c + b) := by
      rw [← add_assoc, add_comm (b * c) a, add_assoc]
    rw [this]

theorem mul_assoc (a b c : LogicNat) : (a * b) * c = a * (b * c) := by
  induction c with
  | identity => rfl
  | step c ih =>
    show (a * b) * succ c = a * (b * succ c)
    rw [mul_succ, ih, mul_succ, mul_add]

theorem mul_comm (a b : LogicNat) : a * b = b * a := by
  induction b with
  | identity =>
    show a * zero = zero * a
    rw [mul_zero, zero_mul]
  | step b ih =>
    show a * succ b = succ b * a
    rw [mul_succ, succ_mul, ih]

/-! ## 6. Order via the existential Peano definition -/

/-- Non-strict order: `n ≤ m` iff there exists `k` with `n + k = m`. -/
def le (n m : LogicNat) : Prop := ∃ k : LogicNat, n + k = m

/-- Strict order: `n < m` iff there exists `k` with `n + succ k = m`. -/
def lt (n m : LogicNat) : Prop := ∃ k : LogicNat, n + succ k = m

instance : LE LogicNat := ⟨le⟩
instance : LT LogicNat := ⟨lt⟩

@[simp] theorem le_def (n m : LogicNat) : n ≤ m ↔ ∃ k, n + k = m := Iff.rfl
@[simp] theorem lt_def (n m : LogicNat) : n < m ↔ ∃ k, n + succ k = m := Iff.rfl

theorem le_refl (n : LogicNat) : n ≤ n := ⟨zero, add_zero n⟩

theorem zero_le (n : LogicNat) : zero ≤ n := ⟨n, zero_add n⟩

theorem le_trans {a b c : LogicNat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  obtain ⟨k1, hk1⟩ := hab
  obtain ⟨k2, hk2⟩ := hbc
  refine ⟨k1 + k2, ?_⟩
  rw [← add_assoc, hk1, hk2]

theorem le_succ (n : LogicNat) : n ≤ succ n :=
  ⟨succ zero, by show n + succ zero = succ n; rw [add_succ, add_zero]⟩

theorem zero_lt_succ (n : LogicNat) : zero < succ n :=
  ⟨n, by show zero + succ n = succ n; rw [zero_add]⟩

theorem lt_iff_succ_le {n m : LogicNat} : n < m ↔ succ n ≤ m := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    show succ n + k = m
    rw [succ_add]
    show succ (n + k) = m
    rw [← add_succ]
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    show n + succ k = m
    rw [add_succ]
    show succ (n + k) = m
    rw [← succ_add]
    exact hk

theorem lt_irrefl (n : LogicNat) : ¬ n < n := by
  rintro ⟨k, hk⟩
  -- n + succ k = n. Apply to get k = ?
  have : n + succ k = n + zero := by rw [add_zero]; exact hk
  have hk' := add_left_cancel this
  exact succ_ne_zero k hk'

theorem lt_trans {a b c : LogicNat} (hab : a < b) (hbc : b < c) : a < c := by
  rw [lt_iff_succ_le] at hab hbc ⊢
  exact le_trans hab (le_trans (le_succ b) hbc)

theorem le_antisymm {a b : LogicNat} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  obtain ⟨k1, hk1⟩ := hab
  obtain ⟨k2, hk2⟩ := hba
  -- a + k1 = b, b + k2 = a, so a + (k1 + k2) = a, so k1 + k2 = 0.
  have hsum : a + (k1 + k2) = a + zero := by
    rw [add_zero, ← add_assoc, hk1, hk2]
  have hk : k1 + k2 = zero := add_left_cancel hsum
  -- k1 + k2 = 0 implies k1 = 0.
  have hk1z : k1 = zero := by
    cases k1 with
    | identity => rfl
    | step k1' =>
      exfalso
      have hsum' : succ k1' + k2 = zero := hk
      rw [succ_add] at hsum'
      exact succ_ne_zero (k1' + k2) hsum'
  -- Use k1 = 0 to conclude a = b.
  rw [hk1z] at hk1
  have hk1' : a + zero = b := hk1
  rw [add_zero] at hk1'
  exact hk1'

theorem succ_le_succ {a b : LogicNat} (h : a ≤ b) : succ a ≤ succ b := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  show succ a + k = succ b
  rw [succ_add, hk]

/-! ## 7. Strong induction (well-foundedness) -/

theorem strongInduction
    {motive : LogicNat → Prop}
    (h : ∀ n, (∀ m, m < n → motive m) → motive n) :
    ∀ n, motive n := by
  intro n
  -- Prove by ordinary induction on `n` that all `m ≤ n` satisfy the motive.
  suffices key : ∀ n, ∀ m, m ≤ n → motive m by
    exact key n n (le_refl n)
  intro n
  induction n with
  | identity =>
    intro m hm
    obtain ⟨k, hk⟩ := hm
    have hk0 : m + k = zero := hk
    have hmz : m = zero := by
      cases m with
      | identity => rfl
      | step m' =>
        exfalso
        have hsum' : succ m' + k = zero := hk0
        rw [succ_add] at hsum'
        exact succ_ne_zero (m' + k) hsum'
    rw [hmz]
    apply h
    intro m' hm'
    exfalso
    obtain ⟨k', hkk⟩ := hm'
    -- hkk : m' + succ k' = zero, definitionally succ (m' + k') = zero.
    exact succ_ne_zero (m' + k') hkk
  | step n ih =>
    intro m hm
    -- m ≤ succ n, so either m = succ n or m ≤ n (i.e. m < succ n).
    obtain ⟨k, hk⟩ := hm
    cases k with
    | identity =>
      -- m + identity = succ n, so m = succ n.
      have hkz : m + zero = succ n := hk
      have hmsucc : m = succ n := by rw [add_zero] at hkz; exact hkz
      rw [hmsucc]
      apply h
      intro m' hm'
      apply ih
      rw [lt_iff_succ_le] at hm'
      obtain ⟨k', hk'⟩ := hm'
      -- succ m' + k' = succ n
      rw [succ_add] at hk'
      have : succ (m' + k') = succ n := hk'
      have heq : m' + k' = n := succ_injective this
      exact ⟨k', heq⟩
    | step k' =>
      apply ih
      have hk2 : m + succ k' = succ n := hk
      have hkS : succ (m + k') = succ n := by
        rw [← add_succ]; exact hk2
      have heq : m + k' = n := succ_injective hkS
      exact ⟨k', heq⟩

end LogicNat

end Core
end RecognitionScience
