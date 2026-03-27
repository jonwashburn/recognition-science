/-
  Framework.lean — Core framework definitions for the exclusivity programme.

  Defines PhysicsFramework, observational equivalence, the quotient state
  space, and the zero-parameter predicate.

  These are the foundational types that every exclusivity module uses.
-/

import Mathlib
import RecognitionScience.Constants

namespace RecognitionScience
namespace Verification
namespace Exclusivity
namespace Framework

set_option autoImplicit false

/-- Abstract interface for any physics framework.
    Deliberately minimal: no topology, no action, no coordinates. -/
structure PhysicsFramework where
  StateSpace  : Type
  evolve      : StateSpace → StateSpace
  Observable  : Type
  measure     : StateSpace → Observable
  hasInitialState : Nonempty StateSpace

/-- A set admits an algorithmic specification if it can be enumerated
    by a finite description + decoder, covering every element. -/
def HasAlgorithmicSpec (StateSpace : Type) : Prop :=
  ∃ (desc   : List Bool)
    (enum   : ℕ → Option (List Bool))
    (decode : List Bool → Option StateSpace),
    ∀ s : StateSpace, ∃ n c, enum n = some c ∧ decode c = some s

/-- A framework has zero parameters if its state space admits an
    algorithmic specification (no tunable real constants). -/
def HasZeroParameters (F : PhysicsFramework) : Prop :=
  HasAlgorithmicSpec F.StateSpace

/-- Observational equivalence: two states are equivalent iff they yield
    the same measured output. -/
def ObsEquiv (F : PhysicsFramework) (s₁ s₂ : F.StateSpace) : Prop :=
  F.measure s₁ = F.measure s₂

theorem obsEquiv_isEquiv (F : PhysicsFramework) :
    Equivalence (ObsEquiv F) where
  refl  := fun _   => rfl
  symm  := fun h   => h.symm
  trans := fun h k => h.trans k

/-- Setoid instance for the observational equivalence. -/
def obsSetoid (F : PhysicsFramework) : Setoid F.StateSpace where
  r    := ObsEquiv F
  iseqv := obsEquiv_isEquiv F

/-- The quotient state space: states modulo observational indistinguishability. -/
def StateQuotient (F : PhysicsFramework) : Type :=
  Quotient (obsSetoid F)

/-- Uniform observables imply quotient collapse (the key lemma). -/
theorem quotient_subsingleton_of_uniform {F : PhysicsFramework}
    (h : ∀ s₁ s₂ : F.StateSpace, F.measure s₁ = F.measure s₂) :
    Subsingleton (StateQuotient F) where
  allEq q₁ q₂ := by
    obtain ⟨a, ha⟩ := Quotient.exists_rep q₁
    obtain ⟨b, hb⟩ := Quotient.exists_rep q₂
    rw [← ha, ← hb]
    apply Quotient.sound
    exact h a b

end Framework
end Exclusivity
end Verification
end RecognitionScience
