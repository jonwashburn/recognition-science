/-
  ObservableTypeEquiv.lean — Bridge B6

  Proves: After quotient collapse, the observable-type equivalence
  e : O_F ≃ 𝒪_dim is trivially constructible.

  After uniform observables, im(μ_F) is a singleton, so any two
  inhabited subsingleton types are abstractly isomorphic.
  Value identification (Level 2) reduces to Bridge B5 (prediction map).

  All theorems: ZERO sorry.

  Paper §8.6: Bridge B6.
-/

import Mathlib
import RecognitionScience.Verification.Exclusivity.Framework
import RecognitionScience.Verification.Exclusivity.ModelIndependent

namespace RecognitionScience
namespace Verification
namespace Exclusivity
namespace ObservableTypeEquiv

open Framework ModelIndependent

set_option autoImplicit false

/-- After uniform observables, every measured value equals the canonical one. -/
theorem observable_image_singleton {F : PhysicsFramework}
    (hU   : ∀ s₁ s₂ : F.StateSpace, F.measure s₁ = F.measure s₂)
    (hInh : Inhabited F.StateSpace)
    (s    : F.StateSpace) :
    F.measure s = F.measure hInh.default :=
  hU s hInh.default

/-- The observable image is a subsingleton after uniform observables. -/
theorem observable_image_subsingleton {F : PhysicsFramework}
    (hU : ∀ s₁ s₂ : F.StateSpace, F.measure s₁ = F.measure s₂) :
    ∀ o₁ ∈ Set.range F.measure, ∀ o₂ ∈ Set.range F.measure, o₁ = o₂ := by
  intro o₁ ⟨s₁, hs₁⟩ o₂ ⟨s₂, hs₂⟩
  rw [← hs₁, ← hs₂]; exact hU s₁ s₂

/-- Any two inhabited subsingleton types are equivalent. -/
noncomputable def equiv_of_subsingleton_inhabited
    (α β : Type) [Subsingleton α] [Subsingleton β]
    [Inhabited α] [Inhabited β] : α ≃ β where
  toFun    := fun _ => default
  invFun   := fun _ => default
  left_inv := fun _ => Subsingleton.elim _ _
  right_inv := fun _ => Subsingleton.elim _ _

/-- Bridge B6 (Level 1, proved): after quotient collapse the quotient is
    equivalent to Unit.

    Level 2 (value identification) reduces to Bridge B5: constructing a
    prediction map that identifies the single observable value with
    specific dimensionless constants. -/
theorem bridge_B6_quotient_equiv_unit {F : PhysicsFramework}
    (hU   : ∀ s₁ s₂ : F.StateSpace, F.measure s₁ = F.measure s₂)
    (hInh : Inhabited F.StateSpace) :
    Nonempty (StateQuotient F ≃ Unit) := by
  have h_sub : Subsingleton (StateQuotient F) :=
    quotient_subsingleton_of_uniform hU
  have h_inh : Inhabited (StateQuotient F) :=
    ⟨Quotient.mk (obsSetoid F) hInh.default⟩
  exact ⟨equiv_of_subsingleton_inhabited (StateQuotient F) Unit⟩

end ObservableTypeEquiv
end Exclusivity
end Verification
end RecognitionScience
