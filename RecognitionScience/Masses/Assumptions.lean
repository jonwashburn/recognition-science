import Mathlib

namespace RecognitionScience
namespace Masses

/-!
# Masses Assumptions (Model Layer)

Centralises phenomenological assumptions used by the masses modules. These
predicates are intentionally lightweight and sit in the `Model` portion of the
codebase.

Definitions
* `mass_ladder_assumption` – current placeholder for the ladder audit.
* `sterile_exclusion_assumption` – imported from physics (surrogate).

See `docs/Assumptions.md` §Masses for context.
-/

open RecognitionScience

/-- Pending surrogate: imported measurements already satisfy the ladder bound. -/
noncomputable def mass_ladder_assumption : Prop :=
  ∀ m ∈ Data.import_measurements,
    |m.value - Constants.phi ^ Basic.rung_exponent m.name| ≤ m.error

/-- Alias for the physics-side sterile exclusion assumption. -/
abbrev sterile_exclusion_assumption : Prop :=
  Physics.sterile_exclusion_assumption

end Masses
end RecognitionScience
