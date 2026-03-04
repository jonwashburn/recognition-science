import Mathlib
-- import RecognitionScience.Patterns  -- [not in public release]

/-!
# Eight-Tick Lower Bound Certificate

This audit certificate packages the **minimality** half of the eight-tick story:

> Any complete cover of 3-bit patterns must have period at least 8.

Together with the existing existence witness (`Patterns.period_exactly_8` / `RecogSpec.eightTickWitness`),
this prevents “8 ticks” from being a merely convenient example: it is *minimal* by counting.
-/

namespace RecognitionScience
namespace Verification
namespace EightTickLowerBound

structure EightTickLowerBoundCert where
  deriving Repr

@[simp] def EightTickLowerBoundCert.verified (_c : EightTickLowerBoundCert) : Prop :=
  ∀ w : RecognitionScience.Patterns.CompleteCover 3, 8 ≤ w.period

@[simp] theorem EightTickLowerBoundCert.verified_any (c : EightTickLowerBoundCert) :
    EightTickLowerBoundCert.verified c := by
  intro w
  -- `w.path : Fin w.period → Pattern 3` and `w.complete : Surjective w.path`
  simpa using
    (RecognitionScience.Patterns.eight_tick_min (T := w.period) w.path w.complete)

end EightTickLowerBound
end Verification
end RecognitionScience

