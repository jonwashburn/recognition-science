import RecognitionScience.Core.LogicNat
import RecognitionScience.Core.LogicInt
import RecognitionScience.Core.LogicRat

/-!
  RecognitionScience.Core

  Mathlib-free arithmetic kernel for Recognition Science.

  The three modules below import nothing beyond Lean's `Init` library:

    * `RecognitionScience.Core.LogicNat` — recovered natural numbers
      with full Peano structure, addition, multiplication, order,
      cancellation, and strong induction.
    * `RecognitionScience.Core.LogicInt` — recovered integers as the
      Grothendieck completion of `LogicNat`, with the additive
      abelian-group structure (zero, addition, negation, identities).
    * `RecognitionScience.Core.LogicRat` — recovered rationals at the
      carrier level (numerator/denominator with non-zero denominator),
      with zero, one, and the embedding of `LogicInt`.

  Multiplication on `LogicInt`, the full ring/field laws on `LogicRat`,
  the Cauchy completion to `LogicReal`, and analytic transcendentals
  remain in the Mathlib-backed companion modules under `Foundation/`.
  Mathlib bridges proving carrier equivalence with Lean's `Nat`,
  `Int`, and `Rat` live under `RecognitionScience.Core.Bridge`.
-/

namespace RecognitionScience
namespace Core

end Core
end RecognitionScience
