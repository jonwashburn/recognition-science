import Mathlib
import IndisputableMonolith.RecogSpec.Spec
import IndisputableMonolith.RecogSpec.RSCompliance

/-!
# MatchesEval Certificate (computed matching, non-existential)

This certificate packages two matching results:

1. **Legacy lane**: `dimlessPack_explicit` matches `UD_explicit` for all ledger/bridge.
   This is the audit surface.
2. **Structural lane**: `dimlessPack_fromStructure` reads from structure and,
   for the canonical RS-compliant pair, the alpha field agrees with the legacy target.
-/

namespace IndisputableMonolith
namespace Verification
namespace MatchesEval

open IndisputableMonolith.RecogSpec

structure MatchesEvalCert where
  deriving Repr

@[simp] def MatchesEvalCert.verified (_c : MatchesEvalCert) : Prop :=
  (∀ (φ : ℝ) (L : RecogSpec.Ledger) (B : RecogSpec.Bridge L),
    RecogSpec.MatchesEval φ L B (RecogSpec.UD_explicit φ)) ∧
  (∀ (L : RSLedger) (B : RSBridge L),
    (dimlessPack_fromStructure Constants.phi L B).alpha = B.alphaExponent) ∧
  RSCompliant Constants.phi canonicalRSLedger (canonicalRSBridge canonicalRSLedger)

@[simp] theorem MatchesEvalCert.verified_any (c : MatchesEvalCert) :
    MatchesEvalCert.verified c := by
  refine ⟨?legacy, ?structural, ?compliant⟩
  · intro φ L B; exact RecogSpec.matchesEval_explicit φ L B
  · intro L B; exact derivation_uses_structure_alpha L B
  · exact canonical_is_compliant

end MatchesEval
end Verification
end IndisputableMonolith
