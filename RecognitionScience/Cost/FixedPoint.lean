import Mathlib
import RecognitionScience.Constants
-- import RecognitionScience.PhiSupport  -- [not in public release]

namespace RecognitionScience
namespace Cost

/-- Canonical lemma: φ is the positive solution of x = 1 + 1/x. -/
lemma phi_is_cost_fixed_point : Constants.phi = 1 + 1 / Constants.phi := by
  simpa using RecognitionScience.PhiSupport.phi_fixed_point

end Cost
end RecognitionScience