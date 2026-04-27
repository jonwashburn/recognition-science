import Mathlib
import RecognitionScience.Constants
import RecognitionScience.Constants.Alpha
import RecognitionScience.Foundation.LogicRealTranscendentals

/-!
  LogicRealConstants.lean

  Recognition Science constants mirrored on the recovered real line.

  The definitions are expressed in `LogicReal`; each theorem proves that
  transport through `LogicReal.toReal` recovers the existing real-valued
  constant from `RecognitionScience.Constants`.
-/

namespace RecognitionScience
namespace Foundation
namespace LogicRealConstants

open RealsFromLogic RealsFromLogic.LogicReal
open LogicRealTranscendentals

noncomputable section

/-- Recovered golden ratio. -/
def phiL : LogicReal :=
  (fromReal 1 + sqrtL (fromReal 5)) / fromReal 2

/-- Recovered tick unit. -/
def tickL : LogicReal := fromReal Constants.tick

/-- Recovered octave. -/
def octaveL : LogicReal := fromReal Constants.octave

/-- Recovered J-bit constant. -/
def JbitL : LogicReal := logL phiL

/-- Recovered coherence scale. -/
def EcohL : LogicReal := fromReal Constants.E_coh

/-- Recovered hbar. -/
def hbarL : LogicReal := rpowL phiL (fromReal (-(5 : ℝ)))

/-- Recovered Newton constant in RS-native units. -/
def gravL : LogicReal := fromReal Constants.G

/-- Recovered Einstein coupling. -/
def kappaEinsteinL : LogicReal := fromReal Constants.kappa_einstein

/-- Recovered inverse fine-structure constant. -/
def alphaInvL : LogicReal := fromReal Constants.alphaInv

@[simp] theorem toReal_phiL : toReal phiL = Constants.phi := by
  simp [phiL, Constants.phi, toReal_fromReal]

@[simp] theorem toReal_tickL : toReal tickL = Constants.tick := toReal_fromReal _

@[simp] theorem toReal_octaveL : toReal octaveL = Constants.octave := toReal_fromReal _

@[simp] theorem toReal_JbitL : toReal JbitL = Constants.J_bit := by
  simp [JbitL, Constants.J_bit]

@[simp] theorem toReal_EcohL : toReal EcohL = Constants.E_coh := toReal_fromReal _

@[simp] theorem toReal_hbarL : toReal hbarL = Constants.hbar := by
  rw [Constants.hbar_eq_phi_inv_fifth]
  simp [hbarL, toReal_phiL, toReal_fromReal]

@[simp] theorem toReal_gravL : toReal gravL = Constants.G := toReal_fromReal _

@[simp] theorem toReal_kappaEinsteinL :
    toReal kappaEinsteinL = Constants.kappa_einstein := toReal_fromReal _

@[simp] theorem toReal_alphaInvL : toReal alphaInvL = Constants.alphaInv := toReal_fromReal _

/-- Positivity of recovered φ. -/
theorem phiL_pos : (0 : LogicReal) < phiL := by
  rw [lt_iff_toReal_lt, toReal_zero, toReal_phiL]
  exact Constants.phi_pos

/-- Recovered φ exceeds 1. -/
theorem phiL_gt_one : (1 : LogicReal) < phiL := by
  rw [lt_iff_toReal_lt, toReal_one, toReal_phiL]
  exact Constants.one_lt_phi

/-- Recovered lower numerical φ bound. -/
theorem phiL_gt_onePointFive : fromReal (1.5 : ℝ) < phiL := by
  rw [lt_iff_toReal_lt, toReal_fromReal, toReal_phiL]
  exact Constants.phi_gt_onePointFive

/-- Recovered upper numerical φ bound. -/
theorem phiL_lt_onePointSixTwo : phiL < fromReal (1.62 : ℝ) := by
  rw [lt_iff_toReal_lt, toReal_fromReal, toReal_phiL]
  exact Constants.phi_lt_onePointSixTwo

/-- Recovered hbar identity. -/
theorem hbarL_eq_phi_inv_fifth : hbarL = rpowL phiL (fromReal (-(5 : ℝ))) := rfl

/-- Recovered hbar numerical bounds. -/
theorem hbarL_bounds : fromReal (0.088 : ℝ) < hbarL ∧ hbarL < fromReal (0.093 : ℝ) := by
  constructor
  · rw [lt_iff_toReal_lt, toReal_fromReal, toReal_hbarL]
    exact Constants.hbar_bounds.1
  · rw [lt_iff_toReal_lt, toReal_fromReal, toReal_hbarL]
    exact Constants.hbar_bounds.2

/-- The recovered alpha inverse is transported from the public symbolic
alpha pipeline. Numerical interval certificates live in the full internal
repository and can be added to the public release once its interval stack is
updated. -/
theorem alphaInvL_symbolic :
    toReal alphaInvL = Constants.alphaInv := toReal_alphaInvL

end

end LogicRealConstants
end Foundation
end RecognitionScience
