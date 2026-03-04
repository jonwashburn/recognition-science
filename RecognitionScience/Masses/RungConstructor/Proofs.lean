import Mathlib
import RecognitionScience.Masses.Anchor
-- import RecognitionScience.RSBridge.Anchor  -- [not in public release]
import RecognitionScience.Masses.RungConstructor.Motif

namespace RecognitionScience
namespace Masses
namespace RungConstructor

open RSBridge

/-- Proof that the rung constructor reproduces the charged lepton table. -/
theorem match_lepton_e : compute_rung (.fermion .e) = 2 := by rfl

theorem match_lepton_mu : compute_rung (.fermion .mu) = 13 := by rfl

theorem match_lepton_tau : compute_rung (.fermion .tau) = 19 := by rfl

/-- Proof that the rung constructor reproduces the up-quark table. -/
theorem match_up_u : compute_rung (.fermion .u) = 4 := by rfl

theorem match_up_c : compute_rung (.fermion .c) = 15 := by rfl

theorem match_up_t : compute_rung (.fermion .t) = 21 := by rfl

/-- Proof that the rung constructor reproduces the down-quark table. -/
theorem match_down_d : compute_rung (.fermion .d) = 4 := by rfl

theorem match_down_s : compute_rung (.fermion .s) = 15 := by rfl

theorem match_down_b : compute_rung (.fermion .b) = 21 := by rfl

/-- Proof that the rung constructor reproduces the boson table. -/
theorem match_boson_W : compute_rung .W = 1 := by rfl

theorem match_boson_Z : compute_rung .Z = 1 := by rfl

theorem match_boson_H : compute_rung .H = 1 := by rfl

/-- Proof that the constructor matches the legacy `RSBridge.rung` mapping for charged leptons. -/
theorem match_rsbridge_rung_charged_leptons :
    compute_rung (.fermion .e) = RSBridge.rung .e ∧
    compute_rung (.fermion .mu) = RSBridge.rung .mu ∧
    compute_rung (.fermion .tau) = RSBridge.rung .tau :=
  ⟨rfl, rfl, rfl⟩

/-- Proof that the constructor matches the legacy `RSBridge.rung` mapping for up-type quarks. -/
theorem match_rsbridge_rung_up_quarks :
    compute_rung (.fermion .u) = RSBridge.rung .u ∧
    compute_rung (.fermion .c) = RSBridge.rung .c ∧
    compute_rung (.fermion .t) = RSBridge.rung .t :=
  ⟨rfl, rfl, rfl⟩

/-- Proof that the constructor matches the legacy `RSBridge.rung` mapping for down-type quarks. -/
theorem match_rsbridge_rung_down_quarks :
    compute_rung (.fermion .d) = RSBridge.rung .d ∧
    compute_rung (.fermion .s) = RSBridge.rung .s ∧
    compute_rung (.fermion .b) = RSBridge.rung .b :=
  ⟨rfl, rfl, rfl⟩

/-- Proof that the constructor matches the legacy `RSBridge.rung` mapping for neutrinos.
    Neutrinos have baseline 0 (due to Z=0) and a different gen-2 step (+8 vs +6). -/
theorem match_rsbridge_rung_neutrinos :
    compute_rung (.fermion .nu1) = RSBridge.rung .nu1 ∧
    compute_rung (.fermion .nu2) = RSBridge.rung .nu2 ∧
    compute_rung (.fermion .nu3) = RSBridge.rung .nu3 :=
  ⟨rfl, rfl, rfl⟩

/-- The master matching theorem: constructor reproduces all legacy rung values. -/
theorem match_rsbridge_rung (f : Fermion) : compute_rung (.fermion f) = RSBridge.rung f := by
  cases f <;> rfl

end RungConstructor
end Masses
end RecognitionScience
