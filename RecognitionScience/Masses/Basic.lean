-- import RecognitionScience.Data.Import  -- [not in public release]
import RecognitionScience.Constants
import RecognitionScience.Masses.Assumptions

open RecognitionScience.Data

/-! Model: charged-lepton ladder surrogate. -/

/-- Exponents for surrogate ladder differences (paper placeholder). -/
@[simp] def rung_exponent (name : String) : Int :=
  if name = "mu_e" then 11 else if name = "tau_mu" then 6 else 0

@[simp] def mass_ladder_matches_pdg (φ : ℝ) : Prop :=
  ∀ m ∈ import_measurements, |m.value - φ ^ rung_exponent m.name| ≤ m.error

/-- Pending proof: relies on `Masses.mass_ladder_assumption` (docs). -/
lemma mass_ladder_holds
    (h : Masses.mass_ladder_assumption) :
    mass_ladder_matches_pdg RecognitionScience.Constants.phi :=
  h
