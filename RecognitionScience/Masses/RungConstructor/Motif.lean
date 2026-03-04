import Mathlib
import RecognitionScience.Masses.RungConstructor.Basic

namespace RecognitionScience
namespace Masses
namespace RungConstructor

/-- Generation step constants derived from cube geometry.
    - step_gen1 = 11: common to all fermion sectors
    - step_gen2_charged = 6: leptons and quarks (gen 2 → gen 3)
    - step_gen2_neutrino = 8: neutrinos (gen 2 → gen 3)

    The neutrino step difference (8 vs 6) arises from the Z=0 charge band
    requiring a different octave offset. -/
def step_gen1 : ℤ := 11
def step_gen2_charged : ℤ := 6
def step_gen2_neutrino : ℤ := 8

/-- Cumulative generation torsion for charged fermions (leptons, quarks). -/
def tau_charged (gen : ℕ) : ℤ :=
  match gen with
  | 0 => 0
  | 1 => step_gen1
  | _ => step_gen1 + step_gen2_charged  -- gen ≥ 2

/-- Cumulative generation torsion for neutrinos. -/
def tau_neutrino (gen : ℕ) : ℤ :=
  match gen with
  | 0 => 0
  | 1 => step_gen1
  | _ => step_gen1 + step_gen2_neutrino  -- gen ≥ 2

/-- Sector-global length baseline. -/
def ell_baseline : Sector → ℤ
  | .Lepton      => 2
  | .Neutrino    => 0  -- Neutrinos have Z=0, so no charge contribution to baseline
  | .UpQuark     => 4
  | .DownQuark   => 4
  | .Electroweak => 1

/-- The master rung constructor.
    Computes r = ell_baseline(sector) + tau(gen).

    For neutrinos, uses tau_neutrino which has a different gen-2 step. -/
def compute_rung (s : Species) : ℤ :=
  match s with
  | .fermion f =>
      let sector := sectorOf (.fermion f)
      let gen := (RSBridge.genOf f).val
      match sector with
      | .Neutrino => ell_baseline sector + tau_neutrino gen
      | _         => ell_baseline sector + tau_charged gen
  | .W | .Z | .H =>
      ell_baseline .Electroweak

end RungConstructor
end Masses
end RecognitionScience
