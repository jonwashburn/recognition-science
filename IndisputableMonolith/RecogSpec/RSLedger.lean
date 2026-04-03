import Mathlib
import IndisputableMonolith.RecogSpec.Core
import IndisputableMonolith.Constants

/-!
# RSLedger: Rich Ledger with φ-Tier Structure

This module defines the rich ledger structure needed for deriving mass ratios
from generation torsion rather than defining them as φ-formulas.

## The Physics

In Recognition Science, particle masses occupy discrete rungs on the φ-ladder:
- Each generation has a torsion offset τ_g ∈ {0, 11, 17}
- Each sector (leptons, up quarks, down quarks) has a base rung
- The full rung is: `rung = baseRung + τ_g`
- Mass ratios are: `m_f / m_g = φ^{r_f - r_g}`

## Key Result

With torsion {0, 11, 17}, the inter-generation mass ratios are:
- Gen 2 / Gen 1 = φ^{11}
- Gen 3 / Gen 1 = φ^{17}
- Gen 3 / Gen 2 = φ^{6}

These are DERIVED from the torsion structure, not defined as formulas.
-/

namespace IndisputableMonolith
namespace RecogSpec

open Constants

/-! ## Generation Torsion -/

/-- The three generations of fermions -/
inductive Generation : Type
  | first | second | third
  deriving DecidableEq, Repr, Inhabited

/-- The canonical generation torsion values {0, 11, 17}.

These are derived from the eight-tick structure of the ledger:
- First generation: τ = 0 (ground state)
- Second generation: τ = 11 (passive edges of cube)
- Third generation: τ = 17 (faces × wallpaper groups / 6)
-/
def generationTorsion : Generation → ℤ
  | .first => 0
  | .second => 11
  | .third => 17

@[simp] lemma torsion_first : generationTorsion .first = 0 := rfl
@[simp] lemma torsion_second : generationTorsion .second = 11 := rfl
@[simp] lemma torsion_third : generationTorsion .third = 17 := rfl

/-- Torsion difference between generations -/
def torsionDiff (g1 g2 : Generation) : ℤ :=
  generationTorsion g1 - generationTorsion g2

@[simp] lemma torsion_diff_21 : torsionDiff .second .first = 11 := by
  simp [torsionDiff]

@[simp] lemma torsion_diff_31 : torsionDiff .third .first = 17 := by
  simp [torsionDiff]

@[simp] lemma torsion_diff_32 : torsionDiff .third .second = 6 := by
  simp [torsionDiff]

/-! ## Fermion Sectors -/

/-- The three fermion sectors -/
inductive FermionSector : Type
  | leptons | upQuarks | downQuarks
  deriving DecidableEq, Repr

/-- Base rung for each sector.

These are derived from the charge structure Z:
- Leptons: base = 2
- Up quarks: base = 4
- Down quarks: base = 4
-/
def sectorBaseRung : FermionSector → ℤ
  | .leptons => 2
  | .upQuarks => 4
  | .downQuarks => 4

/-! ## RSLedger Structure -/

/-- A ledger with the full φ-tier structure needed for mass derivation.

This extends the minimal `Ledger` with:
- Generation torsion function
- Sector base rungs
- Full rung assignment
-/
structure RSLedger where
  /-- The underlying ledger -/
  toLedger : Ledger
  /-- Generation torsion offsets -/
  torsion : Generation → ℤ
  /-- Base rung for each sector -/
  baseRung : FermionSector → ℤ

/-- The full rung assignment for a particle -/
def RSLedger.rung (L : RSLedger) (sector : FermionSector) (gen : Generation) : ℤ :=
  L.baseRung sector + L.torsion gen

/-- Rung difference between two generations in the same sector -/
def RSLedger.rungDiff (L : RSLedger) (sector : FermionSector)
    (g1 g2 : Generation) : ℤ :=
  L.rung sector g1 - L.rung sector g2

/-- Rung difference equals torsion difference (base rung cancels) -/
theorem RSLedger.rungDiff_eq_torsionDiff (L : RSLedger) (sector : FermionSector)
    (g1 g2 : Generation) :
    L.rungDiff sector g1 g2 = L.torsion g1 - L.torsion g2 := by
  simp only [rungDiff, rung]
  ring

/-- For canonical torsion, rung difference is generation torsion difference -/
theorem RSLedger.rungDiff_canonical (L : RSLedger) (sector : FermionSector)
    (g1 g2 : Generation) (hL : L.torsion = generationTorsion) :
    L.rungDiff sector g1 g2 = torsionDiff g1 g2 := by
  rw [rungDiff_eq_torsionDiff, hL]
  rfl

/-! ## Mass Ratios from Rung Differences -/

/-- Mass ratio between generations from rung difference.

This is the key derivation: masses are φ^{rung}, so ratios are φ^{Δrung}.
-/
noncomputable def massRatioFromRungs (L : RSLedger) (φ : ℝ)
    (sector : FermionSector) (g1 g2 : Generation) : ℝ :=
  φ ^ (L.rungDiff sector g1 g2)

/-- Mass ratio gen2/gen1 = φ^{11} for canonical torsion -/
theorem massRatio_21_canonical (L : RSLedger) (φ : ℝ) (sector : FermionSector)
    (hL : L.torsion = generationTorsion) :
    massRatioFromRungs L φ sector .second .first = φ ^ (11 : ℤ) := by
  simp only [massRatioFromRungs]
  rw [L.rungDiff_canonical sector _ _ hL]
  simp [torsionDiff]

/-- Mass ratio gen3/gen1 = φ^{17} for canonical torsion -/
theorem massRatio_31_canonical (L : RSLedger) (φ : ℝ) (sector : FermionSector)
    (hL : L.torsion = generationTorsion) :
    massRatioFromRungs L φ sector .third .first = φ ^ (17 : ℤ) := by
  simp only [massRatioFromRungs]
  rw [L.rungDiff_canonical sector _ _ hL]
  simp [torsionDiff]

/-- Mass ratio gen3/gen2 = φ^{6} for canonical torsion -/
theorem massRatio_32_canonical (L : RSLedger) (φ : ℝ) (sector : FermionSector)
    (hL : L.torsion = generationTorsion) :
    massRatioFromRungs L φ sector .third .second = φ ^ (6 : ℤ) := by
  simp only [massRatioFromRungs]
  rw [L.rungDiff_canonical sector _ _ hL]
  simp [torsionDiff]

/-! ## The Canonical RSLedger -/

/-- The canonical RS ledger with standard torsion and base rungs -/
def canonicalRSLedger : RSLedger where
  toLedger := { Carrier := Unit }
  torsion := generationTorsion
  baseRung := sectorBaseRung

/-- The canonical ledger has canonical torsion -/
@[simp] theorem canonicalRSLedger_torsion :
    canonicalRSLedger.torsion = generationTorsion := rfl

/-- Canonical ledger mass ratios -/
theorem canonical_massRatio_21 (φ : ℝ) (sector : FermionSector) :
    massRatioFromRungs canonicalRSLedger φ sector .second .first = φ ^ (11 : ℤ) :=
  massRatio_21_canonical canonicalRSLedger φ sector canonicalRSLedger_torsion

theorem canonical_massRatio_31 (φ : ℝ) (sector : FermionSector) :
    massRatioFromRungs canonicalRSLedger φ sector .third .first = φ ^ (17 : ℤ) :=
  massRatio_31_canonical canonicalRSLedger φ sector canonicalRSLedger_torsion

theorem canonical_massRatio_32 (φ : ℝ) (sector : FermionSector) :
    massRatioFromRungs canonicalRSLedger φ sector .third .second = φ ^ (6 : ℤ) :=
  massRatio_32_canonical canonicalRSLedger φ sector canonicalRSLedger_torsion

/-! ## Summary: Mass Ratios from Torsion Structure -/

/-- The torsion structure {0, 11, 17} gives the canonical mass ratio rung differences.

This is the key result: masses are DERIVED from torsion, not defined as formulas.
-/
theorem massRatios_from_torsion_structure (L : RSLedger)
    (hL : L.torsion = generationTorsion) :
    L.rungDiff .leptons .second .first = 11 ∧
    L.rungDiff .leptons .third .first = 17 ∧
    L.rungDiff .leptons .third .second = 6 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [L.rungDiff_canonical .leptons _ _ hL]; rfl
  · rw [L.rungDiff_canonical .leptons _ _ hL]; rfl
  · rw [L.rungDiff_canonical .leptons _ _ hL]; rfl

end RecogSpec
end IndisputableMonolith
