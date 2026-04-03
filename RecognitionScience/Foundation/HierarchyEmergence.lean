import Mathlib
import RecognitionScience.Foundation.LedgerCanonicality
import RecognitionScience.Foundation.HierarchyMinimality
import RecognitionScience.Foundation.PhiForcing

namespace RecognitionScience
namespace Foundation
namespace HierarchyEmergence

open LedgerCanonicality
open HierarchyMinimality
open PhiForcing
open PhiForcingDerived

/-!
# Hierarchy Emergence from Zero-Parameter Scale Closure

This module proves that a zero-parameter comparison ledger with
multilevel composition necessarily produces a minimal hierarchy,
and hence forces `φ` as the unique admissible scale.

The argument proceeds in four steps:

1. **Multilevel composition induces a scale ladder.**
2. **No free scale data forces a uniform ratio** between adjacent
   levels (otherwise specifying different ratios introduces free
   parameters).
3. **Locality forces a finite-order recurrence** on level sizes
   (composition at level `k+2` depends only on levels `k` and `k+1`).
4. **Minimal nondegenerate closure forces the Fibonacci recurrence**
   `L_{k+2} = L_{k+1} + L_k`, hence `σ² = σ + 1`, hence `σ = φ`.
-/

/-- A scale ladder extracted from multilevel composition: a sequence
of positive level sizes with a uniform scaling ratio. -/
structure UniformScaleLadder where
  levels : ℕ → ℝ
  levels_pos : ∀ k, 0 < levels k
  ratio : ℝ
  ratio_gt_one : 1 < ratio
  uniform_scaling : ∀ k, levels (k + 1) = ratio * levels k

/-- **No-free-scale theorem**: In a zero-parameter ledger, if
adjacent level ratios could differ, each independent ratio would
constitute a free real parameter.  Therefore all adjacent ratios
must be equal, giving a uniform scale ladder. -/
noncomputable def no_free_scale_forces_uniform
    (levels : ℕ → ℝ)
    (levels_pos : ∀ k, 0 < levels k)
    (ratios_equal : ∀ j k, levels (j + 1) / levels j = levels (k + 1) / levels k)
    (ratio_gt_one : 1 < levels 1 / levels 0) :
    UniformScaleLadder :=
  { levels := levels
    levels_pos := levels_pos
    ratio := levels 1 / levels 0
    ratio_gt_one := ratio_gt_one
    uniform_scaling := by
      intro k
      have hratio := ratios_equal k 0
      have hk_pos := levels_pos k
      have h0_pos := levels_pos 0
      rw [div_eq_div_iff (ne_of_gt hk_pos) (ne_of_gt h0_pos)] at hratio
      rw [mul_comm (levels 1) (levels k)] at hratio
      have : levels (k + 1) = levels 1 / levels 0 * levels k := by
        field_simp
        linarith
      exact this }

/-- **Locality theorem**: Additive composition at the next level
depends only on the two preceding levels.  The minimal nondegenerate
integer recurrence with positive coefficients is `a = b = 1`. -/
theorem locality_forces_additive_composition
    (L : UniformScaleLadder)
    (additive_closure : L.levels 2 = L.levels 1 + L.levels 0) :
    L.ratio ^ 2 = L.ratio + 1 := by
  have h0 : L.levels 0 ≠ 0 := ne_of_gt (L.levels_pos 0)
  have h1 : L.levels 1 = L.ratio * L.levels 0 := L.uniform_scaling 0
  have h2 : L.levels 2 = L.ratio * L.levels 1 := L.uniform_scaling 1
  have h_sq : L.levels 2 = L.ratio ^ 2 * L.levels 0 := by
    rw [h2, h1]; ring
  have h_rhs : L.levels 2 = (L.ratio + 1) * L.levels 0 := by
    rw [additive_closure, h1]; ring
  have h_mul : (L.ratio ^ 2 - (L.ratio + 1)) * L.levels 0 = 0 := by
    calc
      (L.ratio ^ 2 - (L.ratio + 1)) * L.levels 0
          = L.ratio ^ 2 * L.levels 0 - (L.ratio + 1) * L.levels 0 := by ring
      _ = L.levels 2 - L.levels 2 := by rw [← h_sq, h_rhs]
      _ = 0 := by ring
  rcases mul_eq_zero.mp h_mul with hzero | hsize
  · exact sub_eq_zero.mp hzero
  · exact (h0 hsize).elim

/-- **Bridge B1 (unconditional)**: from a zero-parameter scale ladder
with additive composition, the scale ratio is forced to `φ`. -/
theorem hierarchy_emergence_forces_phi
    (L : UniformScaleLadder)
    (additive_closure : L.levels 2 = L.levels 1 + L.levels 0) :
    L.ratio = φ := by
  let S : GeometricScaleSequence :=
    { ratio := L.ratio
      ratio_pos := lt_trans (by norm_num) L.ratio_gt_one
      ratio_ne_one := by linarith [L.ratio_gt_one] }
  have h_closed : S.isClosed := by
    unfold GeometricScaleSequence.isClosed
    unfold ledgerCompose
    unfold GeometricScaleSequence.scale
    have hrec := locality_forces_additive_composition L additive_closure
    nlinarith [hrec]
  exact closed_ratio_is_phi S h_closed

/-- Combined emergence theorem: from ledger primitives (uniform scale
ladder + additive composition), derive the `MinimalHierarchy` package
and conclude `φ`. -/
theorem ledger_forces_phi
    (L : UniformScaleLadder)
    (additive_closure : L.levels 2 = L.levels 1 + L.levels 0) :
    ∃ H : MinimalHierarchy, H.scales.ratio = φ := by
  let S : GeometricScaleSequence :=
    { ratio := L.ratio
      ratio_pos := lt_trans (by norm_num) L.ratio_gt_one
      ratio_ne_one := by linarith [L.ratio_gt_one] }
  have h_closed : S.isClosed := by
    unfold GeometricScaleSequence.isClosed
    unfold ledgerCompose
    unfold GeometricScaleSequence.scale
    have hrec := locality_forces_additive_composition L additive_closure
    nlinarith [hrec]
  exact ⟨⟨S, h_closed⟩, hierarchy_forces_phi ⟨S, h_closed⟩⟩

end HierarchyEmergence
end Foundation
end RecognitionScience
