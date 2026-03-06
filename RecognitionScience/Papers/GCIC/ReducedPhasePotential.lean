import Mathlib
import RecognitionScience.Cost
import RecognitionScience.Constants

/-!
# Reduced Phase Potential J̃ (GCIC Paper, Sec. IV)

Formalizes the reduced phase-mismatch potential induced by the
discrete scaling quotient x ~ b^n x:

  J̃_b(δ) = cosh(lam · d_ℤ(δ)) − 1,   lam = ln b,

where d_ℤ(δ) = min_{n ∈ ℤ} |δ − n| is the distance to the nearest integer.

## Main results

* `distZ` — distance to nearest integer, with periodicity and zero characterization.
* `Jtilde` — the reduced phase potential.
* `Jtilde_nonneg`, `Jtilde_periodic`, `Jtilde_zero_iff` — key structural properties.
* `Jtilde_stiffness_lb` — small-gradient stiffness lower bound κ = lam²/2.

## Reference

Thapa–Washburn, "Rigidity and Compact Phase Emergence in Scale-Invariant
Ratio-Based Energies" (2026), Section IV.
-/

namespace RecognitionScience.Papers.GCIC.ReducedPhasePotential

open Real
open RecognitionScience.Cost

/-! ### Distance to nearest integer -/

/-- Distance to the nearest integer: d_ℤ(δ) = min(fract(δ), 1 − fract(δ)).
    This is in [0, 1/2] and vanishes exactly when δ is an integer. -/
noncomputable def distZ (δ : ℝ) : ℝ :=
  min (Int.fract δ) (1 - Int.fract δ)

theorem distZ_nonneg (δ : ℝ) : 0 ≤ distZ δ := by
  unfold distZ
  exact le_min (Int.fract_nonneg δ) (by linarith [Int.fract_lt_one δ])

theorem distZ_le_half (δ : ℝ) : distZ δ ≤ 1 / 2 := by
  unfold distZ
  rcases le_or_gt (Int.fract δ) (1 / 2) with h | h
  · exact min_le_left _ _ |>.trans h
  · have : 1 - Int.fract δ ≤ 1 / 2 := by linarith
    exact min_le_right _ _ |>.trans this

/-- d_ℤ is 1-periodic: d_ℤ(δ + n) = d_ℤ(δ) for integer n. -/
theorem distZ_add_int (δ : ℝ) (n : ℤ) : distZ (δ + ↑n) = distZ δ := by
  unfold distZ
  rw [Int.fract_add_intCast]

/-- d_ℤ is 1-periodic (special case n = 1). -/
theorem distZ_periodic (δ : ℝ) : distZ (δ + 1) = distZ δ := by
  have h : δ + 1 = δ + ↑(1 : ℤ) := by push_cast; ring
  rw [h]
  exact distZ_add_int δ 1

/-- d_ℤ(δ) = 0 iff δ is an integer. -/
theorem distZ_eq_zero_iff (δ : ℝ) : distZ δ = 0 ↔ ∃ n : ℤ, δ = ↑n := by
  unfold distZ
  constructor
  · intro h
    have hfrac_nonneg := Int.fract_nonneg δ
    have h1sub_pos : 0 < 1 - Int.fract δ := by linarith [Int.fract_lt_one δ]
    have hfrac_zero : Int.fract δ = 0 := by
      rcases le_or_gt (Int.fract δ) (1 - Int.fract δ) with h_le | h_lt
      · rwa [min_eq_left h_le] at h
      · rw [min_eq_right (le_of_lt h_lt)] at h; linarith
    exact ⟨⌊δ⌋, by linarith [Int.fract_add_floor δ]⟩
  · intro ⟨n, hn⟩
    rw [hn, Int.fract_intCast]
    simp

/-! ### The reduced phase potential -/

/-- The reduced phase potential: J̃(lam, δ) = cosh(lam · d_ℤ(δ)) − 1.
    Here lam = ln b for the base b of the discrete quotient. -/
noncomputable def Jtilde (lam : ℝ) (δ : ℝ) : ℝ :=
  cosh (lam * distZ δ) - 1

/-- J̃ ≥ 0. -/
theorem Jtilde_nonneg (lam : ℝ) (δ : ℝ) : 0 ≤ Jtilde lam δ := by
  unfold Jtilde
  linarith [one_le_cosh (lam * distZ δ)]

/-- J̃ is 1-periodic in δ. -/
theorem Jtilde_periodic (lam : ℝ) (δ : ℝ) : Jtilde lam (δ + 1) = Jtilde lam δ := by
  unfold Jtilde
  rw [distZ_periodic]

/-- J̃ is 1-periodic for general integer shifts. -/
theorem Jtilde_add_int (lam : ℝ) (δ : ℝ) (n : ℤ) :
    Jtilde lam (δ + ↑n) = Jtilde lam δ := by
  unfold Jtilde
  rw [distZ_add_int]

/-- cosh(t) = 1 iff t = 0. -/
private lemma cosh_eq_one_iff (t : ℝ) : cosh t = 1 ↔ t = 0 := by
  constructor
  · intro h
    by_contra hne
    exact absurd h (ne_of_gt ((one_lt_cosh).mpr hne))
  · intro h; rw [h, cosh_zero]

/-- J̃(lam, δ) = 0 iff δ is an integer, for lam ≠ 0. -/
theorem Jtilde_zero_iff {lam : ℝ} (hlam : lam ≠ 0) (δ : ℝ) :
    Jtilde lam δ = 0 ↔ ∃ n : ℤ, δ = ↑n := by
  unfold Jtilde
  constructor
  · intro h
    have h1 : cosh (lam * distZ δ) = 1 := by linarith
    have h2 : lam * distZ δ = 0 := (cosh_eq_one_iff _).mp h1
    have h3 : distZ δ = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hlam
      · exact h
    exact (distZ_eq_zero_iff δ).mp h3
  · intro ⟨n, hn⟩
    have hd : distZ δ = 0 := (distZ_eq_zero_iff δ).mpr ⟨n, hn⟩
    simp [hd, cosh_zero]

/-! ### Stiffness (small-gradient regime)

For small δ (near an integer), J̃(lam, δ) ≈ lam² δ² / 2.
The stiffness is κ = lam²/2. -/

/-- Small-gradient lower bound: J̃(lam, δ) ≥ (lam · d_ℤ(δ))² / 2.
    This follows from the quadratic lower bound cosh(t) − 1 ≥ t²/2. -/
theorem Jtilde_stiffness_lb (lam : ℝ) (δ : ℝ) :
    (lam * distZ δ) ^ 2 / 2 ≤ Jtilde lam δ := by
  unfold Jtilde
  linarith [cosh_quadratic_lower_bound (lam * distZ δ)]

/-- The GCIC stiffness for base φ: κ = (ln φ)²/2. -/
noncomputable def gcic_kappa : ℝ := (log Constants.phi) ^ 2 / 2

theorem gcic_kappa_pos : 0 < gcic_kappa := by
  unfold gcic_kappa
  apply div_pos (pow_pos (log_pos Constants.one_lt_phi) 2) (by norm_num)

/-! ### Phase rigidity (Result 3)

On any finite connected graph, the reduced phase energy
  C̃_G[Θ] = Σ_{edges} J̃(lam, Θ_v − Θ_w)
is minimized exactly by constant phase fields. This follows from the
same nonnegativity/unique-zero mechanism as Result 1. -/

/-- **RESULT 3 (Phase Rigidity).**
On a connected graph, if the reduced phase cost J̃(lam, Θ_v − Θ_w) vanishes on
every edge, then the phase field Θ is constant modulo integers. -/
theorem phase_rigidity {V : Type*} {adj : V → V → Prop}
    (hconn : ∀ u v : V, Relation.ReflTransGen adj u v)
    {lam : ℝ} (hlam : lam ≠ 0) {Θ : V → ℝ}
    (hzero : ∀ v w, adj v w → Jtilde lam (Θ v - Θ w) = 0) :
    ∀ v w : V, ∃ n : ℤ, Θ v - Θ w = ↑n := by
  have hadj : ∀ v w, adj v w → ∃ n : ℤ, Θ v - Θ w = ↑n :=
    fun v w hvw => (Jtilde_zero_iff hlam _).mp (hzero v w hvw)
  intro v w
  induction hconn v w with
  | refl => exact ⟨0, by simp⟩
  | tail _ hbc ih =>
    obtain ⟨n₁, hn₁⟩ := ih
    obtain ⟨n₂, hn₂⟩ := hadj _ _ hbc
    exact ⟨n₁ + n₂, by push_cast; linarith⟩

end RecognitionScience.Papers.GCIC.ReducedPhasePotential
