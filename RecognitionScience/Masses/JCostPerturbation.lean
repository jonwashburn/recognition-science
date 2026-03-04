import Mathlib
import RecognitionScience.Constants
import RecognitionScience.Constants.AlphaDerivation
-- import RecognitionScience.Constants.Alpha  -- [not in public release]
-- import RecognitionScience.Physics.MassTopology  -- [not in public release]
-- import RecognitionScience.Physics.LeptonGenerations.Defs  -- [not in public release]
-- import RecognitionScience.Verification.LeptonCoefficientPerturbation  -- [not in public release]

/-!
# Mass-Layer J-Cost Perturbation Bridge

This module upstreams the current O4 perturbative closure into the `Masses.*`
namespace and ties it to the canonical lepton-step definitions.

This module now serves as the Lean closure package for O4 coefficient forcing.
It certifies:
1. the `Jcost(1+α)` perturbative channel form,
2. the explicit `α² + 12α³` radiative decomposition used in `refined_shift`,
3. exact geometric evaluations of the zeroth-order constants in the same path.
-/

namespace RecognitionScience
namespace Masses
namespace JCostPerturbation

open Constants
open Constants.AlphaDerivation
open Physics
open Physics.MassTopology
open Physics.LeptonGenerations
open Verification.LeptonCoefficientPerturbation

noncomputable section

/-- Upstreamed channel form of the `Jcost(1+α)` perturbation. -/
theorem jcost_two_channel_form :
    ∃ c : ℝ, 2 * Cost.Jcost (1 + alpha) = alpha ^ 2 + c * alpha ^ 3 ∧ |c| ≤ 4 :=
  two_jcost_one_plus_alpha_expansion

/-- Upstreamed uniqueness form for the perturbative cubic channel coefficient in
`2*Jcost(1+α) = α² + cα³`. -/
theorem jcost_two_channel_coeff_unique :
    ∃! c : ℝ, 2 * Cost.Jcost (1 + alpha) = alpha ^ 2 + c * alpha ^ 3 :=
  exists_unique_two_jcost_channel_coeff

/-- Canonical cubic-channel coefficient for the doubled `Jcost(1+α)` expansion. -/
noncomputable def jcost_two_channel_coeff : ℝ :=
  by
    classical
    exact Classical.choose (ExistsUnique.exists jcost_two_channel_coeff_unique)

/-- The canonical coefficient satisfies the doubled-channel identity. -/
theorem jcost_two_channel_coeff_spec :
    2 * Cost.Jcost (1 + alpha) = alpha ^ 2 + jcost_two_channel_coeff * alpha ^ 3 := by
  classical
  have h_exists : ∃ c : ℝ, 2 * Cost.Jcost (1 + alpha) = alpha ^ 2 + c * alpha ^ 3 :=
    ExistsUnique.exists jcost_two_channel_coeff_unique
  simpa [jcost_two_channel_coeff] using (Classical.choose_spec h_exists)

/-- Characterization form: a coefficient satisfies the doubled-channel identity
iff it equals the canonical coefficient. -/
theorem jcost_two_channel_coeff_iff (c : ℝ) :
    (2 * Cost.Jcost (1 + alpha) = alpha ^ 2 + c * alpha ^ 3) ↔
      c = jcost_two_channel_coeff := by
  constructor
  · intro hc
    exact two_jcost_cubic_coeff_unique (c1 := c) (c2 := jcost_two_channel_coeff) hc
      jcost_two_channel_coeff_spec
  · intro hc
    simpa [hc] using jcost_two_channel_coeff_spec

/-- Exact edge/face constants appearing in the lepton correction path. -/
theorem mass_topology_counts :
    E_total = 12 ∧ E_passive = 11 ∧ W = 17 := by
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide

/-- Canonical ledger fraction value in the electron-break base shift. -/
theorem ledger_fraction_eq_29_over_44 :
    ledger_fraction = (29 : ℚ) / 44 := by
  native_decide

/-- Algebraic uniqueness of the `29/(11k)` normalization at the canonical ratio. -/
theorem ratio_29_over_11k_forces_k_eq_four
    {k : ℕ} (hk : 0 < k)
    (hfrac : (29 : ℚ) / ((11 : ℚ) * k) = (29 : ℚ) / 44) :
    k = 4 := by
  have hkq_ne : ((11 : ℚ) * k) ≠ 0 := by
    have hk_ne : (k : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hk)
    exact mul_ne_zero (by norm_num) hk_ne
  have hcross : (29 : ℚ) * 44 = (29 : ℚ) * ((11 : ℚ) * k) := by
    exact (div_eq_div_iff hkq_ne (by norm_num : (44 : ℚ) ≠ 0)).mp hfrac
  have hkq : (k : ℚ) = 4 := by
    nlinarith [hcross]
  exact Nat.cast_inj.mp (by simpa using hkq)

/-- In the normalized geometric family `(W+E)/(kE_p)`, the canonical ratio forces `k = 4`. -/
theorem ledger_fraction_denominator_forced
    {k : ℕ} (hk : 0 < k)
    (h : ((W + E_total : ℚ) / (k * E_passive) = ledger_fraction)) :
    k = 4 := by
  have hW : W = 17 := mass_topology_counts.2.2
  have hE : E_total = 12 := mass_topology_counts.1
  have hEp : E_passive = 11 := mass_topology_counts.2.1
  have hraw : ((17 + 12 : ℚ) / ((k : ℚ) * 11)) = ((17 + 12 : ℚ) / ((4 : ℚ) * 11)) := by
    simpa [ledger_fraction, hW, hE, hEp, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hfrac : (29 : ℚ) / ((11 : ℚ) * k) = (29 : ℚ) / 44 := by
    have htmp := hraw
    norm_num at htmp
    simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
  exact ratio_29_over_11k_forces_k_eq_four hk hfrac

/-- Positivity-free denominator forcing in `(W+E)/(kE_p)`:
    canonical ledger-fraction matching still forces `k = 4` without
    explicitly assuming `k > 0`. -/
theorem ledger_fraction_denominator_forced_no_hk
    {k : ℕ}
    (h : ((W + E_total : ℚ) / (k * E_passive) = ledger_fraction)) :
    k = 4 := by
  have hk : 0 < k := by
    by_cases hk0 : k = 0
    · subst hk0
      have hfrac0 : ledger_fraction = (0 : ℚ) := by simpa using h.symm
      have hledger_ne_zero : ledger_fraction ≠ 0 := by
        rw [ledger_fraction_eq_29_over_44]
        norm_num
      exact (hledger_ne_zero hfrac0).elim
    · exact Nat.pos_of_ne_zero hk0
  exact ledger_fraction_denominator_forced hk h

/-- Rational-scale version of denominator forcing in `(W+E)/(cE_p)`: canonical
    ledger fraction matching forces `c = 4`. -/
theorem ledger_fraction_denominator_scale_forced
    {c : ℚ} (hc_pos : 0 < c)
    (h : ((W + E_total : ℚ) / (c * E_passive) = ledger_fraction)) :
    c = 4 := by
  have hW : W = 17 := mass_topology_counts.2.2
  have hE : E_total = 12 := mass_topology_counts.1
  have hEp : E_passive = 11 := mass_topology_counts.2.1
  have hraw : ((17 + 12 : ℚ) / (c * 11)) = ((17 + 12 : ℚ) / ((4 : ℚ) * 11)) := by
    simpa [ledger_fraction, hW, hE, hEp, mul_comm, mul_left_comm, mul_assoc] using h
  have hfrac : (29 : ℚ) / ((11 : ℚ) * c) = (29 : ℚ) / 44 := by
    have htmp := hraw
    norm_num at htmp
    simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hc11_ne : ((11 : ℚ) * c) ≠ 0 := mul_ne_zero (by norm_num) hc_ne
  have hcross : (29 : ℚ) * 44 = (29 : ℚ) * ((11 : ℚ) * c) := by
    exact (div_eq_div_iff hc11_ne (by norm_num : (44 : ℚ) ≠ 0)).mp hfrac
  nlinarith [hcross]

/-- Positivity-free rational-scale denominator forcing in `(W+E)/(cE_p)`:
    canonical ledger-fraction matching still forces `c = 4` without
    explicitly assuming `c > 0`. -/
theorem ledger_fraction_denominator_scale_forced_no_hc_pos
    {c : ℚ}
    (h : ((W + E_total : ℚ) / (c * E_passive) = ledger_fraction)) :
    c = 4 := by
  have hc_ne : c ≠ 0 := by
    intro hc0
    subst hc0
    have hfrac0 : ledger_fraction = (0 : ℚ) := by
      simpa using h.symm
    have hledger_ne_zero : ledger_fraction ≠ 0 := by
      rw [ledger_fraction_eq_29_over_44]
      norm_num
    exact (hledger_ne_zero hfrac0).elim
  have hW : W = 17 := mass_topology_counts.2.2
  have hE : E_total = 12 := mass_topology_counts.1
  have hEp : E_passive = 11 := mass_topology_counts.2.1
  have hraw : ((17 + 12 : ℚ) / (c * 11)) = ((17 + 12 : ℚ) / ((4 : ℚ) * 11)) := by
    simpa [ledger_fraction, hW, hE, hEp, mul_comm, mul_left_comm, mul_assoc] using h
  have hfrac : (29 : ℚ) / ((11 : ℚ) * c) = (29 : ℚ) / 44 := by
    have htmp := hraw
    norm_num at htmp
    simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
  have hc11_ne : ((11 : ℚ) * c) ≠ 0 := mul_ne_zero (by norm_num) hc_ne
  have hcross : (29 : ℚ) * 44 = (29 : ℚ) * ((11 : ℚ) * c) := by
    exact (div_eq_div_iff hc11_ne (by norm_num : (44 : ℚ) ≠ 0)).mp hfrac
  nlinarith [hcross]

/-- In the numerator-offset family `((W+E)+n)/(4E_p)`, canonical matching forces `n = 0`. -/
theorem ledger_fraction_numerator_offset_forced
    {n : ℚ}
    (h : (((W + E_total : ℚ) + n) / (4 * E_passive) = ledger_fraction)) :
    n = 0 := by
  have hW : W = 17 := mass_topology_counts.2.2
  have hE : E_total = 12 := mass_topology_counts.1
  have hEp : E_passive = 11 := mass_topology_counts.2.1
  have hraw : ((29 : ℚ) + n) / 44 = (29 : ℚ) / 44 := by
    simpa [ledger_fraction, hW, hE, hEp, add_assoc, add_comm, add_left_comm,
      mul_comm, mul_left_comm, mul_assoc] using h
  nlinarith [hraw]

/-- In the normalized two-weight family `(aW + bE)/(4E_p)` with total weight `a+b=2`,
    canonical matching forces `(a,b) = (1,1)`. -/
theorem ledger_fraction_weight_split_forced
    {a b : ℚ}
    (hsum : a + b = 2)
    (h : ((a * (W : ℚ) + b * (E_total : ℚ)) / (4 * E_passive) = ledger_fraction)) :
    a = 1 ∧ b = 1 := by
  have hW : W = 17 := mass_topology_counts.2.2
  have hE : E_total = 12 := mass_topology_counts.1
  have hEp : E_passive = 11 := mass_topology_counts.2.1
  have hlin : (a * 17 + b * 12) / 44 = ((17 + 12 : ℚ) / 44) := by
    simpa [ledger_fraction, hW, hE, hEp] using h
  have hcross : (a * 17 + b * 12) * 44 = ((17 + 12 : ℚ) * 44) := by
    exact (div_eq_div_iff (by norm_num : (44 : ℚ) ≠ 0) (by norm_num : (44 : ℚ) ≠ 0)).mp hlin
  have hnum : a * 17 + b * 12 = (17 + 12 : ℚ) := by
    nlinarith [hcross]
  have ha : a = 1 := by nlinarith [hsum, hnum]
  have hb : b = 1 := by nlinarith [hsum, hnum]
  exact ⟨ha, hb⟩

/-- Joint Diophantine forcing for integer numerator/denominator perturbations of the
    ledger fraction: under passive-edge band `n ≤ E_p`, canonical matching in
    `((W+E)+n)/(kE_p)` forces `k = 4` and `n = 0`. -/
theorem ledger_fraction_kn_forced_under_passive_bound
    {k n : ℕ} (hk : 0 < k) (hn_le : n ≤ E_passive)
    (h : ((((W + E_total + n : ℕ) : ℚ) / (k * E_passive)) = ledger_fraction)) :
    k = 4 ∧ n = 0 := by
  have hW : W = 17 := mass_topology_counts.2.2
  have hE : E_total = 12 := mass_topology_counts.1
  have hEp : E_passive = 11 := mass_topology_counts.2.1
  have hraw : (((29 + n : ℕ) : ℚ) / ((k * 11 : ℕ) : ℚ)) = ((12 + 17 : ℚ) / (4 * 11)) := by
    simpa [ledger_fraction, hW, hE, hEp, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      add_assoc, add_comm, add_left_comm] using h
  have hraw29 : (((29 + n : ℕ) : ℚ) / ((k * 11 : ℕ) : ℚ)) = (29 : ℚ) / 44 := by
    have htmp := hraw
    norm_num at htmp
    simpa using htmp
  have hk11_ne : ((k * 11 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hk) (by decide : 11 ≠ 0))
  have hcross : (((29 + n : ℕ) : ℚ) * 44) = (29 : ℚ) * (((k * 11 : ℕ) : ℚ)) := by
    have htmp := hraw29
    field_simp [hk11_ne] at htmp
    nlinarith [htmp]
  have hcrossNat : (29 + n) * 44 = 29 * (k * 11) := by
    exact_mod_cast hcross
  have hlin : 44 * (29 + n) = 319 * k := by
    nlinarith [hcrossNat]
  have hn11 : n ≤ 11 := by
    simpa [hEp] using hn_le
  have hk4 : k = 4 := by
    omega
  have hn0 : n = 0 := by
    omega
  exact ⟨hk4, hn0⟩

/-- Positivity-free integer-band closure for ledger-fraction perturbations:
    under passive-edge band `n ≤ E_p`, canonical matching in
    `((W+E)+n)/(kE_p)` forces `k = 4` and `n = 0` without explicit `k > 0`. -/
theorem ledger_fraction_kn_forced_under_passive_bound_no_hk
    {k n : ℕ} (hn_le : n ≤ E_passive)
    (h : ((((W + E_total + n : ℕ) : ℚ) / (k * E_passive)) = ledger_fraction)) :
    k = 4 ∧ n = 0 := by
  have hk : 0 < k := by
    by_cases hk0 : k = 0
    · subst hk0
      have hfrac0 : ledger_fraction = (0 : ℚ) := by
        simpa using h.symm
      have hledger_ne_zero : ledger_fraction ≠ 0 := by
        rw [ledger_fraction_eq_29_over_44]
        norm_num
      exact (hledger_ne_zero hfrac0).elim
    · exact Nat.pos_of_ne_zero hk0
  exact ledger_fraction_kn_forced_under_passive_bound hk hn_le h

/-- Zeroth-order geometric part of the refined shift in explicit numeric form. -/
theorem base_shift_eq_34_plus_29_over_44 :
    base_shift = (34 : ℝ) + ((29 : ℚ) / 44 : ℚ) := by
  have hW : (W : ℝ) = 17 := by exact_mod_cast mass_topology_counts.2.2
  calc
    base_shift = 2 * (W : ℝ) + (ledger_fraction : ℝ) := by simp [base_shift]
    _ = 2 * 17 + (((29 : ℚ) / 44 : ℚ) : ℝ) := by
          simp [hW, ledger_fraction_eq_29_over_44]
    _ = (34 : ℝ) + ((29 : ℚ) / 44 : ℚ) := by ring

/-- In the affine `W`-multiplier family `uW + ledger_fraction`, canonical
    `base_shift` matching forces `u = 2`. -/
theorem base_shift_wallpaper_multiplier_forced
    {u : ℝ}
    (h : base_shift = u * (W : ℝ) + (ledger_fraction : ℝ)) :
    u = 2 := by
  have hcanon : base_shift = 2 * (W : ℝ) + (ledger_fraction : ℝ) := by
    simp [base_shift]
  have hmul : u * (W : ℝ) = 2 * (W : ℝ) := by
    linarith [h, hcanon]
  have hW_ne : (W : ℝ) ≠ 0 := by
    exact_mod_cast (show W ≠ 0 by native_decide)
  exact mul_right_cancel₀ hW_ne hmul

/-- With canonical `2W` term fixed, matching `base_shift` in the denominator family
    `2W + (W+E)/(kE_p)` forces `k = 4`. -/
theorem base_shift_denominator_forced
    {k : ℕ} (hk : 0 < k)
    (h : base_shift = 2 * (W : ℝ) +
      ((((W + E_total : ℚ) / (k * E_passive)) : ℚ) : ℝ)) :
    k = 4 := by
  have hcanon : base_shift = 2 * (W : ℝ) + (ledger_fraction : ℝ) := by
    simp [base_shift]
  have hfracR :
      ((((W + E_total : ℚ) / (k * E_passive)) : ℚ) : ℝ) = (ledger_fraction : ℝ) := by
    linarith [h, hcanon]
  have hfracQ : ((W + E_total : ℚ) / (k * E_passive)) = ledger_fraction := by
    exact_mod_cast hfracR
  exact ledger_fraction_denominator_forced hk hfracQ

/-- Positivity-free packaged denominator forcing for `base_shift`:
    with canonical `2W` term fixed, matching
    `2W + (W+E)/(kE_p)` still forces `k = 4` without explicit `k > 0`. -/
theorem base_shift_denominator_forced_no_hk
    {k : ℕ}
    (h : base_shift = 2 * (W : ℝ) +
      ((((W + E_total : ℚ) / (k * E_passive)) : ℚ) : ℝ)) :
    k = 4 := by
  have hcanon : base_shift = 2 * (W : ℝ) + (ledger_fraction : ℝ) := by
    simp [base_shift]
  have hfracR :
      ((((W + E_total : ℚ) / (k * E_passive)) : ℚ) : ℝ) = (ledger_fraction : ℝ) := by
    linarith [h, hcanon]
  have hfracQ : ((W + E_total : ℚ) / (k * E_passive)) = ledger_fraction := by
    exact_mod_cast hfracR
  exact ledger_fraction_denominator_forced_no_hk hfracQ

/-- Positivity-free rational-scale packaged denominator forcing for `base_shift`:
    with canonical `2W` term fixed, matching
    `2W + (W+E)/(cE_p)` still forces `c = 4` without explicit `c > 0`. -/
theorem base_shift_denominator_scale_forced_no_hc_pos
    {c : ℚ}
    (h : base_shift = 2 * (W : ℝ) +
      ((((W + E_total : ℚ) / (c * E_passive)) : ℚ) : ℝ)) :
    c = 4 := by
  have hcanon : base_shift = 2 * (W : ℝ) + (ledger_fraction : ℝ) := by
    simp [base_shift]
  have hfracR :
      ((((W + E_total : ℚ) / (c * E_passive)) : ℚ) : ℝ) = (ledger_fraction : ℝ) := by
    linarith [h, hcanon]
  have hfracQ : ((W + E_total : ℚ) / (c * E_passive)) = ledger_fraction := by
    exact_mod_cast hfracR
  exact ledger_fraction_denominator_scale_forced_no_hc_pos hfracQ

/-- With canonical `2W` term fixed, matching `base_shift` in the numerator-offset family
    `2W + ((W+E)+n)/(4E_p)` forces `n = 0`. -/
theorem base_shift_numerator_offset_forced
    {n : ℚ}
    (h : base_shift = 2 * (W : ℝ) +
      (((((W + E_total : ℚ) + n) / (4 * E_passive)) : ℚ) : ℝ)) :
    n = 0 := by
  have hcanon : base_shift = 2 * (W : ℝ) + (ledger_fraction : ℝ) := by
    simp [base_shift]
  have hfracR :
      (((((W + E_total : ℚ) + n) / (4 * E_passive)) : ℚ) : ℝ) = (ledger_fraction : ℝ) := by
    linarith [h, hcanon]
  have hfracQ : (((W + E_total : ℚ) + n) / (4 * E_passive)) = ledger_fraction := by
    exact_mod_cast hfracR
  exact ledger_fraction_numerator_offset_forced hfracQ

/-- With canonical `2W` term fixed, matching `base_shift` in the normalized
    two-weight family `2W + (aW+bE)/(4E_p)` with `a+b=2` forces `(a,b)=(1,1)`. -/
theorem base_shift_weight_split_forced
    {a b : ℚ}
    (hsum : a + b = 2)
    (h : base_shift = 2 * (W : ℝ) +
      ((((a * (W : ℚ) + b * (E_total : ℚ)) / (4 * E_passive)) : ℚ) : ℝ)) :
    a = 1 ∧ b = 1 := by
  have hcanon : base_shift = 2 * (W : ℝ) + (ledger_fraction : ℝ) := by
    simp [base_shift]
  have hfracR :
      ((((a * (W : ℚ) + b * (E_total : ℚ)) / (4 * E_passive)) : ℚ) : ℝ) = (ledger_fraction : ℝ) := by
    linarith [h, hcanon]
  have hfracQ : ((a * (W : ℚ) + b * (E_total : ℚ)) / (4 * E_passive)) = ledger_fraction := by
    exact_mod_cast hfracR
  exact ledger_fraction_weight_split_forced hsum hfracQ

/-- Packaged `base_shift` closure for integer numerator/denominator perturbations:
    under passive-edge band `n ≤ E_p`, matching
    `2W + ((W+E)+n)/(kE_p)` forces `k = 4` and `n = 0`. -/
theorem base_shift_kn_forced_under_passive_bound
    {k n : ℕ} (hk : 0 < k) (hn_le : n ≤ E_passive)
    (h : base_shift = 2 * (W : ℝ) +
      (((((W + E_total + n : ℕ) : ℚ) / (k * E_passive)) : ℚ) : ℝ)) :
    k = 4 ∧ n = 0 := by
  have hcanon : base_shift = 2 * (W : ℝ) + (ledger_fraction : ℝ) := by
    simp [base_shift]
  have hfracR :
      (((((W + E_total + n : ℕ) : ℚ) / (k * E_passive)) : ℚ) : ℝ) = (ledger_fraction : ℝ) := by
    linarith [h, hcanon]
  have hfracQ : ((((W + E_total + n : ℕ) : ℚ) / (k * E_passive)) = ledger_fraction) := by
    exact_mod_cast hfracR
  exact ledger_fraction_kn_forced_under_passive_bound hk hn_le hfracQ

/-- Positivity-free packaged `base_shift` closure for integer perturbations:
    under passive-edge band `n ≤ E_p`, matching
    `2W + ((W+E)+n)/(kE_p)` forces `k = 4` and `n = 0`
    without explicit `k > 0`. -/
theorem base_shift_kn_forced_under_passive_bound_no_hk
    {k n : ℕ} (hn_le : n ≤ E_passive)
    (h : base_shift = 2 * (W : ℝ) +
      (((((W + E_total + n : ℕ) : ℚ) / (k * E_passive)) : ℚ) : ℝ)) :
    k = 4 ∧ n = 0 := by
  have hcanon : base_shift = 2 * (W : ℝ) + (ledger_fraction : ℝ) := by
    simp [base_shift]
  have hfracR :
      (((((W + E_total + n : ℕ) : ℚ) / (k * E_passive)) : ℚ) : ℝ) = (ledger_fraction : ℝ) := by
    linarith [h, hcanon]
  have hfracQ : ((((W + E_total + n : ℕ) : ℚ) / (k * E_passive)) = ledger_fraction) := by
    exact_mod_cast hfracR
  exact ledger_fraction_kn_forced_under_passive_bound_no_hk hn_le hfracQ

/-- Upstreamed radiative decomposition (`α² + 12α³`) used by the mass topology path. -/
theorem radiative_correction_channel_form :
    radiative_correction = alpha ^ 2 + 12 * alpha ^ 3 :=
  radiative_correction_channel_decomposition

/-- Refined shift split into geometric base plus explicit radiative channels. -/
theorem refined_shift_channel_form :
    refined_shift = base_shift + (alpha ^ 2 + 12 * alpha ^ 3) := by
  simpa [refined_shift] using congrArg (fun x => base_shift + x) radiative_correction_channel_form

/-- In the cubic-channel family `α² + cα³`, canonical radiative matching forces `c = 12`. -/
theorem radiative_cubic_coeff_forced
    {c : ℝ}
    (h : radiative_correction = alpha ^ 2 + c * alpha ^ 3) :
    c = 12 := by
  have hcanon : radiative_correction = alpha ^ 2 + 12 * alpha ^ 3 :=
    radiative_correction_channel_form
  have hα_bounds := Physics.ElectronMass.Necessity.alpha_bounds
  have hα_pos : 0 < alpha := by linarith [hα_bounds.1]
  have hα_ne : alpha ≠ 0 := ne_of_gt hα_pos
  have hmul : c * alpha ^ 3 = 12 * alpha ^ 3 := by
    linarith [h, hcanon]
  exact mul_right_cancel₀ (pow_ne_zero 3 hα_ne) hmul

/-- `refined_shift` version of cubic-channel forcing:
    in `base_shift + (α² + cα³)`, canonical matching forces `c = 12`. -/
theorem refined_shift_cubic_coeff_forced
    {c : ℝ}
    (h : refined_shift = base_shift + (alpha ^ 2 + c * alpha ^ 3)) :
    c = 12 := by
  have hcanon : refined_shift = base_shift + radiative_correction := by
    simp [refined_shift]
  have hrad : radiative_correction = alpha ^ 2 + c * alpha ^ 3 := by
    linarith [h, hcanon]
  exact radiative_cubic_coeff_forced hrad

/-- Joint affine-family forcing for `refined_shift` once base-shift role is fixed:
    if `base_shift = uW + ledger_fraction`, then matching
    `refined_shift = uW + ledger_fraction + (α² + cα³)` forces `u = 2` and `c = 12`. -/
theorem refined_shift_full_affine_forced_from_base_role
    {u c : ℝ}
    (hb : base_shift = u * (W : ℝ) + (ledger_fraction : ℝ))
    (h : refined_shift = u * (W : ℝ) + (ledger_fraction : ℝ) + (alpha ^ 2 + c * alpha ^ 3)) :
    u = 2 ∧ c = 12 := by
  have hu : u = 2 := base_shift_wallpaper_multiplier_forced hb
  have hc : c = 12 := by
    have hshift : refined_shift = base_shift + (alpha ^ 2 + c * alpha ^ 3) := by
      calc
        refined_shift = u * (W : ℝ) + (ledger_fraction : ℝ) + (alpha ^ 2 + c * alpha ^ 3) := h
        _ = base_shift + (alpha ^ 2 + c * alpha ^ 3) := by simp [hb]
    exact refined_shift_cubic_coeff_forced hshift
  exact ⟨hu, hc⟩

/-- Dual packaged route for `refined_shift` affine forcing:
    if cubic-channel scale is fixed (`c = 12`), then matching
    `uW + ledger_fraction + (α² + cα³)` forces the wallpaper multiplier `u = 2`. -/
theorem refined_shift_wallpaper_multiplier_forced_from_cubic_scale
    {u c : ℝ}
    (hc : c = 12)
    (h : refined_shift = u * (W : ℝ) + (ledger_fraction : ℝ) + (alpha ^ 2 + c * alpha ^ 3)) :
    u = 2 := by
  have hshift : refined_shift = u * (W : ℝ) + (ledger_fraction : ℝ) + (alpha ^ 2 + 12 * alpha ^ 3) := by
    simpa [hc] using h
  have hbase : base_shift = u * (W : ℝ) + (ledger_fraction : ℝ) := by
    linarith [hshift, refined_shift_channel_form]
  exact base_shift_wallpaper_multiplier_forced hbase

/-- Under fixed base-shift role, affine `refined_shift` matching packages an
    equivalence between wallpaper multiplier and cubic channel:
    `u = 2 ↔ c = 12`. -/
theorem refined_shift_wallpaper_iff_cubic_from_base_role
    {u c : ℝ}
    (hb : base_shift = u * (W : ℝ) + (ledger_fraction : ℝ))
    (h : refined_shift = u * (W : ℝ) + (ledger_fraction : ℝ) + (alpha ^ 2 + c * alpha ^ 3)) :
    u = 2 ↔ c = 12 := by
  have hpair : u = 2 ∧ c = 12 :=
    refined_shift_full_affine_forced_from_base_role hb h
  constructor
  · intro _hu
    exact hpair.2
  · intro hc
    exact refined_shift_wallpaper_multiplier_forced_from_cubic_scale hc h

/-- Electron-to-muon step split: fixed geometric term minus quadratic channel. -/
theorem step_e_mu_channel_split :
    step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 := by
  simp [step_e_mu, correction_order_2]

/-- With fixed inverse-π term and quadratic channel, canonical matching forces
    the passive-edge zeroth-order term in `e→μ`. -/
theorem step_e_mu_passive_term_forced
    {s : ℝ}
    (h : step_e_mu = s + 1 / (4 * Real.pi) - correction_order_2) :
    s = (E_passive : ℝ) := by
  have hcanon : step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 :=
    step_e_mu_channel_split
  linarith [h, hcanon]

/-- In the quadratic-channel family `E_p + 1/(4π) - qα²`, canonical `e→μ`
    matching forces `q = 1`. -/
theorem step_e_mu_quadratic_scale_forced
    {q : ℝ}
    (h : step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - q * correction_order_2) :
    q = 1 := by
  have hcanon : step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 :=
    step_e_mu_channel_split
  have hmul : q * correction_order_2 = correction_order_2 := by
    linarith [h, hcanon]
  have hα_bounds := Physics.ElectronMass.Necessity.alpha_bounds
  have hα_pos : 0 < alpha := by linarith [hα_bounds.1]
  have hα_ne : alpha ≠ 0 := ne_of_gt hα_pos
  have hco2_ne : correction_order_2 ≠ 0 := by
    simpa [correction_order_2] using (pow_ne_zero 2 hα_ne)
  have hmul' : q * correction_order_2 = (1 : ℝ) * correction_order_2 := by
    simpa [one_mul] using hmul
  exact mul_right_cancel₀ hco2_ne hmul'

/-- Joint forcing in the mixed `e→μ` family
    `E_p + 1/(kπ) - qα²`: if the inverse-π slot matches canonically, then
    canonical matching forces both `k = 4` and `q = 1`. -/
theorem step_e_mu_invpi_quadratic_forced
    {k : ℕ} {q : ℝ} (hk : 0 < k)
    (hchan : 1 / ((k : ℝ) * Real.pi) = 1 / (4 * Real.pi))
    (h : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2) :
    k = 4 ∧ q = 1 := by
  have hkpi_ne : ((k : ℝ) * Real.pi) ≠ 0 := by positivity
  have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
  have hmul : (1 : ℝ) * (4 * Real.pi) = (1 : ℝ) * ((k : ℝ) * Real.pi) := by
    exact (div_eq_div_iff hkpi_ne h4pi_ne).1 hchan
  have hden : (k : ℝ) * Real.pi = 4 * Real.pi := by
    nlinarith [hmul]
  have hk_real : (k : ℝ) = 4 := mul_right_cancel₀ (ne_of_gt Real.pi_pos) hden
  have hk4 : k = 4 := Nat.cast_inj.mp (by simpa using hk_real)
  have hq1 : q = 1 := by
    have h' : step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - q * correction_order_2 := by
      simpa [hk4] using h
    exact step_e_mu_quadratic_scale_forced h'
  exact ⟨hk4, hq1⟩

/-- Positivity-free mixed forcing for `e→μ`:
    in `E_p + 1/(kπ) - qα²`, inverse-π slot matching derives denominator
    positivity and forces `k = 4`, `q = 1` without explicit `k > 0`. -/
theorem step_e_mu_invpi_quadratic_forced_no_hk
    {k : ℕ} {q : ℝ}
    (hchan : 1 / ((k : ℝ) * Real.pi) = 1 / (4 * Real.pi))
    (h : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2) :
    k = 4 ∧ q = 1 := by
  have hk : 0 < k := by
    by_cases hk0 : k = 0
    · subst hk0
      have hzero : (0 : ℝ) = 1 / (4 * Real.pi) := by
        calc
          (0 : ℝ) = 1 / ((0 : ℝ) * Real.pi) := by simp
          _ = 1 / (4 * Real.pi) := by simpa using hchan
      have hpos : (0 : ℝ) < 1 / (4 * Real.pi) := by positivity
      linarith
    · exact Nat.pos_of_ne_zero hk0
  exact step_e_mu_invpi_quadratic_forced hk hchan h

/-- Dual packaged route for mixed `e→μ` forcing:
    if quadratic scale is fixed (`q = 1`), then in
    `E_p + 1/(kπ) - qα²` canonical matching forces `k = 4`. -/
theorem step_e_mu_invpi_denominator_forced_from_quadratic_scale
    {k : ℕ} {q : ℝ} (hk : 0 < k)
    (hq : q = 1)
    (h : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2) :
    k = 4 := by
  have h' : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - correction_order_2 := by
    simpa [hq] using h
  have hcanon : step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 :=
    step_e_mu_channel_split
  have hfrac : 1 / ((k : ℝ) * Real.pi) = 1 / (4 * Real.pi) := by
    linarith [h', hcanon]
  have hkpi_ne : ((k : ℝ) * Real.pi) ≠ 0 := by positivity
  have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
  have hmul : (1 : ℝ) * (4 * Real.pi) = (1 : ℝ) * ((k : ℝ) * Real.pi) := by
    exact (div_eq_div_iff hkpi_ne h4pi_ne).1 hfrac
  have hden : (k : ℝ) * Real.pi = 4 * Real.pi := by
    nlinarith [hmul]
  have hk_real : (k : ℝ) = 4 := mul_right_cancel₀ (ne_of_gt Real.pi_pos) hden
  exact Nat.cast_inj.mp (by simpa using hk_real)

/-- Positivity-free quadratic-fixed route for mixed `e→μ` forcing:
    in `E_p + 1/(kπ) - qα²`, canonical matching and `q=1` force `k=4`
    without explicit denominator-positivity assumptions. -/
theorem step_e_mu_invpi_denominator_forced_from_quadratic_scale_no_hk
    {k : ℕ} {q : ℝ}
    (hq : q = 1)
    (h : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2) :
    k = 4 := by
  have h' : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - correction_order_2 := by
    simpa [hq] using h
  by_cases hk0 : k = 0
  · subst hk0
    have hcanon : step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 :=
      step_e_mu_channel_split
    have hEq : (E_passive : ℝ) - correction_order_2 =
        (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 := by
      calc
        (E_passive : ℝ) - correction_order_2 = step_e_mu := by
          simpa using h'.symm
        _ = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 := hcanon
    have hfalse : (1 / (4 * Real.pi) : ℝ) = 0 := by
      linarith [hEq]
    have hpos : (0 : ℝ) < 1 / (4 * Real.pi) := by positivity
    linarith
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    exact step_e_mu_invpi_denominator_forced_from_quadratic_scale hk hq h

/-- Packaged mixed-family closure for `e→μ` under passive role + inverse-π channel match:
    in `s + 1/(kπ) - qα²`, canonical matching forces `s = E_p`, `k = 4`, `q = 1`. -/
theorem step_e_mu_full_mixed_family_forced_from_passive_and_channel
    {s : ℝ} {k : ℕ} {q : ℝ} (hk : 0 < k)
    (hs : s = (E_passive : ℝ))
    (hchan : 1 / ((k : ℝ) * Real.pi) = 1 / (4 * Real.pi))
    (h : step_e_mu = s + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2) :
    s = (E_passive : ℝ) ∧ k = 4 ∧ q = 1 := by
  have hkq : k = 4 ∧ q = 1 := by
    have h' : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2 := by
      simpa [hs] using h
    exact step_e_mu_invpi_quadratic_forced hk hchan h'
  exact ⟨hs, hkq.1, hkq.2⟩

/-- Positivity-free packaged mixed-family closure for `e→μ`
    under passive role + inverse-π channel match:
    in `s + 1/(kπ) - qα²`, canonical matching forces `s = E_p`, `k = 4`, `q = 1`
    without explicit `k > 0`. -/
theorem step_e_mu_full_mixed_family_forced_from_passive_and_channel_no_hk
    {s : ℝ} {k : ℕ} {q : ℝ}
    (hs : s = (E_passive : ℝ))
    (hchan : 1 / ((k : ℝ) * Real.pi) = 1 / (4 * Real.pi))
    (h : step_e_mu = s + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2) :
    s = (E_passive : ℝ) ∧ k = 4 ∧ q = 1 := by
  have hkq : k = 4 ∧ q = 1 := by
    have h' : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2 := by
      simpa [hs] using h
    exact step_e_mu_invpi_quadratic_forced_no_hk hchan h'
  exact ⟨hs, hkq.1, hkq.2⟩

/-- Complementary mixed-family packaging under passive role + quadratic-scale fixation:
    in `s + 1/(kπ) - qα²`, canonical matching and `q=1` force `s = E_p`, `k = 4`, `q = 1`. -/
theorem step_e_mu_full_mixed_family_forced_from_passive_and_quadratic_scale
    {s : ℝ} {k : ℕ} {q : ℝ} (hk : 0 < k)
    (hs : s = (E_passive : ℝ))
    (hq : q = 1)
    (h : step_e_mu = s + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2) :
    s = (E_passive : ℝ) ∧ k = 4 ∧ q = 1 := by
  have hk4 : k = 4 := by
    have h' : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2 := by
      simpa [hs] using h
    exact step_e_mu_invpi_denominator_forced_from_quadratic_scale hk hq h'
  exact ⟨hs, hk4, hq⟩

/-- Positivity-free complementary mixed-family packaging under passive role
    + quadratic-scale fixation:
    in `s + 1/(kπ) - qα²`, canonical matching and `q=1` force
    `s = E_p`, `k = 4`, `q = 1` without explicit `k > 0`. -/
theorem step_e_mu_full_mixed_family_forced_from_passive_and_quadratic_scale_no_hk
    {s : ℝ} {k : ℕ} {q : ℝ}
    (hs : s = (E_passive : ℝ))
    (hq : q = 1)
    (h : step_e_mu = s + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2) :
    s = (E_passive : ℝ) ∧ k = 4 ∧ q = 1 := by
  have hk4 : k = 4 := by
    have h' : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2 := by
      simpa [hs] using h
    exact step_e_mu_invpi_denominator_forced_from_quadratic_scale_no_hk hq h'
  exact ⟨hs, hk4, hq⟩

/-- In the mixed canonical family `E_p + 1/(kπ) - qα²`, denominator and quadratic
    slots are equivalent under canonical matching: `k = 4 ↔ q = 1`. -/
theorem step_e_mu_denominator_iff_quadratic_scale
    {k : ℕ} {q : ℝ} (hk : 0 < k)
    (h : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2) :
    k = 4 ↔ q = 1 := by
  constructor
  · intro hk4
    have h' : step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - q * correction_order_2 := by
      simpa [hk4] using h
    exact step_e_mu_quadratic_scale_forced h'
  · intro hq1
    exact step_e_mu_invpi_denominator_forced_from_quadratic_scale hk hq1 h

/-- In the one-parameter family `E_p + 1/(kπ) - α²`, matching the canonical step forces `k = 4`. -/
theorem step_e_mu_invpi_denominator_forced
    {k : ℕ} (hk : 0 < k)
    (h : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - correction_order_2) :
    k = 4 := by
  have hcanon : step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 :=
    step_e_mu_channel_split
  have hfrac : 1 / ((k : ℝ) * Real.pi) = 1 / (4 * Real.pi) := by
    linarith [h, hcanon]
  have hk_real_pos : 0 < (k : ℝ) := by
    exact_mod_cast hk
  have hkpi_ne : ((k : ℝ) * Real.pi) ≠ 0 := by positivity
  have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
  have hmul : (1 : ℝ) * (4 * Real.pi) = (1 : ℝ) * ((k : ℝ) * Real.pi) := by
    exact (div_eq_div_iff hkpi_ne h4pi_ne).1 hfrac
  have hden : (k : ℝ) * Real.pi = 4 * Real.pi := by
    nlinarith [hmul]
  have hpi_ne : Real.pi ≠ 0 := by exact ne_of_gt Real.pi_pos
  have hk_real : (k : ℝ) = 4 := mul_right_cancel₀ hpi_ne hden
  exact Nat.cast_inj.mp (by simpa using hk_real)

/-- Positivity-free inverse-π forcing for `e→μ`:
    denominator positivity is derived from canonical matching itself. -/
theorem step_e_mu_invpi_denominator_forced_no_hk
    {k : ℕ}
    (h : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - correction_order_2) :
    k = 4 := by
  by_cases hk0 : k = 0
  · subst hk0
    have hcanon : step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 :=
      step_e_mu_channel_split
    have hEq : (E_passive : ℝ) - correction_order_2 =
        (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 := by
      calc
        (E_passive : ℝ) - correction_order_2 = step_e_mu := by
          simpa using h.symm
        _ = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 := hcanon
    have hfalse : (1 / (4 * Real.pi) : ℝ) = 0 := by
      linarith [hEq]
    have hpos : (0 : ℝ) < 1 / (4 * Real.pi) := by positivity
    linarith
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    exact step_e_mu_invpi_denominator_forced hk h

/-- Positivity-free mixed-family equivalence for `e→μ`:
    in the canonical family `E_p + 1/(kπ) - qα²`, denominator and quadratic slots
    remain equivalent under canonical matching without an explicit `k > 0` premise. -/
theorem step_e_mu_denominator_iff_quadratic_scale_no_hk
    {k : ℕ} {q : ℝ}
    (h : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - q * correction_order_2) :
    k = 4 ↔ q = 1 := by
  constructor
  · intro hk4
    have h' : step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - q * correction_order_2 := by
      simpa [hk4] using h
    exact step_e_mu_quadratic_scale_forced h'
  · intro hq1
    have h' : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - correction_order_2 := by
      simpa [hq1] using h
    exact step_e_mu_invpi_denominator_forced_no_hk h'

/-- Real-scale version of the inverse-π forcing for `e→μ`: canonical matching forces scale `4`. -/
theorem step_e_mu_invpi_scale_forced
    {c : ℝ} (hc_pos : 0 < c)
    (h : step_e_mu = (E_passive : ℝ) + 1 / (c * Real.pi) - correction_order_2) :
    c = 4 := by
  have hcanon : step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 :=
    step_e_mu_channel_split
  have hfrac : 1 / (c * Real.pi) = 1 / (4 * Real.pi) := by
    linarith [h, hcanon]
  have hcpi_ne : (c * Real.pi) ≠ 0 := by positivity
  have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
  have hmul : (1 : ℝ) * (4 * Real.pi) = (1 : ℝ) * (c * Real.pi) := by
    exact (div_eq_div_iff hcpi_ne h4pi_ne).1 hfrac
  have hden : c * Real.pi = 4 * Real.pi := by
    nlinarith [hmul]
  exact mul_right_cancel₀ (ne_of_gt Real.pi_pos) hden

/-- Positivity-free real-scale inverse-π forcing for `e→μ`:
    canonical matching forces scale `4` without an explicit `c > 0` premise. -/
theorem step_e_mu_invpi_scale_forced_no_hc_pos
    {c : ℝ}
    (h : step_e_mu = (E_passive : ℝ) + 1 / (c * Real.pi) - correction_order_2) :
    c = 4 := by
  have hcanon : step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 :=
    step_e_mu_channel_split
  have hfrac : 1 / (c * Real.pi) = 1 / (4 * Real.pi) := by
    linarith [h, hcanon]
  by_cases hc0 : c = 0
  · subst hc0
    have hzero : (0 : ℝ) = 1 / (4 * Real.pi) := by
      calc
        (0 : ℝ) = 1 / ((0 : ℝ) * Real.pi) := by simp
        _ = 1 / (4 * Real.pi) := by simpa using hfrac
    have hpos : (0 : ℝ) < 1 / (4 * Real.pi) := by positivity
    linarith
  · have hcpi_ne : (c * Real.pi) ≠ 0 := mul_ne_zero hc0 (ne_of_gt Real.pi_pos)
    have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
    have hmul : (1 : ℝ) * (4 * Real.pi) = (1 : ℝ) * (c * Real.pi) := by
      exact (div_eq_div_iff hcpi_ne h4pi_ne).1 hfrac
    have hden : c * Real.pi = 4 * Real.pi := by
      nlinarith [hmul]
    exact mul_right_cancel₀ (ne_of_gt Real.pi_pos) hden

/-- Full one-parameter forcing for `e→μ` once passive-edge zeroth-order term is fixed:
    in `s + 1/(kπ) - α²`, canonical matching forces `k = 4`. -/
theorem step_e_mu_full_family_forced_from_passive_term
    {s : ℝ} {k : ℕ} (hk : 0 < k)
    (hs : s = (E_passive : ℝ))
    (h : step_e_mu = s + 1 / ((k : ℝ) * Real.pi) - correction_order_2) :
    s = (E_passive : ℝ) ∧ k = 4 := by
  have h' : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - correction_order_2 := by
    simpa [hs] using h
  exact ⟨hs, step_e_mu_invpi_denominator_forced hk h'⟩

/-- Positivity-free full one-parameter forcing for `e→μ` once passive-edge
    zeroth-order term is fixed:
    in `s + 1/(kπ) - α²`, canonical matching forces `k = 4` without explicit
    denominator-positivity assumptions. -/
theorem step_e_mu_full_family_forced_from_passive_term_no_hk
    {s : ℝ} {k : ℕ}
    (hs : s = (E_passive : ℝ))
    (h : step_e_mu = s + 1 / ((k : ℝ) * Real.pi) - correction_order_2) :
    s = (E_passive : ℝ) ∧ k = 4 := by
  have h' : step_e_mu = (E_passive : ℝ) + 1 / ((k : ℝ) * Real.pi) - correction_order_2 := by
    simpa [hs] using h
  exact ⟨hs, step_e_mu_invpi_denominator_forced_no_hk h'⟩

/-- Real-scale full forcing for `e→μ` once passive-edge zeroth-order term is fixed:
    in `s + 1/(cπ) - α²`, canonical matching forces `c = 4`. -/
theorem step_e_mu_full_real_family_forced_from_passive_term
    {s c : ℝ} (hc_pos : 0 < c)
    (hs : s = (E_passive : ℝ))
    (h : step_e_mu = s + 1 / (c * Real.pi) - correction_order_2) :
    s = (E_passive : ℝ) ∧ c = 4 := by
  have h' : step_e_mu = (E_passive : ℝ) + 1 / (c * Real.pi) - correction_order_2 := by
    simpa [hs] using h
  exact ⟨hs, step_e_mu_invpi_scale_forced hc_pos h'⟩

/-- Positivity-free real-scale full forcing for `e→μ` once passive-edge
    zeroth-order term is fixed:
    in `s + 1/(cπ) - α²`, canonical matching forces `c = 4` without explicit
    `c > 0`. -/
theorem step_e_mu_full_real_family_forced_from_passive_term_no_hc_pos
    {s c : ℝ}
    (hs : s = (E_passive : ℝ))
    (h : step_e_mu = s + 1 / (c * Real.pi) - correction_order_2) :
    s = (E_passive : ℝ) ∧ c = 4 := by
  have h' : step_e_mu = (E_passive : ℝ) + 1 / (c * Real.pi) - correction_order_2 := by
    simpa [hs] using h
  exact ⟨hs, step_e_mu_invpi_scale_forced_no_hc_pos h'⟩

/-- Positivity-free real-scale equivalence packaging for `e→μ`:
    under canonical matching in `s + 1/(cπ) - α²`, passive term and
    denominator scale are linked as `c = 4 ↔ s = E_p`. -/
theorem step_e_mu_scale_iff_passive_term_no_hc_pos
    {s c : ℝ}
    (h : step_e_mu = s + 1 / (c * Real.pi) - correction_order_2) :
    c = 4 ↔ s = (E_passive : ℝ) := by
  constructor
  · intro hc4
    have h' : step_e_mu = s + 1 / (4 * Real.pi) - correction_order_2 := by
      simpa [hc4] using h
    linarith [h', step_e_mu_channel_split]
  · intro hs
    have h' : step_e_mu = (E_passive : ℝ) + 1 / (c * Real.pi) - correction_order_2 := by
      simpa [hs] using h
    exact step_e_mu_invpi_scale_forced_no_hc_pos h'

/-- Packaged forcing from inverse-π channel matching in `e→μ`:
    if the inverse-π slot matches canonically, then the denominator and passive
    zeroth-order term are both forced in `s + 1/(kπ) - α²`. -/
theorem step_e_mu_full_family_forced_from_channel_match
    {s : ℝ} {k : ℕ} (hk : 0 < k)
    (hchan : 1 / ((k : ℝ) * Real.pi) = 1 / (4 * Real.pi))
    (h : step_e_mu = s + 1 / ((k : ℝ) * Real.pi) - correction_order_2) :
    s = (E_passive : ℝ) ∧ k = 4 := by
  have hkpi_ne : ((k : ℝ) * Real.pi) ≠ 0 := by positivity
  have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
  have hmul : (1 : ℝ) * (4 * Real.pi) = (1 : ℝ) * ((k : ℝ) * Real.pi) := by
    exact (div_eq_div_iff hkpi_ne h4pi_ne).1 hchan
  have hden : (k : ℝ) * Real.pi = 4 * Real.pi := by
    nlinarith [hmul]
  have hk_real : (k : ℝ) = 4 := by
    exact mul_right_cancel₀ (ne_of_gt Real.pi_pos) hden
  have hk4 : k = 4 := Nat.cast_inj.mp (by simpa using hk_real)
  have hs : s = (E_passive : ℝ) := by
    have h' : step_e_mu = s + 1 / (4 * Real.pi) - correction_order_2 := by
      simpa [hk4] using h
    linarith [h', step_e_mu_channel_split]
  exact ⟨hs, hk4⟩

/-- Positivity-free packaged forcing from inverse-π channel matching in `e→μ`:
    if the inverse-π slot matches canonically, then denominator and passive
    zeroth-order term are forced in `s + 1/(kπ) - α²` without explicit
    denominator-positivity assumptions. -/
theorem step_e_mu_full_family_forced_from_channel_match_no_hk
    {s : ℝ} {k : ℕ}
    (hchan : 1 / ((k : ℝ) * Real.pi) = 1 / (4 * Real.pi))
    (h : step_e_mu = s + 1 / ((k : ℝ) * Real.pi) - correction_order_2) :
    s = (E_passive : ℝ) ∧ k = 4 := by
  have hk : 0 < k := by
    by_cases hk0 : k = 0
    · subst hk0
      have hzero : (0 : ℝ) = 1 / (4 * Real.pi) := by
        calc
          (0 : ℝ) = 1 / ((0 : ℝ) * Real.pi) := by simp
          _ = 1 / (4 * Real.pi) := by simpa using hchan
      have hpos : (0 : ℝ) < 1 / (4 * Real.pi) := by positivity
      linarith
    · exact Nat.pos_of_ne_zero hk0
  exact step_e_mu_full_family_forced_from_channel_match hk hchan h

/-- The linear alpha coefficient in `step_mu_tau` evaluates to `37/2`. -/
theorem step_mu_tau_linear_coeff_eq_37_over_2 :
    ((2 * wallpaper_groups + D : ℝ) / 2) = (37 : ℝ) / 2 := by
  norm_num [wallpaper_groups, D]

/-- Muon-to-tau step in explicit geometric/linear-alpha form. -/
theorem step_mu_tau_channel_split :
    step_mu_tau = (6 : ℝ) - ((37 : ℝ) / 2) * alpha := by
  have hcoeff : ((2 * wallpaper_groups + D : ℝ) / 2) = (37 : ℝ) / 2 :=
    step_mu_tau_linear_coeff_eq_37_over_2
  have hfaces : (cube_faces D : ℝ) = 6 := by
    norm_num [cube_faces, D]
  calc
    step_mu_tau = (cube_faces D : ℝ) - ((2 * wallpaper_groups + D : ℝ) / 2) * alpha := by
      simp [step_mu_tau]
    _ = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by rw [hcoeff]
    _ = (6 : ℝ) - ((37 : ℝ) / 2) * alpha := by rw [hfaces]

/-- With fixed linear-alpha coefficient, canonical matching forces the face-count
    zeroth-order term in `μ→τ`. -/
theorem step_mu_tau_face_term_forced
    {f : ℝ}
    (h : step_mu_tau = f - ((37 : ℝ) / 2) * alpha) :
    f = (cube_faces D : ℝ) := by
  have hcanon : step_mu_tau = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
    calc
      step_mu_tau = (6 : ℝ) - ((37 : ℝ) / 2) * alpha := step_mu_tau_channel_split
      _ = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by norm_num [cube_faces, D]
  linarith [h, hcanon]

/-- Numeric form of `step_mu_tau_face_term_forced`: canonical matching forces `F = 6`. -/
theorem step_mu_tau_face_count_forced
    {f : ℝ}
    (h : step_mu_tau = f - ((37 : ℝ) / 2) * alpha) :
    f = 6 := by
  have hf : f = (cube_faces D : ℝ) := step_mu_tau_face_term_forced h
  have hfaces : (cube_faces D : ℝ) = 6 := by norm_num [cube_faces, D]
  linarith [hf, hfaces]

/-- In the linear family `F - cα`, matching the canonical μ→τ step forces `c = 37/2`. -/
theorem step_mu_tau_linear_coeff_forced
    {c : ℝ}
    (h : step_mu_tau = (cube_faces D : ℝ) - c * alpha) :
    c = (37 : ℝ) / 2 := by
  have hcanon : step_mu_tau = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
    calc
      step_mu_tau = (6 : ℝ) - ((37 : ℝ) / 2) * alpha := step_mu_tau_channel_split
      _ = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by norm_num [cube_faces, D]
  have hα_bounds := Physics.ElectronMass.Necessity.alpha_bounds
  have hα_pos : 0 < alpha := by linarith [hα_bounds.1]
  have hα_ne : alpha ≠ 0 := ne_of_gt hα_pos
  have hmul : c * alpha = ((37 : ℝ) / 2) * alpha := by
    linarith [h, hcanon]
  exact mul_right_cancel₀ hα_ne hmul

/-- Full affine-family forcing for `μ→τ` once the zeroth-order face term is fixed:
    in `f - cα`, canonical matching forces both `f = 6` and `c = 37/2`. -/
theorem step_mu_tau_full_affine_forced_from_face_term
    {f c : ℝ}
    (hf : f = (cube_faces D : ℝ))
    (h : step_mu_tau = f - c * alpha) :
    f = 6 ∧ c = (37 : ℝ) / 2 := by
  have hc : c = (37 : ℝ) / 2 := by
    have h' : step_mu_tau = (cube_faces D : ℝ) - c * alpha := by
      simpa [hf] using h
    exact step_mu_tau_linear_coeff_forced h'
  have hf6 : f = 6 := by
    calc
      f = (cube_faces D : ℝ) := hf
      _ = 6 := by norm_num [cube_faces, D]
  exact ⟨hf6, hc⟩

/-- Convenience specialization: if `f = 6`, canonical matching in `f - cα`
    forces the canonical linear coefficient `c = 37/2`. -/
theorem step_mu_tau_coeff_forced_from_six_face_term
    {c : ℝ}
    (h : step_mu_tau = (6 : ℝ) - c * alpha) :
    c = (37 : ℝ) / 2 := by
  have hf : (6 : ℝ) = (cube_faces D : ℝ) := by
    norm_num [cube_faces, D]
  have h' : step_mu_tau = (cube_faces D : ℝ) - c * alpha := by
    simpa [hf] using h
  exact step_mu_tau_linear_coeff_forced h'

/-- In the denominator family `F - ((2W + D)/k)α`, matching canonical `μ→τ` forces `k = 2`. -/
theorem step_mu_tau_denominator_forced
    {k : ℕ} (hk : 0 < k)
    (h : step_mu_tau = (cube_faces D : ℝ) - (((2 * wallpaper_groups + D : ℝ) / (k : ℝ)) * alpha)) :
    k = 2 := by
  have hcanon : step_mu_tau = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
    calc
      step_mu_tau = (6 : ℝ) - ((37 : ℝ) / 2) * alpha := step_mu_tau_channel_split
      _ = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by norm_num [cube_faces, D]
  have hα_bounds := Physics.ElectronMass.Necessity.alpha_bounds
  have hα_pos : 0 < alpha := by linarith [hα_bounds.1]
  have hα_ne : alpha ≠ 0 := ne_of_gt hα_pos
  have hmul :
      (((2 * wallpaper_groups + D : ℝ) / (k : ℝ)) * alpha) = ((37 : ℝ) / 2) * alpha := by
    linarith [h, hcanon]
  have hcoeff : ((2 * wallpaper_groups + D : ℝ) / (k : ℝ)) = (37 : ℝ) / 2 :=
    mul_right_cancel₀ hα_ne hmul
  have hnum : ((2 * wallpaper_groups + D : ℝ)) = 37 := by
    norm_num [wallpaper_groups, D]
  have h37 : ((37 : ℝ) / (k : ℝ)) = (37 : ℝ) / 2 := by
    calc
      (37 : ℝ) / (k : ℝ) = ((2 * wallpaper_groups + D : ℝ) / (k : ℝ)) := by
        simp [hnum]
      _ = (37 : ℝ) / 2 := hcoeff
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hcross : (37 : ℝ) * 2 = (37 : ℝ) * (k : ℝ) := by
    exact (div_eq_div_iff hk_ne (by norm_num : (2 : ℝ) ≠ 0)).mp h37
  have hk_real : (k : ℝ) = 2 := by nlinarith [hcross]
  exact Nat.cast_inj.mp (by simpa using hk_real)

/-- Real-scale version of μ→τ denominator forcing: canonical matching in
    `F - ((2W + D)/c)α` forces `c = 2`. -/
theorem step_mu_tau_scale_forced
    {c : ℝ} (hc_pos : 0 < c)
    (h : step_mu_tau = (cube_faces D : ℝ) - (((2 * wallpaper_groups + D : ℝ) / c) * alpha)) :
    c = 2 := by
  have hcanon : step_mu_tau = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
    calc
      step_mu_tau = (6 : ℝ) - ((37 : ℝ) / 2) * alpha := step_mu_tau_channel_split
      _ = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by norm_num [cube_faces, D]
  have hα_bounds := Physics.ElectronMass.Necessity.alpha_bounds
  have hα_pos : 0 < alpha := by linarith [hα_bounds.1]
  have hα_ne : alpha ≠ 0 := ne_of_gt hα_pos
  have hmul :
      (((2 * wallpaper_groups + D : ℝ) / c) * alpha) = ((37 : ℝ) / 2) * alpha := by
    linarith [h, hcanon]
  have hcoeff : ((2 * wallpaper_groups + D : ℝ) / c) = (37 : ℝ) / 2 :=
    mul_right_cancel₀ hα_ne hmul
  have hnum : ((2 * wallpaper_groups + D : ℝ)) = 37 := by
    norm_num [wallpaper_groups, D]
  have h37 : ((37 : ℝ) / c) = (37 : ℝ) / 2 := by
    calc
      (37 : ℝ) / c = ((2 * wallpaper_groups + D : ℝ) / c) := by
        simp [hnum]
      _ = (37 : ℝ) / 2 := hcoeff
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hcross : (37 : ℝ) * 2 = (37 : ℝ) * c := by
    exact (div_eq_div_iff hc_ne (by norm_num : (2 : ℝ) ≠ 0)).mp h37
  nlinarith [hcross]

/-- Positivity-free real-scale μ→τ denominator forcing:
    canonical matching in `F - ((2W + D)/c)α` still forces `c = 2`
    without explicitly assuming `c > 0`. -/
theorem step_mu_tau_scale_forced_no_hc_pos
    {c : ℝ}
    (h : step_mu_tau = (cube_faces D : ℝ) - (((2 * wallpaper_groups + D : ℝ) / c) * alpha)) :
    c = 2 := by
  have hc_ne : c ≠ 0 := by
    intro hc0
    subst hc0
    have hface : step_mu_tau = (cube_faces D : ℝ) := by
      simpa using h
    have hcanon : step_mu_tau =
        (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
      calc
        step_mu_tau = (6 : ℝ) - ((37 : ℝ) / 2) * alpha := step_mu_tau_channel_split
        _ = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
          norm_num [cube_faces, D]
    have hα_bounds := Physics.ElectronMass.Necessity.alpha_bounds
    have hα_pos : 0 < alpha := by linarith [hα_bounds.1]
    linarith [hface, hcanon, hα_pos]
  have hcanon : step_mu_tau = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
    calc
      step_mu_tau = (6 : ℝ) - ((37 : ℝ) / 2) * alpha := step_mu_tau_channel_split
      _ = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by norm_num [cube_faces, D]
  have hα_bounds := Physics.ElectronMass.Necessity.alpha_bounds
  have hα_pos : 0 < alpha := by linarith [hα_bounds.1]
  have hα_ne : alpha ≠ 0 := ne_of_gt hα_pos
  have hmul :
      (((2 * wallpaper_groups + D : ℝ) / c) * alpha) = ((37 : ℝ) / 2) * alpha := by
    linarith [h, hcanon]
  have hcoeff : ((2 * wallpaper_groups + D : ℝ) / c) = (37 : ℝ) / 2 :=
    mul_right_cancel₀ hα_ne hmul
  have hnum : ((2 * wallpaper_groups + D : ℝ)) = 37 := by
    norm_num [wallpaper_groups, D]
  have h37 : ((37 : ℝ) / c) = (37 : ℝ) / 2 := by
    calc
      (37 : ℝ) / c = ((2 * wallpaper_groups + D : ℝ) / c) := by simp [hnum]
      _ = (37 : ℝ) / 2 := hcoeff
  have hcross : (37 : ℝ) * 2 = (37 : ℝ) * c := by
    exact (div_eq_div_iff hc_ne (by norm_num : (2 : ℝ) ≠ 0)).mp h37
  nlinarith [hcross]

/-- Positivity-free packaged real-scale forcing for `μ→τ`:
    with face-term role fixed, canonical matching in
    `f - ((2W + D)/c)α` forces `f = 6` and `c = 2`
    without explicit `c > 0`. -/
theorem step_mu_tau_full_real_family_forced_from_face_term_no_hc_pos
    {f c : ℝ}
    (hf : f = (cube_faces D : ℝ))
    (h : step_mu_tau = f - (((2 * wallpaper_groups + D : ℝ) / c) * alpha)) :
    f = 6 ∧ c = 2 := by
  have h' : step_mu_tau =
      (cube_faces D : ℝ) - (((2 * wallpaper_groups + D : ℝ) / c) * alpha) := by
    simpa [hf] using h
  have hc2 : c = 2 := step_mu_tau_scale_forced_no_hc_pos h'
  have hf6 : f = 6 := by
    calc
      f = (cube_faces D : ℝ) := hf
      _ = 6 := by norm_num [cube_faces, D]
  exact ⟨hf6, hc2⟩

/-- Positivity-free real-scale equivalence packaging for `μ→τ`:
    under canonical matching in `f - ((2W + D)/c)α`, the face count and
    denominator scale are linked as `c = 2 ↔ f = 6`. -/
theorem step_mu_tau_scale_iff_face_count_no_hc_pos
    {f c : ℝ}
    (h : step_mu_tau = f - (((2 * wallpaper_groups + D : ℝ) / c) * alpha)) :
    c = 2 ↔ f = 6 := by
  constructor
  · intro hc2
    have hcanon : step_mu_tau = (6 : ℝ) - ((37 : ℝ) / 2) * alpha := step_mu_tau_channel_split
    have h' : step_mu_tau = f - ((37 : ℝ) / 2) * alpha := by
      calc
        step_mu_tau = f - (((2 * wallpaper_groups + D : ℝ) / c) * alpha) := h
        _ = f - (((2 * wallpaper_groups + D : ℝ) / 2) * alpha) := by simp [hc2]
        _ = f - ((37 : ℝ) / 2) * alpha := by norm_num [wallpaper_groups, D]
    linarith [hcanon, h']
  · intro hf6
    have hfCube : f = (cube_faces D : ℝ) := by
      calc
        f = 6 := hf6
        _ = (cube_faces D : ℝ) := by norm_num [cube_faces, D]
    have h' : step_mu_tau =
        (cube_faces D : ℝ) - (((2 * wallpaper_groups + D : ℝ) / c) * alpha) := by
      simpa [hfCube] using h
    exact step_mu_tau_scale_forced_no_hc_pos h'

/-- Cross-sector positivity-free real-scale iff packaging:
    combines `e→μ` and `μ→τ` canonical real-scale matchings into one statement.
    Under canonical matching forms, denominator scales are equivalent to their
    corresponding zeroth-order geometric terms without explicit positivity
    assumptions. -/
theorem lepton_real_scale_iff_bundle_no_hc_pos
    {s c_e f c_mu : ℝ}
    (he : step_e_mu = s + 1 / (c_e * Real.pi) - correction_order_2)
    (hmu : step_mu_tau = f - (((2 * wallpaper_groups + D : ℝ) / c_mu) * alpha)) :
    (c_e = 4 ↔ s = (E_passive : ℝ)) ∧ (c_mu = 2 ↔ f = 6) := by
  refine ⟨?_, ?_⟩
  · exact step_e_mu_scale_iff_passive_term_no_hc_pos he
  · exact step_mu_tau_scale_iff_face_count_no_hc_pos hmu

/-- In the numerator-offset family `F - ((2W+n)/2)α`, canonical matching forces
    the offset to be exactly `n = D` (hence `n = 3`). -/
theorem step_mu_tau_numerator_offset_forced
    {n : ℕ}
    (h : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / 2) * alpha)) :
    n = D := by
  have hcanon : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + D : ℕ) : ℝ) / 2) * alpha) := by
    simp [step_mu_tau]
  have hα_bounds := Physics.ElectronMass.Necessity.alpha_bounds
  have hα_pos : 0 < alpha := by linarith [hα_bounds.1]
  have hα_ne : alpha ≠ 0 := ne_of_gt hα_pos
  have hmul :
      ((((2 * wallpaper_groups + n : ℕ) : ℝ) / 2) * alpha) =
        ((((2 * wallpaper_groups + D : ℕ) : ℝ) / 2) * alpha) := by
    linarith [h, hcanon]
  have hcoeff :
      (((2 * wallpaper_groups + n : ℕ) : ℝ) / 2) =
        (((2 * wallpaper_groups + D : ℕ) : ℝ) / 2) :=
    mul_right_cancel₀ hα_ne hmul
  have hnumR :
      ((2 * wallpaper_groups + n : ℕ) : ℝ) =
        ((2 * wallpaper_groups + D : ℕ) : ℝ) := by
    nlinarith [hcoeff]
  have hnumN : 2 * wallpaper_groups + n = 2 * wallpaper_groups + D := by
    exact_mod_cast hnumR
  exact Nat.add_left_cancel hnumN

/-- Joint Diophantine forcing for the `μ→τ` coefficient family:
    with `n` constrained to the dimensional band `n ≤ D`, canonical matching in
    `F - ((2W+n)/k)α` forces both `k = 2` and `n = D`. -/
theorem step_mu_tau_kn_forced_under_dim_bound
    {k n : ℕ} (hk : 0 < k) (hn_le : n ≤ D)
    (h : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    k = 2 ∧ n = D := by
  have hcanon : step_mu_tau =
      (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
    calc
      step_mu_tau = (6 : ℝ) - ((37 : ℝ) / 2) * alpha := step_mu_tau_channel_split
      _ = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
        norm_num [cube_faces, D]
  have hα_bounds := Physics.ElectronMass.Necessity.alpha_bounds
  have hα_pos : 0 < alpha := by linarith [hα_bounds.1]
  have hα_ne : alpha ≠ 0 := ne_of_gt hα_pos
  have hmul :
      ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)
        = ((37 : ℝ) / 2) * alpha := by
    linarith [h, hcanon]
  have hcoeff :
      (((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ))
        = (37 : ℝ) / 2 := by
    exact mul_right_cancel₀ hα_ne hmul
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hcross :
      (2 : ℝ) * ((2 * wallpaper_groups + n : ℕ) : ℝ) = (37 : ℝ) * (k : ℝ) := by
    have htmp := hcoeff
    field_simp [hk_ne] at htmp
    nlinarith [htmp]
  have hD3 : D = 3 := by native_decide
  have hA_le : 2 * wallpaper_groups + n ≤ 37 := by
    have hn3 : n ≤ 3 := by simpa [hD3] using hn_le
    calc
      2 * wallpaper_groups + n ≤ 2 * wallpaper_groups + 3 := Nat.add_le_add_left hn3 _
      _ = 37 := by native_decide
  have hA_leR : ((2 * wallpaper_groups + n : ℕ) : ℝ) ≤ 37 := by
    exact_mod_cast hA_le
  have hk_le_twoR : (k : ℝ) ≤ 2 := by
    nlinarith [hcross, hA_leR]
  have hk_le_two : k ≤ 2 := by exact_mod_cast hk_le_twoR
  have hcrossNat : 2 * (2 * wallpaper_groups + n) = 37 * k := by
    exact_mod_cast hcross
  have hk_ne_one : k ≠ 1 := by
    intro hk1
    have hcontra : 2 * (2 * wallpaper_groups + n) = 37 := by
      simpa [hk1] using hcrossNat
    omega
  have hk_cases : k = 1 ∨ k = 2 := by
    have hk_ge_one : 1 ≤ k := Nat.succ_le_of_lt hk
    omega
  have hk_two : k = 2 := by
    rcases hk_cases with hk1 | hk2
    · exact (hk_ne_one hk1).elim
    · exact hk2
  have hA_eq37 : 2 * wallpaper_groups + n = 37 := by
    have h74 : 2 * (2 * wallpaper_groups + n) = 74 := by
      simpa [hk_two] using hcrossNat
    omega
  have hW17 : wallpaper_groups = 17 := by native_decide
  have hn3 : n = 3 := by
    omega
  have hnD : n = D := by
    calc
      n = 3 := hn3
      _ = D := by simp [hD3]
  exact ⟨hk_two, hnD⟩

/-- Positivity-free Diophantine forcing for the `μ→τ` coefficient family:
    with `n ≤ D`, canonical matching in `F - ((2W+n)/k)α` still forces
    `k = 2` and `n = D`, deriving denominator positivity from the match itself. -/
theorem step_mu_tau_kn_forced_under_dim_bound_no_hk
    {k n : ℕ} (hn_le : n ≤ D)
    (h : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    k = 2 ∧ n = D := by
  have hk : 0 < k := by
    by_cases hk0 : k = 0
    · subst hk0
      have hface : step_mu_tau = (cube_faces D : ℝ) := by
        simpa using h
      have hcanon : step_mu_tau =
          (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
        calc
          step_mu_tau = (6 : ℝ) - ((37 : ℝ) / 2) * alpha := step_mu_tau_channel_split
          _ = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
            norm_num [cube_faces, D]
      have hα_bounds := Physics.ElectronMass.Necessity.alpha_bounds
      have hα_pos : 0 < alpha := by linarith [hα_bounds.1]
      linarith [hface, hcanon, hα_pos]
    · exact Nat.pos_of_ne_zero hk0
  exact step_mu_tau_kn_forced_under_dim_bound hk hn_le h

/-- Under dimensional band `n ≤ D`, canonical matching in `F - ((2W+n)/k)α`
    makes denominator and numerator slots equivalent: `k = 2 ↔ n = D`. -/
theorem step_mu_tau_denominator_iff_numerator_under_dim_bound
    {k n : ℕ} (hk : 0 < k) (hn_le : n ≤ D)
    (h : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    k = 2 ↔ n = D := by
  have hkn : k = 2 ∧ n = D := step_mu_tau_kn_forced_under_dim_bound hk hn_le h
  constructor
  · intro _hk2
    exact hkn.2
  · intro _hnD
    exact hkn.1

/-- Positivity-free denominator/numerator slot equivalence for `μ→τ`:
    with `n ≤ D`, canonical matching still packages `k = 2 ↔ n = D` without an
    explicit `k > 0` premise. -/
theorem step_mu_tau_denominator_iff_numerator_under_dim_bound_no_hk
    {k n : ℕ} (hn_le : n ≤ D)
    (h : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    k = 2 ↔ n = D := by
  have hkn : k = 2 ∧ n = D := step_mu_tau_kn_forced_under_dim_bound_no_hk hn_le h
  constructor
  · intro _hk2
    exact hkn.2
  · intro _hnD
    exact hkn.1

/-- Cross-sector positivity-free integer-family iff packaging:
    combines `e→μ` mixed-slot equivalence and `μ→τ` denominator/numerator
    equivalence into a single bundled statement. -/
theorem lepton_integer_slot_iff_bundle_no_hk
    {k_e : ℕ} {q : ℝ} {k_mu n : ℕ}
    (h_e : step_e_mu = (E_passive : ℝ) + 1 / ((k_e : ℝ) * Real.pi) - q * correction_order_2)
    (hn_le : n ≤ D)
    (h_mu : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k_mu : ℝ)) * alpha)) :
    (k_e = 4 ↔ q = 1) ∧ (k_mu = 2 ↔ n = D) := by
  refine ⟨?_, ?_⟩
  · exact step_e_mu_denominator_iff_quadratic_scale_no_hk h_e
  · exact step_mu_tau_denominator_iff_numerator_under_dim_bound_no_hk hn_le h_mu

/-- Under dimensional band `n ≤ D`, canonical matching in `F - ((2W+n)/k)α`
    makes coefficient-slot and canonical integer pair equivalent:
    `((2W+n)/k) = 37/2 ↔ (k = 2 ∧ n = D)`. -/
theorem step_mu_tau_coeff_iff_kn_under_dim_bound
    {k n : ℕ} (hk : 0 < k) (hn_le : n ≤ D)
    (h : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    (((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ) = (37 : ℝ) / 2) ↔
      (k = 2 ∧ n = D) := by
  constructor
  · intro _hcoeff
    exact step_mu_tau_kn_forced_under_dim_bound hk hn_le h
  · intro hkn
    rcases hkn with ⟨hk2, hnD⟩
    have hnum : ((2 * wallpaper_groups + n : ℕ) : ℝ) = (37 : ℝ) := by
      calc
        ((2 * wallpaper_groups + n : ℕ) : ℝ)
            = ((2 * wallpaper_groups + D : ℕ) : ℝ) := by simp [hnD]
        _ = (37 : ℝ) := by norm_num [wallpaper_groups, D]
    calc
      (((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ))
          = (37 : ℝ) / (k : ℝ) := by simp [hnum]
      _ = (37 : ℝ) / 2 := by simp [hk2]

/-- Positivity-free coefficient-slot equivalence for `μ→τ`:
    with `n ≤ D`, canonical matching still packages
    `((2W+n)/k = 37/2) ↔ (k = 2 ∧ n = D)` without an explicit `k > 0` premise. -/
theorem step_mu_tau_coeff_iff_kn_under_dim_bound_no_hk
    {k n : ℕ} (hn_le : n ≤ D)
    (h : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    (((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ) = (37 : ℝ) / 2) ↔
      (k = 2 ∧ n = D) := by
  constructor
  · intro _hcoeff
    exact step_mu_tau_kn_forced_under_dim_bound_no_hk hn_le h
  · intro hkn
    rcases hkn with ⟨hk2, hnD⟩
    have hnum : ((2 * wallpaper_groups + n : ℕ) : ℝ) = (37 : ℝ) := by
      calc
        ((2 * wallpaper_groups + n : ℕ) : ℝ)
            = ((2 * wallpaper_groups + D : ℕ) : ℝ) := by simp [hnD]
        _ = (37 : ℝ) := by norm_num [wallpaper_groups, D]
    calc
      (((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ))
          = (37 : ℝ) / (k : ℝ) := by simp [hnum]
      _ = (37 : ℝ) / 2 := by simp [hk2]

/-- Packaged full-family coefficient-slot equivalence for constrained `μ→τ` families:
    with face-term role fixed and dimensional band `n ≤ D`, canonical matching in
    `f - ((2W+n)/k)α` forces `f = 6` and packages
    `((2W+n)/k = 37/2) ↔ (k = 2 ∧ n = D)`. -/
theorem step_mu_tau_full_family_coeff_iff_under_dim_bound
    {f : ℝ} {k n : ℕ} (hk : 0 < k) (hn_le : n ≤ D)
    (hf : f = (cube_faces D : ℝ))
    (h : step_mu_tau = f - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    f = 6 ∧
      ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ) = (37 : ℝ) / 2) ↔
        (k = 2 ∧ n = D)) := by
  have h' : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha) := by
    simpa [hf] using h
  have hcoeffiff :
      ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ) = (37 : ℝ) / 2) ↔
        (k = 2 ∧ n = D)) :=
    step_mu_tau_coeff_iff_kn_under_dim_bound hk hn_le h'
  have hf6 : f = 6 := by
    calc
      f = (cube_faces D : ℝ) := hf
      _ = 6 := by norm_num [cube_faces, D]
  exact ⟨hf6, hcoeffiff⟩

/-- Positivity-free packaged full-family coefficient-slot equivalence for
    constrained `μ→τ` families:
    with face-term role fixed and `n ≤ D`, canonical matching in
    `f - ((2W+n)/k)α` forces `f = 6` and packages
    `((2W+n)/k = 37/2) ↔ (k = 2 ∧ n = D)` without explicit `k > 0`. -/
theorem step_mu_tau_full_family_coeff_iff_under_dim_bound_no_hk
    {f : ℝ} {k n : ℕ} (hn_le : n ≤ D)
    (hf : f = (cube_faces D : ℝ))
    (h : step_mu_tau = f - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    f = 6 ∧
      ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ) = (37 : ℝ) / 2) ↔
        (k = 2 ∧ n = D)) := by
  have h' : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha) := by
    simpa [hf] using h
  have hcoeffiff :
      ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ) = (37 : ℝ) / 2) ↔
        (k = 2 ∧ n = D)) :=
    step_mu_tau_coeff_iff_kn_under_dim_bound_no_hk hn_le h'
  have hf6 : f = 6 := by
    calc
      f = (cube_faces D : ℝ) := hf
      _ = 6 := by norm_num [cube_faces, D]
  exact ⟨hf6, hcoeffiff⟩

/-- Assumption-reduced coefficient equivalence for constrained `μ→τ` families:
    under dimensional band `n ≤ D`, canonical matching in `f - ((2W+n)/k)α`
    makes coefficient-slot matching equivalent to full canonical closure:
    `((2W+n)/k = 37/2) ↔ (f = 6 ∧ k = 2 ∧ n = D)`. -/
theorem step_mu_tau_coeff_iff_full_forced_under_dim_bound
    {f : ℝ} {k n : ℕ} (hk : 0 < k) (hn_le : n ≤ D)
    (h : step_mu_tau = f - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ) = (37 : ℝ) / 2) ↔
      (f = 6 ∧ k = 2 ∧ n = D)) := by
  constructor
  · intro hcoeff
    have hface : step_mu_tau = f - ((37 : ℝ) / 2) * alpha := by
      calc
        step_mu_tau = f - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha) := h
        _ = f - ((37 : ℝ) / 2) * alpha := by rw [hcoeff]
    have hf6 : f = 6 := step_mu_tau_face_count_forced hface
    have hfCube : f = (cube_faces D : ℝ) := by
      calc
        f = 6 := hf6
        _ = (cube_faces D : ℝ) := by norm_num [cube_faces, D]
    have h' : step_mu_tau =
        (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha) := by
      simpa [hfCube] using h
    have hkn : k = 2 ∧ n = D := step_mu_tau_kn_forced_under_dim_bound hk hn_le h'
    exact ⟨hf6, hkn.1, hkn.2⟩
  · intro hfull
    rcases hfull with ⟨hf6, hk2, hnD⟩
    have hnum : ((2 * wallpaper_groups + n : ℕ) : ℝ) = (37 : ℝ) := by
      calc
        ((2 * wallpaper_groups + n : ℕ) : ℝ)
            = ((2 * wallpaper_groups + D : ℕ) : ℝ) := by simp [hnD]
        _ = (37 : ℝ) := by norm_num [wallpaper_groups, D]
    calc
      (((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ))
          = (37 : ℝ) / (k : ℝ) := by simp [hnum]
      _ = (37 : ℝ) / 2 := by simp [hk2]

/-- Assumption-reduced variant of coefficient-match forcing:
    denominator positivity is derived from the coefficient equation itself, so
    `k > 0` need not be assumed explicitly. -/
theorem step_mu_tau_full_family_forced_from_coeff_match_no_hk
    {f : ℝ} {k n : ℕ} (hn_le : n ≤ D)
    (hcoeff : (((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) = (37 : ℝ) / 2)
    (h : step_mu_tau = f - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    f = 6 ∧ k = 2 ∧ n = D := by
  have hk : 0 < k := by
    by_cases hk0 : k = 0
    · subst hk0
      have hfalse : (0 : ℝ) = (37 : ℝ) / 2 := by simpa using hcoeff
      norm_num at hfalse
    · exact Nat.pos_of_ne_zero hk0
  have hiff :
      ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ) = (37 : ℝ) / 2) ↔
        (f = 6 ∧ k = 2 ∧ n = D)) :=
    step_mu_tau_coeff_iff_full_forced_under_dim_bound hk hn_le h
  exact hiff.mp hcoeff

/-- Assumption-reduced coefficient equivalence:
    with dimensional band `n ≤ D`, canonical matching in `f - ((2W+n)/k)α`
    gives `((2W+n)/k = 37/2) ↔ (f = 6 ∧ k = 2 ∧ n = D)` without an explicit
    `k > 0` premise. -/
theorem step_mu_tau_coeff_iff_full_forced_under_dim_bound_no_hk
    {f : ℝ} {k n : ℕ} (hn_le : n ≤ D)
    (h : step_mu_tau = f - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ) = (37 : ℝ) / 2) ↔
      (f = 6 ∧ k = 2 ∧ n = D)) := by
  constructor
  · intro hcoeff
    exact step_mu_tau_full_family_forced_from_coeff_match_no_hk hn_le hcoeff h
  · intro hfull
    rcases hfull with ⟨_hf6, hk2, hnD⟩
    have hnum : ((2 * wallpaper_groups + n : ℕ) : ℝ) = (37 : ℝ) := by
      calc
        ((2 * wallpaper_groups + n : ℕ) : ℝ)
            = ((2 * wallpaper_groups + D : ℕ) : ℝ) := by simp [hnD]
        _ = (37 : ℝ) := by norm_num [wallpaper_groups, D]
    calc
      (((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ))
          = (37 : ℝ) / (k : ℝ) := by simp [hnum]
      _ = (37 : ℝ) / 2 := by simp [hk2]

/-- Packaged equivalence closure for constrained `μ→τ` families:
    with face-term role fixed and dimensional band `n ≤ D`, canonical matching in
    `f - ((2W+n)/k)α` forces `f = 6` and equivalently `k = 2 ↔ n = D`. -/
theorem step_mu_tau_full_family_iff_under_dim_bound
    {f : ℝ} {k n : ℕ} (hk : 0 < k) (hn_le : n ≤ D)
    (hf : f = (cube_faces D : ℝ))
    (h : step_mu_tau = f - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    f = 6 ∧ (k = 2 ↔ n = D) := by
  have h' : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha) := by
    simpa [hf] using h
  have hiff : k = 2 ↔ n = D :=
    step_mu_tau_denominator_iff_numerator_under_dim_bound hk hn_le h'
  have hf6 : f = 6 := by
    calc
      f = (cube_faces D : ℝ) := hf
      _ = 6 := by norm_num [cube_faces, D]
  exact ⟨hf6, hiff⟩

/-- Positivity-free packaged equivalence closure for constrained `μ→τ` families:
    with face-term role fixed and `n ≤ D`, canonical matching in
    `f - ((2W+n)/k)α` forces `f = 6` and packages `k = 2 ↔ n = D`
    without explicit `k > 0`. -/
theorem step_mu_tau_full_family_iff_under_dim_bound_no_hk
    {f : ℝ} {k n : ℕ} (hn_le : n ≤ D)
    (hf : f = (cube_faces D : ℝ))
    (h : step_mu_tau = f - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    f = 6 ∧ (k = 2 ↔ n = D) := by
  have h' : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha) := by
    simpa [hf] using h
  have hiff : k = 2 ↔ n = D :=
    step_mu_tau_denominator_iff_numerator_under_dim_bound_no_hk hn_le h'
  have hf6 : f = 6 := by
    calc
      f = (cube_faces D : ℝ) := hf
      _ = 6 := by norm_num [cube_faces, D]
  exact ⟨hf6, hiff⟩

/-- Packaged constrained-family forcing for `μ→τ`:
    with face-term role fixed and `n ≤ D`, canonical matching in
    `f - ((2W+n)/k)α` forces `f = 6`, `k = 2`, and `n = D`. -/
theorem step_mu_tau_full_family_forced_under_dim_bound
    {f : ℝ} {k n : ℕ} (hk : 0 < k) (hn_le : n ≤ D)
    (hf : f = (cube_faces D : ℝ))
    (h : step_mu_tau = f - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    f = 6 ∧ k = 2 ∧ n = D := by
  have h' : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha) := by
    simpa [hf] using h
  have hkn : k = 2 ∧ n = D := step_mu_tau_kn_forced_under_dim_bound hk hn_le h'
  have hf6 : f = 6 := by
    calc
      f = (cube_faces D : ℝ) := hf
      _ = 6 := by norm_num [cube_faces, D]
  exact ⟨hf6, hkn.1, hkn.2⟩

/-- Positivity-free packaged constrained-family forcing for `μ→τ`:
    with face-term role fixed and `n ≤ D`, canonical matching in
    `f - ((2W+n)/k)α` forces `f = 6`, `k = 2`, and `n = D`
    without explicit `k > 0`. -/
theorem step_mu_tau_full_family_forced_under_dim_bound_no_hk
    {f : ℝ} {k n : ℕ} (hn_le : n ≤ D)
    (hf : f = (cube_faces D : ℝ))
    (h : step_mu_tau = f - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    f = 6 ∧ k = 2 ∧ n = D := by
  have h' : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha) := by
    simpa [hf] using h
  have hkn : k = 2 ∧ n = D := step_mu_tau_kn_forced_under_dim_bound_no_hk hn_le h'
  have hf6 : f = 6 := by
    calc
      f = (cube_faces D : ℝ) := hf
      _ = 6 := by norm_num [cube_faces, D]
  exact ⟨hf6, hkn.1, hkn.2⟩

/-- Complementary packaged forcing for `μ→τ` from canonical coefficient match:
    with dimensional band `n ≤ D`, if the coefficient slot equals `37/2` in
    `f - ((2W+n)/k)α`, then canonical matching forces `f = 6`, `k = 2`, and `n = D`. -/
theorem step_mu_tau_full_family_forced_from_coeff_match
    {f : ℝ} {k n : ℕ} (hk : 0 < k) (hn_le : n ≤ D)
    (hcoeff : (((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) = (37 : ℝ) / 2)
    (h : step_mu_tau = f - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha)) :
    f = 6 ∧ k = 2 ∧ n = D := by
  have hface : step_mu_tau = f - ((37 : ℝ) / 2) * alpha := by
    calc
      step_mu_tau = f - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha) := h
      _ = f - ((37 : ℝ) / 2) * alpha := by rw [hcoeff]
  have hf6 : f = 6 := step_mu_tau_face_count_forced hface
  have hfCube : f = (cube_faces D : ℝ) := by
    calc
      f = 6 := hf6
      _ = (cube_faces D : ℝ) := by norm_num [cube_faces, D]
  have h' : step_mu_tau =
      (cube_faces D : ℝ) - ((((2 * wallpaper_groups + n : ℕ) : ℝ) / (k : ℝ)) * alpha) := by
    simpa [hfCube] using h
  have hkn : k = 2 ∧ n = D := step_mu_tau_kn_forced_under_dim_bound hk hn_le h'
  exact ⟨hf6, hkn.1, hkn.2⟩

/-- O4 closure certificate (channel-level form):
    electron-break refinement splits into canonical geometric + radiative channels,
    and both generation steps are in canonical forced forms. -/
theorem o4_channel_closure_certificate :
    refined_shift = (2 * (W : ℝ) + (ledger_fraction : ℝ)) + (alpha ^ 2 + 12 * alpha ^ 3) ∧
    step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 ∧
    step_mu_tau = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
  refine ⟨?_, step_e_mu_channel_split, ?_⟩
  · calc
      refined_shift = base_shift + (alpha ^ 2 + 12 * alpha ^ 3) := refined_shift_channel_form
      _ = (2 * (W : ℝ) + (ledger_fraction : ℝ)) + (alpha ^ 2 + 12 * alpha ^ 3) := by
            simp [base_shift]
  · calc
      step_mu_tau = (6 : ℝ) - ((37 : ℝ) / 2) * alpha := step_mu_tau_channel_split
      _ = (cube_faces D : ℝ) - ((37 : ℝ) / 2) * alpha := by
            norm_num [cube_faces, D]

/-- O4 closure certificate (coefficient slots):
    canonical integer/rational slots are forced in the primary one-parameter
    constrained families used for the lepton chain. -/
theorem o4_slot_forcing_certificate :
    ledger_fraction = (29 : ℚ) / 44 ∧
    step_mu_tau = (cube_faces D : ℝ) - ((((2 * wallpaper_groups + D : ℕ) : ℝ) / 2) * alpha) ∧
    step_e_mu = (E_passive : ℝ) + 1 / (4 * Real.pi) - correction_order_2 := by
  refine ⟨ledger_fraction_eq_29_over_44, ?_, step_e_mu_channel_split⟩
  simp [step_mu_tau]

end
end JCostPerturbation
end Masses
end RecognitionScience
