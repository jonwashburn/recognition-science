import Mathlib

namespace RecognitionScience
namespace Cost

noncomputable def Jcost (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

structure CostRequirements (F : ℝ → ℝ) : Type where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

lemma Jcost_unit0 : Jcost 1 = 0 := by
  simp [Jcost]

lemma Jcost_symm {x : ℝ} (hx : 0 < x) : Jcost x = Jcost x⁻¹ := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold Jcost
  have : (x + x⁻¹) = (x⁻¹ + (x⁻¹)⁻¹) := by
    field_simp [hx0]
    ring
  simp [this]

lemma Jcost_eq_sq {x : ℝ} (hx : x ≠ 0) :
    Jcost x = (x - 1) ^ 2 / (2 * x) := by
  have hx2 : (2 * x) ≠ 0 := mul_ne_zero two_ne_zero hx
  have hL : Jcost x * (2 * x) = (x - 1) ^ 2 := by
    unfold Jcost
    have : ((x + x⁻¹) / 2 - 1) * (2 * x) = (x - 1) ^ 2 := by
      field_simp [hx]
      ring
    simpa using this
  have hR : ((x - 1) ^ 2 / (2 * x)) * (2 * x) = (x - 1) ^ 2 := by
    field_simp [hx]
  refine (mul_right_cancel₀ hx2) ?_;
  calc
    Jcost x * (2 * x) = (x - 1) ^ 2 := hL
    _ = ((x - 1) ^ 2 / (2 * x)) * (2 * x) := by simpa using hR.symm

lemma Jcost_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ Jcost x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hrepr := Jcost_eq_sq (x := x) hx0
  have hnum : 0 ≤ (x - 1) ^ 2 := by exact sq_nonneg (x - 1)
  have hden : 0 < 2 * x := mul_pos (by norm_num : (0 : ℝ) < 2) hx
  have hfrac : 0 ≤ (x - 1) ^ 2 / (2 * x) :=
    div_nonneg hnum (le_of_lt hden)
  simpa [hrepr] using hfrac

lemma Jcost_one_plus_eps_quadratic (ε : ℝ) (hε : |ε| ≤ (1 : ℝ) / 2) :
    ∃ (c : ℝ), Jcost (1 + ε) = ε ^ 2 / 2 + c * ε ^ 3 ∧ |c| ≤ 2 := by
  classical
  have hbounds := abs_le.mp hε
  have hpos : 0 < 1 + ε := by
    have : -(1 : ℝ) / 2 ≤ ε := by simpa [neg_div] using hbounds.1
    linarith
  have hne : 1 + ε ≠ 0 := ne_of_gt hpos
  have hcalc : Jcost (1 + ε) = ε ^ 2 / (2 * (1 + ε)) := by
    simpa [pow_two, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
      using (Jcost_eq_sq (x := 1 + ε) hne)
  let c : ℝ := -1 / (2 * (1 + ε))
  have h_eq :
      Jcost (1 + ε) = ε ^ 2 / 2 + c * ε ^ 3 := by
    have : ε ^ 2 / (2 * (1 + ε)) = ε ^ 2 / 2 + (-1 / (2 * (1 + ε))) * ε ^ 3 := by
      field_simp [hne]
      ring
    simpa [hcalc, c] using this
  have hden_pos : 0 < 2 * (1 + ε) := by nlinarith [hpos]
  have habs : |c| = 1 / (2 * (1 + ε)) := by
    simp [c, div_eq_mul_inv, abs_mul, abs_inv, abs_of_pos hpos]
  -- Use 1/(2(1+ε)) ≤ 1 from (1+ε) ≥ 1/2
  have hone_le : (1 : ℝ) ≤ 2 * (1 + ε) := by
    have : (1 / 2 : ℝ) ≤ 1 + ε := by linarith
    simpa [two_mul] using mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2)
  have hdiv_le_one : 1 / (2 * (1 + ε)) ≤ 1 := by
    have hpos1 : 0 < (1 : ℝ) := by norm_num
    simpa [one_div] using one_div_le_one_div_of_le hpos1 hone_le
  have hbound : |c| ≤ 2 := by
    have h1 : |c| ≤ 1 := by simpa [habs] using hdiv_le_one
    have h12 : (1 : ℝ) ≤ 2 := by norm_num
    exact le_trans h1 h12
  exact ⟨c, h_eq, hbound⟩

lemma Jcost_small_strain_bound (ε : ℝ) (hε : |ε| ≤ (1 : ℝ) / 10) :
    |Jcost (1 + ε) - ε ^ 2 / 2| ≤ ε ^ 2 / 10 := by
  classical
  have hbounds := abs_le.mp hε
  have hpos : 0 < 1 + ε := by
    have : -(1 : ℝ) / 10 ≤ ε := by simpa [neg_div] using hbounds.1
    linarith
  have hne : 1 + ε ≠ 0 := ne_of_gt hpos
  have hform : Jcost (1 + ε) = ε ^ 2 / (2 * (1 + ε)) := by
    simpa [pow_two, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
      using (Jcost_eq_sq (x := 1 + ε) hne)
  have hden_pos : 0 < 2 * (1 + ε) := by nlinarith [hpos]
  -- Exact difference and absolute value
  have h1 : Jcost (1 + ε) - ε ^ 2 / 2
      = ε ^ 2 / (2 * (1 + ε)) - ε ^ 2 / 2 := by
    simpa [hform]
  have hx : (2 : ℝ) * (1 + ε) ≠ 0 := mul_ne_zero two_ne_zero hne
  have h2 : ε ^ 2 / (2 * (1 + ε)) - ε ^ 2 / 2 = -ε ^ 3 / (2 * (1 + ε)) := by
    field_simp [hx]
    ring
  have hdiff : Jcost (1 + ε) - ε ^ 2 / 2 = -ε ^ 3 / (2 * (1 + ε)) := h1.trans h2
  have habs : |Jcost (1 + ε) - ε ^ 2 / 2| = |ε| ^ 3 / (2 * (1 + ε)) := by
    have hposden : 0 < 2 * (1 + ε) := hden_pos
    simpa [abs_div, abs_neg, abs_pow, abs_of_pos hposden] using
      congrArg (fun z => |z|) hdiff
  -- Now bound using |ε|/(2(1+ε)) ≤ 1/18 from below
  have hx_lower : (9 : ℝ) / 10 ≤ 1 + ε := by linarith [show -(1 : ℝ) / 10 ≤ ε from by simpa [neg_div] using hbounds.1]
  have hx_pos : 0 < (9 : ℝ) / 10 := by norm_num
  have hx_inv : 1 / (1 + ε) ≤ (10 : ℝ) / 9 := by
    have := one_div_le_one_div_of_le hx_pos hx_lower
    simpa using this
  have hrec_bound : 1 / (2 * (1 + ε)) ≤ (5 : ℝ) / 9 := by
    have hmul : (1 / 2 : ℝ) * (1 / (1 + ε)) ≤ (1 / 2) * ((10 : ℝ) / 9) :=
      mul_le_mul_of_nonneg_left hx_inv (by norm_num)
    have hleft : 1 / (2 * (1 + ε)) = (1 / 2) * (1 / (1 + ε)) := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have hright : (5 : ℝ) / 9 = (1 / 2) * ((10 : ℝ) / 9) := by norm_num
    simpa [hleft, hright] using hmul
  have hrec_nonneg : 0 ≤ 1 / (2 * (1 + ε)) := by
    have : 0 ≤ 2 * (1 + ε) := le_of_lt (by nlinarith [hpos])
    exact one_div_nonneg.mpr this
  have hA : |ε| / (2 * (1 + ε)) ≤ (1 : ℝ) / 10 * (1 / (2 * (1 + ε))) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using mul_le_mul_of_nonneg_right hε hrec_nonneg
  have hB : (1 : ℝ) / 10 * (1 / (2 * (1 + ε))) ≤ (1 : ℝ) / 18 := by
    have hmul := mul_le_mul_of_nonneg_left hrec_bound (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 10)
    have hright : (1 : ℝ) / 18 = (1 : ℝ) / 10 * ((5 : ℝ) / 9) := by norm_num
    simpa [hright] using hmul
  have hfrac : |ε| / (2 * (1 + ε)) ≤ (1 : ℝ) / 18 := hA.trans hB
  -- Conclude
  have hineq : |Jcost (1 + ε) - ε ^ 2 / 2| ≤ |ε| ^ 2 / 18 := by
    have hnn : 0 ≤ |ε| ^ 2 := by
      have := sq_nonneg (|ε|); simpa [pow_two] using this
    have hmul := mul_le_mul_of_nonneg_left hfrac hnn
    calc
      |Jcost (1 + ε) - ε ^ 2 / 2| = |ε| ^ 3 / (2 * (1 + ε)) := by simpa [habs]
      _ ≤ |ε| ^ 2 * (1 / 18) := by
        simpa [pow_succ, pow_two, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hmul
      _ = |ε| ^ 2 / 18 := by simp [div_eq_mul_inv]
  have hratio : (1 : ℝ) / 18 ≤ 1 / 10 := by norm_num
  have hsq : |ε| ^ 2 = ε ^ 2 := by
    have h1 : |ε| * |ε| = |ε * ε| := by simpa [abs_mul]
    calc
      |ε| ^ 2 = |ε| * |ε| := by simpa [pow_two]
      _ = |ε * ε| := h1
      _ = |ε ^ 2| := by simpa [pow_two]
      _ = ε ^ 2 := by simpa [abs_of_nonneg (sq_nonneg ε)]
  have hcompare : |ε| ^ 2 / 18 ≤ ε ^ 2 / 10 := by
    have := mul_le_mul_of_nonneg_left hratio (by exact sq_nonneg ε)
    simpa [hsq, pow_two] using this
  exact (hineq.trans hcompare)

def AgreesOnExp (F : ℝ → ℝ) : Prop := ∀ t : ℝ, F (Real.exp t) = Jcost (Real.exp t)

@[simp] lemma Jcost_exp (t : ℝ) :
  Jcost (Real.exp t) = ((Real.exp t) + (Real.exp (-t))) / 2 - 1 := by
  have h : (Real.exp t)⁻¹ = Real.exp (-t) := by
    symm; simp [Real.exp_neg t]
  simp [Jcost, h]

class SymmUnit (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

class AveragingAgree (F : ℝ → ℝ) : Prop where
  agrees : AgreesOnExp F

class AveragingDerivation (F : ℝ → ℝ) : Prop extends SymmUnit F where
  agrees : AgreesOnExp F

class AveragingBounds (F : ℝ → ℝ) : Prop extends SymmUnit F where
  upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

def mkAveragingBounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t))
  (lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)) :
  AveragingBounds F :=
{ toSymmUnit := symm, upper := upper, lower := lower }

class JensenSketch (F : ℝ → ℝ) : Prop extends SymmUnit F where
  axis_upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  axis_lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

noncomputable def F_ofLog (G : ℝ → ℝ) : ℝ → ℝ := fun x => G (Real.log x)

class LogModel (G : ℝ → ℝ) : Prop where
  even_log : ∀ t : ℝ, G (-t) = G t
  base0 : G 0 = 0
  upper_cosh : ∀ t : ℝ, G t ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1)
  lower_cosh : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ G t

@[simp] theorem Jcost_agrees_on_exp : AgreesOnExp Jcost := by
  intro t; rfl

instance : AveragingAgree Jcost := ⟨Jcost_agrees_on_exp⟩

instance : SymmUnit Jcost :=
  { symmetric := by
      intro x hx
      simp [Jcost_symm (x:=x) hx]
    , unit0 := Jcost_unit0 }

instance : AveragingDerivation Jcost :=
  { toSymmUnit := (inferInstance : SymmUnit Jcost)
  , agrees := Jcost_agrees_on_exp }

instance : JensenSketch Jcost :=
  { toSymmUnit := (inferInstance : SymmUnit Jcost)
  , axis_upper := by intro t; exact le_of_eq rfl
  , axis_lower := by intro t; exact le_of_eq rfl }

/-!
## Small-strain Taylor expansion
This section provides small-strain expansions used by Axiom A4.
-/

/-! ## Monotonicity Properties -/

/-- J-cost derivative: d/dx J(x) = 1/2 - 1/(2x²) -/
lemma Jcost_deriv (x : ℝ) (hx : x ≠ 0) :
    deriv Jcost x = (1 - x⁻¹ ^ 2) / 2 := by
  unfold Jcost
  have hdiff : DifferentiableAt ℝ (fun y => (y + y⁻¹) / 2 - 1) x := by
    apply DifferentiableAt.sub
    · apply DifferentiableAt.div_const
      apply DifferentiableAt.add differentiableAt_id (differentiableAt_inv hx)
    · exact differentiableAt_const 1
  have h : deriv (fun y => (y + y⁻¹) / 2 - 1) x = (1 - x⁻¹ ^ 2) / 2 := by
    have h1 : HasDerivAt (fun y => y) 1 x := hasDerivAt_id x
    have h2 : HasDerivAt (fun y => y⁻¹) (-(x^2)⁻¹) x := hasDerivAt_inv hx
    have h3 : HasDerivAt (fun y => y + y⁻¹) (1 + -(x^2)⁻¹) x := h1.add h2
    have h4 : HasDerivAt (fun y => (y + y⁻¹) / 2) ((1 + -(x^2)⁻¹) / 2) x := h3.div_const 2
    have h5 : HasDerivAt (fun y => (y + y⁻¹) / 2 - 1) ((1 + -(x^2)⁻¹) / 2) x := h4.sub_const 1
    rw [h5.deriv]
    field_simp [hx]
    ring
  exact h

/-- J-cost is strictly increasing on (1, ∞) -/
lemma Jcost_strict_mono_on_one_infty (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hx1 : 1 ≤ x) (hxy : x < y) :
    Jcost x < Jcost y := by
  -- Use the squared form: Jcost x = (x-1)²/(2x)
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  rw [Jcost_eq_sq hx0, Jcost_eq_sq hy0]
  -- Need: (x-1)²/(2x) < (y-1)²/(2y)
  have h2x : 0 < 2 * x := by linarith
  have h2y : 0 < 2 * y := by linarith
  rw [div_lt_div_iff₀ h2x h2y]
  -- Need: (x-1)² * (2y) < (y-1)² * (2x)
  have hx_sub : 0 ≤ x - 1 := by linarith
  have hy_sub : 0 < y - 1 := by linarith
  -- Expand: 2y(x-1)² < 2x(y-1)²
  -- Simplify: y(x-1)² < x(y-1)²
  have hmain : (x - 1) ^ 2 * (2 * y) < (y - 1) ^ 2 * (2 * x) := by
    -- Use calculus or direct algebra
    -- (x-1)²·y < (y-1)²·x ⟺ (x-1)²/x < (y-1)²/y for x,y > 0
    -- Let f(t) = (t-1)²/t = t - 2 + 1/t. Then f'(t) = 1 - 1/t² > 0 for t > 1
    -- So f is increasing on (1,∞)
    let f : ℝ → ℝ := fun t => (t - 1) ^ 2 / t
    have hf_mono : ∀ a b : ℝ, 1 ≤ a → a < b → f a < f b := by
      intro a b ha hab
      simp only [f]
      have ha0 : (0 : ℝ) < a := by linarith
      have hb0 : (0 : ℝ) < b := by linarith
      have ha' : a ≠ 0 := ne_of_gt ha0
      have hb' : b ≠ 0 := ne_of_gt hb0
      rw [div_lt_div_iff₀ ha0 hb0]
      -- (a-1)²·b < (b-1)²·a
      have : (a - 1) ^ 2 * b - (b - 1) ^ 2 * a < 0 := by
        have hcalc : (a - 1) ^ 2 * b - (b - 1) ^ 2 * a = (a - b) * (a * b - 1) := by ring
        rw [hcalc]
        have h1 : a - b < 0 := by linarith
        have h2 : a * b - 1 > 0 := by nlinarith
        nlinarith
      linarith
    have := hf_mono x y hx1 hxy
    simp only [f] at this
    have hx0' : 0 < x := hx
    have hy0' : 0 < y := hy
    rw [div_lt_div_iff₀ hx0' hy0'] at this
    -- this : (x - 1) ^ 2 * y < (y - 1) ^ 2 * x
    -- goal : (x - 1) ^ 2 * (2 * y) < (y - 1) ^ 2 * (2 * x)
    have h2 : (0 : ℝ) < 2 := by norm_num
    calc (x - 1) ^ 2 * (2 * y)
        = 2 * ((x - 1) ^ 2 * y) := by ring
      _ < 2 * ((y - 1) ^ 2 * x) := by nlinarith
      _ = (y - 1) ^ 2 * (2 * x) := by ring
  exact hmain

/-- J(x) > 0 for x ≠ 1 and x > 0 -/
lemma Jcost_pos_of_ne_one (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) : 0 < Jcost x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [Jcost_eq_sq hx0]
  apply div_pos
  · have hne : (x - 1) ≠ 0 := sub_ne_zero.mpr hx1
    exact sq_pos_of_ne_zero hne
  · have h2 : (0 : ℝ) < 2 := by norm_num
    exact mul_pos h2 hx

end Cost
end RecognitionScience
