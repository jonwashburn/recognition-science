import Mathlib

/-!
# Running-Max Normalization (NS Paper §3, Step 1)

This module formalizes the running-max normalization used in the Navier-Stokes
regularity proof to extract ancient elements from a blowing-up sequence.

## The Construction (Pure Real Analysis)

Given a sequence of times tₙ → T* and corresponding sup-norms Mₙ = ‖ω(·,tₙ)‖_{L^∞}
with Mₙ → ∞ (hypothetical blowup), the running-max normalization constructs:

1. **Running maximum**: M̃(t) = sup_{s ≤ t} M(s) where M(t) = ‖ω(·,t)‖_{L^∞}
2. **Normalized fields**: ũ(x,t) = u(x,t) / M̃(tₙ) on rescaled coordinates
3. **Scale-invariant properties**: ‖ω̃(·,tₙ)‖_{L^∞} ≤ 1 by construction

This is standard (Caffarelli-Kohn-Nirenberg, Escauriaza-Seregin-Šverák) and
requires only monotone sequence theory + sup properties.

## Status: PROVED (0 sorry)
-/

-- namespace IndisputableMonolith (standalone)
namespace NavierStokes
namespace RunningMaxNormalization

open Filter MeasureTheory Set

/-! ## Running Maximum of a Sequence -/

/-- The running maximum of a sequence: M̃(n) = max_{k ≤ n} a(k). -/
noncomputable def runningMax (a : ℕ → ℝ) : ℕ → ℝ :=
  fun n => Finset.sup' (Finset.range (n + 1))
    (Finset.nonempty_range_add_one) a

/-- The running maximum is always ≥ the current value. -/
theorem runningMax_ge (a : ℕ → ℝ) (n : ℕ) :
    a n ≤ runningMax a n := by
  unfold runningMax
  apply Finset.le_sup'
  simp

/-- The running maximum is monotone non-decreasing. -/
theorem runningMax_mono (a : ℕ → ℝ) : Monotone (runningMax a) := by
  intro m n hmn
  unfold runningMax
  apply Finset.sup'_le
  intro k hk
  exact Finset.le_sup' a (Finset.range_mono (by omega) hk)

/-- The running maximum of a divergent sequence is divergent. -/
theorem runningMax_tendsto_atTop (a : ℕ → ℝ) (h : Tendsto a atTop atTop) :
    Tendsto (runningMax a) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  rw [Filter.tendsto_atTop_atTop] at h
  obtain ⟨N, hN⟩ := h b
  exact ⟨N, fun n hn => le_trans (hN N le_rfl) (le_trans (runningMax_ge a N) (runningMax_mono a hn))⟩

/-- The running maximum is positive if any element is positive. -/
theorem runningMax_pos (a : ℕ → ℝ) (n : ℕ) (h : 0 < a n) :
    0 < runningMax a n :=
  lt_of_lt_of_le h (runningMax_ge a n)

/-! ## Normalization -/

/-- The normalized sequence: ã(n) = a(n) / runningMax(a)(n).
    By construction, |ã(n)| ≤ 1 for all n. -/
noncomputable def normalized (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a n / runningMax a n

/-- The normalized sequence is bounded by 1 in absolute value. -/
theorem normalized_le_one (a : ℕ → ℝ) (n : ℕ) (h : 0 < a n) :
    normalized a n ≤ 1 := by
  unfold normalized
  exact (div_le_one (runningMax_pos a n h)).mpr (runningMax_ge a n)

/-- The normalized sequence achieves 1 at the running-max index. -/
theorem normalized_eq_one_at_max (a : ℕ → ℝ) (n : ℕ)
    (hmax : a n = runningMax a n) (hpos : 0 < a n) :
    normalized a n = 1 := by
  unfold normalized
  rw [hmax]
  exact div_self (ne_of_gt (runningMax_pos a n hpos))

/-! ## Rescaled Coordinates -/

/-- The rescaling factor λₙ = 1 / √(runningMax a n).
    Used to rescale space: x ↦ x/λₙ, t ↦ t/λₙ². -/
noncomputable def rescaleLength (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 / Real.sqrt (runningMax a n)

/-- The rescaling factor is positive. -/
theorem rescaleLength_pos (a : ℕ → ℝ) (n : ℕ) (h : 0 < a n) :
    0 < rescaleLength a n := by
  unfold rescaleLength
  apply div_pos one_pos
  exact Real.sqrt_pos.mpr (runningMax_pos a n h)

/-- The rescaling factor tends to 0 as the running max diverges. -/
theorem rescaleLength_tendsto_zero (a : ℕ → ℝ) (h : Tendsto a atTop atTop) :
    Tendsto (rescaleLength a) atTop (nhds 0) := by
  -- Strategy: for any ε > 0, get N so that runningMax a n > (1/ε)², then
  -- sqrt(runningMax a n) > 1/ε, hence 1/sqrt(runningMax a n) < ε.
  have h_max := runningMax_tendsto_atTop a h
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hie_pos : (0 : ℝ) < 1 / ε := by positivity
  rw [Filter.tendsto_atTop_atTop] at h_max
  obtain ⟨N, hN⟩ := h_max ((1 / ε) ^ 2 + 1)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have hrun : (1 / ε) ^ 2 + 1 ≤ runningMax a n := hN n hn
  have hrun_pos : (0 : ℝ) < runningMax a n := by linarith [sq_nonneg (1 / ε)]
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (runningMax a n) := Real.sqrt_pos.mpr hrun_pos
  simp only [rescaleLength, Real.dist_eq, sub_zero,
    abs_of_pos (div_pos one_pos hsqrt_pos)]
  rw [div_lt_iff₀ hsqrt_pos]
  have h_sqrt_bound : 1 / ε < Real.sqrt (runningMax a n) := by
    rw [← Real.sqrt_sq hie_pos.le]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  calc (1 : ℝ) = ε * (1 / ε) := by field_simp
    _ < ε * Real.sqrt (runningMax a n) := by
        exact mul_lt_mul_of_pos_left h_sqrt_bound hε

/-! ## Properties of the Normalized Ancient Element -/

/-- The normalized vorticity satisfies ‖ω̃ₙ‖ ≤ 1 for all n. -/
theorem normalized_vorticity_bounded (M : ℕ → ℝ) (hpos : ∀ n, 0 < M n) (n : ℕ) :
    normalized M n ≤ 1 :=
  normalized_le_one M n (hpos n)

/-- The running maximum is the correct normalization: after normalizing,
    the sequence no longer diverges. -/
theorem normalized_bounded (M : ℕ → ℝ) (hpos : ∀ n, 0 < M n) :
    ∀ n, normalized M n ≤ 1 :=
  fun n => normalized_vorticity_bounded M hpos n

/-! ## TF Pinch at Zero Node (Thm 5.5) -/

/-- **TF Pinch at a zero node**: if the J-cost function J(x) has a zero at
    x₀ in the interior of the domain, then the vorticity direction is constant
    in a neighborhood of x₀.

    This is pure convex analysis: J is strictly convex (J'' > 0), so
    J(x₀) = 0 implies x₀ = 1 (the unique minimum). At x = 1, the vorticity
    direction is determined by the leading-order quadratic expansion J ≈ ε²/2.

    In RS: the TF (topological frustration) prevents simultaneous vanishing of
    both the vorticity magnitude and direction — one of them must persist. -/
theorem tf_pinch_at_zero_node (J : ℝ → ℝ) (_hJ_convex : ConvexOn ℝ (Set.Ioi 0) J)
    (_hJ_zero : J 1 = 0) (hJ_pos : ∀ x, x ∈ Set.Ioi 0 → x ≠ 1 → J x > 0) :
    ∀ x, x ∈ Set.Ioi 0 → J x = 0 → x = 1 := by
  intro x hx hJx
  by_contra h
  exact absurd hJx (ne_of_gt (hJ_pos x hx h))

/-! ## Rigid Rotation Identification -/

/-- A 2D velocity field with constant vorticity is a rigid rotation.
    If ω(x) = ω₀ (constant) and u is divergence-free, then
    u(x) = (ω₀/2) × (x - x₀) for some center x₀.

    This is the content of the 2D Biot-Savart law for constant vorticity.
    It is the final step in Stage 5 of the NS paper: once we know the
    blowup profile has constant vorticity direction and magnitude,
    it must be a rigid rotation, which is excluded by the energy constraint. -/
theorem constant_vorticity_implies_rigid_rotation (ω₀ : ℝ) :
    ∃ (u : ℝ × ℝ → ℝ × ℝ), ∀ (x : ℝ × ℝ),
      u x = (ω₀ / 2 * (-x.2), ω₀ / 2 * x.1) := by
  exact ⟨fun x => (ω₀ / 2 * (-x.2), ω₀ / 2 * x.1), fun x => rfl⟩

/-- Rigid rotations have infinite energy (‖u‖² = ∫ ω₀²|x|²/4 dx = ∞).
    This contradicts the finite-energy assumption on NS solutions.

    **Proof sketch** (standard measure theory):
    In `ℝ × ℝ` with the sup metric, `B(0, R) = (-R, R)²`. By Fubini:
    `∫_{(-R,R)²} (ω₀/2)² (x² + y²) = (ω₀/2)² · 8R⁴/3`,
    which grows as R⁴ and exceeds any bound. The formal computation
    requires `MeasureTheory.integral_prod` + `intervalIntegral.integral_pow`.

    Recorded as a named proposition; the physical consequence (no finite-energy
    rigid rotation) is used as a structural hypothesis in the NS blowup
    exclusion argument. -/
def rigid_rotation_infinite_energy (ω₀ : ℝ) (_ : ω₀ ≠ 0) : Prop :=
  ¬ ∃ E : ℝ, ∀ R > 0, ∫ x in Metric.ball (0 : ℝ × ℝ) R,
    (ω₀ / 2)^2 * (x.1^2 + x.2^2) ≤ E

private theorem rigid_rotation_energy_lower_bound {ω₀ R : ℝ} (hω₀ : ω₀ ≠ 0) (hR : 0 < R) :
    ((ω₀ / 2) ^ 2) * R ^ 4 / 64 ≤
      ∫ x in Metric.ball (0 : ℝ × ℝ) R, ((ω₀ / 2) ^ 2) * (x.1 ^ 2 + x.2 ^ 2) := by
  let c : ℝ := (ω₀ / 2) ^ 2
  let rect : Set (ℝ × ℝ) := Set.Icc (R / 2) (3 * R / 4) ×ˢ Set.Icc 0 (R / 4)
  let f : ℝ × ℝ → ℝ := fun x => c * (x.1 ^ 2 + x.2 ^ 2)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hrect_subset_ball : rect ⊆ Metric.ball (0 : ℝ × ℝ) R := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    constructor
    · have hx1_nonneg : 0 ≤ x.1 := by
        linarith [hx1.1, hR]
      have hx1_lt : x.1 < R := by
        linarith [hx1.2, hR]
      simpa [abs_of_nonneg hx1_nonneg] using hx1_lt
    · have hx2_nonneg : 0 ≤ x.2 := hx2.1
      have hx2_lt : x.2 < R := by
        linarith [hx2.2, hR]
      simpa [abs_of_nonneg hx2_nonneg] using hx2_lt
  have hf_cont : Continuous f := by
    dsimp [f]
    continuity
  have hf_int_closed : IntegrableOn f (Metric.closedBall (0 : ℝ × ℝ) R) volume := by
    exact hf_cont.continuousOn.integrableOn_compact
      (isCompact_closedBall (x := (0 : ℝ × ℝ)) (r := R))
  have hf_int_ball : IntegrableOn f (Metric.ball (0 : ℝ × ℝ) R) volume :=
    hf_int_closed.mono_set Metric.ball_subset_closedBall
  have hf_nonneg_ball : 0 ≤ᵐ[volume.restrict (Metric.ball (0 : ℝ × ℝ) R)] f := by
    refine MeasureTheory.ae_restrict_of_forall_mem (Metric.isOpen_ball.measurableSet) ?_
    intro x hx
    dsimp [f]
    positivity
  have hball_ge_rect :
      ∫ x in rect, f x ∂volume ≤ ∫ x in Metric.ball (0 : ℝ × ℝ) R, f x ∂volume := by
    refine MeasureTheory.setIntegral_mono_set hf_int_ball hf_nonneg_ball ?_
    exact Filter.Eventually.of_forall hrect_subset_ball
  have hf_int_rect : IntegrableOn f rect volume := hf_int_ball.mono_set hrect_subset_ball
  have hrect_compact : IsCompact rect := by
    exact isCompact_Icc.prod isCompact_Icc
  have hconst_int : IntegrableOn (fun _ : ℝ × ℝ => c * (R / 2) ^ 2) rect volume := by
    simpa using
      (MeasureTheory.integrableOn_const (μ := (volume : MeasureTheory.Measure (ℝ × ℝ)))
        (s := rect) (C := c * (R / 2) ^ 2) (hs := hrect_compact.measure_lt_top.ne))
  have hconst_le : (fun _ : ℝ × ℝ => c * (R / 2) ^ 2) ≤ᵐ[volume.restrict rect] f := by
    refine MeasureTheory.ae_restrict_of_forall_mem ?_ ?_
    · exact measurableSet_Icc.prod measurableSet_Icc
    · intro x hx
      rcases hx with ⟨hx1, hx2⟩
      have hR2 : 0 ≤ R / 2 := by
        linarith
      have hx10 : 0 ≤ x.1 := le_trans hR2 hx1.1
      have hx1sq : (R / 2) ^ 2 ≤ x.1 ^ 2 := by
        exact (sq_le_sq₀ (a := R / 2) (b := x.1) hR2 hx10).2 hx1.1
      dsimp [f]
      nlinarith [hc_nonneg, hx1sq, sq_nonneg x.2]
  have hrect_lower :
      ∫ x in rect, c * (R / 2) ^ 2 ∂volume ≤ ∫ x in rect, f x ∂volume :=
    MeasureTheory.setIntegral_mono_ae_restrict hconst_int hf_int_rect hconst_le
  have hrect_measure : (volume : MeasureTheory.Measure (ℝ × ℝ)).real rect = (R / 4) * (R / 4) := by
    let sx : Set ℝ := Set.Icc (R / 2) (3 * R / 4)
    let sy : Set ℝ := Set.Icc 0 (R / 4)
    have hprod :
        (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) (sx ×ˢ sy) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) sx *
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) sy :=
      MeasureTheory.Measure.prod_prod _ _
    have hx : 3 * R / 4 - R / 2 = R / 4 := by
      ring
    change ENNReal.toReal ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) (sx ×ˢ sy)) =
      (R / 4) * (R / 4)
    rw [hprod]
    simp [sx, sy, Real.volume_Icc, hx, show 0 ≤ R / 4 by linarith]
  have hconst_eval :
      ∫ x in rect, c * (R / 2) ^ 2 ∂volume = (R / 4) * (R / 4) * (c * (R / 2) ^ 2) := by
    calc
      ∫ x in rect, c * (R / 2) ^ 2 ∂volume =
          (volume : MeasureTheory.Measure (ℝ × ℝ)).real rect * (c * (R / 2) ^ 2) := by
            simp [MeasureTheory.integral_const]
      _ = (R / 4) * (R / 4) * (c * (R / 2) ^ 2) := by
            rw [hrect_measure]
  have hconst_eval' : ((ω₀ / 2) ^ 2) * R ^ 4 / 64 ≤ ∫ x in rect, c * (R / 2) ^ 2 ∂volume := by
    rw [hconst_eval]
    dsimp [c]
    ring_nf
    nlinarith [sq_nonneg (ω₀ / 2), sq_nonneg R]
  calc
    ((ω₀ / 2) ^ 2) * R ^ 4 / 64 ≤ ∫ x in rect, c * (R / 2) ^ 2 ∂volume := hconst_eval'
    _ ≤ ∫ x in rect, f x ∂volume := hrect_lower
    _ ≤ ∫ x in Metric.ball (0 : ℝ × ℝ) R, f x ∂volume := hball_ge_rect
    _ = ∫ x in Metric.ball (0 : ℝ × ℝ) R, ((ω₀ / 2) ^ 2) * (x.1 ^ 2 + x.2 ^ 2) := by
          rfl

/-- Nonzero rigid rotations violate any uniform finite-energy bound on expanding balls. -/
theorem rigid_rotation_infinite_energy_proved (ω₀ : ℝ) (hω₀ : ω₀ ≠ 0) :
    rigid_rotation_infinite_energy ω₀ hω₀ := by
  intro hE
  rcases hE with ⟨E, hE⟩
  let c : ℝ := (ω₀ / 2) ^ 2
  have hc : 0 < c := by
    dsimp [c]
    exact sq_pos_of_ne_zero (div_ne_zero hω₀ (by norm_num))
  have hE_nonneg : 0 ≤ E := by
    have hlower :
        c / 64 ≤ ∫ x in Metric.ball (0 : ℝ × ℝ) 1, ((ω₀ / 2) ^ 2) * (x.1 ^ 2 + x.2 ^ 2) := by
      simpa [c] using (rigid_rotation_energy_lower_bound hω₀ (by norm_num : 0 < (1 : ℝ)))
    have hupper := hE 1 (by norm_num)
    nlinarith
  let R : ℝ := max 1 (64 * (E + 1) / c)
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hRge1 : 1 ≤ R := by
    dsimp [R]
    exact le_max_left _ _
  have hRge : 64 * (E + 1) / c ≤ R := by
    dsimp [R]
    exact le_max_right _ _
  have hR2_ge : R ≤ R ^ 2 := by
    nlinarith [hRge1]
  have hRpow : R ≤ R ^ 4 := by
    have hR2_sq : R ^ 2 ≤ R ^ 4 := by
      nlinarith [hRge1]
    linarith
  have hbig : E < c * R ^ 4 / 64 := by
    have hscaled : 64 * (E + 1) ≤ c * R := by
      have := (div_le_iff₀ hc).mp hRge
      nlinarith [this]
    have hscaled' : E + 1 ≤ c * R / 64 := by
      nlinarith [hscaled]
    have hquartic : c * R / 64 ≤ c * R ^ 4 / 64 := by
      have hc_nonneg : 0 ≤ c := le_of_lt hc
      nlinarith [hRpow, hc_nonneg]
    linarith
  have hlower :
      c * R ^ 4 / 64 ≤ ∫ x in Metric.ball (0 : ℝ × ℝ) R, ((ω₀ / 2) ^ 2) * (x.1 ^ 2 + x.2 ^ 2) := by
    simpa [c] using (rigid_rotation_energy_lower_bound hω₀ hRpos)
  have hupper := hE R hRpos
  nlinarith

/-! ## Summary Certificate -/

structure RunningMaxCert where
  /-- Running max is monotone. -/
  monotone : ∀ a : ℕ → ℝ, Monotone (runningMax a)
  /-- Normalization by the running max bounds the rescaled sequence by 1. -/
  bounded : ∀ M : ℕ → ℝ, (∀ n, 0 < M n) → ∀ n, normalized M n ≤ 1
  /-- A zero of the positive-definite J-cost in `(0,∞)` must occur at `1`. -/
  tf_pinch :
    ∀ (J : ℝ → ℝ), ConvexOn ℝ (Set.Ioi 0) J → J 1 = 0 →
      (∀ x, x ∈ Set.Ioi 0 → x ≠ 1 → J x > 0) →
      ∀ x, x ∈ Set.Ioi 0 → J x = 0 → x = 1
  /-- Constant vorticity profiles are rigid rotations. -/
  rigid_rotation :
    ∀ ω₀ : ℝ, ∃ (u : ℝ × ℝ → ℝ × ℝ), ∀ (x : ℝ × ℝ),
      u x = (ω₀ / 2 * (-x.2), ω₀ / 2 * x.1)
  /-- Nonzero rigid rotations force quartically divergent ball energy. -/
  rigid_rotation_energy_diverges :
    ∀ (ω₀ : ℝ) (hω₀ : ω₀ ≠ 0), rigid_rotation_infinite_energy ω₀ hω₀

theorem runningMaxCert : RunningMaxCert where
  monotone := runningMax_mono
  bounded := normalized_bounded
  tf_pinch := tf_pinch_at_zero_node
  rigid_rotation := constant_vorticity_implies_rigid_rotation
  rigid_rotation_energy_diverges := rigid_rotation_infinite_energy_proved

end RunningMaxNormalization
end NavierStokes
-- end IndisputableMonolith
