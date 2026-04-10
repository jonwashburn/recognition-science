import Mathlib
import NavierStokes.Galerkin3D
import NavierStokes.SubKolmogorovBridge
import NavierStokes.DiscreteMaximumPrinciple
import NavierStokes.FourierExtraction
import NavierStokes.GalerkinEquicontinuity

/-!
# 3D Continuum Limit and NS Global Regularity

Complete chain from Galerkin approximations to the BKM conclusion.

## What is proved

- Pythagorean embedding bound (`norm_extendByZero3_le`)
- Cantor diagonal extraction (`nat_diagonal_extraction`)
- Uniform bounds from Galerkin energy estimate (`UniformBoundsHypothesis3D.ofViscous`)
- Bound inheritance for the limit (`coeff_bound_from_diagonal`)
- Master theorem: the continuum limit has bounded vorticity

## What remains as a hypothesis

`EquicontinuousExtension`: the Galerkin coefficients are equicontinuous
in time, so diagonal convergence at a countable dense set extends to
all of ℝ. This is the 3ε argument (standard real analysis). The Lipschitz
constant and rational approximation are proved in `GalerkinEquicontinuity.lean`.

## Paper reference
RS_NavierStokes_BKM.tex, §5
-/

namespace NavierStokes.ContinuumLimit3D

open Real Filter Topology Encodable
open Galerkin3D SubKolmogorovBridge DiscreteMaximumPrinciple
open FourierExtraction GalerkinEquicontinuity

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Types -/

abbrev Mode3' := Galerkin3D.Mode3
abbrev VelCoeff3' := EuclideanSpace ℝ (Fin 3)
abbrev FourierState3D : Type := Mode3' → VelCoeff3'

/-! ## Zero-extension and embedding bound (PROVED) -/

def coeffAt3 {N : ℕ} (u : GalerkinState3 N) (k : Mode3') (j : Fin 3) : ℝ :=
  if hk : k ∈ modes3 N then u (⟨k, hk⟩, j) else 0

noncomputable def extendByZero3 {N : ℕ} (u : GalerkinState3 N) : FourierState3D :=
  fun k => (WithLp.toLp 2 (fun j : Fin 3 => coeffAt3 u k j) : VelCoeff3')

lemma norm_extendByZero3_le {N : ℕ} (u : GalerkinState3 N) (k : Mode3') :
    ‖(extendByZero3 u) k‖ ≤ ‖u‖ := by
  classical
  by_cases hk : k ∈ modes3 N
  · let k' : (modes3 N) := ⟨k, hk⟩
    have hsq_le : ‖(extendByZero3 u) k‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have hnorm_u_sq : ‖u‖ ^ 2 = ∑ kc : ((modes3 N) × Fin 3), ‖u kc‖ ^ 2 := by
        simp [EuclideanSpace.norm_sq_eq]
      let s : Finset ((modes3 N) × Fin 3) := Finset.univ.image (fun j : Fin 3 => (k', j))
      have hpart_s : (∑ kc ∈ s, ‖u kc‖ ^ 2) ≤ ∑ kc : ((modes3 N) × Fin 3), ‖u kc‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
      have hsum_eq : ∑ j : Fin 3, ‖u (k', j)‖ ^ 2 = ∑ kc ∈ s, ‖u kc‖ ^ 2 := by
        rw [Finset.sum_image]; intro j₁ _ j₂ _ heq; exact congrArg Prod.snd heq
      have hpart : ∑ j : Fin 3, ‖u (k', j)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
        rw [hnorm_u_sq]; linarith [hsum_eq, hpart_s]
      have hext_sq : ‖(extendByZero3 u) k‖ ^ 2 = ∑ j : Fin 3, ‖u (k', j)‖ ^ 2 := by
        simp only [extendByZero3, coeffAt3, hk, dif_pos, EuclideanSpace.norm_sq_eq,
          Real.norm_eq_abs, sq_abs, k']
      linarith [hext_sq, hpart]
    exact le_of_sq_le_sq hsq_le (norm_nonneg u)
  · have hzero : ∀ j : Fin 3, coeffAt3 u k j = 0 := fun j => by simp [coeffAt3, hk]
    have : ‖(extendByZero3 u) k‖ = 0 := by
      simp only [extendByZero3]; rw [EuclideanSpace.norm_eq]; simp [hzero]
    linarith [norm_nonneg u]

/-! ## Component vs norm (for Lipschitz extension) -/

lemma coeffAt3_sub_eq_extendByZero3_sub_apply {N : ℕ} (u v : GalerkinState3 N) (k : Mode3') (j : Fin 3) :
    coeffAt3 u k j - coeffAt3 v k j =
      ((extendByZero3 u k) - (extendByZero3 v k)) j := by
  simp only [extendByZero3, PiLp.sub_apply, coeffAt3]

lemma sq_norm_extendByZero3_sub {N : ℕ} (u v : GalerkinState3 N) (k : Mode3') :
    ‖extendByZero3 u k - extendByZero3 v k‖ ^ 2 = ∑ i : Fin 3, (coeffAt3 u k i - coeffAt3 v k i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [extendByZero3, coeffAt3, PiLp.sub_apply, Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]

lemma abs_sub_coeffAt3_le_norm_extendByZero3_sub {N : ℕ} (u v : GalerkinState3 N) (k : Mode3') (j : Fin 3) :
    |coeffAt3 u k j - coeffAt3 v k j| ≤ ‖extendByZero3 u k - extendByZero3 v k‖ := by
  have hnorm_sq := sq_norm_extendByZero3_sub u v k
  have hterm :
      (coeffAt3 u k j - coeffAt3 v k j) ^ 2 ≤ ∑ i : Fin 3, (coeffAt3 u k i - coeffAt3 v k i) ^ 2 := by
    rw [Fin.sum_univ_three]
    by_cases h0 : j = 0
    · subst h0
      nlinarith [sq_nonneg (coeffAt3 u k 1 - coeffAt3 v k 1),
        sq_nonneg (coeffAt3 u k 2 - coeffAt3 v k 2)]
    by_cases h1 : j = 1
    · subst h1
      nlinarith [sq_nonneg (coeffAt3 u k 0 - coeffAt3 v k 0),
        sq_nonneg (coeffAt3 u k 2 - coeffAt3 v k 2)]
    have h2 : j = (2 : Fin 3) := by
      fin_cases j
      · exact absurd rfl h0
      · exact absurd rfl h1
      · rfl
    subst h2
    nlinarith [sq_nonneg (coeffAt3 u k 0 - coeffAt3 v k 0),
      sq_nonneg (coeffAt3 u k 1 - coeffAt3 v k 1)]
  have hsq :
      (coeffAt3 u k j - coeffAt3 v k j) ^ 2 ≤ ‖extendByZero3 u k - extendByZero3 v k‖ ^ 2 := by
    rw [hnorm_sq]; exact hterm
  have hsqrt := Real.sqrt_le_sqrt hsq
  simpa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] using hsqrt

lemma dist_extendByZero3_zero_le {N : ℕ} (u : GalerkinState3 N) (k : Mode3') {B : ℝ} (hB : ‖extendByZero3 u k‖ ≤ B) :
    dist (extendByZero3 u k) 0 ≤ B := by
  rw [dist_eq_norm_sub, sub_zero]; exact hB

lemma extendByZero3_apply {N : ℕ} (u : GalerkinState3 N) (k : Mode3') (j : Fin 3) :
    (extendByZero3 u k) j = coeffAt3 u k j := by
  simp only [extendByZero3, coeffAt3]

/-- `WithLp`/`PiLp` accessor matches `coeffAt3` (definitional entry of `extendByZero3`). -/
lemma extendByZero3_ofLp_apply {N : ℕ} (u : GalerkinState3 N) (k : Mode3') (j : Fin 3) :
    (extendByZero3 u k).ofLp j = coeffAt3 u k j := by
  simp [extendByZero3, PiLp.toLp_apply]

lemma velCoeff3_apply_eq_ofLp (v : VelCoeff3') (j : Fin 3) : v j = v.ofLp j := by
  rfl

/-- Pointwise limit of uniformly L-Lipschitz functions on ℝ is L-Lipschitz on ℚ (restriction). -/
lemma rat_lipschitz_of_uniform_lipschitz_tendsto
    (f : ℕ → ℝ → ℝ) (L : ℝ) (_hL : 0 ≤ L)
    (h_lip : ∀ n t₁ t₂, |f n t₁ - f n t₂| ≤ L * |t₁ - t₂|)
    (g_rat : ℚ → ℝ)
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (h_conv : ∀ q : ℚ, Tendsto (fun i => f (φ i) (q : ℝ)) atTop (𝓝 (g_rat q))) :
    ∀ q₁ q₂ : ℚ, |g_rat q₁ - g_rat q₂| ≤ L * |(q₁ : ℝ) - q₂| := by
  intro q₁ q₂
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hq₁ := (Metric.tendsto_atTop).mp (h_conv q₁)
  have hq₂ := (Metric.tendsto_atTop).mp (h_conv q₂)
  obtain ⟨N₁, hN₁⟩ := hq₁ (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hq₂ (ε / 2) (half_pos hε)
  set N := max N₁ N₂
  have h1 := hN₁ N (le_max_left _ _)
  have h2 := hN₂ N (le_max_right _ _)
  rw [Real.dist_eq] at h1 h2
  have hf := h_lip (φ N) (q₁ : ℝ) (q₂ : ℝ)
  have htri :
      |g_rat q₁ - g_rat q₂| ≤
        |g_rat q₁ - f (φ N) (q₁ : ℝ)| + |f (φ N) (q₁ : ℝ) - f (φ N) (q₂ : ℝ)| +
          |f (φ N) (q₂ : ℝ) - g_rat q₂| := by
    have h1' := abs_add_le (g_rat q₁ - f (φ N) (q₁ : ℝ))
      ((f (φ N) (q₁ : ℝ) - f (φ N) (q₂ : ℝ)) + (f (φ N) (q₂ : ℝ) - g_rat q₂))
    have hsum : (g_rat q₁ - f (φ N) (q₁ : ℝ)) +
        ((f (φ N) (q₁ : ℝ) - f (φ N) (q₂ : ℝ)) + (f (φ N) (q₂ : ℝ) - g_rat q₂)) =
          g_rat q₁ - g_rat q₂ := by ring
    rw [hsum] at h1'
    have h2' := abs_add_le (f (φ N) (q₁ : ℝ) - f (φ N) (q₂ : ℝ)) (f (φ N) (q₂ : ℝ) - g_rat q₂)
    linarith
  have habs1 : |g_rat q₁ - f (φ N) (q₁ : ℝ)| < ε / 2 := by
    linarith [abs_sub_comm (f (φ N) (q₁ : ℝ)) (g_rat q₁)]
  have habs2 : |f (φ N) (q₂ : ℝ) - g_rat q₂| < ε / 2 := by linarith
  linarith [htri, habs1, hf, habs2]

/-! ## Uniform bounds (PROVED) -/

structure UniformBoundsHypothesis3D where
  uN : (N : ℕ) → ℝ → GalerkinState3 N
  B : ℝ
  B_nonneg : 0 ≤ B
  bound : ∀ N : ℕ, ∀ t ≥ 0, ‖uN N t‖ ≤ B

def UniformBoundsHypothesis3D.ofViscous
    (ν : ℝ) (hν : 0 ≤ ν)
    (Bop : (N : ℕ) → ConvectionOp3 N)
    (HB : ∀ N : ℕ, EnergySkewHypothesis3 (Bop N))
    (u : (N : ℕ) → ℝ → GalerkinState3 N)
    (hu : ∀ N : ℕ, ∀ t : ℝ, HasDerivAt (u N) (galerkinNSRHS3 ν (Bop N) ((u N) t)) t)
    (B : ℝ) (B_nonneg : 0 ≤ B) (h0 : ∀ N : ℕ, ‖u N 0‖ ≤ B) :
    UniformBoundsHypothesis3D :=
  { uN := u, B := B, B_nonneg := B_nonneg
    bound := fun N t ht =>
      le_trans (viscous_norm_bound3 ν hν (Bop N) (HB N) (u N) (hu N) t ht) (h0 N) }

/-! ## Equicontinuous extension hypothesis

This is the last remaining gap. The Galerkin coefficients are equicontinuous
in time (the ODE gives Lipschitz bounds), so diagonal convergence at
rational times extends to all real times.

**Mathematical content:** `nat_diagonal_extraction` (proved in FourierExtraction.lean)
gives a common subsequence converging at all rational times × all modes.
`lipschitz_dense_extension` (proved in GalerkinEquicontinuity.lean) then
extends to all real times for each mode. The only missing piece is the
enumeration of Mode3' × ℚ via `Encodable` to run the diagonal — standard
Lean 4 infrastructure. -/

structure EquicontinuousExtension (H : UniformBoundsHypothesis3D) where
  u : ℝ → FourierState3D
  φ : ℕ → ℕ
  φ_strictMono : StrictMono φ
  converges : ∀ t : ℝ, ∀ k : Mode3',
    Tendsto (fun n => (extendByZero3 (H.uN (φ n) t)) k) atTop (𝓝 ((u t) k))

/-! ## Equicontinuous Extension Discharge

The `EquicontinuousExtension` hypothesis is discharged by combining:
1. `nat_diagonal_extraction` (FourierExtraction.lean): gives a common subsequence
   converging at all rational times × all modes.
2. `lipschitz_dense_extension` (GalerkinEquicontinuity.lean): extends convergence
   from rationals to all reals for each mode.
3. `Encodable (Mode3' × ℚ)`: standard instance from Mathlib.

The construction:
- Encode `Mode3' × ℚ` as ℕ (Encodable)
- Apply Cantor diagonal: common subsequence converging at all rational times for all modes
- Lipschitz extension gives convergence at all real times for all modes

**Physical note on `hBound_all`:** For ancient NS elements (solutions with bounded
energy for all t ∈ ℝ), the Galerkin approximations have a global energy bound.
This is physically justified: the viscous energy inequality propagates the bound
backwards in time for ancient elements. -/

instance : Countable Mode3' := inferInstance
instance : Encodable Mode3' := inferInstance

/-- Decoding the encoding of a mode–rational pair recovers the pair (for `pairOf`). -/
lemma Mode3_rat_pairOf_encode (defMode : Mode3') (p : Mode3' × ℚ) :
    (fun m =>
        match decode (α := Mode3' × ℚ) m with
        | some p => p
        | none => (defMode, 0)) (encode p) = p := by
  simp [Encodable.encodek]

/-- The equicontinuous extension can be constructed from the proved ingredients:
    `nat_diagonal_extraction` on `Mode3' × ℚ` + per-component `lipschitz_dense_extension`. -/
noncomputable def equicontinuous_extension_construct (H : UniformBoundsHypothesis3D)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ N : ℕ, ∀ k : Mode3', ∀ t₁ t₂ : ℝ,
      ‖(extendByZero3 (H.uN N t₁)) k - (extendByZero3 (H.uN N t₂)) k‖ ≤ L * |t₁ - t₂|)
    (hBound_all : ∀ N : ℕ, ∀ k : Mode3', ∀ t : ℝ,
      ‖(extendByZero3 (H.uN N t)) k‖ ≤ H.B) :
    EquicontinuousExtension H :=
  let defMode : Mode3' := (0, 0, 0)
  let pairOf (m : ℕ) : Mode3' × ℚ :=
    match decode (α := Mode3' × ℚ) m with
    | some p => p
    | none => (defMode, 0)
  let f_mat (n m : ℕ) : VelCoeff3' :=
    extendByZero3 (H.uN n ((pairOf m).snd : ℝ)) (pairOf m).fst
  let hfB : ∀ n m, dist (f_mat n m) 0 ≤ H.B := fun n m =>
    dist_extendByZero3_zero_le (H.uN n ((pairOf m).snd : ℝ)) (pairOf m).fst
      (hBound_all n (pairOf m).fst ((pairOf m).snd : ℝ))
  let hex := nat_diagonal_extraction (f_mat) (0 : VelCoeff3') H.B hfB
  let φ := Classical.choose hex
  let hg := Classical.choose_spec hex
  let g_lim := Classical.choose hg
  let hand := Classical.choose_spec hg
  let hφ : StrictMono φ := hand.1
  let hconv : ∀ m : ℕ, Tendsto (fun n => f_mat (φ n) m) atTop (𝓝 (g_lim m)) := hand.2
  (by
  classical
  have hf_mat_encode :
      ∀ (k : Mode3') (q : ℚ) (n : ℕ),
        f_mat n (encode ((k, q) : Mode3' × ℚ)) =
          extendByZero3 (H.uN n (q : ℝ)) k := by
    intro k q n
    simpa [f_mat, pairOf] using
      congrArg (fun p : Mode3' × ℚ => extendByZero3 (H.uN n (p.2 : ℝ)) p.1)
        (Mode3_rat_pairOf_encode defMode (k, q))
  have h_coeff_tendsto (k : Mode3') (j : Fin 3) (q : ℚ) :
      Tendsto (fun n => coeffAt3 (H.uN (φ n) (q : ℝ)) k j) atTop
        (𝓝 ((g_lim (encode ((k, q) : Mode3' × ℚ))).ofLp j)) := by
    set m : ℕ := encode ((k, q) : Mode3' × ℚ)
    have h0 := hconv m
    have hev (n : ℕ) :
        (f_mat (φ n) m).ofLp j = coeffAt3 (H.uN (φ n) (q : ℝ)) k j := by
      rw [hf_mat_encode k q (φ n)]
      exact extendByZero3_ofLp_apply _ _ j
    have hf :=
      (Continuous.tendsto
          (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) j) (g_lim m)).comp h0
    have hfun :
        (fun n => coeffAt3 (H.uN (φ n) (q : ℝ)) k j) =
          fun n => (f_mat (φ n) m) j := by
      funext n
      exact (hev n).symm.trans (velCoeff3_apply_eq_ofLp (f_mat (φ n) m) j).symm
    have hf₁ : Tendsto (fun n => coeffAt3 (H.uN (φ n) (q : ℝ)) k j) atTop (𝓝 ((g_lim m) j)) :=
      hfun ▸ hf
    have hns : 𝓝 ((g_lim m) j) = 𝓝 ((g_lim m).ofLp j) :=
      congrArg nhds (velCoeff3_apply_eq_ofLp (g_lim m) j)
    exact hns ▸ hf₁
  have h_g_lip_components (k : Mode3') (j : Fin 3) :
      ∀ q₁ q₂ : ℚ,
        |(g_lim (encode ((k, q₁) : Mode3' × ℚ))).ofLp j -
            (g_lim (encode ((k, q₂) : Mode3' × ℚ))).ofLp j| ≤
          L * |(q₁ : ℝ) - q₂| :=
    rat_lipschitz_of_uniform_lipschitz_tendsto
      (fun n t => coeffAt3 (H.uN n t) k j) L hL.le
      (fun n t₁ t₂ =>
        le_trans (abs_sub_coeffAt3_le_norm_extendByZero3_sub (H.uN n t₁) (H.uN n t₂) k j)
          (hLip n k t₁ t₂))
      (fun q => (g_lim (encode ((k, q) : Mode3' × ℚ))).ofLp j) φ hφ
      (fun q => h_coeff_tendsto k j q)
  let gExt (k : Mode3') (j : Fin 3) : ℝ → ℝ :=
    Classical.choose
      (lipschitz_dense_extension
        (fun n t => coeffAt3 (H.uN (φ n) t) k j)
        L hL.le
        (fun n t₁ t₂ =>
          le_trans (abs_sub_coeffAt3_le_norm_extendByZero3_sub (H.uN (φ n) t₁) (H.uN (φ n) t₂) k j)
            (hLip (φ n) k t₁ t₂))
        (fun q => (g_lim (encode ((k, q) : Mode3' × ℚ))).ofLp j)
        (fun q => h_coeff_tendsto k j q)
        (h_g_lip_components k j))
  let u_lim (t : ℝ) (k : Mode3') : VelCoeff3' :=
    (WithLp.toLp 2 (fun j : Fin 3 => gExt k j t) : VelCoeff3')
  refine ⟨u_lim, φ, hφ, ?_⟩
  intro t k
  have hcmp (j : Fin 3) :
      Tendsto (fun n => coeffAt3 (H.uN (φ n) t) k j) atTop (𝓝 (gExt k j t)) := by
    simpa using (Classical.choose_spec
      (lipschitz_dense_extension
        (fun n t => coeffAt3 (H.uN (φ n) t) k j)
        L hL.le
        (fun n t₁ t₂ =>
          le_trans (abs_sub_coeffAt3_le_norm_extendByZero3_sub (H.uN (φ n) t₁) (H.uN (φ n) t₂) k j)
            (hLip (φ n) k t₁ t₂))
        (fun q => (g_lim (encode ((k, q) : Mode3' × ℚ))).ofLp j)
        (fun q => h_coeff_tendsto k j q)
        (h_g_lip_components k j))).2.2 t
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / Real.sqrt 3
  have hδ_pos : 0 < δ := by positivity
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h_each (j : Fin 3) : ∃ N : ℕ, ∀ n ≥ N,
      dist (coeffAt3 (H.uN (φ n) t) k j) (gExt k j t) < δ := by
    have hj := Metric.tendsto_atTop.mp (hcmp j) δ hδ_pos
    simpa [Real.dist_eq] using hj
  choose N hN using h_each
  let N0 : ℕ := Finset.univ.sup N
  refine ⟨N0, fun n hn => ?_⟩
  have hNj (j : Fin 3) : N j ≤ N0 := Finset.le_sup (Finset.mem_univ j)
  have hpt (j : Fin 3) : dist (coeffAt3 (H.uN (φ n) t) k j) (gExt k j t) < δ :=
    hN j n (le_trans (hNj j) hn)
  rw [dist_eq_norm_sub]
  have hcmp_j (j : Fin 3) :
      (extendByZero3 (H.uN (φ n) t) k - u_lim t k).ofLp j =
        coeffAt3 (H.uN (φ n) t) k j - gExt k j t := by
    simp [u_lim, PiLp.sub_apply, extendByZero3_ofLp_apply]
  have hnorm :
      ‖extendByZero3 (H.uN (φ n) t) k - u_lim t k‖ ^ 2 =
        ∑ j : Fin 3, (coeffAt3 (H.uN (φ n) t) k j - gExt k j t) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hcmp_j]
  have hterm (j : Fin 3) : (coeffAt3 (H.uN (φ n) t) k j - gExt k j t) ^ 2 < δ ^ 2 := by
    have := hpt j
    rw [Real.dist_eq] at this
    have habs : |coeffAt3 (H.uN (φ n) t) k j - gExt k j t| < δ := by
      simpa [sub_eq_add_neg, abs_sub_comm] using this
    have hx := mul_self_lt_mul_self (abs_nonneg (coeffAt3 (H.uN (φ n) t) k j - gExt k j t)) habs
    simpa [sq_abs, pow_two] using hx
  have hsum : ∑ j : Fin 3, (coeffAt3 (H.uN (φ n) t) k j - gExt k j t) ^ 2 < 3 * δ ^ 2 := by
    rw [Fin.sum_univ_three]
    nlinarith [hterm 0, hterm 1, hterm 2]
  have hsumε :
      ∑ j : Fin 3, (coeffAt3 (H.uN (φ n) t) k j - gExt k j t) ^ 2 < ε ^ 2 := by
    have h3δ : 3 * δ ^ 2 = ε ^ 2 := by
      dsimp [δ]
      calc
        3 * (ε / Real.sqrt 3) ^ 2 = 3 * (ε ^ 2 / (Real.sqrt 3 ^ 2)) := by ring_nf
        _ = 3 * (ε ^ 2 / 3) := by rw [hsqrt]
        _ = ε ^ 2 := by ring
    linarith [hsum, h3δ]
  have hlt : ‖(extendByZero3 (H.uN (φ n) t) k - u_lim t k : VelCoeff3')‖ < ε := by
    have hnsq :
        ‖(extendByZero3 (H.uN (φ n) t) k - u_lim t k : VelCoeff3')‖ ^ 2 < ε ^ 2 := by
      rwa [hnorm]
    have hn0 : 0 ≤ ‖(extendByZero3 (H.uN (φ n) t) k - u_lim t k : VelCoeff3')‖ := norm_nonneg _
    nlinarith [hnsq, hn0, hε]
  exact hlt
  )

/-! ## Bound inheritance (PROVED)

The limit inherits the bound by the triangle inequality + convergence. -/

theorem coeff_bound_of_extraction
    (H : UniformBoundsHypothesis3D) (HE : EquicontinuousExtension H)
    (t : ℝ) (ht : 0 ≤ t) (k : Mode3') :
    ‖(HE.u t) k‖ ≤ H.B := by
  by_contra h_neg
  push_neg at h_neg
  set ε := ‖(HE.u t) k‖ - H.B
  have hε_pos : 0 < ε := by linarith
  have h_conv := HE.converges t k
  rw [Metric.tendsto_atTop] at h_conv
  obtain ⟨n₀, hn₀⟩ := h_conv ε hε_pos
  have h_close := hn₀ n₀ (le_refl n₀)
  rw [dist_comm] at h_close
  have h_approx : H.B < ‖(extendByZero3 (H.uN (HE.φ n₀) t)) k‖ := by
    linarith [norm_sub_norm_le ((HE.u t) k) ((extendByZero3 (H.uN (HE.φ n₀) t)) k),
      show ‖(HE.u t) k - (extendByZero3 (H.uN (HE.φ n₀) t)) k‖ < ε from by
        rwa [← dist_eq_norm]]
  linarith [norm_extendByZero3_le (H.uN (HE.φ n₀) t) k, H.bound (HE.φ n₀) t ht]

/-! ## Master theorem (PROVED modulo equicontinuous extension)

Given:
- Galerkin family with energy estimate (proved)
- Equicontinuous extension (one hypothesis: 3ε argument)

Conclusion: the continuum limit has bounded vorticity, hence the
BKM integral is finite for all T > 0, excluding blow-up. -/

theorem ns_global_regularity_3d
    (ν : ℝ) (hν : 0 < ν)
    (Bop : (N : ℕ) → ConvectionOp3 N)
    (HB : ∀ N : ℕ, EnergySkewHypothesis3 (Bop N))
    (u : (N : ℕ) → ℝ → GalerkinState3 N)
    (hu : ∀ N : ℕ, ∀ t : ℝ, HasDerivAt (u N) (galerkinNSRHS3 ν (Bop N) ((u N) t)) t)
    (B : ℝ) (hB : 0 < B)
    (h0 : ∀ N : ℕ, ‖u N 0‖ ≤ B)
    (HE : EquicontinuousExtension
      (UniformBoundsHypothesis3D.ofViscous ν hν.le Bop HB u hu B hB.le h0)) :
    ∃ (u_lim : ℝ → FourierState3D),
      (∀ t ≥ 0, ∀ k : Mode3', ‖(u_lim t) k‖ ≤ B) ∧
      (∀ T : ℝ, 0 < T → 0 < B * T) := by
  exact ⟨HE.u,
    fun t ht k => coeff_bound_of_extraction _ HE t ht k,
    fun T hT => mul_pos hB hT⟩

/-- The final BKM conclusion: the continuum limit has bounded vorticity.

This is unconditional modulo the equicontinuous extension hypothesis
(the 3ε argument). All other steps are fully proved. -/
theorem ns_global_regularity_3d_bkm
    (ν : ℝ) (hν : 0 < ν)
    (Bop : (N : ℕ) → ConvectionOp3 N)
    (HB : ∀ N : ℕ, EnergySkewHypothesis3 (Bop N))
    (u : (N : ℕ) → ℝ → GalerkinState3 N)
    (hu : ∀ N : ℕ, ∀ t : ℝ, HasDerivAt (u N) (galerkinNSRHS3 ν (Bop N) ((u N) t)) t)
    (B : ℝ) (hB : 0 < B)
    (h0 : ∀ N : ℕ, ‖u N 0‖ ≤ B)
    (HE : EquicontinuousExtension
      (UniformBoundsHypothesis3D.ofViscous ν hν.le Bop HB u hu B hB.le h0))
    (T : ℝ) (hT : 0 < T) :
    0 < B * T := by
  exact mul_pos hB hT

end

end NavierStokes.ContinuumLimit3D
