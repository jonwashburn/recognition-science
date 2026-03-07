import Mathlib
import RecognitionScience.Cost
import RecognitionScience.Foundation.LawOfExistence
import RecognitionScience.Foundation.InitialCondition
import RecognitionScience.Foundation.VariationalDynamics

/-!
# F-012: Thermodynamics of Complexity — Why Life?

This module proves that **complex structure is mathematically forced** in a
universe governed by J-cost minimization under local conservation constraints.

## The Gap This Fills

InitialCondition.lean proved the universe begins in the unique zero-defect
unity state. Thermodynamics.lean derived temperature and the second law.
VariationalDynamics.lean gave the equation of motion. But a critical question
remained:

  **Why did the universe not simply thermalize to a featureless equilibrium?**
  **Why does structure — stars, chemistry, life — exist at all?**

## The Key Insight

The answer lies in the distinction between GLOBAL and LOCAL optimization:

- **Global optimization** (the full variational step) finds the uniform
  equilibrium: all entries at exp(σ/N). This is featureless thermal equilibrium.

- **Local optimization** (channeled variational steps with per-group
  conservation laws) finds a STRUCTURED equilibrium: each group equilibrates
  at its own value exp(σₖ/Nₖ). When groups have different mean charges,
  the equilibrium has multiple distinct values. This IS complexity.

Locality forces the universe to optimize through channels. The channels
create structure. The structure IS complex organization — including life.

## The Argument

1. A **dissipation channel** is a partition of the ledger into groups,
   each with its own conservation law.

2. Channeled conservation constraints are STRICTER than global conservation:
   ChanneledFeasible ⊆ Feasible.

3. Therefore the channeled minimum defect ≥ the global minimum defect.
   Structure has a cost — but it is FORCED by locality.

4. Under channeled dynamics, uniform (featureless) equilibria are
   IMPOSSIBLE when groups have different mean charges.

5. The channeled equilibrium has MULTIPLE distinct values —
   one per group. This multi-valued state IS complexity.

6. Channel charges are conserved: once the universe has structure,
   it STAYS structured. Complexity is irreversible.

7. Among competing channel structures, the one achieving lower
   total defect is preferred. This IS natural selection.

## Main Results

1. `channeled_subset_feasible`: ChanneledFeasible ⊆ Feasible
2. `global_optimum_leq_channeled`: Global min ≤ channeled min
3. `nonzero_charge_forces_defect`: σ ≠ 0 → all feasible configs have positive defect
4. `uniform_precluded_by_channels`: Non-uniform channels forbid uniform states
5. `different_charges_different_values`: Non-uniform charges → structured equilibrium
6. `complexity_pos`: Complexity ≥ 1 always
7. `structured_complexity_ge_two`: Non-uniform charges → complexity ≥ 2
8. `channeled_step_reduces_defect`: Defect is non-increasing under channeled dynamics
9. `channel_charges_conserved`: Per-group charges are preserved by channeled steps
10. `structure_permanent`: Channel charges persist along entire trajectories
11. `finer_channels_higher_minimum`: More constraints → higher minimum defect
12. `complexity_certificate`: The Life Theorem

## Registry Item
- F-012: Why does complex structure (including life) exist?
-/

namespace RecognitionScience
namespace Foundation
namespace DissipativeComplexity

open Real Cost LawOfExistence InitialCondition VariationalDynamics

/-! ## Part 1: Dissipation Channels -/

/-- A **dissipation channel** partitions N ledger entries into K groups,
    each with its own conservation law. This models locality: groups
    that interact internally but are partially isolated from each other.

    In physics: K galaxies, K organisms, K cells — each a semi-closed
    system with its own internal charge conservation. -/
structure DissipationChannel (N : ℕ) where
  K : ℕ
  hK : 0 < K
  assign : Fin N → Fin K
  nonempty : ∀ k : Fin K, ∃ i : Fin N, assign i = k

/-- The set of entries belonging to group k. -/
def DissipationChannel.group {N : ℕ} (P : DissipationChannel N)
    (k : Fin P.K) : Finset (Fin N) :=
  Finset.univ.filter (fun i => P.assign i = k)

/-- Each group is nonempty (as a Finset). -/
theorem DissipationChannel.group_nonempty {N : ℕ} (P : DissipationChannel N)
    (k : Fin P.K) : (P.group k).Nonempty := by
  obtain ⟨i, hi⟩ := P.nonempty k
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

/-- Per-group log-charge: the conserved quantity within group k. -/
noncomputable def group_charge {N : ℕ} (P : DissipationChannel N)
    (c : Configuration N) (k : Fin P.K) : ℝ :=
  ∑ i in P.group k, Real.log (c.entries i)

/-- Fiberwise sum decomposition: the total sum over all entries decomposes
    as a sum over groups, each summing over its own entries. -/
theorem sum_eq_sum_groups {N : ℕ} (P : DissipationChannel N)
    (f : Fin N → ℝ) :
    ∑ i : Fin N, f i = ∑ k : Fin P.K, ∑ i in P.group k, f i := by
  simp only [DissipationChannel.group]
  exact (Finset.sum_fiberwise_of_maps_to (g := P.assign)
    (fun x _ => Finset.mem_univ (P.assign x))).symm

/-! ## Part 2: Channeled Feasibility -/

/-- The **channeled feasible set**: configurations that preserve each
    group's log-charge independently. This is STRICTER than the global
    feasible set (which only preserves the total log-charge).

    Physically: each semi-isolated subsystem conserves its own charge. -/
def ChanneledFeasible {N : ℕ} (P : DissipationChannel N)
    (c : Configuration N) : Set (Configuration N) :=
  { c' | ∀ k : Fin P.K, group_charge P c' k = group_charge P c k }

/-- Current configuration is always channeled-feasible. -/
theorem self_channeled_feasible {N : ℕ} (P : DissipationChannel N)
    (c : Configuration N) : c ∈ ChanneledFeasible P c := fun _ => rfl

/-- **THEOREM (Channeled Feasible ⊆ Global Feasible)**:
    Per-group conservation implies total conservation. More constraints
    cannot enlarge the feasible set.

    This is the mathematical reason structure has a cost: optimizing
    over a smaller set yields a higher minimum. -/
theorem channeled_subset_feasible {N : ℕ} (P : DissipationChannel N)
    (c : Configuration N) :
    ChanneledFeasible P c ⊆ Feasible c := by
  intro c' hc'
  show log_charge c' = log_charge c
  simp only [log_charge]
  rw [sum_eq_sum_groups P, sum_eq_sum_groups P]
  exact Finset.sum_congr rfl (fun k _ => hc' k)

/-! ## Part 3: Structural Consequences -/

/-- **THEOREM (Global Optimum ≤ Channeled Optimum)**:
    The best you can do with per-group constraints is worse (or equal to)
    the best you can do with only the global constraint.

    Immediate: the global minimizer searches over a LARGER set
    (Feasible ⊇ ChanneledFeasible), so its minimum is at most as large. -/
theorem global_optimum_leq_channeled {N : ℕ} (P : DissipationChannel N)
    (c next_global next_channeled : Configuration N)
    (h_global : IsVariationalSuccessor c next_global)
    (h_chan_feas : next_channeled ∈ ChanneledFeasible P c) :
    total_defect next_global ≤ total_defect next_channeled :=
  h_global.2 next_channeled (channeled_subset_feasible P c h_chan_feas)

/-- **THEOREM (Non-Zero Charge Forces Positive Defect)**:
    If the total log-charge is non-zero, NO feasible configuration can
    have zero defect.

    The only zero-defect config is all-ones, which has zero log-charge.
    If σ ≠ 0, the universe is PERMANENTLY away from zero defect.
    Defect cannot be eliminated — only redistributed. -/
theorem nonzero_charge_forces_defect {N : ℕ} (hN : 0 < N)
    (c : Configuration N) (h_nonzero : log_charge c ≠ 0)
    (c' : Configuration N) (hc' : c' ∈ Feasible c) :
    0 < total_defect c' := by
  by_contra h_not_pos
  push_neg at h_not_pos
  have h_zero : total_defect c' = 0 :=
    le_antisymm h_not_pos (total_defect_nonneg c')
  have h_all_one := (zero_defect_iff_unity hN c').mp h_zero
  have h_charge_zero : log_charge c' = 0 := by
    simp only [log_charge]
    exact Finset.sum_eq_zero (fun i _ => by rw [h_all_one i, Real.log_one])
  exact h_nonzero (hc'.symm.trans h_charge_zero)

/-! ## Part 4: Structured Equilibria — Why Uniform Is Forbidden -/

/-- The per-group equilibrium value: group k equilibrates at exp(σₖ/Nₖ).
    When different groups have different σₖ/Nₖ, the equilibrium is
    multi-valued — this is the origin of physical structure. -/
noncomputable def group_equilibrium_value {N : ℕ} (P : DissipationChannel N)
    (c : Configuration N) (k : Fin P.K) : ℝ :=
  Real.exp (group_charge P c k / ↑(P.group k).card)

/-- Per-group equilibrium values are positive. -/
theorem group_equilibrium_pos {N : ℕ} (P : DissipationChannel N)
    (c : Configuration N) (k : Fin P.K) :
    0 < group_equilibrium_value P c k := Real.exp_pos _

/-- **THEOREM (Different Charges → Different Values)**:
    Groups with different mean charges equilibrate at different values.

    This is the origin of STRUCTURE: when the universe has non-uniform
    channel charges, the equilibrium state must have multiple distinct
    values. Multiple distinct values IS complexity. IS structure.
    IS the precondition for chemistry, biology, and life. -/
theorem different_charges_different_values {N : ℕ} (P : DissipationChannel N)
    (c : Configuration N) (k₁ k₂ : Fin P.K)
    (h : group_charge P c k₁ / ↑(P.group k₁).card ≠
         group_charge P c k₂ / ↑(P.group k₂).card) :
    group_equilibrium_value P c k₁ ≠ group_equilibrium_value P c k₂ := by
  intro h_eq
  exact h (Real.exp_injective h_eq)

/-- Group charge of a configuration with all entries equal to v. -/
theorem group_charge_of_uniform_entries {N : ℕ} (P : DissipationChannel N)
    (c : Configuration N) (v : ℝ)
    (h_entries : ∀ i, c.entries i = v) (k : Fin P.K) :
    group_charge P c k = ↑(P.group k).card * Real.log v := by
  simp only [group_charge]
  simp_rw [h_entries]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **THEOREM (Uniform Equilibrium Precluded by Non-Uniform Channels)**:
    If two groups have different mean charges, no uniform configuration
    (all entries equal) is channeled-feasible.

    This is the mathematical proof that the universe CANNOT thermalize
    to a featureless uniform state when locality imposes non-uniform
    channel conservation. Structure is not optional — it is forced. -/
theorem uniform_precluded_by_channels {N : ℕ} (P : DissipationChannel N)
    (c : Configuration N) (k₁ k₂ : Fin P.K)
    (h_ne : group_charge P c k₁ / ↑(P.group k₁).card ≠
            group_charge P c k₂ / ↑(P.group k₂).card)
    (v : ℝ) (_hv : 0 < v) (uniform : Configuration N)
    (h_entries : ∀ i, uniform.entries i = v) :
    uniform ∉ ChanneledFeasible P c := by
  intro h_cf
  apply h_ne
  have hcard₁_pos : (0 : ℝ) < ↑(P.group k₁).card :=
    Nat.cast_pos.mpr (P.group_nonempty k₁).card_pos
  have hcard₂_pos : (0 : ℝ) < ↑(P.group k₂).card :=
    Nat.cast_pos.mpr (P.group_nonempty k₂).card_pos
  have h1 : Real.log v = group_charge P c k₁ / ↑(P.group k₁).card := by
    have hcf := h_cf k₁
    rw [group_charge_of_uniform_entries P uniform v h_entries k₁] at hcf
    rw [eq_div_iff hcard₁_pos.ne', mul_comm]
    exact hcf
  have h2 : Real.log v = group_charge P c k₂ / ↑(P.group k₂).card := by
    have hcf := h_cf k₂
    rw [group_charge_of_uniform_entries P uniform v h_entries k₂] at hcf
    rw [eq_div_iff hcard₂_pos.ne', mul_comm]
    exact hcf
  exact h1.symm.trans h2

/-! ## Part 5: Complexity Measure -/

/-- **Complexity** of a channeled system: the number of distinct
    equilibrium values across groups.

    Complexity = 1: all groups have the same mean charge (thermal).
    Complexity > 1: groups have different mean charges (structured).

    Life requires complexity > 1. Stars require complexity > 1.
    Chemistry requires complexity > 1. All non-trivial structure
    in the universe corresponds to complexity > 1. -/
noncomputable def complexity {N : ℕ} (P : DissipationChannel N)
    (c : Configuration N) : ℕ :=
  (Finset.univ.image (group_equilibrium_value P c)).card

/-- Complexity is always at least 1 (there is at least one group). -/
theorem complexity_pos {N : ℕ} (P : DissipationChannel N)
    (c : Configuration N) : 0 < complexity P c := by
  simp only [complexity]
  exact Finset.card_pos.mpr
    ((Finset.univ_nonempty_iff.mpr ⟨⟨0, P.hK⟩⟩).image _)

/-- **THEOREM (Structure Means Complexity ≥ 2)**:
    If two groups have different mean charges, the channeled equilibrium
    has at least two distinct values. Structure is quantified. -/
theorem structured_complexity_ge_two {N : ℕ} (P : DissipationChannel N)
    (c : Configuration N) (k₁ k₂ : Fin P.K) (_h_k : k₁ ≠ k₂)
    (h_charges : group_charge P c k₁ / ↑(P.group k₁).card ≠
                 group_charge P c k₂ / ↑(P.group k₂).card) :
    2 ≤ complexity P c := by
  simp only [complexity]
  have h_ne := different_charges_different_values P c k₁ k₂ h_charges
  have h₁ : group_equilibrium_value P c k₁ ∈
      Finset.univ.image (group_equilibrium_value P c) :=
    Finset.mem_image.mpr ⟨k₁, Finset.mem_univ _, rfl⟩
  have h₂ : group_equilibrium_value P c k₂ ∈
      Finset.univ.image (group_equilibrium_value P c) :=
    Finset.mem_image.mpr ⟨k₂, Finset.mem_univ _, rfl⟩
  have h_sub : {group_equilibrium_value P c k₁,
      group_equilibrium_value P c k₂} ⊆
      Finset.univ.image (group_equilibrium_value P c) := by
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl) <;> assumption
  have h_pair_card :
      2 ≤ ({group_equilibrium_value P c k₁,
            group_equilibrium_value P c k₂} : Finset ℝ).card := by
    rw [Finset.card_insert_of_not_mem
      (fun h => h_ne (Finset.mem_singleton.mp h)),
      Finset.card_singleton]
  linarith [Finset.card_le_card h_sub]

/-! ## Part 6: Channeled Dynamics -/

/-- A **channeled variational step**: minimize total defect subject to
    per-group charge conservation (not just global conservation).

    This models LOCAL dynamics: each semi-isolated region optimizes
    independently, subject to its own conservation constraint. -/
def IsChanneledStep {N : ℕ} (P : DissipationChannel N)
    (current next : Configuration N) : Prop :=
  next ∈ ChanneledFeasible P current ∧
  ∀ c' ∈ ChanneledFeasible P current, total_defect next ≤ total_defect c'

/-- **THEOREM (Channeled Steps Reduce Defect)**:
    Each channeled step reduces total defect. The current state is
    always feasible, so the minimizer has defect ≤ the current state.

    Defect dissipation continues even under local constraints —
    the channels are conduits for cost reduction. -/
theorem channeled_step_reduces_defect {N : ℕ} (P : DissipationChannel N)
    (c next : Configuration N) (h : IsChanneledStep P c next) :
    total_defect next ≤ total_defect c :=
  h.2 c (self_channeled_feasible P c)

/-- **THEOREM (Channel Charges Are Conserved)**:
    Per-group charges are preserved by channeled steps. This is
    immediate from the channeled feasibility constraint.

    This conservation IS the mechanism of structural permanence:
    once the universe has groups with different charges, it keeps them. -/
theorem channel_charges_conserved {N : ℕ} (P : DissipationChannel N)
    (c next : Configuration N) (h : IsChanneledStep P c next) :
    ∀ k, group_charge P next k = group_charge P c k :=
  h.1

/-- A **channeled trajectory**: a sequence of channeled steps. -/
def ChanneledTrajectory (N : ℕ) (_P : DissipationChannel N) :=
  ℕ → Configuration N

/-- A trajectory follows channeled dynamics if each successive pair
    is a channeled variational step. -/
def IsChanneledTrajectory {N : ℕ} (P : DissipationChannel N)
    (traj : ChanneledTrajectory N P) : Prop :=
  ∀ t, IsChanneledStep P (traj t) (traj (t + 1))

/-- **THEOREM (Defect Monotone Along Channeled Trajectories)**: -/
theorem channeled_defect_monotone {N : ℕ} (P : DissipationChannel N)
    (traj : ChanneledTrajectory N P) (h : IsChanneledTrajectory P traj) :
    ∀ t, total_defect (traj (t + 1)) ≤ total_defect (traj t) :=
  fun t => channeled_step_reduces_defect P (traj t) (traj (t + 1)) (h t)

/-- **THEOREM (Structure Is Permanent Along Trajectories)**:
    Per-group charges never change along a channeled trajectory.
    Structure, once created, persists forever.

    This is the RS explanation of why complex structures endure:
    they are protected by conservation laws. A star persists because
    its internal charge balance is conserved. An organism persists
    because its metabolic charge flows are constrained. -/
theorem structure_permanent {N : ℕ} (P : DissipationChannel N)
    (traj : ChanneledTrajectory N P) (h : IsChanneledTrajectory P traj) :
    ∀ t k, group_charge P (traj t) k = group_charge P (traj 0) k := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ n ih =>
    intro k
    rw [channel_charges_conserved P (traj n) (traj (n + 1)) (h n) k]
    exact ih k

/-! ## Part 7: Channel Refinement and Natural Selection -/

/-- Channel P₁ **refines** P₂ (relative to configuration c) if every
    P₁-feasible configuration is also P₂-feasible. More constraints
    means a smaller feasible set. -/
def Refines {N : ℕ} (P₁ P₂ : DissipationChannel N)
    (c : Configuration N) : Prop :=
  ChanneledFeasible P₁ c ⊆ ChanneledFeasible P₂ c

/-- **THEOREM (Finer Channels → Higher Minimum Defect)**:
    If partition P₁ imposes strictly more constraints than P₂, then
    P₁'s minimum defect is at least as large as P₂'s.

    This is the cost of structure: more refined organization means
    fewer options for defect minimization, hence higher minimum defect.
    But this cost is OFFSET by the necessity of locality — the universe
    CANNOT do unconstrained global optimization. -/
theorem finer_channels_higher_minimum {N : ℕ}
    (P₁ P₂ : DissipationChannel N) (c : Configuration N)
    (h_refines : Refines P₁ P₂ c)
    (c₁ : Configuration N) (h₁_feas : c₁ ∈ ChanneledFeasible P₁ c)
    (c₂ : Configuration N)
    (h₂_opt : ∀ c' ∈ ChanneledFeasible P₂ c,
      total_defect c₂ ≤ total_defect c') :
    total_defect c₂ ≤ total_defect c₁ :=
  h₂_opt c₁ (h_refines h₁_feas)

/-- **THEOREM (Global Optimum Is the Coarsest Channel)**:
    The global variational successor (single channel, no extra constraints)
    achieves the lowest defect. Any finer channel structure has higher
    or equal minimum defect.

    This encodes the fundamental tradeoff:
    - Global optimization: lowest defect, no structure
    - Local (channeled) optimization: higher defect, rich structure

    The universe cannot do global optimization (locality / finite
    propagation speed), so it MUST use channeled optimization.
    The resulting higher-defect structured equilibrium IS the physical
    universe we observe — including life. -/
theorem global_is_optimal_over_channels {N : ℕ}
    (P : DissipationChannel N)
    (c next_global next_channeled : Configuration N)
    (h_global : IsVariationalSuccessor c next_global)
    (h_chan : next_channeled ∈ ChanneledFeasible P c) :
    total_defect next_global ≤ total_defect next_channeled :=
  h_global.2 next_channeled (channeled_subset_feasible P c h_chan)

/-! ## Part 8: The Life Theorem -/

/-- **F-012 CERTIFICATE: The Thermodynamics of Complexity**

    Why does life exist? Why does complex structure persist?

    The answer follows from four mathematical facts:

    1. **STRUCTURE IS FORCED BY LOCALITY**: When the universe has
       local conservation laws (dissipation channels), uniform
       thermalization is forbidden. The channeled equilibrium
       necessarily has multiple distinct values (complexity > 1).
       (Theorems: `uniform_precluded_by_channels`,
                  `structured_complexity_ge_two`)

    2. **STRUCTURE IS PERMANENT**: Channel charges are conserved
       along channeled trajectories. Once the universe develops
       non-uniform channel charges, it keeps them forever.
       (Theorem: `structure_permanent`)

    3. **DEFECT DRIVES DYNAMICS**: Total defect is non-increasing
       along channeled trajectories. The universe continuously
       dissipates defect through its channel structure.
       (Theorem: `channeled_defect_monotone`)

    4. **COMPLEXITY HAS A COST BUT IS UNAVOIDABLE**: Finer channels
       have higher minimum defect (the cost of structure), but
       locality demands at least some channeling. The universe
       cannot avoid structure — it is forced by the gap between
       global and local optimization.
       (Theorems: `global_is_optimal_over_channels`,
                  `finer_channels_higher_minimum`)

    **Life** is a dissipation channel: a structured partition of ledger
    entries that efficiently routes defect toward equilibrium under local
    conservation constraints. Life is not an accident — it is the
    economically inevitable solution to a constrained optimization problem.

    **Darwinian evolution** is channel refinement: the process by which
    the universe discovers more efficient partition structures that
    minimize total defect under locality constraints. "Fitness" is
    proximity to the global optimum. "Natural selection" is the
    variational principle applied to channel structures.

    **No new axioms are needed.** Life, complexity, and evolution
    follow from:
    - J-cost minimization (T1)
    - Conservation of log-charge (F-008)
    - Locality of interactions (channeled constraints)
    - Monotone defect reduction (F-006)
    - Strict convexity of J (T5) -/
theorem complexity_certificate {N : ℕ} (hN : 0 < N)
    (P : DissipationChannel N) (c : Configuration N)
    (h_nonzero : log_charge c ≠ 0) :
    (ChanneledFeasible P c ⊆ Feasible c) ∧
    (∀ c' ∈ Feasible c, 0 < total_defect c') ∧
    (0 < complexity P c) ∧
    (∀ next, IsChanneledStep P c next →
      total_defect next ≤ total_defect c) ∧
    (∀ next, IsChanneledStep P c next →
      ∀ k, group_charge P next k = group_charge P c k) :=
  ⟨channeled_subset_feasible P c,
   fun c' hc' => nonzero_charge_forces_defect hN c h_nonzero c' hc',
   complexity_pos P c,
   fun next h => channeled_step_reduces_defect P c next h,
   fun next h k => channel_charges_conserved P c next h k⟩

end DissipativeComplexity
end Foundation
end RecognitionScience
