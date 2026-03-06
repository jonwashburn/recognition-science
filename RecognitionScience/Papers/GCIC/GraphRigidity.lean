import Mathlib
import RecognitionScience.Cost

/-!
# Graph Rigidity for Ratio Energy (GCIC Paper, Result 1)

Machine-verified proof that on any finite connected graph,
the ratio energy C_G[x] = Σ J(x_v/x_w) vanishes if and only if
x is a constant positive field.

## Main results

* `eq_of_reflTransGen` — if a function agrees on related pairs, it agrees
  on the reflexive-transitive closure.
* `ratio_rigidity` — zero ratio energy on a connected graph forces constancy.
* `ratio_rigidity_iff` — full iff characterization (Result 1 of the GCIC paper).

## Reference

Thapa–Washburn, "Rigidity and Compact Phase Emergence in Scale-Invariant
Ratio-Based Energies" (2026), Result 1.
-/

namespace RecognitionScience.Papers.GCIC.GraphRigidity

open RecognitionScience.Cost

variable {V : Type*}

/-! ### Propagation along the reflexive-transitive closure -/

/-- If a real-valued function agrees on all R-related pairs,
    it agrees on the reflexive-transitive closure of R.
    This is the graph-theoretic core: local agreement propagates globally. -/
theorem eq_of_reflTransGen {R : V → V → Prop} {f : V → ℝ}
    (hadj : ∀ a b, R a b → f a = f b) {u v : V}
    (huv : Relation.ReflTransGen R u v) : f u = f v := by
  induction huv with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (hadj _ _ hbc)

/-- On a preconnected graph (every pair related by ReflTransGen),
    agreement on edges implies global constancy. -/
theorem constant_of_preconnected {R : V → V → Prop}
    (hconn : ∀ u v : V, Relation.ReflTransGen R u v) {f : V → ℝ}
    (hadj : ∀ a b, R a b → f a = f b) :
    ∀ v w : V, f v = f w := by
  intro v w
  exact eq_of_reflTransGen hadj (hconn v w)

/-! ### Ratio rigidity (Result 1) -/

/-- Edge cost is nonneg for positive fields. -/
theorem edge_cost_nonneg {x : V → ℝ} {v w : V}
    (hv : 0 < x v) (hw : 0 < x w) :
    0 ≤ Jcost (x v / x w) :=
  Jcost_nonneg (div_pos hv hw)

/-- **RESULT 1 — Forward direction (Finite-Volume Rigidity).**

On a connected graph, if the ratio cost J(x_v/x_w) vanishes on every edge,
then the positive field x is constant.

Proof sketch:
1. J(x_v/x_w) = 0 implies x_v/x_w = 1, i.e. x_v = x_w (unique zero of J).
2. Connectivity propagates edge-wise agreement to all vertex pairs. -/
theorem ratio_rigidity {adj : V → V → Prop}
    (hconn : ∀ u v : V, Relation.ReflTransGen adj u v)
    {x : V → ℝ} (hpos : ∀ v, 0 < x v)
    (hzero : ∀ v w, adj v w → Jcost (x v / x w) = 0) :
    ∀ v w : V, x v = x w := by
  apply constant_of_preconnected hconn
  intro v w hvw
  have hdiv_pos : 0 < x v / x w := div_pos (hpos v) (hpos w)
  have h1 : x v / x w = 1 := Jcost_zero_iff_one hdiv_pos (hzero v w hvw)
  rwa [div_eq_iff (ne_of_gt (hpos w)), one_mul] at h1

/-- **Converse:** constant positive fields have zero ratio cost on every edge. -/
theorem constant_implies_zero_cost {x : V → ℝ} {v w : V}
    (h : x v = x w) (hw : 0 < x w) :
    Jcost (x v / x w) = 0 := by
  rw [h, div_self (ne_of_gt hw)]
  exact Jcost_unit0

/-- **RESULT 1 — Full characterization (iff).**

On a connected graph with a positive field x : V → ℝ_{>0}:

  (∀ edges, J(x_v/x_w) = 0)  ↔  x is constant.

This is the machine-verified version of Result 1. -/
theorem ratio_rigidity_iff {adj : V → V → Prop}
    (hconn : ∀ u v : V, Relation.ReflTransGen adj u v)
    {x : V → ℝ} (hpos : ∀ v, 0 < x v) :
    (∀ v w, adj v w → Jcost (x v / x w) = 0) ↔
    (∀ v w : V, x v = x w) :=
  ⟨ratio_rigidity hconn hpos,
   fun hconst v w _ => constant_implies_zero_cost (hconst v w) (hpos w)⟩

/-! ### Corollary: edge cost characterizations -/

/-- J(x_v/x_w) = 0 iff x_v = x_w, for positive x. -/
theorem edge_cost_zero_iff {x : V → ℝ} {v w : V}
    (hv : 0 < x v) (hw : 0 < x w) :
    Jcost (x v / x w) = 0 ↔ x v = x w := by
  constructor
  · intro h
    have h1 := Jcost_zero_iff_one (div_pos hv hw) h
    rwa [div_eq_iff (ne_of_gt hw), one_mul] at h1
  · intro h
    rw [h, div_self (ne_of_gt hw)]
    exact Jcost_unit0

end RecognitionScience.Papers.GCIC.GraphRigidity
