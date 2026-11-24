/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Basic

/-!
# Degree transport in the right factor of a paired wedge

If the right factor `A` of a paired wedge `φ ∧ A` agrees with `c • B` once its arguments are
relabelled along `Fin.cast h`, then `φ ∧ A` is `c • (φ ∧ B)`, evaluated on the relabelled tuple.
This lets one rewrite a factor whose degree is only propositionally equal to the expected one.

The statement and its proof are the right-hand counterpart of Tau Ceti's
`ContinuousAlternatingMap.pairedWedge_apply_of_left_eq_smul_cast`, whose proof they follow step
by step.

## Main results

* `ContinuousAlternatingMap.pairedWedge_apply_of_right_eq_smul_cast`: degree transport in the
  right factor of a paired wedge.
-/

public section

namespace ContinuousAlternatingMap

variable {E F₁ F₂ F₃ : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
  [AddCommGroup F₃] [Module ℝ F₃] [TopologicalSpace F₃] [IsTopologicalAddGroup F₃]
  [ContinuousConstSMul ℝ F₃]

/-- Degree transport in the second factor of a paired wedge: if `A`, of degree `b`, agrees with
`c • B` after reindexing its arguments along `Fin.cast h : Fin a → Fin b`, then the wedge of `φ`
and `A` is `c •` the wedge of `φ` and `B`, evaluated on the correspondingly transported tuple. -/
theorem pairedWedge_apply_of_right_eq_smul_cast {a b k : ℕ}
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) (h : a = b)
    {A : E [⋀^Fin b]→L[ℝ] F₂} {B : E [⋀^Fin a]→L[ℝ] F₂} (c : ℝ)
    (hAB : ∀ w, A w = c • B (w ∘ Fin.cast h)) (φ : E [⋀^Fin k]→L[ℝ] F₁) (x : Fin (k + b) → E) :
    pairedWedge μ hμ φ A x = c • pairedWedge μ hμ φ B (x ∘ Fin.cast (by omega)) := by
  subst h
  simp only [pairedWedge_apply, hAB, map_smul, smul_comm _ c, Finset.smul_sum]
  -- After `subst`, the transport `Fin.cast` is the identity on values, so both tuples agree.
  rfl

end ContinuousAlternatingMap

end
