/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Continuity of precomposing bilinear forms

For fixed continuous linear maps `f` and `f'`, the map `g ↦ g.bilinearComp f f'`, which sends a
continuous bilinear form `g` to `(x, y) ↦ g (f x) (f' y)`, is continuous for the operator norm.
This is what makes the push-forward of inner products and of symplectic forms along a continuous
linear equivalence continuous.

## Main results

* `ContinuousLinearMap.continuous_bilinearComp`: `g ↦ g.bilinearComp f f'` is continuous.
-/

public section

namespace ContinuousLinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Precomposing a continuous bilinear form with fixed continuous linear maps in both arguments is
continuous in the form, for the operator norm. -/
theorem continuous_bilinearComp (f : F →L[ℝ] E) (f' : G →L[ℝ] E) :
    Continuous fun g : E →L[ℝ] E →L[ℝ] ℝ ↦ g.bilinearComp f f' := by
  have : (fun g : E →L[ℝ] E →L[ℝ] ℝ ↦ g.bilinearComp f f') =
      fun g ↦ (compL ℝ G E ℝ).flip f' ∘L (g ∘L f) := by
    ext
    rfl
  rw [this]
  exact (continuous_id.clm_comp_const f).const_clm_comp _

end ContinuousLinearMap

end
