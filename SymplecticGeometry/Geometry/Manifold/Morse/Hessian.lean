/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Hessian

/-!
# Positive directions of the critical Hessian in charts

At a critical point `x` of a function `f` that is `C²` at `x`, Tau Ceti's critical Hessian
`TauCeti.criticalHessian I f x` is the Hessian of a coordinate expression of `f`, transported by
the chart derivative (`TauCeti.criticalHessian_apply_eq_of_mem_maximalAtlas`). Since the chart
derivative is invertible (`TauCeti.isInvertible_mvfderiv_extend`), the critical Hessian is positive
on some tangent vector exactly when the coordinate Hessian is positive on some vector, in any chart
of the `C²` maximal atlas (`TauCeti.exists_criticalHessian_pos_iff_of_mem_maximalAtlas`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2, for the Hessian at a critical point.
-/

public section

open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

/-- At a critical point `x` of a function `f` which is `C²` at `x`, on a boundaryless manifold,
the critical Hessian is positive on some tangent vector exactly when, in a chart `e` of the `C²`
maximal atlas whose source contains `x`, the Hessian of the coordinate expression of `f` at the
image of `x` is positive on some vector. -/
theorem exists_criticalHessian_pos_iff_of_mem_maximalAtlas {f : M → ℝ} {x : M}
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 2 M) (hx : x ∈ e.source)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : x ∈ criticalPoints I f) :
    (∃ v, 0 < criticalHessian I f x v v) ↔
      ∃ w : E, 0 < fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm)) (e.extend I x) w w := by
  obtain ⟨D, hD⟩ :=
    isInvertible_mvfderiv_extend (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hx
  simp only [criticalHessian_apply_eq_of_mem_maximalAtlas he hx hf (mem_criticalPoints.mp hcrit)]
  refine ⟨fun ⟨v, hv⟩ ↦ ⟨_, hv⟩, fun ⟨w, hw⟩ ↦ ⟨D.symm w, ?_⟩⟩
  rwa [← hD, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

end TauCeti

end
