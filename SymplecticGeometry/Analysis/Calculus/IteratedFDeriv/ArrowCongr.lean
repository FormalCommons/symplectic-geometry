/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import SymplecticGeometry.Analysis.Normed.Operator.ArrowCongr
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv

/-!
# Iterated derivatives of a conjugated map precomposed with an affine map

Let `e₁ : E ≃L[𝕜] F` and `e₂ : E' ≃L[𝕜] F'` be continuous linear equivalences, `p : E`, and
`f : E → E →L[𝕜] E'` any map. The map `z ↦ e₂ ∘ f (e₁⁻¹ z + p) ∘ e₁⁻¹` is `f` followed by the
continuous linear equivalence `e₁.arrowCongr e₂` and preceded by the affine map
`z ↦ e₁⁻¹ z + p`. So its iterated derivatives of order `r` are those of `f`, at most
multiplied by `‖e₂‖ * ‖e₁⁻¹‖ ^ (r + 1)`, with no smoothness of `f` needed.
The bound for the inner change of variables is Tau Ceti's
`ContinuousLinearEquiv.norm_iteratedFDeriv_comp_right_le`.

## Main results

* `ContinuousLinearEquiv.norm_iteratedFDeriv_arrowCongr_comp_le`: that bound.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 E F E' F' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- For any map `f : E → E →L[𝕜] E'`, the iterated derivative of order `r` of
`z ↦ e₂ ∘ f (e₁⁻¹ z + p) ∘ e₁⁻¹` at `z` has norm at most `‖e₂‖ * ‖e₁⁻¹‖ ^ (r + 1)` times that
of `f` at `e₁⁻¹ z + p`. -/
theorem norm_iteratedFDeriv_arrowCongr_comp_le (e₁ : E ≃L[𝕜] F) (e₂ : E' ≃L[𝕜] F')
    (f : E → E →L[𝕜] E') (p : E) (r : ℕ) (z : F) :
    ‖iteratedFDeriv 𝕜 r (fun z ↦ e₁.arrowCongr e₂ (f (e₁.symm z + p))) z‖ ≤
      ‖(e₂ : E' →L[𝕜] F')‖ * ‖(e₁.symm : F →L[𝕜] E)‖ ^ (r + 1) *
        ‖iteratedFDeriv 𝕜 r f (e₁.symm z + p)‖ := by
  rw [← Function.comp_def (⇑(e₁.arrowCongr e₂)), (e₁.arrowCongr e₂).iteratedFDeriv_comp_left]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  have h := e₁.symm.norm_iteratedFDeriv_comp_right_le (fun w ↦ f (w + p)) z r
  rw [iteratedFDeriv_comp_add_right] at h
  calc _ ≤ ‖(e₂ : E' →L[𝕜] F')‖ * ‖(e₁.symm : F →L[𝕜] E)‖ *
        (‖(e₁.symm : F →L[𝕜] E)‖ ^ r * ‖iteratedFDeriv 𝕜 r f (e₁.symm z + p)‖) := by
          gcongr
          · exact norm_arrowCongr_le e₁ e₂
          · exact h
    _ = _ := by ring

end ContinuousLinearEquiv

end
