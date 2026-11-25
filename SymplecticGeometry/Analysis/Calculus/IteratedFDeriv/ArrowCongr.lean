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

/-!
# Iterated derivatives of a conjugated map precomposed with an affine map

Let `e₁ : E ≃L[𝕜] F` and `e₂ : E' ≃L[𝕜] F'` be continuous linear equivalences, `p : E`, and
`f : E → E →L[𝕜] E'` any map. The map `z ↦ e₂ ∘ f (e₁⁻¹ z + p) ∘ e₁⁻¹` is `f` followed by the
continuous linear equivalence `e₁.arrowCongr e₂` and preceded by the affine map
`z ↦ e₁⁻¹ z + p`. So its iterated derivatives of order `r` are those of `f`, at most
multiplied by `‖e₂‖ * ‖e₁⁻¹‖ ^ (r + 1)`, with no smoothness of `f` needed.

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
  have hleft := (e₁.arrowCongr e₂).iteratedFDeriv_comp_left (f := fun z ↦ f (e₁.symm z + p))
    (x := z) (i := r)
  have hright : iteratedFDeriv 𝕜 r ((fun w ↦ f (w + p)) ∘ e₁.symm) z =
      (iteratedFDeriv 𝕜 r (fun w ↦ f (w + p)) (e₁.symm z)).compContinuousLinearMap
        fun _ ↦ (e₁.symm : F →L[𝕜] E) := by
    simpa [iteratedFDerivWithin_univ] using
      e₁.symm.iteratedFDerivWithin_comp_right (fun w ↦ f (w + p)) uniqueDiffOn_univ
        (Set.mem_univ (e₁.symm z)) r
  rw [← Function.comp_def (⇑(e₁.arrowCongr e₂)), hleft]
  refine ((ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (mul_le_mul (norm_arrowCongr_le e₁ e₂) le_rfl (norm_nonneg _) (by positivity))).trans ?_
  rw [show (fun z ↦ f (e₁.symm z + p)) = (fun w ↦ f (w + p)) ∘ e₁.symm from
    (Function.comp_def _ _).symm, hright]
  have hc := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv 𝕜 r (fun w ↦ f (w + p)) (e₁.symm z)) fun _ ↦ (e₁.symm : F →L[𝕜] E)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  calc _ ≤ ‖(e₂ : E' →L[𝕜] F')‖ * ‖(e₁.symm : F →L[𝕜] E)‖ *
        (‖iteratedFDeriv 𝕜 r (fun w ↦ f (w + p)) (e₁.symm z)‖ *
          ‖(e₁.symm : F →L[𝕜] E)‖ ^ r) := by
          gcongr
    _ = _ := by rw [iteratedFDeriv_comp_add_right]; ring

end ContinuousLinearEquiv

end
