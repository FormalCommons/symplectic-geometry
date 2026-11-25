/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.TransAffine
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# An almost complex structure read in a chart followed by an affine map

Let `J` be a smooth almost complex structure on `M`, `φ` a smooth chart of `M` into a real normed
space `G`, `p : G` and `A : G ≃L[ℝ] G`. The chart `φ.transAffine p A` is `φ` followed by
`z ↦ A (z - p)`. Since that affine map has derivative `A` everywhere, `J` read in the new chart at
`z` is `A ∘ J_φ (A⁻¹ z + p) ∘ A⁻¹`, where `J_φ` is `J` read in `φ`. Hence the iterated derivatives
of order `r` of the new structure are bounded by `‖A‖ * ‖A⁻¹‖ ^ (r + 1)` times those of `J_φ`
at the corresponding point.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.chartPushforward_transAffine`: the structure read in
  `φ.transAffine p A`, as a conjugate of the structure read in `φ`.
* `TauCeti.SmoothAlmostComplexStructure.norm_iteratedFDeriv_chartPushforward_transAffine_le`: the
  bound on its iterated derivatives.
* `ContinuousLinearEquiv.norm_iteratedFDeriv_arrowCongr_comp_le`: the same bound for any map
  `f : G → (G →L[ℝ] G)` conjugated by `A` and precomposed with `z ↦ A⁻¹ z + p`, with
  `ContinuousLinearEquiv.norm_arrowCongr_le`, the norm of conjugation by continuous linear
  equivalences.

The formula is the change of chart rule of Tau Ceti,
`ContMDiffAlmostComplexStructure.chartPushforward_symm_trans_comp_fderiv`, for the transition map
from `φ` to `φ.transAffine p A`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 4.2.
-/

public section

open scoped Manifold ContDiff

namespace ContinuousLinearEquiv

/-- The map `X ↦ e₂ ∘ X ∘ e₁⁻¹` between spaces of continuous linear maps has operator norm at most
`‖e₂‖ * ‖e₁⁻¹‖`. -/
theorem norm_arrowCongr_le {𝕜 E F E' F' : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    (e₁ : E ≃L[𝕜] F) (e₂ : E' ≃L[𝕜] F') :
    ‖((e₁.arrowCongr e₂ : (E →L[𝕜] E') ≃L[𝕜] (F →L[𝕜] F')) : (E →L[𝕜] E') →L[𝕜] (F →L[𝕜] F'))‖ ≤
      ‖(e₂ : E' →L[𝕜] F')‖ * ‖(e₁.symm : F →L[𝕜] E)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun X ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
  rw [ContinuousLinearEquiv.coe_coe, arrowCongr_apply]
  calc ‖e₂ (X (e₁.symm w))‖ ≤ ‖(e₂ : E' →L[𝕜] F')‖ * (‖X‖ * (‖(e₁.symm : F →L[𝕜] E)‖ * ‖w‖)) :=
        (e₂ : E' →L[𝕜] F').le_opNorm_of_le
          (X.le_opNorm_of_le ((e₁.symm : F →L[𝕜] E).le_opNorm w))
    _ = ‖(e₂ : E' →L[𝕜] F')‖ * ‖(e₁.symm : F →L[𝕜] E)‖ * ‖X‖ * ‖w‖ := by ring

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- For any map `f` from `G` to its endomorphisms, the iterated derivatives of order `r` of
`z ↦ A ∘ f (A⁻¹ z + p) ∘ A⁻¹` at `z` have norm at most `‖A‖ * ‖A⁻¹‖ ^ (r + 1)` times those of `f`
at `A⁻¹ z + p`. -/
theorem norm_iteratedFDeriv_arrowCongr_comp_le (A : G ≃L[ℝ] G) (f : G → G →L[ℝ] G) (p : G)
    (r : ℕ) (z : G) :
    ‖iteratedFDeriv ℝ r (fun z ↦ A.arrowCongr A (f (A.symm z + p))) z‖ ≤
      ‖(A : G →L[ℝ] G)‖ * ‖(A.symm : G →L[ℝ] G)‖ ^ (r + 1) *
        ‖iteratedFDeriv ℝ r f (A.symm z + p)‖ := by
  have hleft := (A.arrowCongr A).iteratedFDeriv_comp_left (f := fun z ↦ f (A.symm z + p))
    (x := z) (i := r)
  have hright : iteratedFDeriv ℝ r ((fun w ↦ f (w + p)) ∘ A.symm) z =
      (iteratedFDeriv ℝ r (fun w ↦ f (w + p)) (A.symm z)).compContinuousLinearMap
        fun _ ↦ (A.symm : G →L[ℝ] G) := by
    simpa [iteratedFDerivWithin_univ] using
      A.symm.iteratedFDerivWithin_comp_right (fun w ↦ f (w + p)) uniqueDiffOn_univ
        (Set.mem_univ (A.symm z)) r
  rw [show (fun z ↦ A.arrowCongr A (f (A.symm z + p))) =
      ⇑(A.arrowCongr A) ∘ fun z ↦ f (A.symm z + p) from rfl, hleft]
  refine ((ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (mul_le_mul (norm_arrowCongr_le A A) le_rfl (norm_nonneg _) (by positivity))).trans ?_
  rw [show (fun z ↦ f (A.symm z + p)) = (fun w ↦ f (w + p)) ∘ A.symm from rfl, hright]
  have hc := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ r (fun w ↦ f (w + p)) (A.symm z)) fun _ ↦ (A.symm : G →L[ℝ] G)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  calc _ ≤ ‖(A : G →L[ℝ] G)‖ * ‖(A.symm : G →L[ℝ] G)‖ *
        (‖iteratedFDeriv ℝ r (fun w ↦ f (w + p)) (A.symm z)‖ * ‖(A.symm : G →L[ℝ] G)‖ ^ r) := by
          gcongr
    _ = _ := by rw [iteratedFDeriv_comp_add_right]; ring

end ContinuousLinearEquiv

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H M G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup G] [NormedSpace ℝ G] (J : SmoothAlmostComplexStructure I M)
  (φ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) (p : G) (A : G ≃L[ℝ] G)

/-- At a point `z` of the target of `φ.transAffine p A`, the structure `J` read in that chart is
`A ∘ J_φ (A⁻¹ z + p) ∘ A⁻¹`, where `J_φ` is `J` read in `φ`. -/
theorem chartPushforward_transAffine {z : G} (hz : z ∈ (φ.transAffine p A).target) :
    J.chartPushforward (φ.transAffine p A).toOpenPartialHomeomorph z =
      (A : G →L[ℝ] G).comp
        ((J.chartPushforward φ.toOpenPartialHomeomorph (A.symm z + p)).comp
          (A.symm : G →L[ℝ] G)) := by
  set ψ := φ.transAffine p A
  set u := A.symm z + p
  have hu : u ∈ φ.target := (φ.mem_transAffine_target_iff p A).1 hz
  -- The transition map `Θ` from `φ` to `ψ` is the affine map `w ↦ A (w - p)` near `u`.
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ, φ.toOpenPartialHomeomorph.symm.trans ψ.toOpenPartialHomeomorph = Θ :=
    ⟨_, rfl⟩
  have hΘ : ∀ w ∈ φ.target, Θ w = A (w - p) := fun w hw ↦ by
    simp [← hΘdef, ψ, φ.right_inv hw]
  have hΘz : Θ u = z := by simp [hΘ u hu, u]
  have hev : (⇑Θ) =ᶠ[nhds u] fun w ↦ A (w - p) :=
    Filter.eventually_of_mem (φ.open_target.mem_nhds hu) hΘ
  have hAff : HasFDerivAt (fun w ↦ A (w - p)) (A : G →L[ℝ] G) u :=
    (A : G →L[ℝ] G).hasFDerivAt.comp u ((hasFDerivAt_id u).sub_const p)
  have hΘd : HasFDerivAt Θ (A : G →L[ℝ] G) u := hAff.congr_of_eventuallyEq hev
  have hw : u ∈ Θ.source := by
    simp only [← hΘdef, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      PartialDiffeomorph.toOpenPartialHomeomorph_target, Set.mem_inter_iff, Set.mem_preimage,
      PartialDiffeomorph.coe_toOpenPartialHomeomorph_symm,
      PartialDiffeomorph.toOpenPartialHomeomorph_source, ψ, PartialDiffeomorph.transAffine_source]
    exact ⟨hu, φ.map_target hu⟩
  have h := (J.toContMDiff ⊤).chartPushforward_symm_trans_comp_fderiv (hΘdef ▸ hw)
    (φ.mdifferentiableAt (by simp) (φ.map_target hu))
    (by
      rw [hΘdef, hΘz, PartialDiffeomorph.coe_toOpenPartialHomeomorph_symm]
      exact ψ.symm.mdifferentiableAt (by simp) hz)
    (hΘdef ▸ hΘd.differentiableAt)
  rw [hΘdef, toContMDiff_chartPushforward, toContMDiff_chartPushforward, hΘd.fderiv, hΘz] at h
  ext w
  have hw' := DFunLike.congr_fun h (A.symm w)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] at hw'
  rw [hw', ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe]

/-- For every `r` and every point `z` of the target of `φ.transAffine p A`, the iterated
derivative of order `r` of `J` read in that chart has norm at most `‖A‖ * ‖A⁻¹‖ ^ (r + 1)` times
that of `J` read in `φ`, at `A⁻¹ z + p`. -/
theorem norm_iteratedFDeriv_chartPushforward_transAffine_le (r : ℕ) {z : G}
    (hz : z ∈ (φ.transAffine p A).target) :
    ‖iteratedFDeriv ℝ r (J.chartPushforward (φ.transAffine p A).toOpenPartialHomeomorph) z‖ ≤
      ‖(A : G →L[ℝ] G)‖ * ‖(A.symm : G →L[ℝ] G)‖ ^ (r + 1) *
        ‖iteratedFDeriv ℝ r (J.chartPushforward φ.toOpenPartialHomeomorph) (A.symm z + p)‖ := by
  have hev : J.chartPushforward (φ.transAffine p A).toOpenPartialHomeomorph =ᶠ[nhds z]
      fun z ↦ A.arrowCongr A (J.chartPushforward φ.toOpenPartialHomeomorph (A.symm z + p)) :=
    Filter.eventually_of_mem ((φ.transAffine p A).open_target.mem_nhds hz)
      fun _ hz' ↦ (J.chartPushforward_transAffine φ p A hz').trans (by ext; simp)
  rw [(hev.iteratedFDeriv ℝ r).eq_of_nhds]
  exact A.norm_iteratedFDeriv_arrowCongr_comp_le _ p r z

end SmoothAlmostComplexStructure

end TauCeti

end
