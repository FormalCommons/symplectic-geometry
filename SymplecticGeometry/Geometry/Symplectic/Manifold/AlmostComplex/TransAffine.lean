/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.TransAffine
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.ArrowCongr
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

The formula is the change of chart rule of Tau Ceti,
`ContMDiffAlmostComplexStructure.chartPushforward_symm_trans_comp_fderiv`, for the transition map
from `φ` to `φ.transAffine p A`. The bound is
`ContinuousLinearEquiv.norm_iteratedFDeriv_arrowCongr_comp_le`, for `e₁ = e₂ = A`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 4.2.
-/

public section

open scoped Manifold ContDiff

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
  exact A.norm_iteratedFDeriv_arrowCongr_comp_le A _ p r z

end SmoothAlmostComplexStructure

end TauCeti

end
