/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.TransAffine
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
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
* `SmoothAlmostComplexStructure.exists_forall_norm_iteratedFDeriv_chartPushforward_transAffine_le`:
  for a compact set `K` in the source of `φ` and maps `A x` bounded with their inverses on `K`,
  one radius and, for each order, one bound for the charts `φ.transAffine (φ x) (A x)`, `x ∈ K`.

The formula is the change of chart rule
`TauCeti.SmoothAlmostComplexStructure.chartPushforward_symm_trans_comp_fderiv`, for the transition
map from `φ` to `φ.transAffine p A`. The bound is
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
  have h := J.chartPushforward_symm_trans_comp_fderiv φ ψ (hΘdef ▸ hw)
  rw [hΘdef, hΘd.fderiv, hΘz] at h
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

/-- **Uniform bounds for a bounded family of recentred charts.** Let `K` be a compact subset of
the source of `φ`, in a boundaryless manifold, and `A x : G ≃L[ℝ] G`, for `x : M`, maps such that
`‖A x‖` and `‖(A x)⁻¹‖` are at most `C` for `x ∈ K`. Then there is a radius `ρ > 0` such that the
ball of radius `ρ` about `0` lies in the target of `φ.transAffine (φ x) (A x)` for every `x ∈ K`,
and for every `r` one constant bounds the iterated derivatives of order `r` of `J` read in all
these charts on that ball. -/
theorem exists_forall_norm_iteratedFDeriv_chartPushforward_transAffine_le [I.Boundaryless]
    [ProperSpace G] {K : Set M} (hK : IsCompact K) (hKφ : K ⊆ φ.source) (A : M → G ≃L[ℝ] G)
    {C : ℝ} (hA : ∀ x ∈ K, ‖(A x : G →L[ℝ] G)‖ ≤ C ∧ ‖((A x).symm : G →L[ℝ] G)‖ ≤ C) :
    ∃ ρ > 0, (∀ x ∈ K, Metric.ball 0 ρ ⊆ (φ.transAffine (φ x) (A x)).target) ∧
      ∀ r : ℕ, ∃ B, ∀ x ∈ K, ∀ z ∈ Metric.ball (0 : G) ρ,
        ‖iteratedFDeriv ℝ r (J.chartPushforward (φ.transAffine (φ x) (A x)).toOpenPartialHomeomorph)
          z‖ ≤ B := by
  -- The compact set `φ '' K` and a closed thickening of it inside the target of `φ`.
  have hLc : IsCompact (φ '' K) := hK.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hKφ)
  have hLt : φ '' K ⊆ φ.target := Set.image_subset_iff.2 fun x hx ↦ φ.map_source (hKφ hx)
  obtain ⟨δ, hδ, hδt⟩ := hLc.exists_cthickening_subset_open φ.open_target hLt
  set C₀ := max C 1
  have hC₀ : 0 < C₀ := lt_max_of_lt_right one_pos
  -- The points `(A x)⁻¹ z + φ x`, for `z` in the ball, lie in the thickening.
  have hmem : ∀ x ∈ K, ∀ z ∈ Metric.ball (0 : G) (δ / C₀),
      (A x).symm z + φ x ∈ Metric.cthickening δ (φ '' K) := fun x hx z hz ↦ by
    refine Metric.closedBall_subset_cthickening (Set.mem_image_of_mem φ hx) δ ?_
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right]
    rw [mem_ball_zero_iff] at hz
    calc ‖(A x).symm z‖ ≤ ‖((A x).symm : G →L[ℝ] G)‖ * ‖z‖ :=
          ((A x).symm : G →L[ℝ] G).le_opNorm z
      _ ≤ C₀ * (δ / C₀) := by
          gcongr
          exact (hA x hx).2.trans (le_max_left _ _)
      _ = δ := mul_div_cancel₀ δ hC₀.ne'
  have hball : ∀ x ∈ K, Metric.ball 0 (δ / C₀) ⊆ (φ.transAffine (φ x) (A x)).target :=
    fun x hx z hz ↦ (φ.mem_transAffine_target_iff _ _).2 (hδt (hmem x hx z hz))
  refine ⟨δ / C₀, div_pos hδ hC₀, hball, fun r ↦ ?_⟩
  -- The derivatives of `J` read in `φ` are bounded on the compact thickening.
  have hcont := ContinuousOn.continuousOn_iteratedFDeriv
    (J.contDiffOn_chartPushforward_toOpenPartialHomeomorph φ) φ.open_target (k := r)
      (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := hLc.cthickening.exists_bound_of_continuousOn (hcont.mono hδt)
  refine ⟨C₀ * C₀ ^ (r + 1) * max B 0, fun x hx z hz ↦ ?_⟩
  refine (J.norm_iteratedFDeriv_chartPushforward_transAffine_le φ _ _ r (hball x hx hz)).trans ?_
  gcongr
  · exact (hA x hx).1.trans (le_max_left _ _)
  · exact (hA x hx).2.trans (le_max_left _ _)
  · exact (hB _ (hmem x hx z hz)).trans (le_max_left _ _)

end SmoothAlmostComplexStructure

end TauCeti

end
