/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.CovariantDerivative

/-!
# Covariant derivatives read in the charts of a finite bundle atlas

Let `A` be a finite bundle atlas of a real vector bundle `V → M` over a manifold modelled on a
real normed space `E`, and let `cov` be a covariant derivative on `V`. Read in chart `i`, through
the preferred trivializations of the tangent bundle and of `V` at the centre of the chart
(`TauCeti.FiniteBundleAtlas.coord_tangentHom`), it is

`(cov s)ᵢ = d sᵢ + Γᵢ sᵢ`,

where `sᵢ = A.coord i s` is the reading of the section and `Γᵢ = A.chartZeroOrder cov i` is Tau
Ceti's zeroth-order term of chart `i`, the reading of `cov` on the frame of chart `i`.

## Main results

* `IsCovariantDerivativeOn.coord_tangentHom_eq_fderiv_add_chartZeroOrder`: the chart formula.
* `IsCovariantDerivativeOn.chartZeroOrder_apply_eq_coord_tangentHom`: on the image of chart `i`,
  `Γᵢ v` is the reading of `cov` on the section that reads as the constant `v` in the
  trivialization of chart `i`.
* `IsCovariantDerivativeOn.fderiv_coordChangeL_add_chartZeroOrder`: on the overlap of two charts,
  `d (g v) + Γᵢ' (g v) = g ∘ Γᵢ v ∘ dτ`, for `g` the coordinate change of `V` and `τ` the chart
  transition.
* `IsCovariantDerivativeOn.contDiffOn_chartZeroOrder`,
  `IsCovariantDerivativeOn.exists_norm_chartZeroOrder_apply_le`: the zeroth-order term of a `C^n`
  covariant derivative is `C^n`, and bounded on the closure of the chart image.

These adapt the proofs of Tau Ceti's
`TauCeti.FiniteBundleAtlas.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder`,
`TauCeti.FiniteBundleAtlas.chartZeroOrder_apply_eq_coord_tangentHom`,
`TauCeti.FiniteBundleAtlas.complexAntilinearPartL_fderiv_coordChangeL_add_chartZeroOrder`,
`TauCeti.FiniteBundleAtlas.contDiffOn_chartZeroOrder` and
`TauCeti.FiniteBundleAtlas.exists_norm_chartZeroOrder_apply_le`
(`TauCeti/Geometry/Manifold/VectorBundle/CauchyRiemann/Chart.lean`), stated there for real
Cauchy–Riemann operators on a complex manifold, to covariant derivatives on any real manifold,
with the whole derivative in place of its complex antilinear part. The chart formula follows from
the local frame formula `TauCeti.Manifold.covariantDerivative_eq_frameCovariantDerivative_add_sum`
in place of its Cauchy–Riemann version.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open Bundle Module Set TauCeti
open scoped Manifold ContDiff Topology

universe u

namespace IsCovariantDerivativeOn

section Real

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V)
  {cov : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x}

/-- **The chart formula.** In chart `i`, a covariant derivative on the base set of the
trivialization of chart `i` reads as the derivative of the reading of the section plus the
zeroth-order term `chartZeroOrder` applied to that reading. -/
theorem coord_tangentHom_eq_fderiv_add_chartZeroOrder {i : Fin A.n}
    (hcov : IsCovariantDerivativeOn F cov (A.triv i).baseSet) {z : E} (hz : z ∈ A.image i)
    {s : Π x, V x} (hs : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F))
      (fun x ↦ TotalSpace.mk' F x (s x)) ((A.chart i).symm z)) :
    A.tangentHom.coord i (cov s) z =
      fderiv ℝ (A.coord i s) z + A.chartZeroOrder cov i z (A.coord i s z) := by
  have hx : (A.chart i).symm z ∈ (A.triv i).baseSet :=
    A.dom_subset_baseSet i (A.symm_mem_dom hz)
  rw [FiniteBundleAtlas.coord_tangentHom,
    Manifold.covariantDerivative_eq_frameCovariantDerivative_add_sum (finBasis ℝ F) hcov hx hs,
    ← A.inCoordinates_frameCovariantDerivative (finBasis ℝ F) i hz hs]
  ext v
  simp only [ContinuousLinearMap.inCoordinates, FiniteBundleAtlas.chartZeroOrder_apply,
    FiniteBundleAtlas.coord_tangentHom, ContinuousLinearMap.comp_apply,
    add_apply, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, map_add, map_sum, map_smul, add_right_inj]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [(A.triv i).localFrameCoeff_eq_coeff hx, Basis.coord_apply, FiniteBundleAtlas.coord_def]

/-- On the image of chart `i`, the zeroth-order term of chart `i` of a covariant derivative,
applied to `v`, is the reading of the covariant derivative of the section that reads as the
constant `v` in the trivialization of chart `i`. In particular it does not depend on the basis of
`F` used to define it. -/
theorem chartZeroOrder_apply_eq_coord_tangentHom {i : Fin A.n}
    (hcov : IsCovariantDerivativeOn F cov (A.triv i).baseSet) {z : E} (hz : z ∈ A.image i)
    (v : F) :
    A.chartZeroOrder cov i z v = A.tangentHom.coord i (cov fun x ↦ (A.triv i).symm x v) z := by
  have hc : A.coord i (fun x ↦ (A.triv i).symm x v) =ᶠ[𝓝 z] fun _ ↦ v := by
    filter_upwards [(A.image i).isOpen.mem_nhds hz] with y hy using A.coord_triv_symm v hy
  rw [hcov.coord_tangentHom_eq_fderiv_add_chartZeroOrder A hz
    (Manifold.mdifferentiableAt_symm_of_mem_baseSet v
      (A.dom_subset_baseSet i (A.symm_mem_dom hz))),
    hc.fderiv_eq, fderiv_const_apply, zero_add, A.coord_triv_symm v hz]

/-- **Change of chart.** On the overlap of charts `i` and `i'`, let `g` be the coordinate change of
`V` from the trivialization of chart `i` to that of chart `i'`, read in chart `i'`, and let `τ` be
the chart transition. For a covariant derivative on both base sets, the zeroth-order terms of the
two charts are related by `d (g v) + Γᵢ' (g v) = g ∘ Γᵢ v ∘ dτ`. -/
theorem fderiv_coordChangeL_add_chartZeroOrder {i i' : Fin A.n}
    (hcov : IsCovariantDerivativeOn F cov (A.triv i).baseSet)
    (hcov' : IsCovariantDerivativeOn F cov (A.triv i').baseSet) {z : E}
    (hz : z ∈ A.overlap i i') (v : F) :
    fderiv ℝ (fun y ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) v) z +
      A.chartZeroOrder cov i' z ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) v) =
    ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) : F →L[ℝ] F).comp
      ((A.chartZeroOrder cov i (A.transition i i' z) v).comp
        (fderiv ℝ (A.transition i i') z)) := by
  have hz' : z ∈ A.image i' := A.overlap_subset_image i i' hz
  have hτ : A.transition i i' z ∈ A.image i :=
    A.overlap_subset_image i' i (A.transition_mem_overlap hz)
  have hx : (A.chart i').symm z ∈ (A.triv i).baseSet := by
    obtain ⟨x, hx, rfl⟩ := A.mem_overlap.1 hz
    rw [(A.chart i').left_inv (A.dom_subset_chart_source i' hx.2)]
    exact A.dom_subset_baseSet i hx.1
  have hc : A.coord i' (fun x ↦ (A.triv i).symm x v) =ᶠ[𝓝 z]
      fun y ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) v := by
    filter_upwards [(A.isOpen_overlap i i').mem_nhds hz] with y hy
    rw [A.coord_eq_coordChange _ hy,
      A.coord_triv_symm v (A.overlap_subset_image i' i (A.transition_mem_overlap hy))]
  rw [← hc.fderiv_eq, ← hc.eq_of_nhds,
    ← hcov'.coord_tangentHom_eq_fderiv_add_chartZeroOrder A hz'
      (Manifold.mdifferentiableAt_symm_of_mem_baseSet v hx),
    A.coord_tangentHom_eq_coordChange _ hz, hcov.chartZeroOrder_apply_eq_coord_tangentHom A hτ]

end Real

section Smooth

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V)
  {cov : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x}
  {n : ℕ∞ω} [ENat.LEInfty n]

/-- **Smoothness of the zeroth-order term.** If a covariant derivative on an open set `u` is `C^n`
there, its zeroth-order term in chart `i` is `C^n` on the points of the chart target lying over
`u` and the base set of the trivialization of chart `i`. -/
theorem contDiffOn_chartZeroOrder {u : Set M} (hcov : IsCovariantDerivativeOn F cov u)
    (hcovs : ContMDiffCovariantDerivativeOn F n cov u) (hu : IsOpen u) (i : Fin A.n) :
    ContDiffOn ℝ n (A.chartZeroOrder cov i)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' ((A.triv i).baseSet ∩ u)) := by
  lift n to ℕ∞ using ENat.LEInfty.ne_top n
  set a : Set M := (A.chart i).source ∩ ((A.triv i).baseSet ∩ u)
  have ha : IsOpen a := (A.chart i).open_source.inter ((A.triv i).open_baseSet.inter hu)
  have hau : a ⊆ u := fun x hx ↦ hx.2.2
  have hcova : ContMDiffCovariantDerivativeOn F n cov a :=
    hcovs.mono_of_isOpen (hcov.mono hau) ha hau
  -- `chartZeroOrder` is a sum over the basis of `F`, whose body this file does not see.
  have hsum : A.chartZeroOrder cov i = fun z ↦
      ∑ k, (LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord k)).smulRight
        (A.tangentHom.coord i (cov ((A.triv i).localFrame (finBasis ℝ F) k)) z) := by
    ext z v
    simp [FiniteBundleAtlas.chartZeroOrder_apply]
  -- Each frame section is smooth over the base set, so `cov` sends it to a `C^n` one-form on `a`,
  -- whose reading in chart `i` is `C^n`.
  rw [hsum]
  refine ContDiffOn.sum fun k _ ↦ contDiffOn_const.smulRight ?_
  have hframe := (((A.triv i).contMDiffOn_localFrame_baseSet (I := 𝓘(ℝ, E)) ∞
    (finBasis ℝ F) k).of_le
      (show (n : ℕ∞ω) + 1 ≤ ∞ from mod_cast (le_top : n + 1 ≤ ⊤))).mono
      (show a ⊆ (A.triv i).baseSet from fun x hx ↦ hx.2.1)
  have hω := ((A.tangentHom.triv i).contMDiffOn_section_iff ha ?_).1 (hcova.contMDiff hframe)
  · exact ((hω.contDiffOn_comp_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas _)).congr fun y _ ↦ (A.tangentHom.coord_def i _ y)).mono
        fun y hy ↦ ⟨hy.1, (A.chart i).map_target hy.1, hy.2⟩
  · intro x hx
    simp only [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet]
    exact ⟨hx.1, hx.2.1⟩

/-- **Boundedness of the zeroth-order term.** The zeroth-order term in chart `i` of a covariant
derivative on `M` which is `C^n` is bounded on the closure of the image of chart `i`. -/
theorem exists_norm_chartZeroOrder_apply_le (hcov : IsCovariantDerivativeOn F cov univ)
    (hcovs : ContMDiffCovariantDerivativeOn F n cov univ) (i : Fin A.n) :
    ∃ C, ∀ z ∈ closure (A.image i : Set E), ∀ v, ‖A.chartZeroOrder cov i z v‖ ≤ C * ‖v‖ := by
  have hc := (hcov.contDiffOn_chartZeroOrder A hcovs isOpen_univ i).continuousOn
  rw [inter_univ] at hc
  obtain ⟨C, hC⟩ := (A.isCompact_chart_image_closure_dom i).exists_bound_of_continuousOn
    (f := A.chartZeroOrder cov i) (hc.mono (A.chart_image_closure_dom_subset i))
  exact ⟨C, fun z hz v ↦ (A.chartZeroOrder cov i z).le_of_opNorm_le
    (hC z (A.closure_image_subset_chart_image_closure_dom i hz)) v⟩

end Smooth

end IsCovariantDerivativeOn

end
