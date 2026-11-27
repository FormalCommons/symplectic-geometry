/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
public import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DeRham.Map
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Geometry.Manifold.Instances.Icc
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance

/-!
# Closed extensions of the fibre forms

Let `A` be a smooth atlas of a map `proj : M → B` with model fibre `F`, and let `σ` be a form on
`F`. A *closed extension* of the fibre forms is a closed form `τ` on `M` that restricts to `σ`
along `A` (`TauCeti.MapFiber.Atlas.RestrictsTo`). This file compares closed extensions with de Rham
classes on `M`: the class of a closed extension pulls back to the class of `σ` along every fibre
inclusion `j_{e,b} : v ↦ e⁻¹ (b, v)` of a chart `e` of `A`, and, conversely, a class with this
property is the class of a closed extension. Over a connected base it is enough to ask this of one
fibre inclusion. This is the cohomological condition of Thurston's construction of symplectic
forms on symplectic fibrations: step 1 of the proof, which needs neither compactness nor a form on
the base.

## Main results

* `TauCeti.MapFiber.Atlas.map_eq_of_restricts`: the map on de Rham cohomology induced by each fibre
  inclusion of the atlas sends the class of a closed extension of the fibre forms to the class of
  `σ`.
* `TauCeti.MapFiber.Atlas.forall_map_eq_of_map_eq`: for a smooth atlas whose coordinate changes
  preserve a closed form `σ`, over a preconnected base, a class that one fibre inclusion sends to
  the class of `σ` is sent there by every fibre inclusion of the atlas.
* `Bundle.Trivialization.eventually_map_fiberInclusionMap_eq`: the fibre inclusions of a smooth
  trivialization over nearby points of its base set induce the same map on cohomology, since they
  are homotopic along a segment in a chart of the base
  (`TauCeti.deRhamCohomology.map_eq_of_homotopy`).
* `Bundle.Trivialization.map_fiberInclusionMap_eq_of_mem_diffeomorphStabilizer`: the fibre
  inclusions of two charts over a point, whose coordinate change preserves `σ`, send a class to
  the class of `σ` together.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 (Theorem 6.1.4 and its proof).
* [W. P. Thurston, *Some simple examples of symplectic manifolds*][Thurston1976].
-/

public section

open Bundle Set Topology TauCeti
open scoped Manifold ContDiff

namespace Bundle.Trivialization

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF 2 F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM 2 M]
  {proj : M → B} {k : ℕ}

/-- **Fibre inclusions over nearby points.** Let `e` be a trivialization of `proj` with smooth
inverse, over a smooth base. For every `b'` close enough to a point `b` of the base set of `e`,
the fibre inclusions of `e` over `b` and over `b'` induce the same map on de Rham cohomology:
they are smoothly homotopic through the fibre inclusions over a segment from `b` to `b'` in a
chart of the base. -/
theorem eventually_map_fiberInclusionMap_eq [IsManifold IB ∞ B] [IsManifold IF ∞ F]
    {e : Trivialization F proj}
    (he : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target) {b : B}
    (hb : b ∈ e.baseSet) (k : ℕ) :
    ∀ᶠ b' in 𝓝 b, ∃ hb' : b' ∈ e.baseSet,
      deRhamCohomology.map (e.fiberInclusionMap hb') (e.contMDiff_fiberInclusionMap he hb') k =
        deRhamCohomology.map (e.fiberInclusionMap hb) (e.contMDiff_fiberInclusionMap he hb) k := by
  set φ := extChartAt IB b
  -- A ball about `φ b`, cut down to the range of `IB`, on which `φ.symm` lands in the base set.
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhdsWithin_iff.1 (Filter.inter_mem
    (mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds (e.open_baseSet.mem_nhds hb)))
    (extChartAt_target_mem_nhdsWithin (I := IB) b))
  filter_upwards [extChartAt_source_mem_nhds (I := IB) b,
    (continuousAt_extChartAt (I := IB) b).preimage_mem_nhds (Metric.ball_mem_nhds _ hε),
    e.open_baseSet.mem_nhds hb] with b' hs hball hb'
  refine ⟨hb', ?_⟩
  -- The segment from `φ b` to `φ b'`, read back in the base.
  have hseg (t : Icc (0 : ℝ) 1) :
      AffineMap.lineMap (φ b) (φ b') (t : ℝ) ∈ φ.symm ⁻¹' e.baseSet ∩ φ.target :=
    hεS ⟨(convex_ball _ _).lineMap_mem (Metric.mem_ball_self hε) hball t.property,
      IB.convex_range.lineMap_mem (mem_range_self _) (mem_range_self _) t.property⟩
  let γ : Icc (0 : ℝ) 1 → B := fun t ↦ φ.symm (AffineMap.lineMap (φ b) (φ b') (t : ℝ))
  have hγ : ContMDiff (𝓡∂ 1) IB ∞ γ :=
    (contMDiffOn_extChartAt_symm b).comp_contMDiff
      ((AffineMap.contDiff_lineMap (φ b) (φ b')).contMDiff.comp contMDiff_subtypeVal_Icc)
      fun t ↦ (hseg t).2
  refine (deRhamCohomology.map_eq_of_homotopy _ _
    (F := fun q ↦ e.toOpenPartialHomeomorph.symm (γ q.2, q.1))
    (he.comp_contMDiff ((hγ.comp contMDiff_snd).prodMk contMDiff_fst)
      fun q ↦ e.mem_target.2 (hseg q.2).1) (fun v ↦ ?_) (fun v ↦ ?_) k).symm
  · simp only [γ, Icc.coe_zero, AffineMap.lineMap_apply_zero, φ, extChartAt_to_inv,
      fiberInclusionMap_apply]
  · simp only [γ, Icc.coe_one, AffineMap.lineMap_apply_one, φ.left_inv hs,
      fiberInclusionMap_apply]

/-- **Fibre inclusions through two charts in cohomology.** Let `e` and `e'` be trivializations
of `proj` with smooth inverses, whose coordinate change over `b` is a diffeomorphism `φ` of the
fibre that preserves a closed form `σ`. If the fibre inclusion of `e'` over `b` sends a class
`a` to the class of `σ`, so does that of `e`. -/
theorem map_fiberInclusionMap_eq_of_mem_diffeomorphStabilizer {e e' : Trivialization F proj}
    (he : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    (he' : ContMDiffOn (IB.prod IF) IM ∞ e'.toOpenPartialHomeomorph.symm e'.target) {b : B}
    (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) {σ : SmoothForm IF F ℝ k} (hσ : σ.IsClosed)
    {φ : F ≃ₘ⟮IF, IF⟯ F} (hφ : φ ∈ SmoothForm.diffeomorphStabilizer σ)
    (hφe : ⇑φ = e.coordChange e' b) {a : deRhamCohomology IM M k}
    (h : deRhamCohomology.map (e'.fiberInclusionMap hb') (e'.contMDiff_fiberInclusionMap he' hb')
        k a = deRhamCohomology.mk IF k ⟨σ, hσ.mem_closedForms⟩) :
    deRhamCohomology.map (e.fiberInclusionMap hb) (e.contMDiff_fiberInclusionMap he hb) k a =
      deRhamCohomology.mk IF k ⟨σ, hσ.mem_closedForms⟩ := by
  have hj : ⇑(e.fiberInclusionMap hb) = e'.fiberInclusionMap hb' ∘ φ := by
    rw [hφe]
    exact funext fun v ↦ (e.fiberInclusionMap_coordChange e' hb hb' v).symm
  have hmap : ∀ {f g : F → M} (hf : ContMDiff IF IM ∞ f) (hg : ContMDiff IF IM ∞ g), f = g →
      deRhamCohomology.map (I := IF) (I' := IM) f hf k = deRhamCohomology.map g hg k := by
    rintro f _ hf hg rfl
    rfl
  rw [hmap _ ((e'.contMDiff_fiberInclusionMap he' hb').comp φ.contMDiff) hj,
    deRhamCohomology.map_comp _ _ φ.contMDiff (e'.contMDiff_fiberInclusionMap he' hb'),
    LinearMap.comp_apply, h, deRhamCohomology.map_mk]
  congr 1
  ext1
  rw [closedForms.coe_mpullback]
  exact SmoothForm.mem_diffeomorphStabilizer.1 hφ

end Bundle.Trivialization

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF 2 F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM 2 M]
  {proj : M → B} {A : Atlas F proj} {k : ℕ} {σ : SmoothForm IF F ℝ k} {τ : SmoothForm IM M ℝ k}

/-- **Classes of closed extensions of the fibre forms.** Let `τ` be a closed form on `M` that
restricts to `σ` along a smooth atlas `A`. For every chart `A.trivAt b` and every point `b'` of
its base set, the map on de Rham cohomology induced by the fibre inclusion
`v ↦ (A.trivAt b)⁻¹ (b', v)` sends the class of `τ` to the class of `σ`, which is closed by
`RestrictsTo.isClosed`, since the base has the point `b`. -/
theorem map_eq_of_restricts (hA : A.IsContMDiff ∞ IB IF IM) (hτ : A.RestrictsTo σ τ)
    (hτc : τ.IsClosed) {b b' : B} (hb' : b' ∈ (A.trivAt b).baseSet) :
    deRhamCohomology.map ((A.trivAt b).fiberInclusionMap hb')
        ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb') k
        (deRhamCohomology.mk IM k ⟨τ, hτc.mem_closedForms⟩) =
      deRhamCohomology.mk IF k
        ⟨σ, (haveI : Nonempty B := ⟨b⟩; hτ.isClosed hA hτc).mem_closedForms⟩ := by
  rw [deRhamCohomology.map_mk]
  congr 1
  ext1
  rw [closedForms.coe_mpullback, SmoothForm.mpullback_eq_iff]
  exact restrictsTo_iff.1 hτ b b' hb'

/-- **One fibre inclusion is enough.** Let `A` be a smooth atlas, over a smooth preconnected
base, whose coordinate changes preserve a closed form `σ` on the fibre. If the fibre inclusion
`v ↦ (A.trivAt b₀)⁻¹ (b₀', v)` of one chart over one point sends a class `a` on `M` to the class
of `σ`, then so does every fibre inclusion `v ↦ (A.trivAt b)⁻¹ (b', v)` of the atlas. -/
theorem forall_map_eq_of_map_eq [IsManifold IB ∞ B] [IsManifold IF ∞ F] [PreconnectedSpace B]
    (hA : A.IsContMDiff ∞ IB IF IM) (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ))
    (hσ : σ.IsClosed) {a : deRhamCohomology IM M k} {b₀ b₀' : B}
    (hb₀' : b₀' ∈ (A.trivAt b₀).baseSet)
    (h : deRhamCohomology.map ((A.trivAt b₀).fiberInclusionMap hb₀')
        ((A.trivAt b₀).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b₀) hb₀') k a =
      deRhamCohomology.mk IF k ⟨σ, hσ.mem_closedForms⟩)
    {b b' : B} (hb' : b' ∈ (A.trivAt b).baseSet) :
    deRhamCohomology.map ((A.trivAt b).fiberInclusionMap hb')
        ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb') k a =
      deRhamCohomology.mk IF k ⟨σ, hσ.mem_closedForms⟩ := by
  -- `P x`: every fibre inclusion of the atlas over `x` sends `a` to the class of `σ`.
  let P : B → Prop := fun x ↦ ∀ c (hx : x ∈ (A.trivAt c).baseSet),
    deRhamCohomology.map ((A.trivAt c).fiberInclusionMap hx)
      ((A.trivAt c).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm c) hx) k a =
    deRhamCohomology.mk IF k ⟨σ, hσ.mem_closedForms⟩
  -- One chart over `x` is enough, since the coordinate changes preserve `σ`.
  have hP (c x : B) (hx : x ∈ (A.trivAt c).baseSet)
      (hc : deRhamCohomology.map ((A.trivAt c).fiberInclusionMap hx)
        ((A.trivAt c).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm c) hx) k a =
      deRhamCohomology.mk IF k ⟨σ, hσ.mem_closedForms⟩) : P x := fun c' hx' ↦ by
    obtain ⟨φ, hφ, hφe⟩ := hasStructureGroup_iff.1 hH c' c x hx' hx
    exact Trivialization.map_fiberInclusionMap_eq_of_mem_diffeomorphStabilizer
      (hA.contMDiffOn_trivAt_symm c') (hA.contMDiffOn_trivAt_symm c) hx' hx hσ hφ hφe hc
  -- Near `x`, the fibre inclusions of the chart `A.trivAt x` all give the same map.
  have hloc : IsLocallyConstant P := (IsLocallyConstant.iff_eventually_eq P).2 fun x ↦ by
    filter_upwards [(A.trivAt x).eventually_map_fiberInclusionMap_eq
      (hA.contMDiffOn_trivAt_symm x) (A.mem_baseSet_trivAt x) k] with y ⟨hy, hyx⟩
    refine propext ⟨fun hPy ↦ hP x x (A.mem_baseSet_trivAt x) ?_, fun hPx ↦ hP x y hy ?_⟩
    · rw [← hyx]
      exact hPy x hy
    · rw [hyx]
      exact hPx x _
  exact (hloc.apply_eq_of_preconnectedSpace b₀' b' ▸ hP b₀ b₀' hb₀' h) b hb'

end TauCeti.MapFiber.Atlas

end
