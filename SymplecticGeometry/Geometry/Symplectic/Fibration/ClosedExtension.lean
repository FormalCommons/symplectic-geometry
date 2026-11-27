/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
public import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DeRham.Map
import SymplecticGeometry.Geometry.Manifold.FiberBundle.DeRham

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
  the class of `σ` is sent there by every fibre inclusion of the atlas. The proof changes charts
  with `Bundle.Trivialization.map_fiberInclusionMap_eq_of_mem_diffeomorphStabilizer` and moves
  along the base with `Bundle.Trivialization.eventually_map_fiberInclusionMap_eq`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 (Theorem 6.1.4 and its proof).
* [W. P. Thurston, *Some simple examples of symplectic manifolds*][Thurston1976].
-/

public section

open Bundle TauCeti
open scoped Manifold ContDiff

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM 2 M]
  {proj : M → B} {A : Atlas F proj} {k : ℕ}

section Restricts

variable [IsManifold IF 2 F] {σ : SmoothForm IF F ℝ k} {τ : SmoothForm IM M ℝ k}

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
  rw [closedForms.coe_mpullback]
  exact hτ.mpullback_fiberInclusionMap_eq hA hb'

end Restricts

section Connected

variable [IsManifold IF ∞ F] {σ : SmoothForm IF F ℝ k}

/-- **One fibre inclusion is enough.** Let `A` be a smooth atlas, over a smooth preconnected
base, whose coordinate changes preserve a closed form `σ` on the fibre. If the fibre inclusion
`v ↦ (A.trivAt b₀)⁻¹ (b₀', v)` of one chart over one point sends a class `a` on `M` to the class
of `σ`, then so does every fibre inclusion `v ↦ (A.trivAt b)⁻¹ (b', v)` of the atlas. -/
theorem forall_map_eq_of_map_eq [IsManifold IB ∞ B] [PreconnectedSpace B]
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

end Connected

end TauCeti.MapFiber.Atlas

end
