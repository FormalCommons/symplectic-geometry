/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
public import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DeRham.Map

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

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 (Theorem 6.1.4 and its proof).
* [W. P. Thurston, *Some simple examples of symplectic manifolds*][Thurston1976].
-/

public section

open Bundle
open scoped Manifold ContDiff

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
  rw [closedForms.coe_mpullback]
  exact hτ.mpullback_fiberInclusionMap_eq hA hb'

end TauCeti.MapFiber.Atlas

end
