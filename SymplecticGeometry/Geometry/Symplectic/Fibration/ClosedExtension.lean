/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
public import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DeRham.Map
public import SymplecticGeometry.Geometry.Manifold.DeRham.GoodCover.Basic
import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

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
* `Bundle.Trivialization.mpullback_snd_sub_mem_exactForms_of_map_eq`: over a smoothly
  contractible open set `U` of the base set of a smooth trivialization `e`, if the class of a closed
  form `τ₀` on `M` pulls back to that of a closed form `σ` on `F` along one fibre inclusion over
  `U`, then on `proj ⁻¹' U` the forms `τ₀` and the pull-back of `σ` along `x ↦ (e x).2` differ by an
  exact form. Contracting `U` deforms the identity of `proj ⁻¹' U` into the fibre coordinate
  followed by a fibre inclusion, and homotopy invariance of de Rham cohomology concludes. This is
  the local step of the construction of a closed extension with a given class.

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
  rw [closedForms.coe_mpullback, SmoothForm.mpullback_eq_iff]
  exact restrictsTo_iff.1 hτ b b' hb'

end TauCeti.MapFiber.Atlas

namespace Bundle.Trivialization

open TauCeti

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {proj : M → B} {e : Trivialization F proj} {k : ℕ}

/-- The fibre coordinate `x ↦ (e x).2` of a trivialization that is smooth on its source is smooth
on every open set `W` of `M` inside that source. -/
theorem contMDiff_snd_subtypeVal (he : ContMDiffOn IM (IB.prod IF) ∞ e e.source)
    {W : TopologicalSpace.Opens M} (hW : (W : Set M) ⊆ e.source) :
    ContMDiff IM IF ∞ fun x : W ↦ (e x).2 :=
  (contMDiff_snd.comp_contMDiffOn he).comp_contMDiff contMDiff_subtypeVal fun x ↦ hW x.property

/-- **Closed forms over a contractible part of the base.** Let `e` be a smooth trivialization of
`proj` with smooth inverse, `U` a smoothly contractible open set of its base set, and `W` the open
set `proj ⁻¹' U` of `M`. Let `σ` be a closed form on `F` and `τ₀` a closed form on `M` whose
pull-back along the fibre inclusion `v ↦ e⁻¹ (b, v)` over some `b ∈ U` is cohomologous to `σ`.
Then on `W` the pull-back of `σ` along the fibre coordinate `x ↦ (e x).2` minus the restriction
of `τ₀` is exact. -/
theorem mpullback_snd_sub_mem_exactForms_of_map_eq [IsManifold IF ∞ F] [IsManifold IM ∞ M]
    (he : ContMDiffOn IM (IB.prod IF) ∞ e e.source)
    (he' : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    {U : TopologicalSpace.Opens B} (hU : (U : Set B) ⊆ e.baseSet)
    (hUc : SymplecticGeometry.IsSmoothlyContractible IB U) {W : TopologicalSpace.Opens M}
    (hW : (W : Set M) = proj ⁻¹' U) {σ : SmoothForm IF F ℝ k} (hσ : σ.IsClosed)
    {τ₀ : SmoothForm IM M ℝ k} (hτ₀ : τ₀.IsClosed) {b : B} (hb : b ∈ U)
    (h : deRhamCohomology.map (e.fiberInclusionMap (hU hb))
        (e.contMDiff_fiberInclusionMap he' (hU hb)) k
        (deRhamCohomology.mk IM k ⟨τ₀, hτ₀.mem_closedForms⟩) =
      deRhamCohomology.mk IF k ⟨σ, hσ.mem_closedForms⟩) :
    SmoothForm.mpullback _ (contMDiff_snd_subtypeVal he fun x hx ↦
        e.mem_source.2 (hU (hW.subset hx))) σ -
      SmoothForm.mpullback _ contMDiff_subtypeVal τ₀ ∈ exactForms IM W k := by
  obtain ⟨c, G, hG, hG₀, hG₁⟩ := SymplecticGeometry.isSmoothlyContractible_def.1 hUc
  have hWs : ∀ x : W, (x : M) ∈ e.source := fun x ↦
    e.mem_source.2 (hU (hW.subset x.property))
  set p : W → F := fun x ↦ (e x).2
  have hp : ContMDiff IM IF ∞ p := contMDiff_snd_subtypeVal he fun x hx ↦ hWs ⟨x, hx⟩
  -- The base coordinate of `e` on `W`, as a map to `U`.
  set q : W → U := fun x ↦ ⟨(e x).1, by rw [e.coe_fst (hWs x)]; exact hW.subset x.property⟩
  have hq : ContMDiff IM IB ∞ q := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact (contMDiff_fst.comp_contMDiffOn he).comp_contMDiff contMDiff_subtypeVal hWs
  have hsymm := e.contMDiff_symm_val_prod he' hU
  -- The fibre inclusion over the centre `c` of the contraction.
  have hc := e.contMDiff_fiberInclusionMap he' (hU c.property)
  -- Contracting the base coordinate is a homotopy from `j_c ∘ p` to the inclusion of `W`.
  have hH := deRhamCohomology.map_eq_of_homotopy (hc.comp hp) contMDiff_subtypeVal
    (hsymm.comp ((hG.comp (hq.prodMap contMDiff_id)).prodMk (hp.comp contMDiff_fst)))
    (fun x ↦ by simp [hG₀, e.coe_fiberInclusionMap])
    (fun x ↦ by simpa [hG₁, q, p] using e.toOpenPartialHomeomorph.left_inv (hWs x)) k
  -- Moving the base point from `c` to `b` along the contraction.
  have hH' := deRhamCohomology.map_eq_of_homotopy hc
    (e.contMDiff_fiberInclusionMap he' (hU hb))
    (hsymm.comp ((hG.comp ((contMDiff_const (c := (⟨b, hb⟩ : U))).prodMk
      contMDiff_snd)).prodMk contMDiff_fst))
    (fun v ↦ by simp [hG₀, e.coe_fiberInclusionMap])
    (fun v ↦ by simp [hG₁, e.coe_fiberInclusionMap]) k
  have := congrArg (· (deRhamCohomology.mk IM k ⟨τ₀, hτ₀.mem_closedForms⟩)) hH
  rw [deRhamCohomology.map_comp p _ hp hc, LinearMap.comp_apply, hH', h, deRhamCohomology.map_mk,
    deRhamCohomology.map_mk, deRhamCohomology.mk_eq_mk_iff] at this
  simpa using this

end Bundle.Trivialization

end
