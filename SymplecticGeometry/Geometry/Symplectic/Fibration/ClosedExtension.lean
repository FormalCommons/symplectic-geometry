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
import SymplecticGeometry.Geometry.Manifold.DeRham.Map
import SymplecticGeometry.Geometry.Manifold.FiberBundle.DeRham
import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance
import Mathlib.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartitionOfUnity

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
* `Bundle.Trivialization.mpullback_snd_sub_mem_exactForms_of_map_eq`: over a smoothly
  contractible open set `U` of the base set of a smooth trivialization `e`, if the class of a closed
  form `τ₀` on `M` pulls back to that of a closed form `σ` on `F` along one fibre inclusion over
  `U`, then on every open set `W` of `M` over `U` the forms `τ₀` and the pull-back of `σ` along
  `x ↦ (e x).2` differ by an exact form. Contracting `U` deforms the inclusion of `W` into the
  fibre coordinate followed by a fibre inclusion, and homotopy invariance of de Rham cohomology
  concludes. This is the local step of the construction of a closed extension with a given class.
* `TauCeti.MapFiber.Atlas.exists_isClosed_restricts_of_map_eq`: for a smooth atlas whose
  coordinate changes preserve a closed form `σ` of positive degree, over a Hausdorff σ-compact
  base of finite dimension, a class that every fibre inclusion sends to the class of `σ` is the
  class of a closed extension. Write the class as `[τ₀]`, cover the base by smoothly contractible
  open sets `U b`, each inside the base set of the chart `A.trivAt b`, and take a smooth partition
  of unity `ρ` subordinate to them. Over `U b` the local step gives `η b` with
  `dη b = θ b - τ₀`, where `θ b` is the pull-back of `σ` along the fibre coordinate of
  `A.trivAt b`. Glue the `η b` into `Λ` with the weights `ρ b ∘ proj`
  (`SmoothPartitionOfUnity.glueForms`); then `τ = τ₀ + dΛ` has class `[τ₀]`, and on vertical
  vectors it is the average of the `θ b`
  (`SmoothPartitionOfUnity.mextDeriv_glueForms_apply_of_mem_ker`), each of which restricts to `σ`,
  so that `τ` does (`TauCeti.MapFiber.Atlas.restrictsTo_of_apply_eq_sum`).
* `TauCeti.MapFiber.Atlas.exists_isClosed_restricts_iff`: under the same hypotheses, a closed
  extension exists if and only if such a class does.

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
        ⟨σ, (haveI : Nonempty B := ⟨b⟩; hτ.isClosed hA hτc).mem_closedForms⟩ :=
  deRhamCohomology.map_mk_eq_mk_of_mpullback_eq _ (hτ.mpullback_fiberInclusionMap_eq hA hb')

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

/-- **Closed forms over a contractible part of the base.** Let `e` be a smooth trivialization of
`proj` with smooth inverse, `U` a smoothly contractible open set of its base set, and `W` an open
set of `M` over `U`. Let `σ` be a closed form on `F` and `τ₀` a closed form on `M` whose
pull-back along the fibre inclusion `v ↦ e⁻¹ (b, v)` over some `b ∈ U` is cohomologous to `σ`.
Then on `W` the pull-back of `σ` along the fibre coordinate `x ↦ (e x).2` minus the restriction
of `τ₀` is exact. -/
theorem mpullback_snd_sub_mem_exactForms_of_map_eq [IsManifold IF ∞ F] [IsManifold IM ∞ M]
    (he : ContMDiffOn IM (IB.prod IF) ∞ e e.source)
    (he' : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target)
    {U : TopologicalSpace.Opens B} (hU : (U : Set B) ⊆ e.baseSet)
    (hUc : SymplecticGeometry.IsSmoothlyContractible IB U) {W : TopologicalSpace.Opens M}
    (hW : (W : Set M) ⊆ proj ⁻¹' U) {σ : SmoothForm IF F ℝ k} (hσ : σ.IsClosed)
    {τ₀ : SmoothForm IM M ℝ k} (hτ₀ : τ₀.IsClosed) {b : B} (hb : b ∈ U)
    (h : deRhamCohomology.map (e.fiberInclusionMap (hU hb))
        (e.contMDiff_fiberInclusionMap he' (hU hb)) k
        (deRhamCohomology.mk IM k ⟨τ₀, hτ₀.mem_closedForms⟩) =
      deRhamCohomology.mk IF k ⟨σ, hσ.mem_closedForms⟩) :
    SmoothForm.mpullback _ (e.contMDiff_snd_subtypeVal he fun _ hx ↦
        e.mem_source.2 (hU (hW hx))) σ -
      SmoothForm.mpullback _ contMDiff_subtypeVal τ₀ ∈ exactForms IM W k := by
  obtain ⟨c, G, hG, hG₀, hG₁⟩ := SymplecticGeometry.isSmoothlyContractible_def.1 hUc
  have hWs : ∀ x : W, (x : M) ∈ e.source := fun x ↦
    e.mem_source.2 (hU (hW x.property))
  set p : W → F := fun x ↦ (e x).2
  have hp : ContMDiff IM IF ∞ p := e.contMDiff_snd_subtypeVal he fun x hx ↦ hWs ⟨x, hx⟩
  -- The base coordinate of `e` on `W`, as a map to `U`.
  set q : W → U := fun x ↦ ⟨(e x).1, by rw [e.coe_fst (hWs x)]; exact hW x.property⟩
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

namespace TauCeti.MapFiber.Atlas

open Set TopologicalSpace

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M]
  {proj : M → B} {A : Atlas F proj} {k : ℕ} {σ : SmoothForm IF F ℝ (k + 1)}

/-- **Closed extensions with a given class.** Let `A` be a smooth atlas of `proj`, over a
Hausdorff, σ-compact base modelled on a finite-dimensional space, whose coordinate changes
preserve a closed form `σ` of positive degree on the fibre. If a de Rham class `a` on `M` is sent
to the class of `σ` by the fibre inclusion `v ↦ (A.trivAt b)⁻¹ (b', v)` of every chart over every
point of its base set, then `a` is the class of a closed form `τ` that restricts to `σ` along
`A`. -/
theorem exists_isClosed_restricts_of_map_eq [IsManifold IB ∞ B] [FiniteDimensional ℝ EB]
    [T2Space B] [SigmaCompactSpace B] (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsClosed)
    {a : deRhamCohomology IM M (k + 1)}
    (h : ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      deRhamCohomology.map ((A.trivAt b).fiberInclusionMap hb')
          ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb') (k + 1)
          a =
        deRhamCohomology.mk IF (k + 1) ⟨σ, hσ.mem_closedForms⟩) :
    ∃ τ : SmoothForm IM M ℝ (k + 1), ∃ hτ : τ.IsClosed, A.RestrictsTo σ τ ∧
      deRhamCohomology.mk IM (k + 1) ⟨τ, hτ.mem_closedForms⟩ = a := by
  obtain ⟨⟨τ₀, hτ₀⟩, rfl⟩ := deRhamCohomology.mk_surjective IM (k + 1) a
  have hτ₀c : τ₀.IsClosed := (SmoothForm.isClosed_iff_mem_closedForms τ₀).2 hτ₀
  have hproj := hA.contMDiff_proj
  -- A cover of `B` by smoothly contractible open sets `U b ⊆ (A.trivAt b).baseSet`, and a
  -- partition of unity subordinate to it.
  choose U hbU hUe hUc using fun b ↦ SymplecticGeometry.exists_mem_subset_isSmoothlyContractible
    (I := IB) ((A.trivAt b).open_baseSet.mem_nhds (A.mem_baseSet_trivAt b))
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate IB isClosed_univ
    (fun b ↦ (U b : Set B)) (fun b ↦ (U b).isOpen) fun b _ ↦ mem_iUnion.2 ⟨b, hbU b⟩
  let W : B → Opens M := fun b ↦ ⟨proj ⁻¹' U b, (U b).isOpen.preimage hproj.continuous⟩
  have hW : ∀ b, proj ⁻¹' tsupport (ρ b) ⊆ W b := fun b ↦ preimage_mono (hρ b)
  -- The pull-back of `σ` along the fibre coordinate of the chart `A.trivAt b`.
  set θ : B → RoughForm IM M ℝ (k + 1) := fun b ↦
    TauCeti.mpullback IM IF (fun y ↦ (A.trivAt b y).2) σ.val
  -- Over `U b`, it differs from `τ₀` by the derivative of a form `η b`.
  have hex := fun b ↦ (A.trivAt b).mpullback_snd_sub_mem_exactForms_of_map_eq
    (hA.contMDiffOn_trivAt b) (hA.contMDiffOn_trivAt_symm b) (hUe b) (hUc b) (W := W b)
    subset_rfl hσ hτ₀c (hbU b) (h b b _)
  simp only [exactForms_succ, LinearMap.mem_range] at hex
  choose η hη using hex
  let Λ : SmoothForm IM M ℝ k := ⟨ρ.glueForms proj W fun b ↦ (η b).val,
    (ρ.isSmoothForm_glueForms hproj hW fun b ↦ (η b).isSmoothForm).mem_smoothBundleForms⟩
  set τ := τ₀ + mextDerivₗ IM k Λ with hτ
  have hτc : τ.IsClosed := (SmoothForm.isClosed_iff_mem_closedForms τ).2
    (add_mem hτ₀ (mextDerivₗ_mem_closedForms IM k Λ))
  -- On vertical vectors, `τ` is the average of the forms `θ b` with the weights `ρ b ∘ proj`.
  have hval : ∀ (x : M) {u : Fin (k + 1) → TangentSpace IM x},
      (∀ i, u i ∈ (mfderiv IM IB proj x).ker) →
      τ.val x u = ∑ b ∈ ρ.fintsupport (proj x), ρ b (proj x) * θ b x u := by
    intro x u hu
    have hterm : ∀ (b : B) (hx : x ∈ W b), mextDeriv (η b).val ⟨x, hx⟩ u = θ b x u - τ₀.val x u :=
      fun b hx ↦ by
        rw [← mextDerivₗ_apply, hη b, Submodule.coe_sub, Pi.sub_apply]
        refine (ContinuousAlternatingMap.sub_apply _ _ _).trans ?_
        rw [SmoothForm.coe_mpullback_subtype_val_apply]
        congr 1
        -- The fibre coordinate on `W b` is `(fun y ↦ (A.trivAt b y).2) ∘ Subtype.val`.
        exact DFunLike.congr_fun (SmoothForm.coe_mpullback_comp_subtypeVal_apply
          (f := fun y ↦ (A.trivAt b y).2) _ σ _) u
    rw [hτ, Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, mextDerivₗ_apply,
      ρ.mextDeriv_glueForms_apply_of_mem_ker (hproj.of_le (by simp)) hW
        (fun b ↦ (η b).isSmoothForm.of_le (by simp)) x hu]
    simp only [hterm]
    rw [Finset.sum_attach (ρ.fintsupport (proj x))
        fun b ↦ ρ b (proj x) * (θ b x u - τ₀.val x u)]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ρ.sum_finsupport' _ (mem_univ _) (ρ.finsupport_subset_fintsupport _), one_mul]
    abel
  refine ⟨τ, hτc, restrictsTo_of_apply_eq_sum hA hH (fun c ↦ (hρ c).trans (hUe c)) hval, ?_⟩
  rw [deRhamCohomology.mk_eq_mk_iff]
  simp [hτ]

/-- **Existence of closed extensions.** For a smooth atlas `A` of `proj`, over a Hausdorff,
σ-compact base modelled on a finite-dimensional space, whose coordinate changes preserve a closed
form `σ` of positive degree on the fibre, some closed form on `M` restricts to `σ` along `A` if
and only if some de Rham class on `M` is sent to the class of `σ` by the fibre inclusion of
every chart over every point of its base set. -/
theorem exists_isClosed_restricts_iff [IsManifold IB ∞ B] [FiniteDimensional ℝ EB]
    [T2Space B] [SigmaCompactSpace B] (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsClosed) :
    (∃ τ : SmoothForm IM M ℝ (k + 1), τ.IsClosed ∧ A.RestrictsTo σ τ) ↔
      ∃ a : deRhamCohomology IM M (k + 1), ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
        deRhamCohomology.map ((A.trivAt b).fiberInclusionMap hb')
            ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb') (k + 1)
            a =
          deRhamCohomology.mk IF (k + 1) ⟨σ, hσ.mem_closedForms⟩ := by
  refine ⟨fun ⟨τ, hτc, hτ⟩ ↦ ⟨_, fun b b' hb' ↦ map_eq_of_restricts hA hτ hτc hb'⟩,
    fun ⟨a, ha⟩ ↦ ?_⟩
  obtain ⟨τ, hτc, hτ, -⟩ := exists_isClosed_restricts_of_map_eq hA hH hσ ha
  exact ⟨τ, hτc, hτ⟩

end TauCeti.MapFiber.Atlas

end
