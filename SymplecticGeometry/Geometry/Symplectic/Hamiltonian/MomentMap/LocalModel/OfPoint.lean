/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Slice.MomentMap
public import SymplecticGeometry.Geometry.Lie.Subgroup.IdentityComponent
public import SymplecticGeometry.Geometry.Manifold.GroupAction.TangentRepresentation.Smooth
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Data

/-!
# The local model's data at a point of a Hamiltonian `G`-manifold

Let a real Lie group `G` act smoothly on a manifold `M` with a nondegenerate two-form `σ` and a
coadjoint-equivariant moment map `μ`, and let `x ∈ M` have compact stabilizer `H = G_x` which
preserves `σ`. Give `H` the Lie group structure of an embedded Lie subgroup `d` of `G`, such as
the closed-subgroup structure `TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`. This file feeds
`x` into the Marle–Guillemin–Sternberg local model `G ×_H (𝔪* × V)`: it builds the data
`SymplecticGeometry.LocalModelData H V A` of the model from `x`.

The covector is `τ = μ x`, fixed by `H` by equivariance, and `𝔥` is the isotropy algebra `𝔤_x`,
the image of the differential at `1` of the inclusion `H → G`
(`TauCeti.Lie.EmbeddedLieSubgroupData.range_groupLieAlgebraMap_stabilizer_subtype`). The
complements `𝔪` of `𝔤_x` in `𝔤_{μ x}` and `𝔮` of `𝔤_{μ x}` in `𝔤` are taken as arguments, so that
they can be those to which Tau Ceti applies its equivariant linear normal form
(`exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_symplecticSlice`, in
`MomentMap/LinearNormalForm.lean`) at `x`;
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_subrepresentation_complements`
gives some. The symplectic vector space of the model is the symplectic slice
`W^σ ⧸ (W ∩ W^σ)` at `x`, `W = 𝔤 · x`, with its reduced form, carried to a normed space `V` by a
linear isomorphism `eV`, since the model asks for a normed space; likewise `A` is a normed space
with a linear isomorphism `eA : A ≃ 𝔪*`. The representation of `H` is
`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceRepresentation`, `[u] ↦ [dh_x u]`, and its
infinitesimal map is `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceIsotropyAction`,
`[u] ↦ [A_ξ u]`, both carried to `V` by `eV`.

The smoothness of the representation and its derivative at `1` come from those of the tangent
representation `h ↦ dh_x` (`TauCeti.contMDiff_tangentRepresentation_apply` and
`TauCeti.mfderiv_tangentRepresentation_apply_one`), through continuous linear maps
`T_x M → V` and `V → T_x M` that read the quotient `W^σ ⧸ (W ∩ W^σ)` on `W^σ`.

## Main definitions

* `SymplecticGeometry.LocalModelData.ofPoint`: the data of the local model at `x`.

## Main results

* `SymplecticGeometry.LocalModelData.ofPoint_τ`, `SymplecticGeometry.LocalModelData.ofPoint_𝔥`,
  `SymplecticGeometry.LocalModelData.ofPoint_𝔪`, `SymplecticGeometry.LocalModelData.ofPoint_𝔮`,
  `SymplecticGeometry.LocalModelData.ofPoint_equivDual𝔪`: the covector, the splitting and `A ≃ 𝔪*`.
* `SymplecticGeometry.LocalModelData.ofPoint_σ`,
  `SymplecticGeometry.LocalModelData.isSymplectomorphism_ofPoint_σ`: `eV` is a linear
  symplectomorphism onto the symplectic slice with its reduced form.
* `SymplecticGeometry.LocalModelData.ofPoint_rep_apply`,
  `SymplecticGeometry.LocalModelData.ofPoint_ρ_apply`: `eV` intertwines the representation and
  its infinitesimal map with those of the stabilizer and of the isotropy algebra on the slice.
* `TauCeti.SymplecticForm.conj_mem_skewAdjointLieSubalgebra_transport`: conjugation by a linear
  isomorphism carries `sp(V, ω)` to the symplectic Lie algebra of the transported form.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open MulAction TauCeti TauCeti.Lie
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {x : M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

/-- Transporting a symplectic form along a linear isomorphism `e` carries its symplectic Lie
algebra to that of the transported form, by conjugation `A ↦ e ∘ A ∘ e⁻¹`. -/
theorem _root_.TauCeti.SymplecticForm.conj_mem_skewAdjointLieSubalgebra_transport
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {ν : SymplecticForm V} {A : Module.End ℝ V} (hA : A ∈ skewAdjointLieSubalgebra ν.toBilinForm)
    (e : V ≃ₗ[ℝ] W) :
    e.conj A ∈ skewAdjointLieSubalgebra (ν.transport e).toBilinForm :=
  (LinearMap.mem_skewAdjointSubmodule _).2 fun u w ↦ by
    have h := (LinearMap.mem_skewAdjointSubmodule A).1 hA (e.symm u) (e.symm w)
    simpa [LinearEquiv.conj_apply] using h

omit [I'.Boundaryless] [T2Space M] in
/-- A linear isomorphism `V ≃ W^σ ⧸ (W ∩ W^σ)` is read through continuous linear maps
`L : T_x M → V` and `S : V → T_x M`: `L u = [u]` on `W^σ`, and `S v ∈ W^σ` lifts `v`. -/
private theorem exists_clm_symplecticSlice (hσ : σ.IsNondegenerate)
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] {a : InfinitesimalAction 𝔤 I' M}
    (eV : V ≃ₗ[ℝ] hσ.SymplecticSlice a x) :
    ∃ (L : E' →L[ℝ] V) (S : V →L[ℝ] E'),
      (∀ (u : TangentSpace I' x) (hu : u ∈ (hσ.symplecticFormAt x).orthogonal (a.orbitTangent x)),
        L u = eV.symm (Submodule.Quotient.mk ⟨u, hu⟩)) ∧
      ∀ v, ∃ hv : S v ∈ (hσ.symplecticFormAt x).orthogonal (a.orbitTangent x),
        (Submodule.Quotient.mk ⟨S v, hv⟩ : hσ.SymplecticSlice a x) = eV v := by
  set W := (hσ.symplecticFormAt x).orthogonal (a.orbitTangent x)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  obtain ⟨s, hs⟩ := (LinearMap.ker ((hσ.symplecticFormAt x).toBilinForm.restrict W)).mkQ
    |>.exists_rightInverse_of_surjective (Submodule.range_mkQ _)
  refine ⟨LinearMap.toContinuousLinearMap (eV.symm.toLinearMap ∘ₗ Submodule.mkQ _ ∘ₗ
      Submodule.projectionOnto W C hC),
    LinearMap.toContinuousLinearMap (W.subtype ∘ₗ s ∘ₗ eV.toLinearMap), fun u hu ↦ ?_,
    fun v ↦ ⟨(s (eV v)).property, ?_⟩⟩
  · simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
      LinearEquiv.coe_coe]
    exact congrArg (fun w ↦ eV.symm (Submodule.Quotient.mk w))
      (Submodule.projectionOnto_apply_left hC ⟨u, hu⟩)
  · exact LinearMap.congr_fun hs (eV v)

variable (hσ : σ.IsNondegenerate)
  (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
    (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
  (hμ : σ.IsEquivariantMomentMap μ)
  [IsClosed (stabilizer G x : Set G)] [CompactSpace (stabilizer G x)]
  (d : EmbeddedLieSubgroupData I (stabilizer G x) F)
  {𝔪 𝔮 : Subrepresentation ((adjointRepresentation ℝ I G).comp (stabilizer G x).subtype)}
  (h𝔪 : Disjoint ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule
    𝔪.toSubmodule)
  (h𝔪' : ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule ⊔ 𝔪.toSubmodule =
    (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ x)).toSubmodule)
  (h𝔮 : IsCompl (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ x)).toSubmodule 𝔮.toSubmodule)
  (eV : V ≃ₗ[ℝ] hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x)
  (eA : A ≃ₗ[ℝ] Module.Dual ℝ 𝔪.toSubmodule)

-- The definition is exposed so that other files see its `𝔥`, `𝔪` and `𝔮` as the given subspaces
-- by definition: the types of its fields, such as that of `equivDual𝔪`, are stated with them.
/-- **The data of the local model at a point `x` of a Hamiltonian `G`-manifold** `(M, σ)` with
coadjoint-equivariant moment map `μ`, whose stabilizer `H = G_x` is compact and carries the Lie
group structure of an embedded Lie subgroup `d`, for instance
`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`, and preserves `σ`:

* `τ = μ x`;
* `𝔥` is the isotropy algebra `𝔤_x`;
* `𝔪` and `𝔮` are given `H`-invariant complements, `𝔤_x ⊕ 𝔪 = 𝔤_{μ x}` and `𝔤_{μ x} ⊕ 𝔮 = 𝔤`,
  as `TauCeti.SmoothTwoForm.IsNondegenerate.exists_subrepresentation_complements` provides;
* `(V, σ_V, rep)` is the symplectic slice at `x` with its reduced form and the representation
  `TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceRepresentation`, carried to `V` by
  `eV : V ≃ W^σ ⧸ (W ∩ W^σ)`, and `ρ` is `symplecticSliceIsotropyAction` carried to `V`;
* `A ≃ 𝔪*` is `eA`. -/
@[expose]
def LocalModelData.ofPoint :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    LocalModelData (I := I) (stabilizer G x) (F := F) V A := by
  intro _ _ _
  have hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x :=
    fun g _ ↦ ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g x
  exact
  { τ := μ x
    coadjointRepresentation_τ k := by
      rw [← hμ.apply_smul, mem_stabilizer_iff.1 k.property]
    𝔥 := ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule
    range_groupLieAlgebraMap_subtype := d.range_groupLieAlgebraMap_stabilizer_subtype
    𝔪 := 𝔪.toSubmodule
    𝔮 := 𝔮.toSubmodule
    disjoint_𝔥_𝔪 := h𝔪
    𝔥_sup_𝔪 := h𝔪'
    isCompl_𝔮 := h𝔮
    adjointRepresentation_mem_𝔪 k _ hξ := 𝔪.apply_mem_toSubmodule k hξ
    adjointRepresentation_mem_𝔮 k _ hξ := 𝔮.apply_mem_toSubmodule k hξ
    σ := ((hσ.symplecticFormAt x).reduction ((hσ.symplecticFormAt x).orthogonal
      ((InfinitesimalAction.fundamental I G I' M).orbitTangent x))).transport eV.symm
    rep :=
      { toFun k := eV.trans ((hσ.symplecticSliceRepresentation hσG k).trans eV.symm)
        map_one' := by ext; simp
        map_mul' k l := by ext; simp }
    isSymplectomorphism_rep k :=
      have he := SymplecticForm.isSymplectomorphism_iff_transport_eq.2
        (SymplecticForm.transport_transport_symm _ eV)
      he.trans ((hσ.isSymplectomorphism_symplecticSliceRepresentation hσG k).trans he.symm)
    contMDiff_rep := by
      obtain ⟨L, S, hL, hS⟩ := exists_clm_symplecticSlice hσ eV
      refine (L.contMDiff.comp ((contMDiff_tangentRepresentation_apply d hd).comp
        (contMDiff_fst.prodMk (S.contMDiff.comp contMDiff_snd)))).congr fun p ↦ ?_
      obtain ⟨hv, hv'⟩ := hS p.2
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply, Function.comp_apply]
      rw [← hv', SmoothTwoForm.IsNondegenerate.symplecticSliceRepresentation_mk]
      exact (hL _ (hσ.tangentRepresentation_mem_orthogonal_orbitTangent hσG hd p.1 hv)).symm
    ρ :=
      { toFun ξ := ⟨eV.symm.conj (hσ.symplecticSliceIsotropyAction hσG ⟨ξ.val, ξ.property⟩ :
            Module.End ℝ (hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x)),
          SymplecticForm.conj_mem_skewAdjointLieSubalgebra_transport
            (hσ.symplecticSliceIsotropyAction hσG ⟨ξ.val, ξ.property⟩).property eV.symm⟩
        map_add' ξ ζ := Subtype.ext <| by
          have h := map_add (hσ.symplecticSliceIsotropyAction (I := I) hσG) ⟨ξ.val, ξ.property⟩
            ⟨ζ.val, ζ.property⟩
          rw [Subtype.ext_iff, AddMemClass.coe_add] at h
          exact (congrArg eV.symm.conj h).trans (map_add _ _ _)
        map_smul' c ξ := Subtype.ext <| by
          have h := map_smul (hσ.symplecticSliceIsotropyAction (I := I) hσG) c ⟨ξ.val, ξ.property⟩
          rw [Subtype.ext_iff, SetLike.val_smul] at h
          exact (congrArg eV.symm.conj h).trans (map_smul _ _ _) }
    mfderiv_rep_apply_of_mem ξ hξ v := by
      obtain ⟨L, S, hL, hS⟩ := exists_clm_symplecticSlice hσ eV
      obtain ⟨hv, hv'⟩ := hS v
      have hφ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E')
          (fun k : stabilizer G x ↦ show E' from tangentRepresentation hd k (S v)) 1 :=
        (((contMDiff_tangentRepresentation_apply d hd).comp
          (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp)) 1
      have hfun : (fun k : stabilizer G x ↦
          eV.symm (hσ.symplecticSliceRepresentation hσG k (eV v))) =
          fun k ↦ L (show E' from tangentRepresentation hd k (S v)) := funext fun k ↦ by
        rw [← hv', SmoothTwoForm.IsNondegenerate.symplecticSliceRepresentation_mk]
        exact (hL _ (hσ.tangentRepresentation_mem_orthogonal_orbitTangent hσG hd k hv)).symm
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply, LinearMap.coe_mk,
        AddHom.coe_mk]
      have h2 := (L.hasMFDerivAt.comp 1 hφ.hasMFDerivAt).mfderiv
      rw [Function.comp_def] at h2
      rw [hfun, h2]
      refine (congrArg L (mfderiv_tangentRepresentation_apply_one d hd ξ (S v))).trans ?_
      rw [hL _ (hσ.isotropyLinearization_apply_mem_orthogonal hσG _ hv), LinearEquiv.conj_apply,
        LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.symm_symm]
      simp only [LinearEquiv.coe_coe]
      rw [← hv', SmoothTwoForm.IsNondegenerate.symplecticSliceIsotropyAction_mk]
    equivDual𝔪 := eA }

namespace LocalModelData

/-- The covector of the local model at `x` is `μ x`. -/
@[simp]
theorem ofPoint_τ :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    (ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA).τ = μ x :=
  (rfl)

/-- The Lie algebra `𝔥` of the local model at `x` is the isotropy algebra `𝔤_x`. -/
@[simp]
theorem ofPoint_𝔥 :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    (ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA).𝔥 =
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule :=
  (rfl)

@[simp]
theorem ofPoint_𝔪 :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    (ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA).𝔪 = 𝔪.toSubmodule :=
  (rfl)

@[simp]
theorem ofPoint_𝔮 :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    (ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA).𝔮 = 𝔮.toSubmodule :=
  (rfl)

/-- The symplectic form of the local model at `x` is the reduced form of the symplectic slice,
carried to `V` by `eV`. -/
theorem ofPoint_σ :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    (ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA).σ =
      ((hσ.symplecticFormAt x).reduction ((hσ.symplecticFormAt x).orthogonal
        ((InfinitesimalAction.fundamental I G I' M).orbitTangent x))).transport eV.symm :=
  (rfl)

/-- `eV` is a linear symplectomorphism from the symplectic form of the local model at `x` to the
reduced form of the symplectic slice. -/
theorem isSymplectomorphism_ofPoint_σ :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    SymplecticForm.IsSymplectomorphism (ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA).σ
      ((hσ.symplecticFormAt x).reduction ((hσ.symplecticFormAt x).orthogonal
        ((InfinitesimalAction.fundamental I G I' M).orbitTangent x))) eV :=
  SymplecticForm.isSymplectomorphism_iff_transport_eq.2
    (SymplecticForm.transport_transport_symm _ eV)

/-- `eV` intertwines the representation of the local model at `x` with the representation
`[u] ↦ [dh_x u]` of the stabilizer on the symplectic slice. -/
@[simp]
theorem ofPoint_rep_apply :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    ∀ (k : stabilizer G x) (v : V), eV ((ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA).rep k v) =
      hσ.symplecticSliceRepresentation hσG k (eV v) := by
  intro _ _ _ k v
  exact eV.apply_symm_apply _

/-- `eV` intertwines the infinitesimal map `ρ` of the local model at `x` with the action
`[u] ↦ [A_ξ u]` of the isotropy algebra on the symplectic slice. -/
@[simp]
theorem ofPoint_ρ_apply :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    ∀ (ξ : (ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA).𝔥) (v : V),
      eV (((ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA).ρ ξ : Module.End ℝ V) v) =
        (hσ.symplecticSliceIsotropyAction hσG ⟨ξ.val, ξ.property⟩ :
          Module.End ℝ (hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x))
          (eV v) := by
  intro _ _ _ ξ v
  exact eV.apply_symm_apply _

@[simp]
theorem ofPoint_equivDual𝔪 :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    (ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA).equivDual𝔪 = eA :=
  (rfl)

end LocalModelData

end SymplecticGeometry
