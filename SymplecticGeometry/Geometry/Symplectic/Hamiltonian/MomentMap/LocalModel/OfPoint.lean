/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.LinearNormalForm
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Slice.MomentMap
public import SymplecticGeometry.Geometry.Lie.Subgroup.IdentityComponent
public import SymplecticGeometry.Geometry.Manifold.GroupAction.TangentRepresentation.Smooth
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Data
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.TangentSpace

/-!
# The local model at a point of a Hamiltonian `G`-manifold, and its tangent space at `[1, 0]`

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

Finally, the tangent space of the model `Y = G ×_H (A × V)` at `[1, 0]` is identified with
`T_x M`: `SymplecticGeometry.LocalModelData.linearModelEquiv` identifies it with the linear model
`(𝔪 × 𝔪*) × (𝔮 × V)`, and Tau Ceti's equivariant linear normal form at `x`, with `V` read as the
slice through `eV`, identifies that model with `T_x M`. A direction `(ξ, 0)` at `(1, 0, 0)` with
`ξ = h + m + q`, `h ∈ 𝔤_x`, `m ∈ 𝔪`, `q ∈ 𝔮`, has the same image under `dπ` as `(m + q, 0)`
(`SymplecticGeometry.LocalModelData.linearModelEquiv_mk_zero_mk_zero`), and `h_M(x) = 0`, so the
composite sends it to `ξ_M(x)`.

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
* `TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_symplecticSliceRepresentation_apply`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_symplecticSliceRepresentation_apply_one`: the
  representation of the stabilizer on the symplectic slice, read on `V` through `eV`, is smooth,
  and its derivative at `1` is the action of the isotropy algebra.
* `SymplecticGeometry.LocalModelData.exists_linearEquiv_tangentSpace_ofPoint`: a linear
  isomorphism from the tangent space of the model at `[1, 0]` to `T_x M` that takes the
  descended form to `σ_x`, intertwines the actions of the stabilizer, and sends `dπ (ξ, 0)` to
  `ξ_M(x)`.
* `SymplecticGeometry.LocalModelData.isCompl_orbitTangent_range_linearEquiv_comp_fiberTangentMap`:
  for such an isomorphism `T`, the fibre directions `p ↦ T (dπ_(1, 0, 0) (0, p))` span a
  complement of the orbit tangent space `𝔤 · x`. They are injective since `T` and
  `SymplecticGeometry.LocalModelData.fiberTangentMap` are, and equivariant by
  `SymplecticGeometry.LocalModelData.map_fiberTangentMap_smul` applied to `T`.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open MulAction TauCeti TauCeti.Lie TauCeti.Manifold
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

section SliceRepresentation

variable (hσ : σ.IsNondegenerate)
  (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
    (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
  (eV : V ≃ₗ[ℝ] hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x)

omit [I.Boundaryless] [T2Space G] [I'.Boundaryless] [T2Space M] [FiniteDimensional ℝ V] in
/-- Read through maps `L`, `S` as in `exists_clm_symplecticSlice`, the representation of the
stabilizer on the symplectic slice is the tangent representation. -/
private theorem symm_symplecticSliceRepresentation_apply_eq {L : E' →L[ℝ] V} {S : V →L[ℝ] E'}
    (hL : ∀ (u : TangentSpace I' x)
      (hu : u ∈ (hσ.symplecticFormAt x).orthogonal
        ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)),
      L u = eV.symm (Submodule.Quotient.mk ⟨u, hu⟩))
    (hS : ∀ v, ∃ hv : S v ∈ (hσ.symplecticFormAt x).orthogonal
        ((InfinitesimalAction.fundamental I G I' M).orbitTangent x),
      (Submodule.Quotient.mk ⟨S v, hv⟩ :
        hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x) = eV v)
    (k : stabilizer G x) (v : V) :
    eV.symm (hσ.symplecticSliceRepresentation hσG k (eV v)) =
      L (tangentRepresentation (fun g _ ↦
        ContMDiffSMul.mdifferentiable_const_smul (I := I) (I' := I') (n := ∞) (by simp) g x) k
        (S v)) := by
  obtain ⟨hv, hv'⟩ := hS v
  rw [← hv', SmoothTwoForm.IsNondegenerate.symplecticSliceRepresentation_mk]
  exact (hL _ _).symm

omit [I.Boundaryless] [T2Space G] [I'.Boundaryless] [T2Space M] [FiniteDimensional ℝ F] in
/-- For an embedded Lie subgroup structure `d` on the stabilizer `G_x` and a linear isomorphism
`eV` of `V` with the symplectic slice at `x`, the representation `[u] ↦ [dh_x u]` of `G_x` on the
slice, read on `V` through `eV`, is jointly smooth on `G_x × V`. -/
theorem _root_.TauCeti.SmoothTwoForm.IsNondegenerate.contMDiff_symplecticSliceRepresentation_apply
    (d : EmbeddedLieSubgroupData I (stabilizer G x) F) :
    let _ := d.chartedSpace
    ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) ∞ fun p : stabilizer G x × V ↦
      eV.symm (hσ.symplecticSliceRepresentation hσG p.1 (eV p.2)) := by
  intro _
  obtain ⟨L, S, hL, hS⟩ := exists_clm_symplecticSlice hσ eV
  exact (L.contMDiff.comp ((contMDiff_tangentRepresentation_apply d _).comp
    (contMDiff_fst.prodMk (S.contMDiff.comp contMDiff_snd)))).congr fun p ↦
      symm_symplecticSliceRepresentation_apply_eq hσ hσG eV hL hS p.1 p.2

/-- For an embedded Lie subgroup structure `d` on the stabilizer `G_x` and a linear isomorphism
`eV` of `V` with the symplectic slice at `x`, the derivative at `1` in the direction `ζ` of
`k ↦ eV⁻¹ (k · eV v)` is `eV⁻¹ ([A_ξ] (eV v))`, where `ξ ∈ 𝔤_x` is the image of `ζ` under the
differential at `1` of the inclusion `G_x → G` and `[A_ξ]` is
`TauCeti.SmoothTwoForm.IsNondegenerate.symplecticSliceIsotropyAction`. -/
theorem _root_.TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_symplecticSliceRepresentation_apply_one
    (d : EmbeddedLieSubgroupData I (stabilizer G x) F) :
    let _ := d.chartedSpace
    ∀ (ζ : GroupLieAlgebra 𝓘(ℝ, F) (stabilizer G x)) (v : V),
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, V)
          (fun k : stabilizer G x ↦ eV.symm (hσ.symplecticSliceRepresentation hσG k (eV v))) 1 ζ =
        eV.symm ((hσ.symplecticSliceIsotropyAction hσG
          ⟨(stabilizer G x).subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ζ,
            d.groupLieAlgebraMap_subtype_mem_isotropy (I' := I') ζ⟩ :
            Module.End ℝ (hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x))
          (eV v)) := by
  intro _ ζ v
  obtain ⟨L, S, hL, hS⟩ := exists_clm_symplecticSlice hσ eV
  obtain ⟨hv, hv'⟩ := hS v
  have hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I' I' (fun y : M ↦ g • y) x :=
    fun g _ ↦ ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g x
  have hφ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E')
      (fun k : stabilizer G x ↦ show E' from tangentRepresentation hd k (S v)) 1 :=
    (((contMDiff_tangentRepresentation_apply d hd).comp
      (contMDiff_id.prodMk contMDiff_const)).mdifferentiable (by simp)) 1
  have h2 := (L.hasMFDerivAt.comp 1 hφ.hasMFDerivAt).mfderiv
  rw [Function.comp_def] at h2
  rw [funext (symm_symplecticSliceRepresentation_apply_eq hσ hσG eV hL hS · v), h2]
  refine (congrArg L (mfderiv_tangentRepresentation_apply_one d hd ζ (S v))).trans ?_
  rw [hL _ (hσ.isotropyLinearization_apply_mem_orthogonal hσG _ hv), ← hv',
    SmoothTwoForm.IsNondegenerate.symplecticSliceIsotropyAction_mk]

end SliceRepresentation

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
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply]
      exact hσ.contMDiff_symplecticSliceRepresentation_apply hσG eV d
    ρ := (skewAdjointLieSubalgebraEquiv _ eV).symm.toLinearEquiv.toLinearMap ∘ₗ
      hσ.symplecticSliceIsotropyAction hσG
    mfderiv_rep_apply_of_mem ξ hξ v := by
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply]
      -- The ascription states the rest in `V` rather than in the tangent space `T V`.
      refine (hσ.mfderiv_symplecticSliceRepresentation_apply_one hσG eV d ξ v).trans
        (?_ : (_ : V) = _)
      -- `ρ` is defined on `𝔥` as a submodule, the isotropy action on the isotropy Lie
      -- subalgebra; the two types agree by definition, and `change` states `ρ` on the latter.
      change _ = ((skewAdjointLieSubalgebraEquiv _ eV).symm
        (hσ.symplecticSliceIsotropyAction hσG ⟨_, hξ⟩) : Module.End ℝ V) v
      rw [skewAdjointLieSubalgebraEquiv_symm_apply, LinearEquiv.lieConj_apply,
        LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm]
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
  -- `ρ` is defined on `𝔥` as a submodule, the isotropy action on the isotropy Lie subalgebra;
  -- the two types agree by definition, and `change` states `ρ` on the latter.
  change eV (((skewAdjointLieSubalgebraEquiv _ eV).symm
    (hσ.symplecticSliceIsotropyAction hσG ⟨ξ.val, ξ.property⟩) : Module.End ℝ V) v) = _
  rw [skewAdjointLieSubalgebraEquiv_symm_apply, LinearEquiv.lieConj_apply,
    LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

@[simp]
theorem ofPoint_equivDual𝔪 :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    (ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA).equivDual𝔪 = eA :=
  (rfl)

/-! ### The tangent space at `[1, 0]` -/

/-- **The tangent space of the local model at `[1, 0]` is `T_x M`.** For the data `D` of the
local model at `x`, with `Y = G ×_{G_x} (A × V)`, its descended form `ω = D.descendedForm` and the
projection `π (g, p) = [g, p]`, some linear isomorphism `T : T_{[1, 0]} Y ≃ T_x M`

* takes `ω` at `[1, 0]` to `σ_x`;
* intertwines the differential at `[1, 0]` of `y ↦ k • y` with `dk_x`, for each `k ∈ G_x`;
* sends `dπ_(1, 0, 0) (ξ, 0)` to the fundamental vector `ξ_M(x)`, for each `ξ ∈ 𝔤`. -/
theorem exists_linearEquiv_tangentSpace_ofPoint :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    let D := ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I
      𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
      (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∃ T : TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
          ((0 : A), (0 : V))) ≃ₗ[ℝ] TangentSpace I' x,
      (∀ u v, SmoothBundleForm.eval₂ σ x (T u) (T v) =
        SmoothBundleForm.eval₂ D.descendedForm
          (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
            ((0 : A), (0 : V))) u v) ∧
      (∀ (k : stabilizer G x) u,
        T (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
          𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
          (fun y : BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V) ↦
            (k : G) • y)
          (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
            ((0 : A), (0 : V))) u) =
          tangentRepresentation (fun (g : G) _ ↦
            ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g x) k
            (T u)) ∧
      ∀ ξ : GroupLieAlgebra I G,
        T (D.orbitTangentMap ξ) = InfinitesimalAction.fundamental I G I' M ξ x := by
  intro _ _ _ D
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
    (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
  obtain ⟨e, he, he𝔪, he𝔮, -, hek⟩ :=
    hσ.exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_symplecticSlice hσG
      (hμ.momentCocycle_eq_zero x) (isCompact_iff_compactSpace.2 ‹_›) h𝔪 h𝔪' h𝔮
  -- `D`'s model `(𝔪 × 𝔪*) × (𝔮 × V)` is Tau Ceti's with the symplectic slice read on `V`.
  let ψ : ((D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V)) ≃ₗ[ℝ]
      ((𝔪.toSubmodule × Module.Dual ℝ 𝔪.toSubmodule) ×
        (𝔮.toSubmodule × hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x)) :=
    (LinearEquiv.refl ℝ _).prodCongr ((LinearEquiv.refl ℝ _).prodCongr eV)
  have hψ (m f q b) : ψ ((m, f), (q, b)) = ((m, f), (q, eV b)) := rfl
  refine ⟨D.linearModelEquiv.symm ≪≫ₗ ψ ≪≫ₗ e, fun u v ↦ ?_, fun k u ↦ ?_, fun ξ ↦ ?_⟩
  · obtain ⟨y₁, rfl⟩ := D.linearModelEquiv.surjective u
    obtain ⟨y₂, rfl⟩ := D.linearModelEquiv.surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    refine (hσ.symplecticFormAt_apply x _ _).symm.trans ((he.apply _ _).trans ?_)
    rw [eval₂_descendedForm_linearModelEquiv]
    obtain ⟨⟨m₁, f₁⟩, q₁, b₁⟩ := y₁
    obtain ⟨⟨m₂, f₂⟩, q₂, b₂⟩ := y₂
    simp only [hψ, SymplecticForm.prod_apply]
    -- `ofPoint` is exposed: the `𝔪`, `𝔮` and `τ` of `D` are those of `x` by definition, and its
    -- form `σ` is the reduced form read through `eV`, so the two sides agree by unfolding `D`.
    rfl
  · obtain ⟨y, rfl⟩ := D.linearModelEquiv.surjective u
    rw [← linearModelEquiv_linearModelRepresentation]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← hek]
    congr 1
    obtain ⟨⟨m, f⟩, q, b⟩ := y
    rw [linearModelRepresentation_apply, hψ, hψ]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · exact Subtype.ext (coe_adjoint𝔪_apply _ k m)
    · -- `D.sub𝔪` is `𝔪` by definition, since `sub𝔪` and `ofPoint` are exposed.
      rw [adjoint𝔪_def]
      rfl
    · exact Subtype.ext (coe_adjoint𝔮_apply _ k q)
    · exact (congrArg eV (repV_apply _ k b)).trans
        (ofPoint_rep_apply hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA k b)
  · -- Write `ξ = h + m + q` with `h ∈ 𝔤_x`, `m ∈ 𝔪` and `q ∈ 𝔮`.
    obtain ⟨κ, hκ, q, hq, rfl⟩ := Submodule.mem_sup.1 (h𝔮.sup_eq_top ▸ Submodule.mem_top (x := ξ))
    obtain ⟨h, hh, m, hm, rfl⟩ := Submodule.mem_sup.1 (h𝔪'.symm ▸ hκ)
    -- The `𝔥` direction is in the kernel of `dπ`, so `dπ (ξ, 0)` is in the image of the model.
    have hm' : m ∈ D.𝔪 := hm
    have hq' : q ∈ D.𝔮 := hq
    rw [← D.linearModelEquiv_mk_zero_mk_zero ⟨m, hm'⟩ ⟨q, hq'⟩
      ((congrArg (· ∈ D.𝔥) (by abel : h + m + q - (m + q) = h)).mpr hh)]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hψ, map_zero]
    -- `e` sends `((m, 0), (q, 0))` to `m_M(x) + q_M(x)`, and `h_M(x) = 0`.
    have he𝔪𝔮 (m' : 𝔪.toSubmodule) (q' : 𝔮.toSubmodule) :
        e ((m', 0), (q', 0)) =
          InfinitesimalAction.fundamental I G I' M (m' + q' : GroupLieAlgebra I G) x := by
      rw [← InfinitesimalAction.eval_apply, map_add, InfinitesimalAction.eval_apply,
        InfinitesimalAction.eval_apply, ← he𝔪, ← he𝔮, ← map_add]
      simp
    refine (he𝔪𝔮 ⟨m, hm⟩ ⟨q, hq⟩).trans ?_
    have h0 : (InfinitesimalAction.fundamental I G I' M).eval x h = 0 :=
      (InfinitesimalAction.eval_apply _ x h).trans ((InfinitesimalAction.mem_isotropy_iff _ x).1 hh)
    rw [← InfinitesimalAction.eval_apply, ← InfinitesimalAction.eval_apply, map_add, map_add,
      map_add, h0, zero_add]

/-- **The fibre directions in `T_x M` are a complement of the orbit.** Let `T` be a linear
isomorphism from the tangent space of the local model `Y = G ×_{G_x} (A × V)` at `[1, 0]` to
`T_x M` that sends `dπ_(1, 0, 0) (ξ, 0)` to the fundamental vector `ξ_M(x)`, for each `ξ ∈ 𝔤`.
Then the image of `p ↦ T (dπ_(1, 0, 0) (0, p))` is a complement in `T_x M` of the tangent space
`𝔤 · x` of the orbit. -/
theorem isCompl_orbitTangent_range_linearEquiv_comp_fiberTangentMap :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    let D := ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I
      𝓘(ℝ, A × V) F
    ∀ T : TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
          ((0 : A), (0 : V))) ≃ₗ[ℝ] TangentSpace I' x,
      (∀ ξ : GroupLieAlgebra I G,
        T (D.orbitTangentMap ξ) = InfinitesimalAction.fundamental I G I' M ξ x) →
      IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)
        (LinearMap.range (T.toLinearMap ∘ₗ D.fiberTangentMap)) := by
  intro _ _ _ D T hT
  rw [InfinitesimalAction.orbitTangent_eq_range]
  exact D.isCompl_range_range_comp_fiberTangentMap T _
    (LinearMap.ext fun ξ ↦ (hT ξ).trans (InfinitesimalAction.eval_apply _ x ξ).symm)

end LocalModelData

end SymplecticGeometry

end
