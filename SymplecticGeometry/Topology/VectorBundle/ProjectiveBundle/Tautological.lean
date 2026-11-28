/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Subbundle
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.OfBundle
public import SymplecticGeometry.Topology.Algebra.Module.Equiv.Submodule
public import SymplecticGeometry.Topology.VectorBundle.ProjectiveBundle.Basic
public import SymplecticGeometry.LinearAlgebra.Projectivization.Basic
import SymplecticGeometry.Topology.Algebra.Projectivization
import SymplecticGeometry.Topology.VectorBundle.Basic

/-!
# Tautological lines

For a topological vector space `V` over a nontrivially normed field `𝕜`, the tautological line
`Projectivization.Tautological 𝕜 V` over the projective space `ℙ 𝕜 V` has the line `ℓ` itself as
its fibre over `ℓ`. Its total space is a subspace of `ℙ 𝕜 V × V`. A continuous linear form `φ`
trivializes it over the open set of lines on which `φ` does not vanish, by `v ↦ φ v`; the inverse
sends `t` to `t` times the representative of `ℓ` on which `φ` is `1`
(`Projectivization.normalizedRep`), which depends continuously on `ℓ`. When continuous linear forms
separate points, every line has such a form, and these trivializations make the tautological line a
vector bundle with model fibre `𝕜`. The complement of its zero section is the space of nonzero
vectors of `V` (`Projectivization.tautologicalComplZeroHomeomorph`). An injective linear map
`f : V → W` maps each line `ℓ` isomorphically onto the line `map f ℓ`, so the tautological line
of `ℙ 𝕜 V` is the pull-back of that of `ℙ 𝕜 W` along `map f`
(`Projectivization.tautologicalMapEquiv`), by an isomorphism that is continuous on total spaces
when `f` is continuous.

For a vector bundle `E → B` with model fibre `G`, the tautological line
`SymplecticGeometry.Bundle.ProjectiveBundle.Tautological 𝕜 G E` over the projective bundle has the
line `p ⊆ E b` itself as its fibre over `p`. Its total space is a subspace of the pull-back of `E`
along the projection (`ProjectiveBundle.isEmbedding_tautologicalInclusion`). It is trivialized in
the same way, a trivialization `e` of `E` reading the line `p` as a line of `G`. Its restriction to
the fibre over `b` is the tautological line of `ℙ 𝕜 (E b)`, and its pull-backs along
`ProjectiveBundle.map`, `ProjectiveBundle.pullbackMap`, `ProjectiveBundle.inl` and
`ProjectiveBundle.inr` are the tautological lines of their sources, by fibrewise isomorphisms that
are continuous on total spaces.

Tau Ceti has two line bundles of the same kind, and neither serves here. Its
`Projectivization.twistCore (-1)` is the bundle `𝒪(-1)` on `ℙ 𝕜 (Fin (n + 1) → 𝕜)` given by its
transition functions: its fibres are copies of `𝕜`, not the lines, so it is not a subbundle of a
pull-back of `E`, and it is defined only on coordinate projective spaces. Its
`finiteGrassmannian.Tautological 𝕜 1 N` has the lines as fibres, but lives on the Grassmannian of
lines of `Fin N → 𝕜`, with model fibre `Fin 1 → 𝕜` and for `RCLike 𝕜`, while the fibres
`ℙ 𝕜 (E b)` of a projective bundle need `ℙ 𝕜 V` for every `V`. On `ℙ 𝕜 (Fin (n + 1) → 𝕜)` both
are isomorphic to `Projectivization.Tautological`; this file does not use or prove that.

The topology of the tautological line over the projective bundle is Tau Ceti's
`TauCeti.subbundleTopology` of the family of lines in the fibres of the pull-back of `E`, and its
embedding and the topology of its fibres come from `TauCeti.isEmbedding_totalSpace_subbundle` and
`TauCeti.isInducing_totalSpaceMk_subbundle`. Its trivializations are built here, since Tau Ceti's
`TauCeti.HasLocalSubbundleFrames.vectorBundle` is stated for `IsRCLikeNormedField 𝕜`, with model
fibre `ι → 𝕜` rather than `𝕜`.

## Main definitions

* `Projectivization.Tautological 𝕜 V`: the tautological line over `ℙ 𝕜 V`, with its trivializations
  `Projectivization.tautologicalTrivialization` and its `FiberBundle` and `VectorBundle`
  instances.
* `Projectivization.toTautological`: the isomorphism `z ↦ z • v` from `𝕜` onto the fibre over a
  line spanned by a nonzero vector `v`.
* `Projectivization.tautologicalCore 𝕜 V`: the tautological line as a finite-rank core of rank
  one, through `TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEq`.
* `Projectivization.tautologicalComplZeroHomeomorph`: the complement of the zero section is
  homeomorphic to the nonzero vectors of `V`.
* `Projectivization.tautologicalMapEquiv`: the restriction of an injective linear map to the
  lines, a fibrewise isomorphism over `Projectivization.map`.
* `Projectivization.tautologicalMapProjectivizationEquiv`: the restriction of a continuous
  linear equivalence to the lines, a fibrewise isomorphism over
  `ContinuousLinearEquiv.mapProjectivization`.
* `SymplecticGeometry.Bundle.ProjectiveBundle.Tautological 𝕜 G E`: the tautological line over the
  projective bundle, with its trivializations `ProjectiveBundle.tautologicalTrivialization` and
  its `FiberBundle` and `VectorBundle` instances.
* `ProjectiveBundle.tautologicalInclusion`: its inclusion into the pull-back of `E`.
* `ProjectiveBundle.tautologicalFiberHomeomorph`: its restriction to a fibre is the tautological
  line of `ℙ 𝕜 (E b)`.
* `ProjectiveBundle.tautologicalMapEquiv`, `ProjectiveBundle.tautologicalPullbackHomeomorph`,
  `ProjectiveBundle.tautologicalInlEquiv`, `ProjectiveBundle.tautologicalInrEquiv`: its pull-backs
  along the maps of projective bundles of `ProjectiveBundle/Basic.lean`.

## Main results

* `ProjectiveBundle.isEmbedding_tautologicalInclusion`: the tautological line is a subspace of the
  pull-back of `E`.
* `Projectivization.continuous_tautologicalMapEquiv`,
  `ProjectiveBundle.continuous_tautologicalMapEquiv`,
  `ProjectiveBundle.continuous_tautologicalInlEquiv`,
  `ProjectiveBundle.continuous_tautologicalInrEquiv`: the fibrewise isomorphisms are continuous on
  total spaces.

## Implementation notes

Both tautological lines carry the subspace topology, so that a map into their total spaces is
continuous as soon as its base point and its vector are
(`Projectivization.continuous_totalSpace_tautological_iff`,
`ProjectiveBundle.continuous_totalSpace_tautological_iff`). The scalars are any nontrivially normed
field, and the `FiberBundle` instances assume `SeparatingDual 𝕜 V` or `SeparatingDual 𝕜 G`. Mathlib
has this instance for normed spaces over `RCLike 𝕜`, which covers `G` over `ℝ` and `ℂ`, and for
locally convex T1 spaces over `ℝ`. For a fibre `E b` of a vector bundle, which has no norm, it must
be supplied. The pull-backs along `ProjectiveBundle.map`, `ProjectiveBundle.inl` and
`ProjectiveBundle.inr` have the lines of the target as fibres by definition, which is why these
maps, `ProjectiveBundle.projection` and `ProjectiveBundle.pullbackMap` are `@[expose]`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the
  tautological subbundle of the pull-back of a vector bundle to its projective bundle).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §2 (the canonical line bundle over a projective space).
-/

public section

noncomputable section

open Bundle Set Topology
open TauCeti (zeroSectionCompl mem_zeroSectionCompl)
open scoped LinearAlgebra.Projectivization

namespace Projectivization

/-! ### The tautological line over a projective space -/

section Tautological

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (V : Type*) [AddCommGroup V] [Module 𝕜 V]

/-- The tautological line over the projective space `ℙ 𝕜 V`: its fibre over a point `ℓ` is the
line `ℓ` itself, as a subspace of `V`. -/
abbrev Tautological : ℙ 𝕜 V → Type _ := fun ℓ ↦ ℓ.submodule

/-- A vector of the tautological line as a point of `ℙ 𝕜 V × V`. -/
def tautologicalToProd (v : TotalSpace 𝕜 (Tautological 𝕜 V)) : ℙ 𝕜 V × V :=
  (v.proj, v.snd)

@[simp]
theorem tautologicalToProd_apply (v : TotalSpace 𝕜 (Tautological 𝕜 V)) :
    tautologicalToProd 𝕜 V v = (v.proj, (v.snd : V)) :=
  (rfl)

variable {𝕜 V} in
/-- For a nonzero vector `v` spanning the line `ℓ`, the linear isomorphism `z ↦ z • v` from `𝕜`
onto the fibre of the tautological line over `ℓ`. -/
def toTautological {ℓ : ℙ 𝕜 V} {v : V} (hv : v ≠ 0) (h : ℓ.submodule = 𝕜 ∙ v) :
    𝕜 ≃ₗ[𝕜] Tautological 𝕜 V ℓ :=
  LinearEquiv.toSpanNonzeroSingleton 𝕜 V v hv ≪≫ₗ LinearEquiv.ofEq _ _ h.symm

variable {𝕜 V} in
theorem toTautological_def {ℓ : ℙ 𝕜 V} {v : V} (hv : v ≠ 0) (h : ℓ.submodule = 𝕜 ∙ v) :
    toTautological hv h =
      LinearEquiv.toSpanNonzeroSingleton 𝕜 V v hv ≪≫ₗ LinearEquiv.ofEq _ _ h.symm :=
  (rfl)

variable {𝕜 V} in
@[simp]
theorem coe_toTautological_apply {ℓ : ℙ 𝕜 V} {v : V} (hv : v ≠ 0) (h : ℓ.submodule = 𝕜 ∙ v)
    (z : 𝕜) : (toTautological hv h z : V) = z • v :=
  (rfl)

variable [TopologicalSpace V]

/-- The total space of the tautological line carries the topology of a subspace of
`ℙ 𝕜 V × V`. -/
instance : TopologicalSpace (TotalSpace 𝕜 (Tautological 𝕜 V)) :=
  .induced (tautologicalToProd 𝕜 V) inferInstance

theorem isEmbedding_tautologicalToProd : IsEmbedding (tautologicalToProd 𝕜 V) := by
  refine ⟨⟨rfl⟩, ?_⟩
  rintro ⟨ℓ, v⟩ ⟨ℓ', v'⟩ h
  simp only [tautologicalToProd_apply, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  exact congrArg (TotalSpace.mk ℓ) (Subtype.ext h)

variable {𝕜 V} in
/-- A map into the total space of the tautological line is continuous if and only if its base
point and its vector are. -/
theorem continuous_totalSpace_tautological_iff {X : Type*} [TopologicalSpace X]
    {g : X → TotalSpace 𝕜 (Tautological 𝕜 V)} :
    Continuous g ↔ Continuous (fun x ↦ (g x).proj) ∧ Continuous (fun x ↦ ((g x).snd : V)) :=
  (isEmbedding_tautologicalToProd 𝕜 V).isInducing.continuous_iff.trans continuous_prodMk

theorem continuous_proj_tautological : Continuous (π 𝕜 (Tautological 𝕜 V)) :=
  (continuous_totalSpace_tautological_iff.1 continuous_id).1

theorem continuous_snd_tautological :
    Continuous fun v : TotalSpace 𝕜 (Tautological 𝕜 V) ↦ (v.snd : V) :=
  (continuous_totalSpace_tautological_iff.1 continuous_id).2

/-- The complement of the zero section of the tautological line is homeomorphic to the nonzero
vectors of `V`, by `(ℓ, v) ↦ v`; the inverse sends `v` to `([v], v)`. -/
def tautologicalComplZeroHomeomorph :
    zeroSectionCompl 𝕜 (Tautological 𝕜 V) ≃ₜ {v : V // v ≠ 0} where
  toFun v := ⟨v.val.snd, fun h ↦ mem_zeroSectionCompl.1 v.property (Subtype.ext h)⟩
  invFun v := ⟨⟨mk 𝕜 v.val v.property, ⟨v.val, mem_submodule_iff.2 fun _ ↦ rfl⟩⟩,
    mem_zeroSectionCompl.2 fun h ↦ v.property (congrArg Subtype.val h)⟩
  left_inv := by
    rintro ⟨⟨ℓ, v, hv⟩, h₀⟩
    have hv₀ : v ≠ 0 := fun h ↦ mem_zeroSectionCompl.1 h₀ (Subtype.ext h)
    obtain rfl := mem_submodule_iff.1 hv hv₀
    rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_snd_tautological 𝕜 V).comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_totalSpace_tautological_iff.2 ⟨?_, ?_⟩) _
    · exact continuous_mk'
    · exact continuous_subtypeVal

variable {V} in
@[simp]
theorem coe_tautologicalComplZeroHomeomorph_apply
    (v : zeroSectionCompl 𝕜 (Tautological 𝕜 V)) :
    (tautologicalComplZeroHomeomorph 𝕜 V v : V) = v.val.snd :=
  (rfl)

variable {V} in
@[simp]
theorem tautologicalComplZeroHomeomorph_symm_apply (v : {v : V // v ≠ 0}) :
    ((tautologicalComplZeroHomeomorph 𝕜 V).symm v).val =
      ⟨mk 𝕜 v.val v.property, ⟨v.val, mem_submodule_iff.2 fun _ ↦ rfl⟩⟩ :=
  (rfl)

variable {V} [SeparatingDual 𝕜 V] in
/-- A continuous linear form not vanishing on the line `ℓ`. -/
def tautologicalForm (ℓ : ℙ 𝕜 V) : V →L[𝕜] 𝕜 :=
  (SeparatingDual.exists_ne_zero (R := 𝕜) ℓ.rep_ne_zero).choose

variable {V} [SeparatingDual 𝕜 V] in
theorem mem_linearProjectionDomain_tautologicalForm (ℓ : ℙ 𝕜 V) :
    ℓ ∈ linearProjectionDomain (tautologicalForm 𝕜 ℓ : V →ₗ[𝕜] 𝕜) :=
  (mem_linearProjectionDomain_iff _).2
    (SeparatingDual.exists_ne_zero (R := 𝕜) ℓ.rep_ne_zero).choose_spec

variable [ContinuousSMul 𝕜 V]

/-- The trivialization of the tautological line over the open set of the lines on which a
continuous linear form `φ` does not vanish: it sends a vector `v ∈ ℓ` to `(ℓ, φ v)`. -/
def tautologicalTrivialization (φ : V →L[𝕜] 𝕜) : Trivialization 𝕜 (π 𝕜 (Tautological 𝕜 V)) where
  toFun v := (v.proj, φ v.snd)
  invFun q := ⟨q.1, ⟨q.2 • normalizedRep (φ : V →ₗ[𝕜] 𝕜) q.1,
    Submodule.smul_mem _ _ (normalizedRep_mem_submodule _ _)⟩⟩
  source := π 𝕜 (Tautological 𝕜 V) ⁻¹' linearProjectionDomain (φ : V →ₗ[𝕜] 𝕜)
  target := linearProjectionDomain (φ : V →ₗ[𝕜] 𝕜) ×ˢ univ
  map_source' _ hv := ⟨hv, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' := by
    rintro ⟨ℓ, v⟩ hv
    exact congrArg (TotalSpace.mk ℓ) (Subtype.ext (apply_smul_normalizedRep hv v.property))
  right_inv' := by
    rintro ⟨ℓ, t⟩ hq
    simp only [map_smul, smul_eq_mul]
    rw [← ContinuousLinearMap.coe_coe φ, apply_normalizedRep hq.1, mul_one]
  open_source := (isOpen_linearProjectionDomain φ.continuous).preimage
    (continuous_proj_tautological 𝕜 V)
  open_target := (isOpen_linearProjectionDomain φ.continuous).prod isOpen_univ
  continuousOn_toFun := ((continuous_proj_tautological 𝕜 V).prodMk
    (φ.continuous.comp (continuous_snd_tautological 𝕜 V))).continuousOn
  continuousOn_invFun := by
    rw [(isEmbedding_tautologicalToProd 𝕜 V).isInducing.continuousOn_iff]
    exact continuousOn_fst.prodMk (continuousOn_snd.smul
      ((continuousOn_normalizedRep φ.continuous).comp continuousOn_fst fun _ hq ↦ hq.1))
  baseSet := linearProjectionDomain (φ : V →ₗ[𝕜] 𝕜)
  open_baseSet := isOpen_linearProjectionDomain φ.continuous
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable {V}

@[simp]
theorem tautologicalTrivialization_baseSet (φ : V →L[𝕜] 𝕜) :
    (tautologicalTrivialization 𝕜 V φ).baseSet = linearProjectionDomain (φ : V →ₗ[𝕜] 𝕜) :=
  (rfl)

@[simp]
theorem tautologicalTrivialization_apply (φ : V →L[𝕜] 𝕜) (v : TotalSpace 𝕜 (Tautological 𝕜 V)) :
    tautologicalTrivialization 𝕜 V φ v = (v.proj, φ v.snd) :=
  (rfl)

theorem tautologicalTrivialization_symm_apply (φ : V →L[𝕜] 𝕜) (q : ℙ 𝕜 V × 𝕜) :
    (tautologicalTrivialization 𝕜 V φ).toOpenPartialHomeomorph.symm q =
      ⟨q.1, ⟨q.2 • normalizedRep (φ : V →ₗ[𝕜] 𝕜) q.1,
        Submodule.smul_mem _ _ (normalizedRep_mem_submodule _ _)⟩⟩ :=
  (rfl)

/-- The inverse of the trivialization `tautologicalTrivialization 𝕜 V φ` on the fibre over `ℓ`
sends `t` to `t` times the representative of `ℓ` normalized by `φ`. -/
theorem coe_tautologicalTrivialization_symm (φ : V →L[𝕜] 𝕜) {ℓ : ℙ 𝕜 V}
    (hℓ : ℓ ∈ linearProjectionDomain (φ : V →ₗ[𝕜] 𝕜)) (t : 𝕜) :
    ((tautologicalTrivialization 𝕜 V φ).symm ℓ t : V) =
      t • normalizedRep (φ : V →ₗ[𝕜] 𝕜) ℓ := by
  have h := (tautologicalTrivialization 𝕜 V φ).mk_symm hℓ t
  rw [tautologicalTrivialization_symm_apply] at h
  exact congrArg Subtype.val (eq_of_heq (TotalSpace.mk.inj h).2)

instance (φ : V →L[𝕜] 𝕜) : (tautologicalTrivialization 𝕜 V φ).IsLinear 𝕜 where
  linear _ _ :=
    { map_add := fun v w ↦ by simp
      map_smul := fun c v ↦ by simp }

variable [SeparatingDual 𝕜 V]

/-- The tautological line is a fibre bundle with model fibre `𝕜`, trivialized over the lines on
which a continuous linear form does not vanish. -/
instance : FiberBundle 𝕜 (Tautological 𝕜 V) where
  totalSpaceMk_isInducing' ℓ := by
    rw [← (isEmbedding_tautologicalToProd 𝕜 V).isInducing.of_comp_iff]
    exact isInducing_const_prod.2 IsInducing.subtypeVal
  trivializationAtlas' := range (tautologicalTrivialization 𝕜 V)
  trivializationAt' ℓ := tautologicalTrivialization 𝕜 V (tautologicalForm 𝕜 ℓ)
  mem_baseSet_trivializationAt' ℓ := by
    rw [tautologicalTrivialization_baseSet]
    exact mem_linearProjectionDomain_tautologicalForm 𝕜 ℓ
  trivialization_mem_atlas' _ := mem_range_self _

theorem trivializationAt_tautological (ℓ : ℙ 𝕜 V) :
    trivializationAt 𝕜 (Tautological 𝕜 V) ℓ =
      tautologicalTrivialization 𝕜 V (tautologicalForm 𝕜 ℓ) :=
  (rfl)

theorem mem_trivializationAtlas_tautological_iff (e : Trivialization 𝕜 (π 𝕜 (Tautological 𝕜 V))) :
    e ∈ trivializationAtlas 𝕜 (Tautological 𝕜 V) ↔ ∃ φ, tautologicalTrivialization 𝕜 V φ = e :=
  Iff.rfl

/-- The tautological line over `ℙ 𝕜 V` is a vector bundle with model fibre `𝕜`. -/
instance : VectorBundle 𝕜 𝕜 (Tautological 𝕜 V) where
  trivialization_linear' e he := by
    obtain ⟨φ, rfl⟩ := (mem_trivializationAtlas_tautological_iff 𝕜 e).1 he.out
    infer_instance
  continuousOn_coordChange' e e' he he' := by
    obtain ⟨φ, rfl⟩ := (mem_trivializationAtlas_tautological_iff 𝕜 e).1 he.out
    obtain ⟨ψ, rfl⟩ := (mem_trivializationAtlas_tautological_iff 𝕜 e').1 he'.out
    refine ContinuousOn.congr (f := fun ℓ ↦ ψ (normalizedRep (φ : V →ₗ[𝕜] 𝕜) ℓ) •
      ContinuousLinearMap.id 𝕜 𝕜) (((ψ.continuous.comp_continuousOn
        (continuousOn_normalizedRep φ.continuous)).mono inter_subset_left).smul
          continuousOn_const) fun ℓ hℓ ↦ ?_
    refine ContinuousLinearMap.ext_ring ?_
    rw [ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply' _ _ hℓ,
      tautologicalTrivialization_symm_apply]
    simp [mul_comm]

variable (V) [CompleteSpace 𝕜]

/-- The tautological line of `ℙ 𝕜 V`, whose fibre over a point is the line itself, as a
finite-rank core of rank one. -/
-- Expose the rank so that the fibre model reduces to `Fin 1 → 𝕜`.
@[expose, implicit_reducible]
def tautologicalCore : TauCeti.FiniteRankBundleCore 𝕜 (ℙ 𝕜 V) :=
  TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEq 𝕜 𝕜 (Tautological 𝕜 V) (Module.finrank_self 𝕜)

theorem tautologicalCore_def : tautologicalCore 𝕜 V =
    TauCeti.FiniteRankBundleCore.ofBundleOfFinrankEq 𝕜 𝕜 (Tautological 𝕜 V)
      (Module.finrank_self 𝕜) :=
  (rfl)

@[simp]
theorem rank_tautologicalCore : (tautologicalCore 𝕜 V).rank = 1 :=
  (rfl)

end Tautological

/-! ### Restriction of a continuous linear equivalence -/

section MapProjectivizationEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  {W : Type*} [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W]

/-- A continuous linear equivalence `e : V ≃L[𝕜] W` restricts to an isomorphism of the line `ℓ`
onto the line `e.mapProjectivization ℓ`: the fibrewise isomorphism of the tautological line of
`ℙ 𝕜 V` with the pull-back of that of `ℙ 𝕜 W` along the homeomorphism `e.mapProjectivization`. -/
def tautologicalMapProjectivizationEquiv (e : V ≃L[𝕜] W) (ℓ : ℙ 𝕜 V) :
    Tautological 𝕜 V ℓ ≃L[𝕜] Tautological 𝕜 W (e.mapProjectivization ℓ) :=
  e.ofSubmodules ℓ.submodule (e.mapProjectivization ℓ).submodule
    (e.submodule_mapProjectivization ℓ).symm

@[simp]
theorem coe_tautologicalMapProjectivizationEquiv_apply (e : V ≃L[𝕜] W) (ℓ : ℙ 𝕜 V)
    (v : Tautological 𝕜 V ℓ) : (tautologicalMapProjectivizationEquiv e ℓ v : W) = e v :=
  (rfl)

end MapProjectivizationEquiv

/-! ### Pull-backs along maps of projective spaces -/

section Map

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V]
  {W : Type*} [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕜 W] [T2Space W]
  (f : V →ₗ[𝕜] W) (hf : Function.Injective f)

/-- An injective linear map `f : V → W` restricts to an isomorphism of the line `ℓ` onto the line
`map f ℓ`: the fibrewise isomorphism of the tautological line of `ℙ 𝕜 V` with the pull-back of
that of `ℙ 𝕜 W` along `map f`. -/
noncomputable def tautologicalMapEquiv (ℓ : ℙ 𝕜 V) :
    Tautological 𝕜 V ℓ ≃L[𝕜] Tautological 𝕜 W (map f hf ℓ) :=
  ((Submodule.equivMapOfInjective f hf ℓ.submodule).trans
    (LinearEquiv.ofEq _ _ (submodule_map f hf ℓ).symm)).toContinuousLinearEquiv

@[simp]
theorem coe_tautologicalMapEquiv_apply (ℓ : ℙ 𝕜 V) (v : Tautological 𝕜 V ℓ) :
    (tautologicalMapEquiv f hf ℓ v : W) = f v :=
  (rfl)

/-- The fibrewise isomorphism `tautologicalMapEquiv` is continuous on total spaces, over the
continuous map `map f` of projective spaces, when `f` is continuous. -/
theorem continuous_tautologicalMapEquiv (hfc : Continuous f) :
    Continuous fun v : TotalSpace 𝕜 (Tautological 𝕜 V) ↦
      TotalSpace.mk' 𝕜 (E := Tautological 𝕜 W) (map f hf v.proj)
        (tautologicalMapEquiv f hf v.proj v.snd) :=
  continuous_totalSpace_tautological_iff.2
    ⟨(continuous_map hf hfc).comp (continuous_proj_tautological 𝕜 V),
      hfc.comp (continuous_snd_tautological 𝕜 V)⟩

end Map

end Projectivization

/-! ### The tautological line over a projective bundle -/

namespace SymplecticGeometry.Bundle

namespace ProjectiveBundle

open Projectivization

variable {𝕜 : Type*} {B : Type*} [NontriviallyNormedField 𝕜]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {E : B → Type*} [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]

variable (𝕜 G E) in
/-- The tautological line over the projective bundle of `E`: its fibre over a line `p ⊆ E b` is
the line `p` itself, as a subspace of `E b`. -/
abbrev Tautological : ProjectiveBundle 𝕜 G E → Type _ := fun p ↦ p.snd.submodule

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace G E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle G E] [VectorBundle 𝕜 G E]

/-- The total space of the tautological line carries the topology of a subspace of the pull-back
of `E` along the projection of the projective bundle, Tau Ceti's `TauCeti.subbundleTopology` of
the family of lines `p ↦ p.snd.submodule` of the fibres of that pull-back. -/
instance : TopologicalSpace (TotalSpace 𝕜 (Tautological 𝕜 G E)) :=
  TauCeti.subbundleTopology G (E := projection 𝕜 G E *ᵖ E) (F' := 𝕜) fun p ↦ p.snd.submodule

variable (𝕜 G E) in
/-- The inclusion of the tautological line into the pull-back of `E` along the projection of the
projective bundle: a vector `v` of the line `p` goes to `v`, as a vector of `E` over `p`. -/
def tautologicalInclusion :
    C(TotalSpace 𝕜 (Tautological 𝕜 G E), TotalSpace G (projection 𝕜 G E *ᵖ E)) where
  toFun v := ⟨v.proj, (v.snd : E v.proj.proj)⟩
  continuous_toFun := IsEmbedding.continuous (X := TotalSpace 𝕜 (Tautological 𝕜 G E))
    (TauCeti.isEmbedding_totalSpace_subbundle G 𝕜 (E := projection 𝕜 G E *ᵖ E)
      fun p ↦ p.snd.submodule)

@[simp]
theorem tautologicalInclusion_apply (v : TotalSpace 𝕜 (Tautological 𝕜 G E)) :
    tautologicalInclusion 𝕜 G E v = ⟨v.proj, (v.snd : E v.proj.proj)⟩ :=
  (rfl)

variable (𝕜 G E) in
/-- The tautological line is a subspace of the pull-back of `E` to the projective bundle. -/
theorem isEmbedding_tautologicalInclusion : IsEmbedding (tautologicalInclusion 𝕜 G E) :=
  TauCeti.isEmbedding_totalSpace_subbundle G 𝕜 (E := projection 𝕜 G E *ᵖ E)
    fun p ↦ p.snd.submodule

/-- A map into the total space of the tautological line over the projective bundle is continuous
if and only if its base point and its vector, as a vector of `E`, are. -/
theorem continuous_totalSpace_tautological_iff {X : Type*} [TopologicalSpace X]
    {g : X → TotalSpace 𝕜 (Tautological 𝕜 G E)} :
    Continuous g ↔ Continuous (fun x ↦ (g x).proj) ∧
      Continuous (fun x ↦ (⟨(g x).proj.proj, (g x).snd⟩ : TotalSpace G E)) :=
  (isEmbedding_tautologicalInclusion 𝕜 G E).isInducing.continuous_iff.trans Pullback.continuous_iff

/-- A map into the total space of the tautological line over the projective bundle is continuous
on a set if and only if its base point and its vector, as a vector of `E`, are. -/
theorem continuousOn_totalSpace_tautological_iff {X : Type*} [TopologicalSpace X]
    {g : X → TotalSpace 𝕜 (Tautological 𝕜 G E)} {s : Set X} :
    ContinuousOn g s ↔ ContinuousOn (fun x ↦ (g x).proj) s ∧
      ContinuousOn (fun x ↦ (⟨(g x).proj.proj, (g x).snd⟩ : TotalSpace G E)) s := by
  simp only [continuousOn_iff_continuous_domRestrict]
  exact continuous_totalSpace_tautological_iff

variable (𝕜 G E) in
theorem continuous_proj_tautological : Continuous (π 𝕜 (Tautological 𝕜 G E)) :=
  (continuous_totalSpace_tautological_iff.1 continuous_id).1

variable (𝕜 G E) in
theorem continuous_toTotalSpace_tautological :
    Continuous fun v : TotalSpace 𝕜 (Tautological 𝕜 G E) ↦
      (⟨v.proj.proj, v.snd⟩ : TotalSpace G E) :=
  (continuous_totalSpace_tautological_iff.1 continuous_id).2

variable (𝕜 G E) in
/-- The lines `p` over the base set of the trivialization `e` of `E` at `b₀` whose image `e p`
does not lie in the kernel of the linear form `φ`. -/
def tautologicalBaseSet (b₀ : B) (φ : G →L[𝕜] 𝕜) : Set (ProjectiveBundle 𝕜 G E) :=
  {p | p.proj ∈ (trivializationAt G E b₀).baseSet ∧
    (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b₀ p).2 ∈
      linearProjectionDomain (φ : G →ₗ[𝕜] 𝕜)}

theorem mem_tautologicalBaseSet_iff {b₀ : B} {φ : G →L[𝕜] 𝕜} {p : ProjectiveBundle 𝕜 G E} :
    p ∈ tautologicalBaseSet 𝕜 G E b₀ φ ↔ p.proj ∈ (trivializationAt G E b₀).baseSet ∧
      (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b₀ p).2 ∈
        linearProjectionDomain (φ : G →ₗ[𝕜] 𝕜) :=
  Iff.rfl

theorem isOpen_tautologicalBaseSet (b₀ : B) (φ : G →L[𝕜] 𝕜) :
    IsOpen (tautologicalBaseSet 𝕜 G E b₀ φ) := by
  convert (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b₀).isOpen_inter_preimage
    (isOpen_univ.prod (isOpen_linearProjectionDomain φ.continuous)) using 1
  ext p
  simp [mem_tautologicalBaseSet_iff, Trivialization.mem_source, trivializationAt_baseSet]

theorem continuousOn_normalizedRep_trivializationAt (b₀ : B) (φ : G →L[𝕜] 𝕜) :
    ContinuousOn (fun p : ProjectiveBundle 𝕜 G E ↦ normalizedRep (φ : G →ₗ[𝕜] 𝕜)
      (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b₀ p).2) (tautologicalBaseSet 𝕜 G E b₀ φ) :=
  (continuousOn_normalizedRep φ.continuous).comp (continuous_snd.comp_continuousOn
    ((trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b₀).continuousOn.mono fun p hp ↦
      by rw [Trivialization.mem_source, trivializationAt_baseSet]; exact hp.1))
    fun _ hp ↦ hp.2

variable (𝕜 G E) in
/-- The trivialization of the tautological line over the projective bundle given by the
trivialization `e` of `E` at `b₀` and a continuous linear form `φ` on `G`: over
`tautologicalBaseSet 𝕜 G E b₀ φ`, it sends a vector `v ∈ p` to `(p, φ (e v))`. -/
def tautologicalTrivialization (b₀ : B) (φ : G →L[𝕜] 𝕜) :
    Trivialization 𝕜 (π 𝕜 (Tautological 𝕜 G E)) where
  toFun v := (v.proj, φ (trivializationAt G E b₀ ⟨v.proj.proj, v.snd⟩).2)
  invFun q := ⟨q.1, ⟨(trivializationAt G E b₀).symmL 𝕜 q.1.proj (q.2 • normalizedRep
      (φ : G →ₗ[𝕜] 𝕜) (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b₀ q.1).2),
    symmL_mem_submodule (Submodule.smul_mem _ _ (normalizedRep_mem_submodule _ _))⟩⟩
  source := π 𝕜 (Tautological 𝕜 G E) ⁻¹' tautologicalBaseSet 𝕜 G E b₀ φ
  target := tautologicalBaseSet 𝕜 G E b₀ φ ×ˢ univ
  map_source' _ hv := ⟨hv, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' := by
    rintro ⟨p, v⟩ hpv
    obtain ⟨hp, hpφ⟩ : p ∈ tautologicalBaseSet 𝕜 G E b₀ φ := hpv
    refine congrArg (TotalSpace.mk p) (Subtype.ext ?_)
    simp only
    rw [← ContinuousLinearMap.coe_coe φ,
      apply_smul_normalizedRep hpφ (trivializationAt_mem_submodule hp v.property),
      Trivialization.symmL_apply _ hp, Trivialization.symm_apply_apply_mk _ hp]
  right_inv' := by
    rintro ⟨p, t⟩ hpt
    obtain ⟨hp, hpφ⟩ : p ∈ tautologicalBaseSet 𝕜 G E b₀ φ := hpt.1
    simp only
    rw [Trivialization.symmL_apply _ hp, Trivialization.apply_mk_symm _ hp, map_smul, smul_eq_mul,
      ← ContinuousLinearMap.coe_coe φ, apply_normalizedRep hpφ, mul_one]
  open_source := (isOpen_tautologicalBaseSet b₀ φ).preimage (continuous_proj_tautological 𝕜 G E)
  open_target := (isOpen_tautologicalBaseSet b₀ φ).prod isOpen_univ
  continuousOn_toFun := by
    refine (continuous_proj_tautological 𝕜 G E).continuousOn.prodMk ?_
    refine φ.continuous.comp_continuousOn (continuous_snd.comp_continuousOn
      ((trivializationAt G E b₀).continuousOn.comp
        (continuous_toTotalSpace_tautological 𝕜 G E).continuousOn fun v hv ↦ ?_))
    exact (trivializationAt G E b₀).mem_source.2 hv.1
  continuousOn_invFun := by
    refine continuousOn_totalSpace_tautological_iff.2 ⟨continuousOn_fst, ?_⟩
    refine ((trivializationAt G E b₀).continuousOn_symm.comp
      (((FiberBundle.continuous_proj _ _).comp continuous_fst).continuousOn.prodMk
        (continuousOn_snd.smul ((continuousOn_normalizedRep_trivializationAt b₀ φ).comp
          continuousOn_fst mapsTo_fst_prod)))
      fun q hq ↦ ⟨hq.1.1, mem_univ _⟩).congr fun q hq ↦ ?_
    simp only [Function.comp_apply, Pi.smul_apply', Trivialization.symmL_apply _ hq.1.1]
  baseSet := tautologicalBaseSet 𝕜 G E b₀ φ
  open_baseSet := isOpen_tautologicalBaseSet b₀ φ
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem tautologicalTrivialization_baseSet (b₀ : B) (φ : G →L[𝕜] 𝕜) :
    (tautologicalTrivialization 𝕜 G E b₀ φ).baseSet = tautologicalBaseSet 𝕜 G E b₀ φ :=
  (rfl)

@[simp]
theorem tautologicalTrivialization_apply (b₀ : B) (φ : G →L[𝕜] 𝕜)
    (v : TotalSpace 𝕜 (Tautological 𝕜 G E)) :
    tautologicalTrivialization 𝕜 G E b₀ φ v =
      (v.proj, φ (trivializationAt G E b₀ ⟨v.proj.proj, v.snd⟩).2) :=
  (rfl)

theorem tautologicalTrivialization_symm_apply (b₀ : B) (φ : G →L[𝕜] 𝕜)
    (q : ProjectiveBundle 𝕜 G E × 𝕜) :
    (tautologicalTrivialization 𝕜 G E b₀ φ).toOpenPartialHomeomorph.symm q =
      ⟨q.1, ⟨(trivializationAt G E b₀).symmL 𝕜 q.1.proj (q.2 • normalizedRep
        (φ : G →ₗ[𝕜] 𝕜) (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b₀ q.1).2),
      symmL_mem_submodule (Submodule.smul_mem _ _ (normalizedRep_mem_submodule _ _))⟩⟩ :=
  (rfl)

/-- The inverse of the trivialization `tautologicalTrivialization 𝕜 G E b₀ φ` on the fibre over a
line `p` of its base set sends `t` to the vector of `E` over `p` whose coordinates in the
trivialization of `E` at `b₀` are `t` times the representative, normalized by `φ`, of the line `p`
read in that trivialization. -/
theorem coe_tautologicalTrivialization_symm (b₀ : B) (φ : G →L[𝕜] 𝕜)
    {p : ProjectiveBundle 𝕜 G E} (hp : p ∈ tautologicalBaseSet 𝕜 G E b₀ φ) (t : 𝕜) :
    ((tautologicalTrivialization 𝕜 G E b₀ φ).symm p t : E p.proj) =
      (trivializationAt G E b₀).symm p.proj (t • normalizedRep (φ : G →ₗ[𝕜] 𝕜)
        (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b₀ p).2) := by
  have h := (tautologicalTrivialization 𝕜 G E b₀ φ).mk_symm hp t
  rw [tautologicalTrivialization_symm_apply] at h
  rw [← Trivialization.symmL_apply (R := 𝕜) _ hp.1]
  exact congrArg Subtype.val (eq_of_heq (TotalSpace.mk.inj h).2)

instance (b₀ : B) (φ : G →L[𝕜] 𝕜) : (tautologicalTrivialization 𝕜 G E b₀ φ).IsLinear 𝕜 where
  linear _ hp :=
    { map_add := fun v w ↦ by
        simp [((trivializationAt G E b₀).linear 𝕜 hp.1).map_add]
      map_smul := fun c v ↦ by
        simp [((trivializationAt G E b₀).linear 𝕜 hp.1).map_smul] }

section FiberBundle

variable [SeparatingDual 𝕜 G]

/-- The tautological line over the projective bundle is a fibre bundle with model fibre `𝕜`. -/
instance : FiberBundle 𝕜 (Tautological 𝕜 G E) where
  totalSpaceMk_isInducing' p := by
    exact TauCeti.isInducing_totalSpaceMk_subbundle G 𝕜 (E := projection 𝕜 G E *ᵖ E)
      (fun p ↦ p.snd.submodule) p
  trivializationAtlas' := range fun q : B × (G →L[𝕜] 𝕜) ↦ tautologicalTrivialization 𝕜 G E q.1 q.2
  trivializationAt' p := tautologicalTrivialization 𝕜 G E p.proj
    (tautologicalForm 𝕜 (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) p.proj p).2)
  mem_baseSet_trivializationAt' p := by
    rw [tautologicalTrivialization_baseSet]
    exact ⟨mem_baseSet_trivializationAt G E p.proj, mem_linearProjectionDomain_tautologicalForm 𝕜 _⟩
  trivialization_mem_atlas' p := mem_range_self (f := fun q : B × (G →L[𝕜] 𝕜) ↦
    tautologicalTrivialization 𝕜 G E q.1 q.2) (p.proj, _)

theorem trivializationAt_tautological (p : ProjectiveBundle 𝕜 G E) :
    trivializationAt 𝕜 (Tautological 𝕜 G E) p = tautologicalTrivialization 𝕜 G E p.proj
      (tautologicalForm 𝕜 (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) p.proj p).2) :=
  (rfl)

theorem mem_trivializationAtlas_tautological_iff
    (e : Trivialization 𝕜 (π 𝕜 (Tautological 𝕜 G E))) :
    e ∈ trivializationAtlas 𝕜 (Tautological 𝕜 G E) ↔
      ∃ b₀ φ, tautologicalTrivialization 𝕜 G E b₀ φ = e :=
  ⟨fun ⟨q, h⟩ ↦ ⟨q.1, q.2, h⟩, fun ⟨b₀, φ, h⟩ ↦ ⟨(b₀, φ), h⟩⟩

/-- The tautological line over the projective bundle is a vector bundle with model fibre `𝕜`. -/
instance : VectorBundle 𝕜 𝕜 (Tautological 𝕜 G E) where
  trivialization_linear' e he := by
    obtain ⟨b₀, φ, rfl⟩ := (mem_trivializationAtlas_tautological_iff e).1 he.out
    infer_instance
  continuousOn_coordChange' e e' he he' := by
    obtain ⟨b₀, φ, rfl⟩ := (mem_trivializationAtlas_tautological_iff e).1 he.out
    obtain ⟨b₁, ψ, rfl⟩ := (mem_trivializationAtlas_tautological_iff e').1 he'.out
    have hc : ContinuousOn (fun p : ProjectiveBundle 𝕜 G E ↦ ψ (trivializationAt G E b₁
        ⟨p.proj, (trivializationAt G E b₀).symm p.proj (normalizedRep (φ : G →ₗ[𝕜] 𝕜)
          (trivializationAt (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b₀ p).2)⟩).2)
        (tautologicalBaseSet 𝕜 G E b₀ φ ∩ tautologicalBaseSet 𝕜 G E b₁ ψ) := by
      refine ψ.continuous.comp_continuousOn (continuous_snd.comp_continuousOn
        ((trivializationAt G E b₁).continuousOn.comp
          ((trivializationAt G E b₀).continuousOn_symm.comp
          ((FiberBundle.continuous_proj _ _).continuousOn.prodMk
            ((continuousOn_normalizedRep_trivializationAt b₀ φ).mono inter_subset_left))
          fun p hp ↦ ⟨hp.1.1, mem_univ _⟩) fun p hp ↦ ?_))
      exact (trivializationAt G E b₁).mem_source.2 hp.2.1
    refine (hc.smul (continuousOn_const (c := ContinuousLinearMap.id 𝕜 𝕜))).congr fun p hp ↦ ?_
    refine ContinuousLinearMap.ext_ring ?_
    rw [ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply' _ _ hp,
      tautologicalTrivialization_symm_apply]
    simp [Trivialization.symmL_apply _ hp.1.1]

end FiberBundle

/-! ### The restriction to a fibre -/

variable (𝕜 G E) in
/-- The restriction of the tautological line to the fibre of the projective bundle over `b` is
the tautological line of the projective space `ℙ 𝕜 (E b)`: the two have the same points, and the
identity is a homeomorphism. -/
def tautologicalFiberHomeomorph (b : B) :
    TotalSpace 𝕜 (Projectivization.Tautological 𝕜 (E b)) ≃ₜ
      TotalSpace 𝕜 (TotalSpace.mk' (ℙ 𝕜 G) (E := fun b ↦ ℙ 𝕜 (E b)) b *ᵖ
        (Tautological 𝕜 G E)) where
  toFun v := ⟨v.proj, v.snd⟩
  invFun v := ⟨v.proj, v.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Pullback.continuous_iff.2
    ⟨Projectivization.continuous_proj_tautological 𝕜 (E b),
      continuous_totalSpace_tautological_iff.2
        ⟨(FiberBundle.totalSpaceMk_isInducing (ℙ 𝕜 G) (fun b ↦ ℙ 𝕜 (E b)) b).continuous.comp
          (Projectivization.continuous_proj_tautological 𝕜 (E b)),
        (FiberBundle.totalSpaceMk_isInducing G E b).continuous.comp
          (Projectivization.continuous_snd_tautological 𝕜 (E b))⟩⟩
  continuous_invFun := Projectivization.continuous_totalSpace_tautological_iff.2
    ⟨Pullback.continuous_proj _ _ _, (FiberBundle.totalSpaceMk_isInducing G E b).continuous_iff.2
      ((continuous_toTotalSpace_tautological 𝕜 G E).comp (Pullback.continuous_lift _ _ _))⟩

@[simp]
theorem tautologicalFiberHomeomorph_apply (b : B)
    (v : TotalSpace 𝕜 (Projectivization.Tautological 𝕜 (E b))) :
    tautologicalFiberHomeomorph 𝕜 G E b v = ⟨v.proj, v.snd⟩ :=
  (rfl)

@[simp]
theorem tautologicalFiberHomeomorph_symm_apply (b : B)
    (v : TotalSpace 𝕜 (TotalSpace.mk' (ℙ 𝕜 G) (E := fun b ↦ ℙ 𝕜 (E b)) b *ᵖ
      (Tautological 𝕜 G E))) :
    (tautologicalFiberHomeomorph 𝕜 G E b).symm v = ⟨v.proj, v.snd⟩ :=
  (rfl)

/-! ### Pull-backs along maps of projective bundles -/

section Map

variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G'] {E' : B → Type*}
  [∀ b, AddCommGroup (E' b)] [∀ b, Module 𝕜 (E' b)] [TopologicalSpace (TotalSpace G' E')]
  [∀ b, TopologicalSpace (E' b)] [FiberBundle G' E'] [VectorBundle 𝕜 G' E'] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 G] {φ : ∀ b, E b ≃L[𝕜] E' b}
  (hφ : Continuous fun v : TotalSpace G E ↦ TotalSpace.mk' G' v.proj (φ v.proj v.snd))

/-- The pull-back of the tautological line of `E'` along the map of projective bundles induced by
a fibrewise isomorphism `φ` is the tautological line of `E`: on the fibre over a line `p`, the
isomorphism is the restriction of `φ` to `p`. -/
def tautologicalMapEquiv (p : ProjectiveBundle 𝕜 G E) :
    Tautological 𝕜 G E p ≃L[𝕜] (map φ hφ *ᵖ (Tautological 𝕜 G' E')) p :=
  tautologicalMapProjectivizationEquiv (φ p.proj) p.snd

@[simp]
theorem coe_tautologicalMapEquiv_apply (p : ProjectiveBundle 𝕜 G E) (v : Tautological 𝕜 G E p) :
    (tautologicalMapEquiv hφ p v).val = φ p.proj v :=
  (rfl)

theorem continuous_tautologicalMapEquiv :
    Continuous fun v : TotalSpace 𝕜 (Tautological 𝕜 G E) ↦
      TotalSpace.mk' 𝕜 (E := map φ hφ *ᵖ (Tautological 𝕜 G' E')) v.proj
        (tautologicalMapEquiv hφ v.proj v.snd) :=
  Pullback.continuous_iff.2 ⟨continuous_proj_tautological 𝕜 G E,
    continuous_totalSpace_tautological_iff.2 ⟨(map φ hφ).continuous.comp
      (continuous_proj_tautological 𝕜 G E), hφ.comp (continuous_toTotalSpace_tautological 𝕜 G E)⟩⟩

end Map

section Pullback

variable {B' : Type*} [TopologicalSpace B'] (f : C(B', B))

variable (𝕜 G E) in
/-- The pull-back of the tautological line of `E` along `ProjectiveBundle.pullbackMap f` is the
tautological line of `f *ᵖ E`: the two have the same points, and the identity is a
homeomorphism. -/
def tautologicalPullbackHomeomorph :
    TotalSpace 𝕜 (Tautological 𝕜 G (f *ᵖ E)) ≃ₜ
      TotalSpace 𝕜 (pullbackMap 𝕜 G E f *ᵖ (Tautological 𝕜 G E)) where
  toFun v := ⟨v.proj, v.snd⟩
  invFun v := ⟨v.proj, v.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Pullback.continuous_iff.2 ⟨continuous_proj_tautological 𝕜 G (f *ᵖ E),
    continuous_totalSpace_tautological_iff.2 ⟨(pullbackMap 𝕜 G E f).continuous.comp
      (continuous_proj_tautological 𝕜 G (f *ᵖ E)), (Pullback.continuous_lift G E f).comp
        (continuous_toTotalSpace_tautological 𝕜 G (f *ᵖ E))⟩⟩
  continuous_invFun := continuous_totalSpace_tautological_iff.2 ⟨Pullback.continuous_proj _ _ _,
    Pullback.continuous_iff.2 ⟨(projection 𝕜 G (f *ᵖ E)).continuous.comp
      (Pullback.continuous_proj _ _ _),
      (continuous_toTotalSpace_tautological 𝕜 G E).comp (Pullback.continuous_lift _ _ _)⟩⟩

@[simp]
theorem tautologicalPullbackHomeomorph_apply (v : TotalSpace 𝕜 (Tautological 𝕜 G (f *ᵖ E))) :
    tautologicalPullbackHomeomorph 𝕜 G E f v = ⟨v.proj, v.snd⟩ :=
  (rfl)

@[simp]
theorem tautologicalPullbackHomeomorph_symm_apply
    (v : TotalSpace 𝕜 (pullbackMap 𝕜 G E f *ᵖ (Tautological 𝕜 G E))) :
    (tautologicalPullbackHomeomorph 𝕜 G E f).symm v = ⟨v.proj, v.snd⟩ :=
  (rfl)

end Pullback

section Prod

variable {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] {E₁ : B → Type*}
  [∀ b, AddCommGroup (E₁ b)] [∀ b, Module 𝕜 (E₁ b)] [TopologicalSpace (TotalSpace G₁ E₁)]
  [∀ b, TopologicalSpace (E₁ b)] [FiberBundle G₁ E₁] [VectorBundle 𝕜 G₁ E₁]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂] {E₂ : B → Type*}
  [∀ b, AddCommGroup (E₂ b)] [∀ b, Module 𝕜 (E₂ b)] [TopologicalSpace (TotalSpace G₂ E₂)]
  [∀ b, TopologicalSpace (E₂ b)] [FiberBundle G₂ E₂] [VectorBundle 𝕜 G₂ E₂]

variable (G₂ E₂) in
/-- The pull-back of the tautological line of `E₁ ×ᵇ E₂` along `ProjectiveBundle.inl` is the
tautological line of `E₁`: on the fibre over a line `p`, the isomorphism sends `v` to `(v, 0)`. -/
def tautologicalInlEquiv (p : ProjectiveBundle 𝕜 G₁ E₁) :
    Tautological 𝕜 G₁ E₁ p ≃L[𝕜] (inl G₂ E₂ *ᵖ (Tautological 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂))) p :=
  ((ContinuousLinearMap.inl 𝕜 (E₁ p.proj) (E₂ p.proj)).equivMapOfLeftInverse
    (ContinuousLinearMap.fst 𝕜 (E₁ p.proj) (E₂ p.proj)) (fun _ ↦ rfl) p.snd.submodule).trans
      (.ofEq _ _ (submodule_map (LinearMap.inl 𝕜 (E₁ p.proj) (E₂ p.proj)) LinearMap.inl_injective
        p.snd).symm)

@[simp]
theorem coe_tautologicalInlEquiv_apply (p : ProjectiveBundle 𝕜 G₁ E₁)
    (v : Tautological 𝕜 G₁ E₁ p) :
    (tautologicalInlEquiv G₂ E₂ p v).val = ((v : E₁ p.proj), 0) :=
  ContinuousLinearMap.coe_equivMapOfLeftInverse_apply (ContinuousLinearMap.inl 𝕜 _ _)
    (ContinuousLinearMap.fst 𝕜 (E₁ p.proj) (E₂ p.proj)) (fun _ ↦ rfl) p.snd.submodule v

theorem continuous_tautologicalInlEquiv :
    Continuous fun v : TotalSpace 𝕜 (Tautological 𝕜 G₁ E₁) ↦
      TotalSpace.mk' 𝕜 (E := inl G₂ E₂ *ᵖ (Tautological 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂))) v.proj
        (tautologicalInlEquiv G₂ E₂ v.proj v.snd) :=
  Pullback.continuous_iff.2 ⟨continuous_proj_tautological 𝕜 G₁ E₁,
    continuous_totalSpace_tautological_iff.2 ⟨(inl G₂ E₂).continuous.comp
      (continuous_proj_tautological 𝕜 G₁ E₁),
      (FiberBundle.Prod.isInducing_diag G₁ E₁ G₂ E₂).continuous_iff.2 <|
        ((continuous_toTotalSpace_tautological 𝕜 G₁ E₁).prodMk
          ((Trivialization.continuous_zeroSection 𝕜 (F := G₂) (E := E₂)).comp
            ((FiberBundle.continuous_proj G₁ E₁).comp
              (continuous_toTotalSpace_tautological 𝕜 G₁ E₁)))).congr fun v ↦ by
          -- `simp` leaves `HEq` goals whose types agree only by unfolding `inl` or `inr`.
          ext <;> simp [Pullback.lift, zeroSection_def] <;> rfl⟩⟩

variable (G₁ E₁) in
/-- The pull-back of the tautological line of `E₁ ×ᵇ E₂` along `ProjectiveBundle.inr` is the
tautological line of `E₂`: on the fibre over a line `p`, the isomorphism sends `v` to `(0, v)`. -/
def tautologicalInrEquiv (p : ProjectiveBundle 𝕜 G₂ E₂) :
    Tautological 𝕜 G₂ E₂ p ≃L[𝕜] (inr G₁ E₁ *ᵖ (Tautological 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂))) p :=
  ((ContinuousLinearMap.inr 𝕜 (E₁ p.proj) (E₂ p.proj)).equivMapOfLeftInverse
    (ContinuousLinearMap.snd 𝕜 (E₁ p.proj) (E₂ p.proj)) (fun _ ↦ rfl) p.snd.submodule).trans
      (.ofEq _ _ (submodule_map (LinearMap.inr 𝕜 (E₁ p.proj) (E₂ p.proj)) LinearMap.inr_injective
        p.snd).symm)

@[simp]
theorem coe_tautologicalInrEquiv_apply (p : ProjectiveBundle 𝕜 G₂ E₂)
    (v : Tautological 𝕜 G₂ E₂ p) :
    (tautologicalInrEquiv G₁ E₁ p v).val = (0, (v : E₂ p.proj)) :=
  ContinuousLinearMap.coe_equivMapOfLeftInverse_apply (ContinuousLinearMap.inr 𝕜 _ _)
    (ContinuousLinearMap.snd 𝕜 (E₁ p.proj) (E₂ p.proj)) (fun _ ↦ rfl) p.snd.submodule v

theorem continuous_tautologicalInrEquiv :
    Continuous fun v : TotalSpace 𝕜 (Tautological 𝕜 G₂ E₂) ↦
      TotalSpace.mk' 𝕜 (E := inr G₁ E₁ *ᵖ (Tautological 𝕜 (G₁ × G₂) (E₁ ×ᵇ E₂))) v.proj
        (tautologicalInrEquiv G₁ E₁ v.proj v.snd) :=
  Pullback.continuous_iff.2 ⟨continuous_proj_tautological 𝕜 G₂ E₂,
    continuous_totalSpace_tautological_iff.2 ⟨(inr G₁ E₁).continuous.comp
      (continuous_proj_tautological 𝕜 G₂ E₂),
      (FiberBundle.Prod.isInducing_diag G₁ E₁ G₂ E₂).continuous_iff.2 <|
        (((Trivialization.continuous_zeroSection 𝕜 (F := G₁) (E := E₁)).comp
            ((FiberBundle.continuous_proj G₂ E₂).comp
              (continuous_toTotalSpace_tautological 𝕜 G₂ E₂))).prodMk
          (continuous_toTotalSpace_tautological 𝕜 G₂ E₂)).congr fun v ↦ by
          -- `simp` leaves `HEq` goals whose types agree only by unfolding `inl` or `inr`.
          ext <;> simp [Pullback.lift, zeroSection_def] <;> rfl⟩⟩

end Prod

end ProjectiveBundle

end SymplecticGeometry.Bundle
