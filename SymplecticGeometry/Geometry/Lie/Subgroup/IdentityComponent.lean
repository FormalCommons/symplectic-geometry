/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Lie.Subgroup.Stabilizer
public import TauCeti.Geometry.Lie.Subgroup.Torus
public import SymplecticGeometry.Geometry.Lie.GroupLieAlgebraLieHom

/-!
# The identity component of a subgroup of a Lie group

Let `S` be a subgroup of a finite-dimensional real Lie group `G`, and let
`K = (Subgroup.connectedComponentOfOne S).map S.subtype` be its identity component, viewed as a
subgroup of `G`.

* `K` and `S` have the same Lie algebra `TauCeti.Lie.lieSubalgebraOfSubgroup`: a one-parameter
  subgroup lying in `S` is a connected curve through `1`, so it lies in `K`. For `S = ⊤` this is
  Tau Ceti's `TauCeti.Lie.lieSubalgebraOfSubgroup_connectedComponentOfOne`, whose proof (and that
  of `TauCeti.Lie.lieExp_mem_connectedComponent_one`) ours adapts to a subgroup.
* If `S` is compact and commutative, `K` is a torus.
* For the stabilizer `S = G_x` of a point of a manifold on which `G` acts smoothly, the Lie algebra
  of `K` is the isotropy algebra `𝔤_x`, by Tau Ceti's
  `TauCeti.Lie.lieSubalgebraOfSubgroup_stabilizer`.
* For any embedded Lie subgroup structure on a subgroup `K`, the differential at `1` of the
  inclusion `K → G`, as a map of tangent spaces `K.subtype.groupLieAlgebraMap`, is injective, and
  its range is the image of the Lie algebra of `K` in the tangent space `𝔤 = T₁G`. This restates
  Tau Ceti's `EmbeddedLieSubgroupData.injective_lieMapSubtypeVal` and
  `EmbeddedLieSubgroupData.range_lieMapSubtypeVal_eq`, stated for derivations, on tangent
  vectors. For a stabilizer, and for its identity component, the range is `𝔤_x`. The inclusion
  also carries the exponential of `K` to that of `G` through this differential, by the
  library's `ContMDiffMonoidMorphism.map_mulInvariantExp`.

These let the weight chart at a point `x` of a torus action, which Tau Ceti builds for a torus
fixing `x`, be read on the isotropy algebra of `G` itself.

## Main results

* `TauCeti.Lie.lieSubalgebraOfSubgroup_map_connectedComponentOfOne`: `Lie(S⁰) = Lie(S)`.
* `TauCeti.Lie.isTorus_map_connectedComponentOfOne`: the identity component of a compact
  commutative subgroup is a torus.
* `TauCeti.Lie.lieSubalgebraOfSubgroup_map_connectedComponentOfOne_stabilizer`: `Lie(G_x⁰)` is
  the isotropy algebra.
* `TauCeti.Lie.EmbeddedLieSubgroupData.injective_groupLieAlgebraMap_subtype` and
  `TauCeti.Lie.EmbeddedLieSubgroupData.range_groupLieAlgebraMap_subtype`: the differential of the
  inclusion of an embedded Lie subgroup is injective, with range its Lie algebra.
* `TauCeti.Lie.EmbeddedLieSubgroupData.coe_mulInvariantExp`: the inclusion carries the
  exponential of `K` to that of `G`, through that differential.
* `TauCeti.Lie.EmbeddedLieSubgroupData.range_groupLieAlgebraMap_subtype_eq_isotropy`: for a
  subgroup with the same Lie algebra as `G_x`, that range is `𝔤_x`.
* `TauCeti.Lie.EmbeddedLieSubgroupData.range_groupLieAlgebraMap_subtype_stabilizer` and
  `TauCeti.Lie.EmbeddedLieSubgroupData.range_groupLieAlgebraMap_stabilizer_subtype`: for the
  identity component of `G_x`, and for `G_x` itself, that range is `𝔤_x`.
* `TauCeti.Lie.EmbeddedLieSubgroupData.groupLieAlgebraEquivIsotropy`: that differential, as a
  linear equivalence from the tangent space at `1` of the identity component of `G_x` onto `𝔤_x`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 20.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3, and Chapter IV, § 1.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.Lie

section Topological

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- **The identity component of a compact commutative subgroup is a torus.** -/
theorem isTorus_map_connectedComponentOfOne {S : Subgroup G} (hS : IsCompact (S : Set G))
    [IsMulCommutative S] :
    IsTorus ((Subgroup.connectedComponentOfOne S).map S.subtype) := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  refine IsTorus.map ⟨?_, ?_, inferInstance⟩ S.subtype continuous_subtypeVal <;>
    rw [Subgroup.coe_connectedComponentOfOne]
  · exact isClosed_connectedComponent.isCompact
  · exact isConnected_connectedComponent

end Topological

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

section IdentityComponent

variable [IsTopologicalGroup G]

/-- **A subgroup and its identity component have the same Lie algebra**: a one-parameter subgroup
lying in `S` is a connected curve through `1` in `S`. No closedness of `S` is needed. -/
@[simp]
theorem lieSubalgebraOfSubgroup_map_connectedComponentOfOne (S : Subgroup G) :
    lieSubalgebraOfSubgroup (I := I) ((Subgroup.connectedComponentOfOne S).map S.subtype) =
      lieSubalgebraOfSubgroup (I := I) S := by
  refine le_antisymm (lieSubalgebraOfSubgroup_mono (Subgroup.map_subtype_le _))
    (lieSubalgebraOfSubgroup_le_iff.mpr fun X hX ↦ mem_lieSubalgebraOfSubgroup_of_forall fun t ↦ ?_)
  -- The one-parameter subgroup of `X`, as a curve in `S`.
  let γ : ℝ → S := fun s ↦ ⟨lieExp (I := I) (s • X), hX s⟩
  have hγ : Continuous γ := by
    refine Continuous.subtype_mk ?_ _
    simpa only [oneParameterSubgroup_apply] using
      (contMDiff_oneParameterSubgroup (I := I) X).continuous
  refine ⟨γ t, ?_, rfl⟩
  rw [Subgroup.coe_connectedComponentOfOne]
  refine (isPreconnected_range hγ).subset_connectedComponent ⟨0, ?_⟩ ⟨t, rfl⟩
  ext
  simp [γ]

end IdentityComponent

section Stabilizer

variable [IsTopologicalGroup G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M]
  [IsManifold I' ∞ M] [T2Space M] [BoundarylessManifold I' M] [ContMDiffSMul I I' ∞ G M]

/-- **The Lie algebra of the identity component of a stabilizer is the isotropy algebra.** Under
the identification of left-invariant derivations with `𝔤` by evaluation at the identity, the Lie
algebra of the identity component of `G_x` is `𝔤_x = {ξ | ξ_M(x) = 0}`. -/
theorem lieSubalgebraOfSubgroup_map_connectedComponentOfOne_stabilizer
    (h₁ : I.IsInteriorPoint 1) (x : M) :
    lieSubalgebraOfSubgroup (I := I) ((Subgroup.connectedComponentOfOne
        (MulAction.stabilizer G x)).map (MulAction.stabilizer G x).subtype) =
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).comap
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G) h₁).toLieHom := by
  rw [lieSubalgebraOfSubgroup_map_connectedComponentOfOne,
    lieSubalgebraOfSubgroup_stabilizer (I' := I') h₁ x]

end Stabilizer

namespace EmbeddedLieSubgroupData

variable {K : Subgroup G} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [FiniteDimensional ℝ F] in
/-- **The differential at `1` of the inclusion of an embedded Lie subgroup is injective.** This is
`TauCeti.Lie.EmbeddedLieSubgroupData.injective_lieMapSubtypeVal` on tangent vectors. -/
theorem injective_groupLieAlgebraMap_subtype (d : EmbeddedLieSubgroupData I K F) :
    let _ : ChartedSpace F K := d.chartedSpace
    Function.Injective (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I) := by
  let _ : ChartedSpace F K := d.chartedSpace
  dsimp only
  intro v w h
  rw [MonoidHom.groupLieAlgebraMap_apply, MonoidHom.groupLieAlgebraMap_apply] at h
  exact d.injective_mfderiv_subtypeVal 1 h

omit [T2Space G] in
/-- The Lie algebra map of the smooth inclusion `K → G` of an embedded Lie subgroup is the
differential at `1` of the inclusion `K.subtype`. -/
theorem groupLieAlgebraLieHom_subtypeVal (d : EmbeddedLieSubgroupData I K F) :
    let _ : ChartedSpace F K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, F) ∞ K := d.lieGroup
    ∀ ζ, d.subtypeVal.groupLieAlgebraLieHom ζ = K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ζ := by
  let _ : ChartedSpace F K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, F) ∞ K := d.lieGroup
  dsimp only
  intro ζ
  rw [ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom, MonoidHom.groupLieAlgebraMap_apply,
    MonoidHom.groupLieAlgebraMap_apply, ContMDiffMonoidMorphism.coe_toMonoidHom,
    mfderiv_congr (funext fun k ↦ d.subtypeVal_apply k), Subgroup.coe_subtype]
  -- The two sides differ only in instance arguments, which agree up to unfolding.
  rfl

/-- **The range of the differential at `1` of the inclusion of an embedded Lie subgroup `K` is its
Lie algebra**, carried to the tangent space `𝔤 = T₁G` by evaluation at the identity. This is
`TauCeti.Lie.EmbeddedLieSubgroupData.range_lieMapSubtypeVal_eq` on tangent vectors; it does not
depend on the model `F` of `K`. -/
theorem range_groupLieAlgebraMap_subtype (d : EmbeddedLieSubgroupData I K F)
    (h₁ : I.IsInteriorPoint 1) :
    let _ : ChartedSpace F K := d.chartedSpace
    LinearMap.range (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap =
      (lieSubalgebraOfSubgroup (I := I) K).toSubmodule.map
        ((leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G) h₁).toLinearEquiv :
          LeftInvariantDerivation I G →ₗ[ℝ] GroupLieAlgebra I G) := by
  let _ : ChartedSpace F K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, F) ∞ K := d.lieGroup
  dsimp only
  let eK := leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, F)) (G := K)
    (ContMDiffMul.isInteriorPoint (n := ∞) (by simp) 1)
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G) h₁
  have key₀ (D : LeftInvariantDerivation 𝓘(ℝ, F) K) :
      K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I (eK D) = e (d.lieMapSubtypeVal D) := by
    rw [lieMapSubtypeVal_apply,
      ContMDiffMonoidMorphism.leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap_eq,
      d.groupLieAlgebraLieHom_subtypeVal]
  have key : (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap ∘ₗ
      (eK.toLinearEquiv : LeftInvariantDerivation 𝓘(ℝ, F) K →ₗ[ℝ] GroupLieAlgebra 𝓘(ℝ, F) K) =
      (e.toLinearEquiv : LeftInvariantDerivation I G →ₗ[ℝ] GroupLieAlgebra I G) ∘ₗ
        d.lieMapSubtypeVal.toLinearMap := LinearMap.ext key₀
  rw [← d.range_lieMapSubtypeVal_eq, ← LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range eK.toLinearEquiv), key, LinearMap.range_comp,
    LieHom.range_toSubmodule]

/-- The inclusion of an embedded Lie subgroup `K` carries its exponential to that of `G`:
`(exp ζ : G) = exp (dι₁ ζ)`, where `ι : K → G` is the inclusion. -/
theorem coe_mulInvariantExp (d : EmbeddedLieSubgroupData I K F) :
    let _ : ChartedSpace F K := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, F) ∞ K := d.lieGroup
    ∀ ζ, ((mulInvariantExp ζ : K) : G) =
      mulInvariantExp (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ζ) := by
  let _ : ChartedSpace F K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, F) ∞ K := d.lieGroup
  dsimp only
  intro ζ
  rw [← d.subtypeVal_apply, d.subtypeVal.map_mulInvariantExp, d.groupLieAlgebraLieHom_subtypeVal]

variable [IsTopologicalGroup G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M]
  [IsManifold I' ∞ M] [T2Space M] [BoundarylessManifold I' M] [ContMDiffSMul I I' ∞ G M]

omit [IsTopologicalGroup G] in
/-- **A subgroup with the Lie algebra of a stabilizer has tangent space `𝔤_x` at `1`.** For any
embedded Lie subgroup structure on a subgroup `K` of `G` whose Lie algebra is that of `G_x`, the
differential at `1` of the inclusion `K → G` has range `𝔤_x = {ξ | ξ_M(x) = 0}`. -/
theorem range_groupLieAlgebraMap_subtype_eq_isotropy {x : M} (d : EmbeddedLieSubgroupData I K F)
    (hK : lieSubalgebraOfSubgroup (I := I) K =
      lieSubalgebraOfSubgroup (I := I) (MulAction.stabilizer G x)) :
    let _ := d.chartedSpace
    LinearMap.range (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap =
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule := by
  let _ := d.chartedSpace
  dsimp only
  have h₁ : I.IsInteriorPoint (1 : G) := BoundarylessManifold.isInteriorPoint
  rw [d.range_groupLieAlgebraMap_subtype h₁, hK, lieSubalgebraOfSubgroup_stabilizer (I' := I') h₁ x]
  exact Submodule.map_comap_eq_of_surjective
    (leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G) h₁).toLinearEquiv.surjective _

/-- **The tangent space at `1` of the identity component of a stabilizer is the isotropy
algebra.** For any embedded Lie subgroup structure on the identity component `K` of `G_x`, the
differential at `1` of the inclusion `K → G` has range `𝔤_x = {ξ | ξ_M(x) = 0}`. -/
theorem range_groupLieAlgebraMap_subtype_stabilizer {x : M}
    (d : EmbeddedLieSubgroupData I ((Subgroup.connectedComponentOfOne
      (MulAction.stabilizer G x)).map (MulAction.stabilizer G x).subtype) F) :
    let _ := d.chartedSpace
    LinearMap.range ((Subgroup.map (MulAction.stabilizer G x).subtype
        (Subgroup.connectedComponentOfOne (MulAction.stabilizer G x))).subtype.groupLieAlgebraMap
          𝓘(ℝ, F) I).toLinearMap =
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule :=
  d.range_groupLieAlgebraMap_subtype_eq_isotropy (I' := I')
    (lieSubalgebraOfSubgroup_map_connectedComponentOfOne _)

omit [IsTopologicalGroup G] in
/-- **The tangent space at `1` of a stabilizer is the isotropy algebra.** For any embedded Lie
subgroup structure on the stabilizer `G_x`, the differential at `1` of the inclusion `G_x → G` has
range `𝔤_x = {ξ | ξ_M(x) = 0}`. -/
theorem range_groupLieAlgebraMap_stabilizer_subtype {x : M}
    (d : EmbeddedLieSubgroupData I (MulAction.stabilizer G x) F) :
    let _ := d.chartedSpace
    LinearMap.range
        ((MulAction.stabilizer G x).subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap =
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule :=
  d.range_groupLieAlgebraMap_subtype_eq_isotropy (I' := I') rfl

omit [IsTopologicalGroup G] in
/-- For any embedded Lie subgroup structure on the stabilizer `G_x`, the differential at `1` of the
inclusion `G_x → G` takes values in the isotropy algebra `𝔤_x = {ξ | ξ_M(x) = 0}`. -/
theorem groupLieAlgebraMap_subtype_mem_isotropy {x : M}
    (d : EmbeddedLieSubgroupData I (MulAction.stabilizer G x) F) :
    let _ := d.chartedSpace
    ∀ ζ, (MulAction.stabilizer G x).subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ζ ∈
      (InfinitesimalAction.fundamental I G I' M).isotropy x :=
  fun ζ ↦ (d.range_groupLieAlgebraMap_stabilizer_subtype (I' := I')).le
    (LinearMap.mem_range_self _ ζ)

/-- **The tangent space at `1` of the identity component of a stabilizer, as the isotropy
algebra.** For an embedded Lie subgroup structure on the identity component `K` of `G_x`, the
differential at `1` of the inclusion `K → G`, with its codomain cut down to its range
`𝔤_x = {ξ | ξ_M(x) = 0}`, as a linear equivalence from `T₁K` onto `𝔤_x`. -/
def groupLieAlgebraEquivIsotropy {x : M}
    (d : EmbeddedLieSubgroupData I ((Subgroup.connectedComponentOfOne
      (MulAction.stabilizer G x)).map (MulAction.stabilizer G x).subtype) F) :
    let _ := d.chartedSpace
    GroupLieAlgebra 𝓘(ℝ, F) ((Subgroup.connectedComponentOfOne
      (MulAction.stabilizer G x)).map (MulAction.stabilizer G x).subtype) ≃ₗ[ℝ]
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule :=
  let _ := d.chartedSpace
  (LinearEquiv.ofInjective _ d.injective_groupLieAlgebraMap_subtype).trans
    (LinearEquiv.ofEq _ _ (d.range_groupLieAlgebraMap_subtype_stabilizer (I' := I')))

theorem groupLieAlgebraEquivIsotropy_def {x : M}
    (d : EmbeddedLieSubgroupData I ((Subgroup.connectedComponentOfOne
      (MulAction.stabilizer G x)).map (MulAction.stabilizer G x).subtype) F) :
    let _ := d.chartedSpace
    d.groupLieAlgebraEquivIsotropy (I' := I') =
      (LinearEquiv.ofInjective _ d.injective_groupLieAlgebraMap_subtype).trans
        (LinearEquiv.ofEq _ _ (d.range_groupLieAlgebraMap_subtype_stabilizer (I' := I'))) :=
  (rfl)

/-- `TauCeti.Lie.EmbeddedLieSubgroupData.groupLieAlgebraEquivIsotropy` is the differential at `1`
of the inclusion `K → G`. -/
@[simp]
theorem coe_groupLieAlgebraEquivIsotropy {x : M}
    (d : EmbeddedLieSubgroupData I ((Subgroup.connectedComponentOfOne
      (MulAction.stabilizer G x)).map (MulAction.stabilizer G x).subtype) F) :
    let _ := d.chartedSpace
    ∀ η, (d.groupLieAlgebraEquivIsotropy (I' := I') η : GroupLieAlgebra I G) =
      ((Subgroup.connectedComponentOfOne (MulAction.stabilizer G x)).map
        (MulAction.stabilizer G x).subtype).subtype.groupLieAlgebraMap 𝓘(ℝ, F) I η :=
  fun _ ↦ rfl

/-- The differential at `1` of the inclusion `K → G` sends the inverse of
`TauCeti.Lie.EmbeddedLieSubgroupData.groupLieAlgebraEquivIsotropy` at `ξ ∈ 𝔤_x` back to `ξ`. -/
@[simp]
theorem groupLieAlgebraMap_subtype_groupLieAlgebraEquivIsotropy_symm {x : M}
    (d : EmbeddedLieSubgroupData I ((Subgroup.connectedComponentOfOne
      (MulAction.stabilizer G x)).map (MulAction.stabilizer G x).subtype) F) :
    let _ := d.chartedSpace
    ∀ ξ, ((Subgroup.connectedComponentOfOne (MulAction.stabilizer G x)).map
        (MulAction.stabilizer G x).subtype).subtype.groupLieAlgebraMap 𝓘(ℝ, F) I
          ((d.groupLieAlgebraEquivIsotropy (I' := I')).symm ξ) = (ξ : GroupLieAlgebra I G) := by
  let _ := d.chartedSpace
  dsimp only
  intro ξ
  rw [← coe_groupLieAlgebraEquivIsotropy (I' := I'), LinearEquiv.apply_symm_apply]

end EmbeddedLieSubgroupData

end TauCeti.Lie
