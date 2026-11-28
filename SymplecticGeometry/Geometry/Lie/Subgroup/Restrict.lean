/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Functor
public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Lie.Tangent.Differential
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Restricting a smooth homomorphism to embedded Lie subgroups

Let `f : G → G'` be a smooth homomorphism of finite-dimensional real Lie groups, the model of `G'`
having no boundary, and let `K ≤ G`, `K' ≤ G'` be subgroups with `f` mapping `K` into `K'`, each
carrying an embedded Lie subgroup structure (`TauCeti.Lie.EmbeddedLieSubgroupData`), for instance
the one that Cartan's closed-subgroup theorem gives a closed subgroup,
`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`.

The restriction `K → K'` of `f` is again a smooth homomorphism: its composite with the inclusion
`K' → G'` is `f` after the inclusion `K → G`, which is smooth, and the inclusion of `K'` is a smooth
embedding (`TauCeti.Lie.EmbeddedLieSubgroupData.isSmoothEmbedding_subtypeVal`), so smoothness into
`K'` can be tested after it (`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`). By the chain rule at
the identity, the differentials at `1` of the restriction, of `f` and of the two inclusions form a
commutative square.

## Main definitions and results

* `ContMDiffMonoidMorphism.restrict`: the restriction `K → K'` of `f`, as a smooth homomorphism.
* `ContMDiffMonoidMorphism.coe_restrict_apply`: it agrees with `f` on `K`.
* `ContMDiffMonoidMorphism.restrict_injective`: it is injective when `f` is.
* `ContMDiffMonoidMorphism.groupLieAlgebraMap_subtype_groupLieAlgebraLieHom_restrict`: the
  differentials at `1` commute with the inclusions.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapters 5 and
  7.
-/

public section

noncomputable section

open scoped ContDiff Manifold

open TauCeti.Lie

namespace ContMDiffMonoidMorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E'] [LieGroup I' ∞ G']
  {K : Subgroup G} {K' : Subgroup G'}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- **The restriction of a smooth homomorphism `f : G → G'` to embedded Lie subgroups** `K ≤ G`
and `K' ≤ G'` with `f` mapping `K` into `K'`: the map `k ↦ f k` from `K` to `K'`, a smooth
homomorphism for the smooth structures that `d` and `d'` give `K` and `K'`. -/
def restrict (f : ContMDiffMonoidMorphism I I' ∞ G G') (d : EmbeddedLieSubgroupData I K F)
    (d' : EmbeddedLieSubgroupData I' K' F') (h : Set.MapsTo f K K') :
    let _ := d.chartedSpace
    let _ := d'.chartedSpace
    ContMDiffMonoidMorphism 𝓘(ℝ, F) 𝓘(ℝ, F') ∞ K K' :=
  let _ := d.chartedSpace
  let _ := d'.chartedSpace
  { toMonoidHom := (f.toMonoidHom.domRestrict K).codRestrict K' fun k ↦ h k.property
    contMDiff_toFun := d'.isSmoothEmbedding_subtypeVal.contMDiff_iff_comp.2 <|
      f.contMDiff_toFun.comp d.contMDiff_subtypeVal }

/-- The underlying homomorphism of `ContMDiffMonoidMorphism.restrict` is the restriction of `f`
to `K`, with its codomain cut down to `K'`. -/
theorem toMonoidHom_restrict (f : ContMDiffMonoidMorphism I I' ∞ G G')
    (d : EmbeddedLieSubgroupData I K F) (d' : EmbeddedLieSubgroupData I' K' F')
    (h : Set.MapsTo f K K') :
    let _ := d.chartedSpace
    let _ := d'.chartedSpace
    (f.restrict d d' h).toMonoidHom =
      (f.toMonoidHom.domRestrict K).codRestrict K' fun k ↦ h k.property :=
  (rfl)

/-- `ContMDiffMonoidMorphism.restrict` agrees with `f` on `K`. -/
@[simp]
theorem coe_restrict_apply (f : ContMDiffMonoidMorphism I I' ∞ G G')
    (d : EmbeddedLieSubgroupData I K F) (d' : EmbeddedLieSubgroupData I' K' F')
    (h : Set.MapsTo f K K') :
    let _ := d.chartedSpace
    let _ := d'.chartedSpace
    ∀ k : K, ((f.restrict d d' h k : K') : G') = f k :=
  fun _ ↦ rfl

/-- The restriction of an injective smooth homomorphism to embedded Lie subgroups is injective. -/
theorem restrict_injective {f : ContMDiffMonoidMorphism I I' ∞ G G'} (hf : Function.Injective f)
    (d : EmbeddedLieSubgroupData I K F) (d' : EmbeddedLieSubgroupData I' K' F')
    (h : Set.MapsTo f K K') :
    let _ := d.chartedSpace
    let _ := d'.chartedSpace
    Function.Injective (f.restrict d d' h) := by
  let _ := d.chartedSpace
  let _ := d'.chartedSpace
  dsimp only
  intro k l hkl
  have := congrArg (fun x : K' ↦ (x : G')) hkl
  simp only [coe_restrict_apply] at this
  exact Subtype.ext (hf this)

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G] [CompleteSpace F] [CompleteSpace F']

/-- **The differentials at `1` of a restriction to embedded Lie subgroups commute with the
inclusions**: for `ζ` in the Lie algebra of `K`, the differential of the inclusion `K' → G'` at the
image of `ζ` under the restriction's differential is the differential of `f` at the image of `ζ`
under the differential of the inclusion `K → G`. -/
theorem groupLieAlgebraMap_subtype_groupLieAlgebraLieHom_restrict
    (f : ContMDiffMonoidMorphism I I' ∞ G G') (d : EmbeddedLieSubgroupData I K F)
    (d' : EmbeddedLieSubgroupData I' K' F') (h : Set.MapsTo f K K') :
    let _ := d.chartedSpace
    let _ := d'.chartedSpace
    let _ := d.lieGroup
    let _ := d'.lieGroup
    ∀ ζ, K'.subtype.groupLieAlgebraMap 𝓘(ℝ, F') I' ((f.restrict d d' h).groupLieAlgebraLieHom ζ) =
      f.groupLieAlgebraLieHom (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ζ) := by
  let _ := d.chartedSpace
  let _ := d'.chartedSpace
  let _ := d.lieGroup
  let _ := d'.lieGroup
  dsimp only
  intro ζ
  have hcomp : K'.subtype.comp (f.restrict d d' h).toMonoidHom = f.toMonoidHom.comp K.subtype :=
    MonoidHom.ext fun k ↦ f.coe_restrict_apply d d' h k
  have hK : MDifferentiableAt 𝓘(ℝ, F) I K.subtype 1 :=
    d.contMDiff_subtypeVal.mdifferentiableAt (by simp)
  have hK' : MDifferentiableAt 𝓘(ℝ, F') I' K'.subtype 1 :=
    d'.contMDiff_subtypeVal.mdifferentiableAt (by simp)
  have hr : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F') (f.restrict d d' h).toMonoidHom 1 :=
    (f.restrict d d' h).contMDiff_toFun.mdifferentiableAt (by simp)
  have hf : MDifferentiableAt I I' f.toMonoidHom 1 :=
    f.contMDiff_toFun.mdifferentiableAt (by simp)
  rw [coe_groupLieAlgebraLieHom, coe_groupLieAlgebraLieHom, ← ContinuousLinearMap.comp_apply,
    ← MonoidHom.groupLieAlgebraMap_comp _ _ hK' hr, hcomp,
    MonoidHom.groupLieAlgebraMap_comp _ _ hf hK, ContinuousLinearMap.comp_apply]

end ContMDiffMonoidMorphism
