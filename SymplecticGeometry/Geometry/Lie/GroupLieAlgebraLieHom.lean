/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Lie.Subgroup.Kernel

/-!
# The Lie algebra map of a smooth homomorphism, on the tangent space at `1`

Tau Ceti states the Lie functor on smooth homomorphisms in two forms: `lieMap φ`, on
left-invariant derivations, and `ContMDiffMonoidMorphism.groupLieAlgebraLieHom φ`, on the tangent
spaces at `1`. Its results on the exponential and on injectivity are stated for `lieMap`. This file
moves them to `groupLieAlgebraLieHom`, and states there the naturality of the adjoint action.

## Main results

* `ContMDiffMonoidMorphism.leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap_eq`: the two
  forms correspond under evaluation at `1`.
* `ContMDiffMonoidMorphism.map_mulInvariantExp`: a smooth homomorphism `φ` satisfies
  `φ (exp ξ) = exp (φ.groupLieAlgebraLieHom ξ)`.
* `ContMDiffMonoidMorphism.groupLieAlgebraLieHom_injective`: the Lie algebra map of an injective
  smooth homomorphism is injective.
* `ContMDiffMonoidMorphism.groupLieAlgebraLieHom_tangentAd`: `φ.groupLieAlgebraLieHom` intertwines
  `Ad g` and `Ad (φ g)`.

The exponential law is the tangent-space form of Tau Ceti's `map_lieExp` (Tau Ceti proves it
privately, as `monoidHom_mulInvariantExp`); here it is derived from `map_lieExp`. Injectivity is
derived from Tau Ceti's `ContinuousMonoidHom.lieMap_injective_of_discreteTopology_ker`. The
naturality of `Ad` restates Tau Ceti's `MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap`
for `groupLieAlgebraLieHom` and `TauCeti.Lie.tangentAd`.
-/

public section

noncomputable section

open Function Manifold
open scoped Manifold ContDiff

section Coe

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Monoid G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Monoid G']

/-- The underlying monoid homomorphism of a smooth monoid morphism has the same values. -/
@[simp]
theorem ContMDiffMonoidMorphism.coe_toMonoidHom {n : WithTop ℕ∞}
    (φ : ContMDiffMonoidMorphism I I' n G G') : ⇑φ.toMonoidHom = φ :=
  (rfl)

end Coe

section Adjoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [LieGroup I' ∞ G']

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- A smooth homomorphism intertwines the adjoint actions through its Lie algebra map:
`φ.groupLieAlgebraLieHom (Ad g ξ) = Ad (φ g) (φ.groupLieAlgebraLieHom ξ)`. -/
theorem ContMDiffMonoidMorphism.groupLieAlgebraLieHom_tangentAd
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (g : G)
    (ξ : GroupLieAlgebra I G) :
    φ.groupLieAlgebraLieHom (TauCeti.Lie.tangentAd (I := I) g ξ) =
      TauCeti.Lie.tangentAd (I := I') (φ g) (φ.groupLieAlgebraLieHom ξ) := by
  simpa only [ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom,
    TauCeti.Lie.tangentAd_apply, ContMDiffMonoidMorphism.coe_toMonoidHom] using
    φ.toMonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap g ξ

end Adjoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [LieGroup I' ∞ G']

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

namespace ContMDiffMonoidMorphism

/-- Evaluation at `1` carries Tau Ceti's `lieMap φ`, on left-invariant derivations, to
`φ.groupLieAlgebraLieHom`, on the tangent spaces at `1`. -/
theorem leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap_eq
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (D : LeftInvariantDerivation I G) :
    leftInvariantDerivationLieEquivGroupLieAlgebra
        (ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G')) (lieMap φ D) =
      φ.groupLieAlgebraLieHom
        (leftInvariantDerivationLieEquivGroupLieAlgebra
          (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)) D) := by
  rw [leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap, coe_groupLieAlgebraLieHom,
    MonoidHom.groupLieAlgebraMap_apply, coe_toMonoidHom]

/-- A smooth homomorphism intertwines the exponentials through its Lie algebra map:
`φ (exp ξ) = exp (φ.groupLieAlgebraLieHom ξ)`. -/
theorem map_mulInvariantExp [T2Space G] [T2Space G'] (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    (ξ : GroupLieAlgebra I G) :
    φ (mulInvariantExp ξ) = mulInvariantExp (φ.groupLieAlgebraLieHom ξ) := by
  obtain ⟨D, rfl⟩ := (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint).surjective ξ
  have h := map_lieExp φ D
  simp only [lieExp_eq_mulInvariantExp] at h
  rw [h, ← leftInvariantDerivationLieEquivGroupLieAlgebra_apply,
    ← leftInvariantDerivationLieEquivGroupLieAlgebra_apply,
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap_eq]

/-- The Lie algebra map of an injective smooth homomorphism is injective. -/
theorem groupLieAlgebraLieHom_injective (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    (hφ : Injective φ) : Injective φ.groupLieAlgebraLieHom := by
  let f : G →ₜ* G' := ⟨φ.toMonoidHom, φ.contMDiff_toFun.continuous⟩
  have hf : f.toContMDiffMonoidMorphism I I' = φ :=
    DFunLike.ext _ _ fun _ ↦
      ContinuousMonoidHom.coe_toContMDiffMonoidMorphism (I := I) (I' := I') f ▸ rfl
  have : Subsingleton f.ker :=
    ⟨fun a b ↦ Subtype.ext (hφ (a.property.trans b.property.symm))⟩
  have hinj := ContinuousMonoidHom.lieMap_injective_of_discreteTopology_ker (I := I) (I' := I') f
  rw [ContinuousMonoidHom.lieMap_def, hf] at hinj
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  let e' := leftInvariantDerivationLieEquivGroupLieAlgebra
    (ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G'))
  intro ξ η h
  rw [← e.apply_symm_apply ξ, ← e.apply_symm_apply η,
    ← leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap_eq,
    ← leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap_eq] at h
  exact e.symm.injective (hinj (e'.injective h))

end ContMDiffMonoidMorphism
