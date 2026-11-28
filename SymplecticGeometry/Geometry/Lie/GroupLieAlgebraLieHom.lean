/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Lie.Subgroup.Kernel
import TauCeti.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# The Lie algebra map of a smooth homomorphism, on the tangent space at `1`

Tau Ceti states the Lie functor on smooth homomorphisms in two forms: `lieMap φ`, on
left-invariant derivations, and `ContMDiffMonoidMorphism.groupLieAlgebraLieHom φ`, on the tangent
spaces at `1`. Its exponential law is stated for `lieMap`, and its injectivity result for `mfderiv`
at every point. This file restates both for `groupLieAlgebraLieHom`, the second for an injective
`ContMDiffMonoidMorphism`, and states there the naturality of the adjoint action. For a smooth
homomorphism `ρ` into the units `Rˣ` of a complete normed real algebra, it also identifies
`ρ.groupLieAlgebraLieHom`, read in `R`, with the derivative at `1` of `g ↦ (ρ g : R)`.

## Main results

* `ContMDiffMonoidMorphism.map_mulInvariantExp`: a smooth homomorphism `φ` satisfies
  `φ (exp ξ) = exp (φ.groupLieAlgebraLieHom ξ)`.
* `ContMDiffMonoidMorphism.groupLieAlgebraLieHom_injective`: the Lie algebra map of an injective
  smooth homomorphism is injective.
* `ContMDiffMonoidMorphism.groupLieAlgebraLieHom_tangentAd`: `φ.groupLieAlgebraLieHom` intertwines
  `Ad g` and `Ad (φ g)`.
* `ContMDiffMonoidMorphism.mfderiv_inv_mul_mfderiv`: `φ.groupLieAlgebraLieHom` carries the
  left-trivialized derivative `d(L_{x⁻¹})_x v` to `d(L_{(φ x)⁻¹})_{φ x} (dφ_x v)`.
* `ContMDiffMonoidMorphism.contMDiff_coe`: for a smooth homomorphism `ρ` into `Rˣ`, the map
  `g ↦ (ρ g : R)` is smooth.
* `ContMDiffMonoidMorphism.mfderiv_coe_apply_one`: for a smooth homomorphism `ρ` into `Rˣ`, the
  derivative at `1` of `g ↦ (ρ g : R)` is `ρ.groupLieAlgebraLieHom`, read in `R`.

The exponential law is the tangent-space form of Tau Ceti's `map_lieExp` (Tau Ceti proves it
privately, as `monoidHom_mulInvariantExp`); here it is derived from `map_lieExp`. Injectivity is
the case `g = 1` of Tau Ceti's `ContinuousMonoidHom.injective_mfderiv_of_discreteTopology_ker`. The
naturality of `Ad` restates Tau Ceti's `MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap`
for `groupLieAlgebraLieHom` and `TauCeti.Lie.tangentAd`. The identity `mfderiv_inv_mul_mfderiv`
is derived from Tau Ceti's `ContMDiffMonoidMorphism.mfderiv_mulInvariantVectorField`, by writing
`v` as the value at `x` of a left-invariant vector field. The identity `mfderiv_coe_apply_one` is
the chain rule through Tau Ceti's `Units.hasMFDerivAt_val`, the steps that Tau Ceti's private
`groupLieAlgebraMap_toUnitsSmoothHom` takes for the special orthogonal group.
-/

public section

noncomputable section

open Function Manifold
open scoped Manifold ContDiff

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

/-- A smooth homomorphism carries left-trivialized derivatives to left-trivialized derivatives
through its Lie algebra map: for `v` tangent at `x`,
`d(L_{(φ x)⁻¹})_{φ x} (dφ_x v) = φ.groupLieAlgebraLieHom (d(L_{x⁻¹})_x v)`. -/
theorem ContMDiffMonoidMorphism.mfderiv_inv_mul_mfderiv
    (φ : ContMDiffMonoidMorphism I I' ∞ G G') (x : G) (v : TangentSpace I x) :
    mfderiv I' I' ((φ x)⁻¹ * ·) (φ x) (mfderiv I I' φ x v) =
      φ.groupLieAlgebraLieHom (mfderiv I I (x⁻¹ * ·) x v) := by
  obtain ⟨X, rfl⟩ := TauCeti.exists_mulInvariantVectorField_eq v
  rw [φ.mfderiv_mulInvariantVectorField, TauCeti.mfderiv_inv_mul_mulInvariantVectorField,
    TauCeti.mfderiv_inv_mul_mulInvariantVectorField,
    ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom]

end Adjoint

section Units

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- For a smooth homomorphism `ρ : G → Rˣ`, the map `g ↦ (ρ g : R)` is smooth. -/
theorem ContMDiffMonoidMorphism.contMDiff_coe (ρ : ContMDiffMonoidMorphism I 𝓘(ℝ, R) ∞ G Rˣ) :
    ContMDiff I 𝓘(ℝ, R) ∞ (fun g ↦ (ρ g : R)) :=
  Units.contMDiff_val.comp ρ.contMDiff_toFun

/-- For a smooth homomorphism `ρ : G → Rˣ`, the map `g ↦ (ρ g : R)` is differentiable at `1`. -/
theorem ContMDiffMonoidMorphism.mdifferentiableAt_coe_one
    (ρ : ContMDiffMonoidMorphism I 𝓘(ℝ, R) ∞ G Rˣ) :
    MDifferentiableAt I 𝓘(ℝ, R) (fun g ↦ (ρ g : R)) 1 :=
  (ρ.contMDiff_coe 1).mdifferentiableAt (by simp)

variable [CompleteSpace E] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The Lie algebra map of a homomorphism into `Rˣ`, read in `R`.** For a smooth homomorphism
`ρ : G → Rˣ` and `ξ` in the Lie algebra of `G`, the derivative at `1` of `g ↦ (ρ g : R)` at `ξ`
is `ρ.groupLieAlgebraLieHom ξ`, read in `R` through `groupLieAlgebraEquivModelVectorSpace`. -/
theorem ContMDiffMonoidMorphism.mfderiv_coe_apply_one
    (ρ : ContMDiffMonoidMorphism I 𝓘(ℝ, R) ∞ G Rˣ) (ξ : GroupLieAlgebra I G) :
    mfderiv I 𝓘(ℝ, R) (fun g ↦ (ρ g : R)) 1 ξ =
      (groupLieAlgebraEquivModelVectorSpace (ρ.groupLieAlgebraLieHom ξ) : R) := by
  have hρ : HasMFDerivAt I 𝓘(ℝ, R) ρ 1 (mfderiv I 𝓘(ℝ, R) ρ 1) :=
    (ρ.contMDiff_toFun.mdifferentiableAt (by simp)).hasMFDerivAt
  rw [show (fun g ↦ (ρ g : R)) = Units.val ∘ ρ from rfl,
    (((Units.hasMFDerivAt_val (𝕜 := ℝ) (ρ 1)).comp 1 hρ).congr_mfderiv
      (ContinuousLinearMap.id_comp _)).mfderiv,
    ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom, MonoidHom.groupLieAlgebraMap_apply,
    ContMDiffMonoidMorphism.coe_toMonoidHom]
  -- Both sides are `mfderiv I 𝓘(ℝ, R) ρ 1 ξ`: `groupLieAlgebraEquivModelVectorSpace` is
  -- `LinearEquiv.refl`, but `rw` cannot use `LinearEquiv.refl_apply` here, since the tangent
  -- space of `Rˣ` at `ρ 1` and the Lie algebra of `Rˣ` are `R` only by definition.
  rfl

end Units

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [LieGroup I' ∞ G']

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

namespace ContMDiffMonoidMorphism

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
    ← leftInvariantDerivationLieEquivGroupLieAlgebra_symm_groupLieAlgebraMap,
    LieEquiv.apply_symm_apply, coe_groupLieAlgebraLieHom]

/-- The Lie algebra map of an injective smooth homomorphism is injective. -/
theorem groupLieAlgebraLieHom_injective (φ : ContMDiffMonoidMorphism I I' ∞ G G')
    (hφ : Injective φ) : Injective φ.groupLieAlgebraLieHom := by
  let f : G →ₜ* G' := ⟨φ.toMonoidHom, φ.contMDiff_toFun.continuous⟩
  have : Subsingleton f.ker :=
    ⟨fun a b ↦ Subtype.ext (hφ (a.property.trans b.property.symm))⟩
  intro ξ η h
  rw [coe_groupLieAlgebraLieHom, MonoidHom.groupLieAlgebraMap_apply,
    MonoidHom.groupLieAlgebraMap_apply] at h
  exact ContinuousMonoidHom.injective_mfderiv_of_discreteTopology_ker (I := I) (I' := I') f 1 h

end ContMDiffMonoidMorphism
