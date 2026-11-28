/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
public import TauCeti.Analysis.Matrix.Polar.SpecialLinear
public import TauCeti.Geometry.Diffeomorphism.Topology
public import TauCeti.Geometry.Manifold.Instances.OnePoint.PSLAction
public import SymplecticGeometry.Geometry.Diffeomorphism.Sphere.ComplexStructure
public import SymplecticGeometry.Geometry.Manifold.Algebra.SMul
import Mathlib.Analysis.Complex.Polynomial.Basic
import SymplecticGeometry.Geometry.Manifold.Complex.Pullback
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.Automorphism
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Diffeomorphism.LieGroup
import TauCeti.Geometry.Manifold.Instances.OnePoint.DistinctTriples
import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# The Möbius group as the stabilizer of the complex structure of the sphere

Regard the Riemann sphere `OnePoint ℂ` as a real surface, with the model `𝓘(ℝ, ℂ)`, and let `i`
be its almost complex structure `ofComplexManifold ℂ (OnePoint ℂ)`. This file identifies the
Möbius group with the diffeomorphisms of this surface that pull `i` back to itself, as a group and
as a topological group, and deformation retracts it onto the rotations.

## Main definitions

* `SymplecticGeometry.mobiusHom`: the homomorphism from `PSL(2, ℂ)` to the group of smooth
  diffeomorphisms of the sphere, sending `g` to `x ↦ g • x`.
* `SymplecticGeometry.mobiusSubgroup`: the subgroup of diffeomorphisms `φ` with `φ^* i = i`.
* `SymplecticGeometry.mobiusEquiv`: the isomorphism of topological groups from `PSL(2, ℂ)`, with
  Tau Ceti's quotient topology, onto `mobiusSubgroup`, with the subspace topology of the weak
  Whitney topology.
* `SymplecticGeometry.rotationSubgroup`: the rotations, the image of `PSU(2)` under `mobiusHom`.
* `SymplecticGeometry.mobiusPolarRetraction` and `SymplecticGeometry.mobiusPolarHomotopy`: the
  polar retraction of `mobiusSubgroup` onto the rotations, and a homotopy relative to the
  rotations from the identity to it.

## Main results

* `OnePoint.instContMDiffSMulPSLReal`: the action of `PSL(2, ℂ)` on the sphere is jointly `Cⁿ`
  over `ℝ`, for every `n`.
* `SymplecticGeometry.mobiusHom_injective`: distinct elements of `PSL(2, ℂ)` act differently.
* `SymplecticGeometry.pullback_ofComplexManifold_onePoint_eq_self_iff`: a diffeomorphism `φ` of
  the sphere has `φ^* i = i` exactly when it is `mobiusHom g` for some `g`.
* `SymplecticGeometry.mobiusSubgroup_eq_range`: so `mobiusSubgroup` is the range of `mobiusHom`.
* `SymplecticGeometry.mobiusSubgroup_le_diffPlus`: Möbius transformations preserve the
  orientation.
* `SymplecticGeometry.continuous_mobiusHom` and `SymplecticGeometry.isEmbedding_mobiusHom`:
  `mobiusHom` is a topological embedding.
* `SymplecticGeometry.rotationSubgroup_le_mobiusSubgroup`: rotations are Möbius transformations.

A diffeomorphism with `φ^* i = i` and its inverse are holomorphic
(`TauCeti.SmoothAlmostComplexStructure.pullback_ofComplexManifold_eq_iff`), so `φ` is a
biholomorphism of the Riemann sphere, and so `x ↦ g • x` for some `g` in `PSL(2, ℂ)`
(`Diffeomorph.exists_coe_eq_psl_smul`, from Tau Ceti's `Diffeomorph.exists_coe_eq_smul`).

The map `mobiusHom` is continuous because the action of `PSL(2, ℂ)` on the sphere is jointly
analytic (Tau Ceti's `OnePoint.instContMDiffSMulPSL`), hence jointly smooth over `ℝ`, so it is
Tau Ceti's continuous homomorphism `Diffeomorph.smulContinuousMonoidHom`. It is an embedding
because evaluation at `0`, `1`, `∞` after it is Tau Ceti's homeomorphism
`OnePoint.pslHomeomorphDistinctTriples` of `PSL(2, ℂ)` onto the triples of distinct points.
The homotopy `mobiusPolarHomotopy` is Tau Ceti's
`Matrix.ProjectiveSpecialLinearGroup.polarHomotopy (Fin 2) ℂ`, conjugated by `mobiusEquiv` with
Tau Ceti's `ContinuousMap.HomotopyRel.precomp`.

## References

* [C. J. Earle, J. Eells, *The diffeomorphism group of a compact Riemann
  surface*][EarleEells1967]
* [S. Smale, *Diffeomorphisms of the 2-sphere*][Smale1959]
-/

public section

open TauCeti TauCeti.SmoothAlmostComplexStructure Matrix
open scoped Manifold ContDiff MatrixGroups TauCeti.ComplexManifold TauCeti.DiffeomorphWeakWhitney

namespace OnePoint

/-- The Möbius action of `PSL(2, ℂ)` on the Riemann sphere, both regarded as real manifolds, is
jointly `Cⁿ` for every `n`, since it is jointly analytic over `ℂ`. -/
instance instContMDiffSMulPSLReal (n : ℕ∞ω) :
    ContMDiffSMul 𝓘(ℝ, SpecialLinearGroup.Model (Fin 2) ℂ) 𝓘(ℝ, ℂ) n PSL(2, ℂ) (OnePoint ℂ) where
  contMDiff_smul := by
    have h := (contMDiff_smul (I := 𝓘(ℂ, SpecialLinearGroup.Model (Fin 2) ℂ)) (I' := 𝓘(ℂ))
      (n := ω) (G := PSL(2, ℂ)) (M := OnePoint ℂ)).restrictScalars ℝ
    rw [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars,
      modelWithCornersSelf_restrictScalars] at h
    exact h.of_le le_top

end OnePoint

namespace SymplecticGeometry

/-- The Möbius transformations as diffeomorphisms of the Riemann sphere regarded as a real surface:
the homomorphism sending `g ∈ PSL(2, ℂ)` to the smooth diffeomorphism `x ↦ g • x`. -/
noncomputable def mobiusHom : PSL(2, ℂ) →* TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞ :=
  Diffeomorph.constSmulHom 𝓘(ℝ, ℂ) ∞

/-- The Möbius homomorphism is `Diffeomorph.constSmulHom` for the action of `PSL(2, ℂ)` on the
sphere. -/
theorem mobiusHom_def : mobiusHom = Diffeomorph.constSmulHom 𝓘(ℝ, ℂ) ∞ := (rfl)

/-- The Möbius transformation of `g` sends `x` to `g • x`. -/
@[simp]
theorem mobiusHom_apply (g : PSL(2, ℂ)) (x : OnePoint ℂ) : mobiusHom g x = g • x := by
  rw [mobiusHom_def, Diffeomorph.constSmulHom_apply, Diffeomorph.constSmul_apply]

/-- The Möbius transformation of `g` is the map `x ↦ g • x`. -/
theorem coe_mobiusHom (g : PSL(2, ℂ)) : ⇑(mobiusHom g) = fun x ↦ g • x :=
  funext (mobiusHom_apply g)

/-- Distinct elements of `PSL(2, ℂ)` give distinct diffeomorphisms of the sphere. -/
theorem mobiusHom_injective : Function.Injective mobiusHom :=
  mobiusHom_def ▸ Diffeomorph.constSmulHom_injective

/-- The Möbius group as a subgroup of the diffeomorphisms of the sphere: the diffeomorphisms `φ`
that pull the almost complex structure `i` of the Riemann sphere back to itself. -/
noncomputable def mobiusSubgroup : Subgroup (TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) where
  carrier := {φ | (ofComplexManifold ℂ (OnePoint ℂ)).pullback φ = ofComplexManifold ℂ (OnePoint ℂ)}
  one_mem' := pullback_one _
  mul_mem' {φ ψ} hφ hψ := by
    simp only [Set.mem_ofPred_eq, pullback_mul] at hφ hψ ⊢
    rw [hφ, hψ]
  inv_mem' {φ} hφ := (pullback_inv_eq_iff φ).2 hφ

/-- A diffeomorphism of the sphere lies in `mobiusSubgroup` exactly when it pulls the almost
complex structure of the Riemann sphere back to itself. -/
theorem mem_mobiusSubgroup_iff {φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞} :
    φ ∈ mobiusSubgroup ↔
      (ofComplexManifold ℂ (OnePoint ℂ)).pullback φ = ofComplexManifold ℂ (OnePoint ℂ) :=
  Iff.rfl

/-- A smooth diffeomorphism of the Riemann sphere, regarded as a real surface, pulls its almost
complex structure back to itself exactly when it is a Möbius transformation of `PSL(2, ℂ)`. -/
theorem pullback_ofComplexManifold_onePoint_eq_self_iff
    {φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞} :
    (ofComplexManifold ℂ (OnePoint ℂ)).pullback φ = ofComplexManifold ℂ (OnePoint ℂ) ↔
      ∃ g, φ = mobiusHom g := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- `φ` is a biholomorphism of the Riemann sphere, hence a Möbius transformation.
    let f : OnePoint ℂ ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ OnePoint ℂ :=
      { toEquiv := φ.toEquiv
        contMDiff_toFun := ((pullback_ofComplexManifold_eq_iff φ).1 h).contMDiff
        contMDiff_invFun := (mdifferentiable_symm_of_pullback_eq φ h).contMDiff }
    obtain ⟨g, hg⟩ := f.exists_coe_eq_psl_smul one_ne_zero
    have hf : ⇑f = ⇑φ := by rw [← f.coe_toEquiv, ← φ.coe_toEquiv]
    exact ⟨g, Diffeomorph.ext fun x ↦ by rw [mobiusHom_apply, ← congrFun hg x, hf]⟩
  · -- A Möbius transformation is holomorphic.
    rintro ⟨g, rfl⟩
    rw [pullback_ofComplexManifold_eq_iff, coe_mobiusHom]
    exact (contMDiff_const_smul (I := 𝓘(ℂ)) (n := 1) g).mdifferentiable one_ne_zero

/-- The Möbius group of the sphere is the image of `PSL(2, ℂ)`. -/
theorem mobiusSubgroup_eq_range : mobiusSubgroup = mobiusHom.range := by
  ext φ
  rw [mem_mobiusSubgroup_iff, pullback_ofComplexManifold_onePoint_eq_self_iff, MonoidHom.mem_range]
  exact exists_congr fun g ↦ eq_comm

/-- A Möbius transformation preserves the orientation of the sphere: `mobiusSubgroup` lies in
`diffPlus`. -/
theorem mobiusSubgroup_le_diffPlus : mobiusSubgroup ≤ diffPlus := fun φ hφ ↦ by
  rw [mem_diffPlus_iff_tames_pullback, mem_mobiusSubgroup_iff.1 hφ]
  exact OnePoint.compatible_fubiniStudyForm.tames

/-! ### The topology of the Möbius group -/

/-- The Möbius homomorphism is continuous from the quotient topology of `PSL(2, ℂ)` to the weak
Whitney topology. -/
theorem continuous_mobiusHom : Continuous mobiusHom := by
  refine (map_continuous <| Diffeomorph.smulContinuousMonoidHom
    𝓘(ℝ, SpecialLinearGroup.Model (Fin 2) ℂ) 𝓘(ℝ, ℂ) ∞ PSL(2, ℂ) (OnePoint ℂ)).congr fun g ↦ ?_
  ext x
  rw [Diffeomorph.smulContinuousMonoidHom_apply_apply, mobiusHom_apply]

/-- The Möbius homomorphism is a topological embedding of `PSL(2, ℂ)` into the diffeomorphisms
of the sphere with the weak Whitney topology. -/
theorem isEmbedding_mobiusHom : Topology.IsEmbedding mobiusHom := by
  -- Evaluation at `0`, `1`, `∞` after `mobiusHom` is Tau Ceti's homeomorphism of `PSL(2, ℂ)`
  -- onto the triples of distinct points, followed by the inclusion of the triples.
  let b : OnePoint.distinctTriples ℂ :=
    ⟨_, OnePoint.mem_distinctTriples.2 (OnePoint.zeroOneInftyTriple ℂ).property⟩
  have hev : Continuous fun φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞ ↦
      fun i ↦ φ ((b : Fin 3 → OnePoint ℂ) i) :=
    continuous_pi fun i ↦ Diffeomorph.continuous_eval_const _
  refine Topology.IsEmbedding.of_comp continuous_mobiusHom hev ?_
  convert Topology.IsEmbedding.subtypeVal.comp
    (OnePoint.pslHomeomorphDistinctTriples b).isEmbedding using 1
  ext g i
  simp only [Function.comp_apply, mobiusHom_apply, OnePoint.pslHomeomorphDistinctTriples_apply_coe]

/-- Every Möbius transformation lies in `mobiusSubgroup`. -/
@[simp]
theorem mobiusHom_mem_mobiusSubgroup (g : PSL(2, ℂ)) : mobiusHom g ∈ mobiusSubgroup :=
  mobiusSubgroup_eq_range ▸ ⟨g, rfl⟩

/-- **The Möbius group as a topological group.** `PSL(2, ℂ)`, with its quotient topology, is
isomorphic as a topological group to `mobiusSubgroup`, the stabilizer of `i` among the
diffeomorphisms of the sphere, with the subspace topology of the weak Whitney topology. The
isomorphism sends `g` to `x ↦ g • x`. -/
noncomputable def mobiusEquiv : PSL(2, ℂ) ≃ₜ* mobiusSubgroup :=
  let e : PSL(2, ℂ) ≃* mobiusSubgroup := (MonoidHom.ofInjective mobiusHom_injective).trans
    (MulEquiv.subgroupCongr mobiusSubgroup_eq_range.symm)
  .mk' (e.toEquiv.toHomeomorphOfIsInducing
    (isEmbedding_mobiusHom.codRestrict _ mobiusHom_mem_mobiusSubgroup).isInducing) (map_mul e)

/-- The image of `g` under `mobiusEquiv` is the Möbius transformation `mobiusHom g`. -/
@[simp]
theorem coe_mobiusEquiv_apply (g : PSL(2, ℂ)) :
    (mobiusEquiv g : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) = mobiusHom g :=
  (rfl)

/-- The Möbius transformation of the preimage of `φ` under `mobiusEquiv` is `φ`. -/
@[simp]
theorem mobiusHom_mobiusEquiv_symm_apply (φ : mobiusSubgroup) :
    mobiusHom (mobiusEquiv.symm φ) = φ := by
  rw [← coe_mobiusEquiv_apply, ContinuousMulEquiv.apply_symm_apply]

/-- The preimage under `mobiusEquiv` of the Möbius transformation of `g` is `g`. -/
@[simp]
theorem mobiusEquiv_symm_apply_mk (g : PSL(2, ℂ)) (h : mobiusHom g ∈ mobiusSubgroup) :
    mobiusEquiv.symm ⟨mobiusHom g, h⟩ = g :=
  mobiusEquiv.symm_apply_eq.2 (Subtype.ext (coe_mobiusEquiv_apply g).symm)

/-! ### The rotations and the polar retraction -/

/-- The rotations of the sphere: the image under `mobiusHom` of `PSU(2)`, the image of the special
unitary group `SU(2)` in `PSL(2, ℂ)`. -/
noncomputable def rotationSubgroup : Subgroup (TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) :=
  (specialUnitaryGroup.toPSL : specialUnitaryGroup (Fin 2) ℂ →* PSL(2, ℂ)).range.map mobiusHom

/-- The rotations are the image of `PSU(2)` under `mobiusHom`. -/
theorem rotationSubgroup_def : rotationSubgroup =
    (specialUnitaryGroup.toPSL : specialUnitaryGroup (Fin 2) ℂ →* PSL(2, ℂ)).range.map mobiusHom :=
  (rfl)

/-- A diffeomorphism of the sphere is a rotation exactly when it is the Möbius transformation of
the class of a special unitary matrix. -/
theorem mem_rotationSubgroup_iff {φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞} :
    φ ∈ rotationSubgroup ↔ ∃ k : specialUnitaryGroup (Fin 2) ℂ,
      mobiusHom (specialUnitaryGroup.toPSL k) = φ := by
  simp [rotationSubgroup_def]

/-- The rotations are Möbius transformations. -/
theorem rotationSubgroup_le_mobiusSubgroup : rotationSubgroup ≤ mobiusSubgroup :=
  mobiusSubgroup_eq_range ▸ Subgroup.map_le_range _ _

/-- An element of `mobiusSubgroup` is a rotation exactly when its preimage under `mobiusEquiv`
lies in `PSU(2)`. -/
theorem coe_mem_rotationSubgroup_iff {φ : mobiusSubgroup} :
    (φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) ∈ rotationSubgroup ↔
      mobiusEquiv.symm φ ∈
        (specialUnitaryGroup.toPSL : specialUnitaryGroup (Fin 2) ℂ →* PSL(2, ℂ)).range := by
  rw [rotationSubgroup_def, Subgroup.mem_map]
  refine ⟨?_, fun h ↦ ⟨_, h, ?_⟩⟩
  · rintro ⟨g, hg, hgφ⟩
    rwa [show φ = mobiusEquiv g from Subtype.ext hgφ.symm, ContinuousMulEquiv.symm_apply_apply]
  · exact mobiusHom_mobiusEquiv_symm_apply φ

/-- The polar retraction of the Möbius group onto the rotations: Tau Ceti's polar retraction
`PSL(2, ℂ) → PSU(2)`, carried to `mobiusSubgroup` by `mobiusEquiv`. -/
noncomputable def mobiusPolarRetraction : C(mobiusSubgroup, mobiusSubgroup) where
  toFun φ := mobiusEquiv (ProjectiveSpecialLinearGroup.polarRetraction (Fin 2) ℂ
    (mobiusEquiv.symm φ))
  continuous_toFun := by fun_prop

/-- The polar retraction of `φ` is the Möbius transformation of the polar retraction of the
preimage of `φ` in `PSL(2, ℂ)`. -/
@[simp]
theorem coe_mobiusPolarRetraction_apply (φ : mobiusSubgroup) :
    (mobiusPolarRetraction φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) =
      mobiusHom (ProjectiveSpecialLinearGroup.polarRetraction (Fin 2) ℂ (mobiusEquiv.symm φ)) :=
  (rfl)

/-- The polar retraction takes its values in the rotations. -/
theorem coe_mobiusPolarRetraction_mem_rotationSubgroup (φ : mobiusSubgroup) :
    (mobiusPolarRetraction φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) ∈ rotationSubgroup := by
  rw [coe_mobiusPolarRetraction_apply, rotationSubgroup_def]
  exact Subgroup.mem_map_of_mem _ (Subtype.property _)

/-- **The Möbius group deformation retracts onto the rotations.** Tau Ceti's polar homotopy
`ProjectiveSpecialLinearGroup.polarHomotopy (Fin 2) ℂ`, carried to `mobiusSubgroup` by
`mobiusEquiv`: a homotopy from the identity of `mobiusSubgroup` to the polar retraction onto the
rotations, which fixes every rotation at all times. -/
noncomputable def mobiusPolarHomotopy :
    (ContinuousMap.id mobiusSubgroup).HomotopyRel mobiusPolarRetraction
      {φ | (φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) ∈ rotationSubgroup} :=
  -- The two `show`s state the set and the end map as in the type, so that the lemmas about
  -- `cast` and `mono` rewrite applications of `mobiusPolarHomotopy`.
  ((((ProjectiveSpecialLinearGroup.polarHomotopy (Fin 2) ℂ).precomp
    (mobiusEquiv.symm : C(mobiusSubgroup, PSL(2, ℂ)))).compContinuousMap
      (mobiusEquiv : C(PSL(2, ℂ), mobiusSubgroup))).mono
        (show {φ : mobiusSubgroup | (φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) ∈
          rotationSubgroup} ⊆ _ from fun _ ↦ coe_mem_rotationSubgroup_iff.1)).cast
    (ContinuousMap.ext fun φ ↦ mobiusEquiv.apply_symm_apply φ)
    (show _ = mobiusPolarRetraction from rfl)

/-- The polar homotopy of the Möbius group at time `t` sends `φ` to the Möbius transformation of
the polar homotopy of `PSL(2, ℂ)` at time `t` applied to the preimage of `φ`. -/
@[simp]
theorem coe_mobiusPolarHomotopy_apply (t : unitInterval) (φ : mobiusSubgroup) :
    (mobiusPolarHomotopy (t, φ) : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) =
      mobiusHom (ProjectiveSpecialLinearGroup.polarHomotopy (Fin 2) ℂ (t, mobiusEquiv.symm φ)) := by
  rw [mobiusPolarHomotopy, ContinuousMap.HomotopyRel.cast_apply,
    ContinuousMap.HomotopyRel.mono_apply, ContinuousMap.HomotopyRel.compContinuousMap_apply,
    ContinuousMap.HomotopyRel.precomp_apply, ContinuousMap.coe_ofClass, ContinuousMap.coe_ofClass,
    coe_mobiusEquiv_apply]

end SymplecticGeometry

end
