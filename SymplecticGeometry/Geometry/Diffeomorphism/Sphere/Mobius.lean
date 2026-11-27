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
import SymplecticGeometry.Geometry.Manifold.Algebra.SMul
import SymplecticGeometry.Geometry.Manifold.Complex.Pullback
import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.Automorphism
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# Möbius transformations as the stabilizer of the complex structure of the sphere

Regard the Riemann sphere `OnePoint ℂ` as a real surface, with the model `𝓘(ℝ, ℂ)`, and let `i`
be its almost complex structure `ofComplexManifold ℂ (OnePoint ℂ)`. This file identifies the
Möbius group with the diffeomorphisms of this surface that pull `i` back to itself.

## Main definitions

* `SymplecticGeometry.mobiusHom`: the homomorphism from `PSL(2, ℂ)` to the group of smooth
  diffeomorphisms of the sphere, sending `g` to `x ↦ g • x`.
* `SymplecticGeometry.mobiusSubgroup`: the subgroup of diffeomorphisms `φ` with `φ^* i = i`.

## Main results

* `SymplecticGeometry.mobiusHom_injective`: distinct elements of `PSL(2, ℂ)` act differently.
* `SymplecticGeometry.pullback_ofComplexManifold_onePoint_eq_self_iff`: a diffeomorphism `φ` of
  the sphere has `φ^* i = i` exactly when it is `mobiusHom g` for some `g`.
* `SymplecticGeometry.mobiusSubgroup_eq_range`: so `mobiusSubgroup` is the range of `mobiusHom`.

A diffeomorphism with `φ^* i = i` and its inverse are holomorphic
(`TauCeti.SmoothAlmostComplexStructure.pullback_ofComplexManifold_eq_iff`), so `φ` is a
biholomorphism of the Riemann sphere, and so `x ↦ g • x` for some `g` in `PSL(2, ℂ)`
(`Diffeomorph.exists_coe_eq_psl_smul`, from Tau Ceti's `Diffeomorph.exists_coe_eq_smul`).

## References

* [C. J. Earle, J. Eells, *The diffeomorphism group of a compact Riemann
  surface*][EarleEells1967]
* [S. Smale, *Diffeomorphisms of the 2-sphere*][Smale1959]
-/

public section

open TauCeti TauCeti.SmoothAlmostComplexStructure
open scoped Manifold ContDiff MatrixGroups TauCeti.ComplexManifold

namespace SymplecticGeometry

/-- The Möbius transformations as diffeomorphisms of the Riemann sphere regarded as a real surface:
the homomorphism sending `g ∈ PSL(2, ℂ)` to the smooth diffeomorphism `x ↦ g • x`. -/
noncomputable def mobiusHom : PSL(2, ℂ) →* TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞ :=
  Diffeomorph.constSmulHom 𝓘(ℝ, ℂ) ∞

/-- The Möbius transformation of `g` is the diffeomorphism `Diffeomorph.constSmul` of `g`. -/
theorem mobiusHom_def (g : PSL(2, ℂ)) : mobiusHom g = Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g := by
  rw [mobiusHom, Diffeomorph.constSmulHom_apply]

/-- The Möbius transformation of `g` sends `x` to `g • x`. -/
@[simp]
theorem mobiusHom_apply (g : PSL(2, ℂ)) (x : OnePoint ℂ) : mobiusHom g x = g • x := by
  rw [mobiusHom_def, Diffeomorph.constSmul_apply]

/-- The Möbius transformation of `g` is the map `x ↦ g • x`. -/
theorem coe_mobiusHom (g : PSL(2, ℂ)) : ⇑(mobiusHom g) = fun x ↦ g • x :=
  funext (mobiusHom_apply g)

/-- Distinct elements of `PSL(2, ℂ)` give distinct diffeomorphisms of the sphere. -/
theorem mobiusHom_injective : Function.Injective mobiusHom :=
  Diffeomorph.constSmulHom_injective

/-- The Möbius group as a subgroup of the diffeomorphisms of the sphere: the diffeomorphisms `φ`
that pull the almost complex structure `i` of the Riemann sphere back to itself. -/
noncomputable def mobiusSubgroup : Subgroup (TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) where
  carrier := {φ | (ofComplexManifold ℂ (OnePoint ℂ)).pullback φ = ofComplexManifold ℂ (OnePoint ℂ)}
  one_mem' := pullback_refl _
  mul_mem' {φ ψ} hφ hψ := by
    simp only [Set.mem_ofPred_eq, Diffeomorph.mul_def, pullback_trans] at hφ hψ ⊢
    rw [hφ, hψ]
  inv_mem' {φ} hφ := (pullback_symm_eq_iff φ).2 hφ

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

end SymplecticGeometry

end
