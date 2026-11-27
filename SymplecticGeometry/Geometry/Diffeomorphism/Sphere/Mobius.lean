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
import Mathlib.Analysis.Complex.Polynomial.Basic
import SymplecticGeometry.Geometry.Manifold.Complex.Pullback
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Instances.OnePoint.Automorphism

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
biholomorphism of the Riemann sphere. The proof that it is a Möbius transformation follows Tau
Ceti's `Diffeomorph.exists_coe_eq_smul`, with `PSL(2, ℂ)` in place of `GL(2, ℂ)`: the element of
`PSL(2, ℂ)` that agrees with `φ` at `0`, `1` and `∞`
(`OnePoint.existsUnique_psl_smul_zero_one_infty_eq`)
differs from `φ` by a biholomorphism fixing these three points, which is the identity
(`Diffeomorph.eq_refl_of_apply_zero_one_infty_eq_self`).

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
noncomputable def mobiusHom : PSL(2, ℂ) →* TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞ where
  toFun g := Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g
  map_one' := Diffeomorph.constSmul_one
  map_mul' g h := Diffeomorph.constSmul_mul g h

/-- The Möbius transformation of `g` is the diffeomorphism `Diffeomorph.constSmul` of `g`. -/
theorem mobiusHom_def (g : PSL(2, ℂ)) : mobiusHom g = Diffeomorph.constSmul 𝓘(ℝ, ℂ) ∞ g := (rfl)

/-- The Möbius transformation of `g` sends `x` to `g • x`. -/
@[simp]
theorem mobiusHom_apply (g : PSL(2, ℂ)) (x : OnePoint ℂ) : mobiusHom g x = g • x := by
  rw [mobiusHom_def, Diffeomorph.constSmul_apply]

/-- The Möbius transformation of `g` is the map `x ↦ g • x`. -/
theorem coe_mobiusHom (g : PSL(2, ℂ)) : ⇑(mobiusHom g) = fun x ↦ g • x :=
  funext (mobiusHom_apply g)

/-- Distinct elements of `PSL(2, ℂ)` give distinct diffeomorphisms of the sphere. -/
theorem mobiusHom_injective : Function.Injective mobiusHom :=
  Diffeomorph.constSmul_injective (I := 𝓘(ℝ, ℂ)) (n := ∞)

/-- The Möbius group as a subgroup of the diffeomorphisms of the sphere: the diffeomorphisms `φ`
that pull the almost complex structure `i` of the Riemann sphere back to itself. -/
noncomputable def mobiusSubgroup : Subgroup (TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) where
  carrier := {φ | (ofComplexManifold ℂ (OnePoint ℂ)).pullback φ = ofComplexManifold ℂ (OnePoint ℂ)}
  one_mem' := pullback_refl _
  mul_mem' {φ ψ} hφ hψ := by
    simp only [Set.mem_ofPred_eq, Diffeomorph.mul_def, pullback_trans] at hφ hψ ⊢
    rw [hφ, hψ]
  inv_mem' {φ} hφ := pullback_symm_eq_of_pullback_eq φ hφ

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
  · -- `φ` is a biholomorphism of the Riemann sphere.
    let f : OnePoint ℂ ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ OnePoint ℂ :=
      { toEquiv := φ.toEquiv
        contMDiff_toFun := ((pullback_ofComplexManifold_eq_iff φ).1 h).contMDiff
        contMDiff_invFun := (mdifferentiable_symm_of_pullback_eq φ h).contMDiff }
    have hf (x : OnePoint ℂ) : f x = φ x := rfl
    obtain ⟨g, ⟨h0, h1, hinf⟩, -⟩ := OnePoint.existsUnique_psl_smul_zero_one_infty_eq
      (φ.injective.ne (by simp : ((0 : ℂ) : OnePoint ℂ) ≠ (1 : ℂ)))
      (φ.injective.ne (OnePoint.coe_ne_infty 0)) (φ.injective.ne (OnePoint.coe_ne_infty 1))
    -- It differs from `g` by a biholomorphism fixing `0`, `1` and `∞`.
    have hid := (f.trans (Diffeomorph.constSmul 𝓘(ℂ) 1 g⁻¹)).eq_refl_of_apply_zero_one_infty_eq_self
      one_ne_zero (by simp [hf, inv_smul_eq_iff, h0]) (by simp [hf, inv_smul_eq_iff, h1])
      (by simp [hf, inv_smul_eq_iff, hinf])
    refine ⟨g, Diffeomorph.ext fun x ↦ ?_⟩
    have hx := congr($hid x)
    simp only [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.constSmul_apply,
      Diffeomorph.coe_refl, id, hf] at hx
    rw [mobiusHom_apply]
    exact inv_smul_eq_iff.mp hx
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
