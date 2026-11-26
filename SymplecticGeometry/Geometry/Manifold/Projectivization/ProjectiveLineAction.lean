/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import SymplecticGeometry.Geometry.Manifold.RegularValue.CriticalSet
public import TauCeti.Geometry.Manifold.Projectivization.ProjectiveLine
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.RestrictScalars
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.Projectivization.Map

/-!
# Projective transformations of the projective line and maps into it

A matrix `g : GL (Fin 2) ℂ` acts on `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` by a biholomorphism, Tau Ceti's
`Diffeomorph.constSmul`; on the underlying real manifold it is a diffeomorphism
`Projectivization.smulDiffeomorph g`. Postcomposing a map `π : X → ℂℙ¹` with it changes neither
its critical set nor, up to the move by `g`, its regular values. Since `SL₂(ℂ)` acts
two-transitively on `ℂℙ¹`, a map with finitely many critical points can thus be moved so that a
given regular value and some second one land on any two prescribed distinct points.

## Main results

* `Matrix.SpecialLinearGroup.toGL_smul`: `SL_n(K)` acts on `ℙ K (n → K)` through `GL_n(K)`.
* `Projectivization.smulDiffeomorph`: the diffeomorphism `g • ·` of the real manifold `ℂℙ¹`.
* `Projectivization.criticalSet_smul`, `Projectivization.isRegularValue_smul_iff`: moving a map
  into `ℂℙ¹` by `g` keeps its critical set and moves its regular values by `g`.
* `Projectivization.exists_smul_isRegularValue`: for a map into `ℂℙ¹` with finitely many critical
  points, a regular value `y` and distinct points `z₀`, `z₁`, some `g` sends `y` to `z₀` and makes
  both `z₀` and `z₁` regular values of `x ↦ g • π x`.
-/

public section

open Set TauCeti
open scoped Manifold LinearAlgebra.Projectivization

namespace Matrix.SpecialLinearGroup

/-- A special linear matrix acts on the projective space `ℙ K (n → K)` as its image in the general
linear group does. -/
theorem toGL_smul {n K : Type*} [Fintype n] [DecidableEq n] [Field K] (g : SpecialLinearGroup n K)
    (x : ℙ K (n → K)) : toGL g • x = g • x := by
  induction x using Projectivization.ind with
  | h v hv => simp [Projectivization.smul_mk, SpecialLinearGroup.smul_def, Units.smul_def]

end Matrix.SpecialLinearGroup

namespace Projectivization

/-- The projective line `ℂℙ¹` is infinite: the affine coordinate `t ↦ [1 : t]` is injective. -/
instance infinite_projectiveLine : Infinite (ℙ ℂ (Fin 2 → ℂ)) :=
  Infinite.of_injective (ProjectiveLine.affineParam 0) fun s t hst ↦ by
    simpa using congrFun (congrArg (affineChart (K := ℂ) (n := 1) 0) hst) 0

/-- The diffeomorphism `g • ·` of `ℂℙ¹` for a projective transformation `g`, on the underlying
real manifold. -/
noncomputable def smulDiffeomorph (g : GL (Fin 2) ℂ) :
    ℙ ℂ (Fin 2 → ℂ) ≃ₘ^⊤⟮𝓘(ℝ, Fin 1 → ℂ), 𝓘(ℝ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ) :=
  (Diffeomorph.constSmul 𝓘(ℂ, Fin 1 → ℂ) ⊤ g :
    ℙ ℂ (Fin 2 → ℂ) ≃ₘ^⊤⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ)).restrictScalars' ℝ

/-- The diffeomorphism `smulDiffeomorph g` is the map `x ↦ g • x`. -/
@[simp]
theorem coe_smulDiffeomorph (g : GL (Fin 2) ℂ) : ⇑(smulDiffeomorph g) = (g • ·) := by
  rw [smulDiffeomorph, Diffeomorph.coe_restrictScalars', Diffeomorph.coe_constSmul]

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  (g : GL (Fin 2) ℂ) (π : X → ℙ ℂ (Fin 2 → ℂ))

/-- Moving a map into `ℂℙ¹` by a projective transformation `g` does not change its critical
set. -/
theorem criticalSet_smul :
    SymplecticGeometry.criticalSet I 𝓘(ℝ, Fin 1 → ℂ) (fun x ↦ g • π x) =
      SymplecticGeometry.criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π := by
  simpa [Function.comp_def] using (smulDiffeomorph g).criticalSet_comp (I := I) (by simp) π

/-- Moving a map `π` into `ℂℙ¹` by a projective transformation `g` moves its regular values:
`g • y` is a regular value of `x ↦ g • π x` exactly when `y` is one of `π`. -/
theorem isRegularValue_smul_iff {y : ℙ ℂ (Fin 2 → ℂ)} :
    IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) (fun x ↦ g • π x) (g • y) ↔
      IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π y := by
  simpa [Function.comp_def] using
    (smulDiffeomorph g).comp_isRegularValue_iff (I := I) (f := π) (y := y) (by simp)

variable {g π}

/-- **Moving two regular values to two given points.** Let `π : X → ℂℙ¹` have finitely many
critical points, let `y` be a regular value of `π`, and let `z₀ ≠ z₁` be points of `ℂℙ¹`. Then
some projective transformation `g` sends `y` to `z₀` and makes both `z₀` and `z₁` regular values
of `x ↦ g • π x`. -/
theorem exists_smul_isRegularValue
    (hfin : (SymplecticGeometry.criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π).Finite) {y : ℙ ℂ (Fin 2 → ℂ)}
    (hy : IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π y) {z₀ z₁ : ℙ ℂ (Fin 2 → ℂ)} (hz : z₀ ≠ z₁) :
    ∃ g : GL (Fin 2) ℂ, g • y = z₀ ∧ IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) (fun x ↦ g • π x) z₀ ∧
      IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) (fun x ↦ g • π x) z₁ := by
  obtain ⟨b, hb⟩ := ((hfin.image π).insert y).infinite_compl.nonempty
  rw [mem_compl_iff, mem_insert_iff, not_or] at hb
  have hb' : b ∈ {y | IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π y} := by
    rw [setOf_isRegularValue_eq_compl_image, ← SymplecticGeometry.criticalSet_def]
    exact mem_compl hb.2
  rw [mem_ofPred_eq] at hb'
  -- `SL₂(ℂ)` acts two-transitively on `ℂℙ¹`.
  obtain ⟨g, hg₀, hg₁⟩ := MulAction.is_two_pretransitive_iff.1
    (inferInstance : MulAction.IsMultiplyPretransitive (Matrix.SpecialLinearGroup (Fin 2) ℂ)
      (ℙ ℂ (Fin 2 → ℂ)) 2) (Ne.symm hb.1) hz
  refine ⟨Matrix.SpecialLinearGroup.toGL g, by rw [Matrix.SpecialLinearGroup.toGL_smul, hg₀],
    ?_, ?_⟩
  · rwa [← hg₀, ← Matrix.SpecialLinearGroup.toGL_smul, isRegularValue_smul_iff]
  · rwa [← hg₁, ← Matrix.SpecialLinearGroup.toGL_smul, isRegularValue_smul_iff]

end Projectivization

end
