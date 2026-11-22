/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# Restricting the scalars of diffeomorphisms to the trivial models

Let `𝕜'` be a normed algebra over `𝕜`, and let the model spaces be normed spaces over both fields,
compatibly. A `C^n` diffeomorphism for the trivial models `𝓘(𝕜', E)` and `𝓘(𝕜', E')` is, with the
same underlying equivalence, a `C^n` diffeomorphism for `𝓘(𝕜, E)` and `𝓘(𝕜, E')`, by
`ContMDiff.restrictScalars'`. Tau Ceti's `Diffeomorph.restrictScalars` gives it for the models
`𝓘(𝕜', E).restrictScalars 𝕜` and `𝓘(𝕜', E').restrictScalars 𝕜`, which equal the trivial models
over `𝕜` only propositionally; the definition here avoids that cast. It and its lemmas follow
Tau Ceti's `Diffeomorph.restrictScalars`, `Diffeomorph.coe_restrictScalars`,
`Diffeomorph.restrictScalars_refl`, `Diffeomorph.restrictScalars_symm` and
`Diffeomorph.restrictScalars_trans`, for the trivial models.

The main example is a biholomorphism between complex manifolds modelled on `𝓘(ℂ, E)` and
`𝓘(ℂ, E')`, which is a diffeomorphism for the models `𝓘(ℝ, E)` and `𝓘(ℝ, E')` of the underlying
real manifolds.

## Main definitions

* `Diffeomorph.restrictScalars'`: a diffeomorphism for the trivial models over `𝕜'` regarded as a
  diffeomorphism for the trivial models over `𝕜`.

## Main results

* `Diffeomorph.coe_restrictScalars'`: it has the same underlying map.
* `Diffeomorph.restrictScalars'_refl`, `Diffeomorph.restrictScalars'_symm`,
  `Diffeomorph.restrictScalars'_trans`: it commutes with the identity, inverses, and composition.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Chapter 1.
-/

public section

open Function
open scoped Manifold

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜' E'] [IsScalarTower 𝕜 𝕜' E'] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace F P] {n : WithTop ℕ∞}

namespace Diffeomorph

variable (𝕜)

/-- A `C^n` diffeomorphism for the trivial models over `𝕜'` is a `C^n` diffeomorphism for the
trivial models over the smaller field `𝕜`, with the same underlying equivalence. For instance, a
biholomorphism between complex manifolds is a diffeomorphism of the underlying real manifolds. -/
def restrictScalars' (Φ : M ≃ₘ^n⟮𝓘(𝕜', E), 𝓘(𝕜', E')⟯ N) : M ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ N where
  toEquiv := Φ.toEquiv
  contMDiff_toFun := Φ.contMDiff.restrictScalars' 𝕜
  contMDiff_invFun := Φ.symm.contMDiff.restrictScalars' 𝕜

variable (Φ : M ≃ₘ^n⟮𝓘(𝕜', E), 𝓘(𝕜', E')⟯ N)

/-- Restricting the scalars of a diffeomorphism does not change its underlying equivalence. -/
@[simp]
theorem restrictScalars'_toEquiv : (Φ.restrictScalars' 𝕜).toEquiv = Φ.toEquiv :=
  (rfl)

/-- Restricting the scalars of a diffeomorphism does not change its underlying map. -/
@[simp]
theorem coe_restrictScalars' : ⇑(Φ.restrictScalars' 𝕜) = Φ :=
  (rfl)

/-- Restricting the scalars of a diffeomorphism does not change its underlying homeomorphism. -/
@[simp]
theorem restrictScalars'_toHomeomorph :
    (Φ.restrictScalars' 𝕜).toHomeomorph = Φ.toHomeomorph :=
  (rfl)

/-- Restricting the scalars of diffeomorphisms is injective. -/
theorem restrictScalars'_injective :
    Injective (restrictScalars' 𝕜 : (M ≃ₘ^n⟮𝓘(𝕜', E), 𝓘(𝕜', E')⟯ N) → _) :=
  fun _ _ h ↦ ext fun x ↦ DFunLike.congr_fun h x

/-- Restricting the scalars of the identity diffeomorphism gives the identity diffeomorphism. -/
@[simp]
theorem restrictScalars'_refl :
    (Diffeomorph.refl 𝓘(𝕜', E) M n).restrictScalars' 𝕜 = Diffeomorph.refl 𝓘(𝕜, E) M n :=
  (rfl)

/-- Restricting scalars commutes with taking the inverse diffeomorphism. -/
@[simp]
theorem restrictScalars'_symm : (Φ.restrictScalars' 𝕜).symm = Φ.symm.restrictScalars' 𝕜 :=
  (rfl)

/-- Restricting scalars commutes with the composition of diffeomorphisms. -/
@[simp]
theorem restrictScalars'_trans (Ψ : N ≃ₘ^n⟮𝓘(𝕜', E'), 𝓘(𝕜', F)⟯ P) :
    (Φ.trans Ψ).restrictScalars' 𝕜 = (Φ.restrictScalars' 𝕜).trans (Ψ.restrictScalars' 𝕜) :=
  (rfl)

end Diffeomorph

end
