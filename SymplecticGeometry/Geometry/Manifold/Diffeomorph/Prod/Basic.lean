/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Diffeomorphisms of products

A diffeomorphism of `N × M` onto `N × M'` that preserves the first coordinate has, at each
`t : N`, a slice: a diffeomorphism of `M` onto `M'`. The product `id × ψ` of the identity of `N`
with a diffeomorphism `ψ` of `M` onto `M'`, whose models may have different vector spaces, is
Tau Ceti's `(Diffeomorph.refl J N n).prodCongrOfModels ψ`.

## Main definitions

* `Diffeomorph.slice Ψ hΨ t`: the slice at `t` of a diffeomorphism `Ψ` of `N × M` onto `N × M'`
  that preserves the first coordinate.
* `Diffeomorph.prodModelSelf 𝕜 A B`: the identity of `A × B`, from the self-model of the product
  to the product of the self-models.
* `Diffeomorph.prodModelEquiv`: a diffeomorphism between products of normed spaces for the
  self-models of the products is the same as one for the products of the self-models.

## Implementation notes

The smoothness fields of `Diffeomorph.prodModelSelf` come from Tau Ceti's
`contMDiff_prod_modelWithCornersSelf_iff`, which changes the model of the source.
`Diffeomorph.prodModelEquiv` conjugates by `Diffeomorph.prodModelSelf`.
-/

public section

open scoped Manifold

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F H H' G M M' N : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] {n : WithTop ℕ∞}

/-- Mathlib's product `ψ.prodCongr (Diffeomorph.refl J N n)` of `ψ` with the identity of `N`
sends `x` to `(ψ x.1, x.2)`. -/
@[simp]
theorem prodCongr_refl_right_apply (ψ : M ≃ₘ^n⟮I, I'⟯ M') (x : M × N) :
    ψ.prodCongr (Diffeomorph.refl J N n) x = (ψ x.1, x.2) :=
  (rfl)

section slice

variable (Ψ : (N × M) ≃ₘ^n⟮J.prod I, J.prod I'⟯ N × M') (hΨ : ∀ p, (Ψ p).1 = p.1)

/-- The slice at `t` of a diffeomorphism `Ψ` of `N × M` onto `N × M'` that preserves the first
coordinate: the diffeomorphism of `M` onto `M'` that sends `x` to the second coordinate of
`Ψ (t, x)`. -/
def slice (t : N) : M ≃ₘ^n⟮I, I'⟯ M' where
  toFun x := (Ψ (t, x)).2
  invFun y := (Ψ.symm (t, y)).2
  left_inv x := by
    have hp : (t, (Ψ (t, x)).2) = Ψ (t, x) := Prod.ext (hΨ (t, x)).symm rfl
    simp only
    rw [hp, Ψ.symm_apply_apply]
  right_inv y := by
    have hp : (t, (Ψ.symm (t, y)).2) = Ψ.symm (t, y) :=
      Prod.ext (by simpa using hΨ (Ψ.symm (t, y))) rfl
    simp only
    rw [hp, Ψ.apply_symm_apply]
  contMDiff_toFun := contMDiff_snd.comp (Ψ.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))
  contMDiff_invFun :=
    contMDiff_snd.comp (Ψ.symm.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))

@[simp]
theorem slice_apply (t : N) (x : M) : Ψ.slice hΨ t x = (Ψ (t, x)).2 :=
  (rfl)

@[simp]
theorem symm_slice_apply (t : N) (y : M') : (Ψ.slice hΨ t).symm y = (Ψ.symm (t, y)).2 :=
  (rfl)

/-- A diffeomorphism that preserves the first coordinate acts on `(t, x)` through its slice
at `t`. -/
theorem apply_eq_slice (p : N × M) : Ψ p = (p.1, Ψ.slice hΨ p.1 p.2) :=
  Prod.ext (hΨ p) rfl

end slice

section prodModel

variable {A B C D A' B' : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A] [NormedAddCommGroup B]
  [NormedSpace 𝕜 B] [NormedAddCommGroup C] [NormedSpace 𝕜 C] [NormedAddCommGroup D]
  [NormedSpace 𝕜 D] [NormedAddCommGroup A'] [NormedSpace 𝕜 A'] [NormedAddCommGroup B']
  [NormedSpace 𝕜 B']

variable (𝕜 A B) in
/-- The identity of a product `A × B` of normed spaces, as a `C^n` diffeomorphism from the
self-model `𝓘(𝕜, A × B)` of the product to the product `𝓘(𝕜, A).prod 𝓘(𝕜, B)` of the
self-models. -/
def prodModelSelf : (A × B) ≃ₘ^n⟮𝓘(𝕜, A × B), 𝓘(𝕜, A).prod 𝓘(𝕜, B)⟯ A × B where
  toEquiv := Equiv.refl _
  contMDiff_toFun := contMDiff_prod_modelWithCornersSelf_iff.1 contMDiff_id
  contMDiff_invFun := contMDiff_prod_modelWithCornersSelf_iff.2 contMDiff_id

@[simp]
theorem coe_prodModelSelf : ⇑(prodModelSelf 𝕜 A B (n := n)) = id :=
  (rfl)

@[simp]
theorem coe_prodModelSelf_symm : ⇑(prodModelSelf 𝕜 A B (n := n)).symm = id :=
  (rfl)

@[simp]
theorem toEquiv_prodModelSelf : (prodModelSelf 𝕜 A B (n := n)).toEquiv = Equiv.refl _ :=
  (rfl)

/-- A diffeomorphism between products `A × B` and `C × D` of normed spaces, each with the
self-model of the product, is the same as a diffeomorphism between them for the products
`𝓘(𝕜, A).prod 𝓘(𝕜, B)` and `𝓘(𝕜, C).prod 𝓘(𝕜, D)` of the self-models: this equivalence keeps
the underlying equivalence and changes only the models. It conjugates by
`Diffeomorph.prodModelSelf`. -/
def prodModelEquiv :
    ((A × B) ≃ₘ^n⟮𝓘(𝕜, A × B), 𝓘(𝕜, C × D)⟯ C × D) ≃
      ((A × B) ≃ₘ^n⟮𝓘(𝕜, A).prod 𝓘(𝕜, B), 𝓘(𝕜, C).prod 𝓘(𝕜, D)⟯ C × D) where
  toFun Φ := (prodModelSelf 𝕜 A B).symm.trans (Φ.trans (prodModelSelf 𝕜 C D))
  invFun Φ := (prodModelSelf 𝕜 A B).trans (Φ.trans (prodModelSelf 𝕜 C D).symm)
  left_inv _ := rfl
  right_inv _ := rfl

theorem prodModelEquiv_def (Φ : (A × B) ≃ₘ^n⟮𝓘(𝕜, A × B), 𝓘(𝕜, C × D)⟯ C × D) :
    prodModelEquiv Φ = (prodModelSelf 𝕜 A B).symm.trans (Φ.trans (prodModelSelf 𝕜 C D)) :=
  (rfl)

theorem prodModelEquiv_symm_def
    (Φ : (A × B) ≃ₘ^n⟮𝓘(𝕜, A).prod 𝓘(𝕜, B), 𝓘(𝕜, C).prod 𝓘(𝕜, D)⟯ C × D) :
    prodModelEquiv.symm Φ =
      (prodModelSelf 𝕜 A B).trans (Φ.trans (prodModelSelf 𝕜 C D).symm) :=
  (rfl)

@[simp]
theorem coe_prodModelEquiv (Φ : (A × B) ≃ₘ^n⟮𝓘(𝕜, A × B), 𝓘(𝕜, C × D)⟯ C × D) :
    ⇑(prodModelEquiv Φ) = Φ :=
  (rfl)

@[simp]
theorem coe_prodModelEquiv_symm
    (Φ : (A × B) ≃ₘ^n⟮𝓘(𝕜, A).prod 𝓘(𝕜, B), 𝓘(𝕜, C).prod 𝓘(𝕜, D)⟯ C × D) :
    ⇑(prodModelEquiv.symm Φ) = Φ :=
  (rfl)

@[simp]
theorem toEquiv_prodModelEquiv (Φ : (A × B) ≃ₘ^n⟮𝓘(𝕜, A × B), 𝓘(𝕜, C × D)⟯ C × D) :
    (prodModelEquiv Φ).toEquiv = Φ.toEquiv :=
  (rfl)

@[simp]
theorem toEquiv_prodModelEquiv_symm
    (Φ : (A × B) ≃ₘ^n⟮𝓘(𝕜, A).prod 𝓘(𝕜, B), 𝓘(𝕜, C).prod 𝓘(𝕜, D)⟯ C × D) :
    (prodModelEquiv.symm Φ).toEquiv = Φ.toEquiv :=
  (rfl)

@[simp]
theorem toHomeomorph_prodModelEquiv (Φ : (A × B) ≃ₘ^n⟮𝓘(𝕜, A × B), 𝓘(𝕜, C × D)⟯ C × D) :
    (prodModelEquiv Φ).toHomeomorph = Φ.toHomeomorph :=
  (rfl)

@[simp]
theorem toHomeomorph_prodModelEquiv_symm
    (Φ : (A × B) ≃ₘ^n⟮𝓘(𝕜, A).prod 𝓘(𝕜, B), 𝓘(𝕜, C).prod 𝓘(𝕜, D)⟯ C × D) :
    (prodModelEquiv.symm Φ).toHomeomorph = Φ.toHomeomorph :=
  (rfl)

/-- Changing the models commutes with taking the inverse. -/
@[simp]
theorem symm_prodModelEquiv (Φ : (A × B) ≃ₘ^n⟮𝓘(𝕜, A × B), 𝓘(𝕜, C × D)⟯ C × D) :
    (prodModelEquiv Φ).symm = prodModelEquiv Φ.symm :=
  (rfl)

@[simp]
theorem symm_prodModelEquiv_symm
    (Φ : (A × B) ≃ₘ^n⟮𝓘(𝕜, A).prod 𝓘(𝕜, B), 𝓘(𝕜, C).prod 𝓘(𝕜, D)⟯ C × D) :
    (prodModelEquiv.symm Φ).symm = prodModelEquiv.symm Φ.symm :=
  (rfl)

/-- Changing the models of the identity diffeomorphism gives the identity diffeomorphism. -/
@[simp]
theorem prodModelEquiv_refl :
    prodModelEquiv (Diffeomorph.refl 𝓘(𝕜, A × B) (A × B) n) =
      Diffeomorph.refl (𝓘(𝕜, A).prod 𝓘(𝕜, B)) (A × B) n :=
  (rfl)

@[simp]
theorem prodModelEquiv_symm_refl :
    prodModelEquiv.symm (Diffeomorph.refl (𝓘(𝕜, A).prod 𝓘(𝕜, B)) (A × B) n) =
      Diffeomorph.refl 𝓘(𝕜, A × B) (A × B) n :=
  (rfl)

/-- Changing the models commutes with the composition of diffeomorphisms. -/
@[simp]
theorem prodModelEquiv_trans (Φ : (A × B) ≃ₘ^n⟮𝓘(𝕜, A × B), 𝓘(𝕜, C × D)⟯ C × D)
    (Ψ : (C × D) ≃ₘ^n⟮𝓘(𝕜, C × D), 𝓘(𝕜, A' × B')⟯ A' × B') :
    prodModelEquiv (Φ.trans Ψ) = (prodModelEquiv Φ).trans (prodModelEquiv Ψ) :=
  (rfl)

@[simp]
theorem prodModelEquiv_symm_trans
    (Φ : (A × B) ≃ₘ^n⟮𝓘(𝕜, A).prod 𝓘(𝕜, B), 𝓘(𝕜, C).prod 𝓘(𝕜, D)⟯ C × D)
    (Ψ : (C × D) ≃ₘ^n⟮𝓘(𝕜, C).prod 𝓘(𝕜, D), 𝓘(𝕜, A').prod 𝓘(𝕜, B')⟯ A' × B') :
    prodModelEquiv.symm (Φ.trans Ψ) = (prodModelEquiv.symm Φ).trans (prodModelEquiv.symm Ψ) :=
  (rfl)

end prodModel

end Diffeomorph

end
