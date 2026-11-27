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

For a diffeomorphism `ψ : M ≃ₘ^n⟮I, I'⟯ M'` and a manifold `N` modelled on `J`, the map
`Prod.map id ψ` is a diffeomorphism of `N × M` onto `N × M'`. Conversely, a diffeomorphism of
`N × M` onto `N × M'` that preserves the first coordinate has, at each `t : N`, a slice: a
diffeomorphism of `M` onto `M'`.

Mathlib's `Diffeomorph.prodCongr` builds the product of two diffeomorphisms, but asks that the
models of the second factor's source and target share their vector space, so
`(Diffeomorph.refl J N n).prodCongr ψ` does not typecheck when `I` and `I'` are modelled on
different spaces. This file gives that product with the models of `ψ` free.

## Main definitions

* `Diffeomorph.reflProdCongr N ψ`: the diffeomorphism `id × ψ` of `N × M` onto `N × M'`.
* `Diffeomorph.slice Ψ hΨ t`: the slice at `t` of a diffeomorphism `Ψ` of `N × M` onto `N × M'`
  that preserves the first coordinate.
* `Diffeomorph.prodModelEquiv`: a diffeomorphism between products of normed spaces for the
  self-models of the products is the same as one for the products of the self-models.

## Implementation notes

The definition of `Diffeomorph.reflProdCongr` is Mathlib's `Diffeomorph.prodCongr` of
`Diffeomorph.refl` and `ψ`, with the models of `ψ` freed. It belongs upstream as a
generalization of that definition.

The smoothness fields of `Diffeomorph.prodModelEquiv` come from Tau Ceti's
`contMDiff_prod_modelWithCornersSelf_iff`, which changes the model of the source.
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

variable (N) in
/-- The diffeomorphism `id × ψ` of `N × M` onto `N × M'`, for a diffeomorphism `ψ` of `M` onto
`M'` and any manifold `N`. -/
def reflProdCongr (ψ : M ≃ₘ^n⟮I, I'⟯ M') : (N × M) ≃ₘ^n⟮J.prod I, J.prod I'⟯ N × M' where
  toEquiv := (Equiv.refl N).prodCongr ψ.toEquiv
  contMDiff_toFun := contMDiff_fst.prodMk (ψ.contMDiff.comp contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk (ψ.symm.contMDiff.comp contMDiff_snd)

@[simp]
theorem coe_reflProdCongr (ψ : M ≃ₘ^n⟮I, I'⟯ M') :
    ⇑(ψ.reflProdCongr N (J := J)) = Prod.map id ψ :=
  (rfl)

/-- Mathlib's product `ψ.prodCongr (Diffeomorph.refl J N n)` of `ψ` with the identity of `N`
sends `x` to `(ψ x.1, x.2)`. -/
@[simp]
theorem prodCongr_refl_right_apply (ψ : M ≃ₘ^n⟮I, I'⟯ M') (x : M × N) :
    ψ.prodCongr (Diffeomorph.refl J N n) x = (ψ x.1, x.2) :=
  (rfl)

@[simp]
theorem reflProdCongr_symm (ψ : M ≃ₘ^n⟮I, I'⟯ M') :
    (ψ.reflProdCongr N (J := J)).symm = ψ.symm.reflProdCongr N :=
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

variable {A B C D : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A] [NormedAddCommGroup B]
  [NormedSpace 𝕜 B] [NormedAddCommGroup C] [NormedSpace 𝕜 C] [NormedAddCommGroup D]
  [NormedSpace 𝕜 D]

/-- A diffeomorphism between products `A × B` and `C × D` of normed spaces, each with the
self-model of the product, is the same as a diffeomorphism between them for the products
`𝓘(𝕜, A).prod 𝓘(𝕜, B)` and `𝓘(𝕜, C).prod 𝓘(𝕜, D)` of the self-models: this equivalence keeps
the underlying equivalence and changes only the models. -/
def prodModelEquiv :
    ((A × B) ≃ₘ^n⟮𝓘(𝕜, A × B), 𝓘(𝕜, C × D)⟯ C × D) ≃
      ((A × B) ≃ₘ^n⟮𝓘(𝕜, A).prod 𝓘(𝕜, B), 𝓘(𝕜, C).prod 𝓘(𝕜, D)⟯ C × D) where
  toFun Φ :=
    { toEquiv := Φ.toEquiv
      contMDiff_toFun := contMDiff_prod_modelWithCornersSelf_iff.2 <|
        (contMDiff_prod_modelWithCornersSelf_iff.1
          (contMDiff_id (I := 𝓘(𝕜, C).prod 𝓘(𝕜, D)))).comp Φ.contMDiff
      contMDiff_invFun := contMDiff_prod_modelWithCornersSelf_iff.2 <|
        (contMDiff_prod_modelWithCornersSelf_iff.1
          (contMDiff_id (I := 𝓘(𝕜, A).prod 𝓘(𝕜, B)))).comp Φ.symm.contMDiff }
  invFun Φ :=
    { toEquiv := Φ.toEquiv
      contMDiff_toFun := (contMDiff_prod_modelWithCornersSelf_iff.2
          (contMDiff_id (I := 𝓘(𝕜, C × D)))).comp
        (contMDiff_prod_modelWithCornersSelf_iff.1 Φ.contMDiff)
      contMDiff_invFun := (contMDiff_prod_modelWithCornersSelf_iff.2
          (contMDiff_id (I := 𝓘(𝕜, A × B)))).comp
        (contMDiff_prod_modelWithCornersSelf_iff.1 Φ.symm.contMDiff) }
  left_inv _ := rfl
  right_inv _ := rfl

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

end prodModel

end Diffeomorph

end
