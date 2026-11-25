/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

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

## Implementation notes

The definition of `Diffeomorph.reflProdCongr` is Mathlib's `Diffeomorph.prodCongr` of
`Diffeomorph.refl` and `ψ`, with the models of `ψ` freed. It belongs upstream as a
generalization of that definition.
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
theorem coe_prodCongr_refl (ψ : M ≃ₘ^n⟮I, I'⟯ M') :
    ⇑(ψ.prodCongr (Diffeomorph.refl J N n)) = fun x ↦ (ψ x.1, x.2) :=
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

end Diffeomorph

end
