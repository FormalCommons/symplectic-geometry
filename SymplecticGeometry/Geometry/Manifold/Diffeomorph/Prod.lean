/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The product of the identity with a diffeomorphism

For a diffeomorphism `ψ : M ≃ₘ^n⟮I, I'⟯ M'` and a manifold `N` modelled on `J`, the map
`Prod.map id ψ` is a diffeomorphism of `N × M` onto `N × M'`.

Mathlib's `Diffeomorph.prodCongr` builds the product of two diffeomorphisms, but asks that the
models of the second factor's source and target share their vector space, so
`(Diffeomorph.refl J N n).prodCongr ψ` does not typecheck when `I` and `I'` are modelled on
different spaces. This file gives that product with the models of `ψ` free.

## Main definitions

* `Diffeomorph.reflProdCongr N ψ`: the diffeomorphism `id × ψ` of `N × M` onto `N × M'`.

## Implementation notes

The definition is Mathlib's `Diffeomorph.prodCongr` of `Diffeomorph.refl` and `ψ`, with the models
of `ψ` freed. It belongs upstream as a generalization of that definition.
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

@[simp]
theorem reflProdCongr_symm (ψ : M ≃ₘ^n⟮I, I'⟯ M') :
    (ψ.reflProdCongr N (J := J)).symm = ψ.symm.reflProdCongr N :=
  (rfl)

end Diffeomorph

end
