/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# Injective local diffeomorphisms

If `e` is an open partial homeomorphism from `M` to `N` whose inverse `e.symm` is a `C^n` local
diffeomorphism on `e.target`, then `e` itself is `C^n` on `e.source`
(`OpenPartialHomeomorph.contMDiffOn_of_isLocalDiffeomorphOn_symm`). The inverse is injective on
`e.target` and maps it onto `e.source`, and on `e.source` the map `e` is the inverse of `e.symm`
on `e.target` in the sense of `Function.invFunOn`, so this is Tau Ceti's
`IsLocalDiffeomorphOn.contMDiffOn_invFunOn`.

The same Tau Ceti lemma, on the whole domain, shows that the left inverse
`Function.invFunOn f univ` of an injective local diffeomorphism `f` is smooth on the range of `f`
(`IsLocalDiffeomorph.contMDiffOn_invFunOn`).

Tau Ceti's `IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn` on `univ` makes an injective local
diffeomorphism `f` a partial diffeomorphism from `M` to `N` with source `univ` and target
`range f` (`IsLocalDiffeomorph.partialDiffeomorphOfInjective`). Tau Ceti's
`IsLocalDiffeomorph.diffeomorphOfInjective` gives the same map as a diffeomorphism onto the open
subset `hf.image` instead, which changes the codomain.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 4.6
-/

public section

open Set Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞}

namespace OpenPartialHomeomorph

/-- An open partial homeomorphism `e` whose inverse is a `C^n` local diffeomorphism on `e.target`
is `C^n` on `e.source`. -/
theorem contMDiffOn_of_isLocalDiffeomorphOn_symm (e : OpenPartialHomeomorph M N)
    (he : IsLocalDiffeomorphOn J I n e.symm e.target) :
    ContMDiffOn I J n e e.source := fun x hx ↦ by
  have : Nonempty N := ⟨e x⟩
  have hinj : InjOn e.symm e.target := e.symm_source ▸ e.symm.injOn
  have key := he.contMDiffOn_invFunOn e.open_target hinj
  rw [e.symm_image_target_eq_source] at key
  refine (key.congr fun y hy ↦ ?_) x hx
  calc e y = invFunOn e.symm e.target (e.symm (e y)) :=
        (hinj.leftInvOn_invFunOn (e.map_source hy)).symm
    _ = invFunOn e.symm e.target y := by rw [e.left_inv hy]

end OpenPartialHomeomorph

namespace IsLocalDiffeomorph

/-- The left inverse `Function.invFunOn f univ` of an injective `C^n` local diffeomorphism `f` is
`C^n` on the range of `f`. -/
theorem contMDiffOn_invFunOn [Nonempty M] {f : M → N} (hf : IsLocalDiffeomorph I J n f)
    (hinj : Injective f) : ContMDiffOn J I n (invFunOn f univ) (range f) := by
  simpa only [image_univ] using
    (hf.isLocalDiffeomorphOn univ).contMDiffOn_invFunOn isOpen_univ hinj.injOn

/-- An injective `C^n` local diffeomorphism `f : M → N`, as a partial diffeomorphism from `M` to
`N` with source `univ` and target `range f`; its inverse is `Function.invFunOn f univ`. -/
noncomputable def partialDiffeomorphOfInjective [Nonempty M] {f : M → N}
    (hf : IsLocalDiffeomorph I J n f) (hinj : Injective f) : PartialDiffeomorph I J M N n :=
  (hf.isLocalDiffeomorphOn univ).partialDiffeomorphOfInjOn isOpen_univ hinj.injOn

variable [Nonempty M] {f : M → N} (hf : IsLocalDiffeomorph I J n f) (hinj : Injective f)

theorem partialDiffeomorphOfInjective_def :
    hf.partialDiffeomorphOfInjective hinj =
      (hf.isLocalDiffeomorphOn univ).partialDiffeomorphOfInjOn isOpen_univ hinj.injOn :=
  (rfl)

/-- The partial diffeomorphism is `f` itself as a function. -/
@[simp]
theorem coe_partialDiffeomorphOfInjective : ⇑(hf.partialDiffeomorphOfInjective hinj) = f :=
  IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn ..

/-- Its source is all of `M`. -/
@[simp]
theorem partialDiffeomorphOfInjective_source :
    (hf.partialDiffeomorphOfInjective hinj).source = univ :=
  IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source ..

/-- Its target is the range of `f`. -/
@[simp]
theorem partialDiffeomorphOfInjective_target :
    (hf.partialDiffeomorphOfInjective hinj).target = range f :=
  (IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target ..).trans image_univ

/-- Its inverse is `Function.invFunOn f univ`. -/
@[simp]
theorem partialDiffeomorphOfInjective_symm_apply (y : N) :
    (hf.partialDiffeomorphOfInjective hinj).toPartialEquiv.symm y = invFunOn f univ y :=
  IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_symm_apply ..

/-- Its inverse sends `f x` back to `x`. -/
@[simp]
theorem partialDiffeomorphOfInjective_symm_apply_apply (x : M) :
    (hf.partialDiffeomorphOfInjective hinj).toPartialEquiv.symm (f x) = x := by
  rw [partialDiffeomorphOfInjective_symm_apply]
  exact hinj.injOn.leftInvOn_invFunOn (mem_univ x)

end IsLocalDiffeomorph

end
