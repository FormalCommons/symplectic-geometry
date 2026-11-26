/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective

/-!
# Open partial homeomorphisms whose inverse is a local diffeomorphism

If `e` is an open partial homeomorphism from `M` to `N` whose inverse `e.symm` is a `C^n` local
diffeomorphism on `e.target`, then `e` itself is `C^n` on `e.source`
(`OpenPartialHomeomorph.contMDiffOn_of_isLocalDiffeomorphOn_symm`). The inverse is injective on
`e.target` and maps it onto `e.source`, and on `e.source` the map `e` is the inverse of `e.symm`
on `e.target` in the sense of `Function.invFunOn`, so this is Tau Ceti's
`IsLocalDiffeomorphOn.contMDiffOn_invFunOn`.

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

end
