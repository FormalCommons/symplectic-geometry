/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The complement of an immersion

An immersion `f : M → N` of a nonempty manifold comes with a linear equivalence `E × F ≃ E'`
between the product of the model space `E` of `M` with the chosen complement `F` and the model
space `E'` of `N` (`Manifold.IsImmersionAtOfComplement.equiv`). So if `F` were trivial, `E` and
`E'` would have the same rank: when `E'` has larger rank than `E`, the complement is nontrivial.

## Main results

* `Manifold.IsImmersion.nontrivial_complement`: the complement of an immersion of a nonempty
  manifold into one whose model space has larger rank is nontrivial.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 4.
-/

public section

universe u v

namespace Manifold.IsImmersion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} {H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type v} {H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞} {f : M → N}

/-- If `f : M → N` is an immersion of a nonempty manifold, and the model space `E'` of `N` has
larger rank than the model space `E` of `M`, then the complement chosen by the immersion is
nontrivial. -/
theorem nontrivial_complement [Nonempty M] (h : IsImmersion I J n f)
    (hE : Cardinal.lift.{v} (Module.rank 𝕜 E) < Cardinal.lift.{u} (Module.rank 𝕜 E')) :
    Nontrivial h.complement := by
  obtain ⟨x⟩ := ‹Nonempty M›
  by_contra hF
  rw [not_nontrivial_iff_subsingleton] at hF
  have : Unique h.complement := uniqueOfSubsingleton 0
  have := ((LinearEquiv.prodUnique (R := 𝕜) (M := E) (M₂ := h.complement)).symm.trans
    (h.isImmersionOfComplement_complement x).equiv.toLinearEquiv).lift_rank_eq
  exact hE.ne (by simpa using this)

end Manifold.IsImmersion

end
