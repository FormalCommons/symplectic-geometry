/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The complement of an immersion

An immersion `f : M → N` of a nonempty manifold comes with a linear equivalence `E × F ≃ E'`
between the product of the model space `E` of `M` with the chosen complement `F` and the model
space `E'` of `N` (`Manifold.IsImmersionAtOfComplement.equiv`). So if `F` were trivial, `E` and
`E'` would have the same dimension: when `E'` has larger finite rank than `E`, the complement is
nontrivial.

## Main results

* `Manifold.IsImmersion.nontrivial_complement`: the complement of an immersion of a nonempty
  manifold into one of larger dimension is nontrivial.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 4.
-/

public section

open Module

namespace Manifold.IsImmersion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞} {f : M → N}

/-- If `f : M → N` is an immersion of a nonempty manifold and the model space of `N` has larger
finite rank than that of `M`, then the complement chosen by the immersion is nontrivial. -/
theorem nontrivial_complement [Nonempty M] (h : IsImmersion I J n f)
    (hE : finrank 𝕜 E < finrank 𝕜 E') : Nontrivial h.complement := by
  obtain ⟨x⟩ := ‹Nonempty M›
  by_contra hF
  rw [not_nontrivial_iff_subsingleton] at hF
  have : Unique h.complement := uniqueOfSubsingleton 0
  have := ((LinearEquiv.prodUnique (R := 𝕜) (M := E) (M₂ := h.complement)).symm.trans
    (h.isImmersionOfComplement_complement x).equiv.toLinearEquiv).finrank_eq
  omega

end Manifold.IsImmersion

end
