/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The complement of an immersion

An immersion `f : M → N` at a point with complement `F` comes with a linear equivalence
`E × F ≃ E'` between the product of the model space `E` of `M` with `F` and the model space `E'`
of `N` (`Manifold.IsImmersionAtOfComplement.equiv`). So if `F` were trivial, `E` and `E'` would
have the same rank: when `E'` has larger rank than `E`, the complement is nontrivial. The same
equivalence embeds `F` linearly into `E'`, so `F` is finite-dimensional when `E'` is.

## Main results

* `Manifold.IsImmersionAtOfComplement.nontrivial_complement`: the complement `F` of an
  immersion at a point into a manifold whose model space has larger rank is nontrivial.
* `Manifold.IsImmersion.nontrivial_complement`: the same for the complement chosen by an
  immersion of a nonempty manifold.
* `Manifold.IsImmersionAtOfComplement.finiteDimensional_complement`: the complement `F` of an
  immersion at a point into a manifold with finite-dimensional model space is finite-dimensional.
* `Manifold.IsImmersionAt.finiteDimensional_complement`: the same for the complement chosen by
  `Manifold.IsImmersionAt`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 4.
-/

public section

universe u v

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} {H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type v} {H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞} {f : M → N}

namespace Manifold.IsImmersionAtOfComplement

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `f : M → N` is an immersion at `x` with complement `F`, and the model space `E'` of `N` has
larger rank than the model space `E` of `M`, then `F` is nontrivial. -/
theorem nontrivial_complement {x : M} (h : IsImmersionAtOfComplement F I J n f x)
    (hE : Cardinal.lift.{v} (Module.rank 𝕜 E) < Cardinal.lift.{u} (Module.rank 𝕜 E')) :
    Nontrivial F := by
  by_contra hF
  rw [not_nontrivial_iff_subsingleton] at hF
  have : Unique F := uniqueOfSubsingleton 0
  have := ((LinearEquiv.prodUnique (R := 𝕜) (M := E) (M₂ := F)).symm.trans
    h.equiv.toLinearEquiv).lift_rank_eq
  exact hE.ne (by simpa using this)

/-- If `f : M → N` is an immersion at `x` with complement `F`, and the model space `E'` of `N` is
finite-dimensional, then `F` is finite-dimensional. -/
theorem finiteDimensional_complement [FiniteDimensional 𝕜 E'] {x : M}
    (h : IsImmersionAtOfComplement F I J n f x) : FiniteDimensional 𝕜 F :=
  FiniteDimensional.of_injective
    ((h.equiv : E × F →L[𝕜] E').comp (ContinuousLinearMap.inr 𝕜 E F)).toLinearMap
    (h.equiv.injective.comp (Prod.mk_right_injective (0 : E)))

end Manifold.IsImmersionAtOfComplement

namespace Manifold.IsImmersionAt

/-- If `f : M → N` is an immersion at `x` and the model space `E'` of `N` is finite-dimensional,
then the complement chosen by the immersion is finite-dimensional. -/
theorem finiteDimensional_complement [FiniteDimensional 𝕜 E'] {x : M}
    (h : IsImmersionAt I J n f x) : FiniteDimensional 𝕜 h.complement :=
  h.isImmersionAtOfComplement_complement.finiteDimensional_complement

end Manifold.IsImmersionAt

namespace Manifold.IsImmersion

/-- If `f : M → N` is an immersion of a nonempty manifold, and the model space `E'` of `N` has
larger rank than the model space `E` of `M`, then the complement chosen by the immersion is
nontrivial. -/
theorem nontrivial_complement [Nonempty M] (h : IsImmersion I J n f)
    (hE : Cardinal.lift.{v} (Module.rank 𝕜 E) < Cardinal.lift.{u} (Module.rank 𝕜 E')) :
    Nontrivial h.complement :=
  (h.isImmersionOfComplement_complement (Classical.arbitrary M)).nontrivial_complement hE

end Manifold.IsImmersion

end
