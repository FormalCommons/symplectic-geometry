/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System

/-!
# Transport of the images of global classes in local homology

Let `M` be a Hausdorff manifold modelled on a finite-dimensional real normed space `E`. A class
`α` of `Hₖ(M; N)` has an image in each local homology group `Hₖ(M, M ∖ {x}; N)`. Transport along
a path class from `x` to `y` (`TauCeti.localHomologyTransport`) carries the image at `x` to the
image at `y`: `TauCeti.localHomologyTransport_singularHomologyToLocalHomology_of_hom`. This is the
pointwise form of Tau Ceti's
`TauCeti.localHomologyRestriction_univ_comp_localHomologyTransport`; Tau Ceti uses the same step
inside the proof of `TauCeti.singularHomologyToLocalHomology_eq_zero_of_joined`. Tau Ceti's
`TauCeti.localHomologyTransport_singularHomologyToLocalHomology` is the case of a loop, in the top
degree of a compact manifold.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

open CategoryTheory Set

universe w

namespace TauCeti

variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {Λ : Type*} [Ring Λ] (N : ModuleCat.{w} Λ)

/-- **Transport preserves the images of global classes.** For a class `α` of `Hₖ(M; N)` and a
path class `f` from `x` to `y`, the transport along `f` sends the image of `α` in
`Hₖ(M, M ∖ {x}; N)` to its image in `Hₖ(M, M ∖ {y}; N)`. -/
@[simp]
theorem localHomologyTransport_singularHomologyToLocalHomology_of_hom {k : ℕ}
    {x y : FundamentalGroupoid M} (f : x ⟶ y)
    (α : ((TopCat.toSSet.obj (TopCat.of M)).homology N k : ModuleCat.{w} Λ)) :
    localHomologyTransport N M E k f (singularHomologyToLocalHomology N x.as k α) =
      singularHomologyToLocalHomology N y.as k α := by
  rw [singularHomologyToLocalHomology_apply, singularHomologyToLocalHomology_apply,
    ← ConcreteCategory.comp_apply, localHomologyRestriction_univ_comp_localHomologyTransport]

end TauCeti

end
