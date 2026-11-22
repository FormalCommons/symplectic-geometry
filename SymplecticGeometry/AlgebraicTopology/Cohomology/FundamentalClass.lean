/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass

/-!
# Evaluation on a fundamental class and change of cochain values

Tau Ceti's `TauCeti.HomologicalOrientation.evalFundamentalClass` evaluates a class of
`Hⁿ(X; M)` on the image `f_*[N]` of the fundamental class of a compact oriented `n`-manifold,
with values in the coefficient module `M`. This file shows that the evaluation commutes with a
change of cochain values `g : M ⟶ M'` (`TopCat.singularCohomologyValueMap`), since the Kronecker
pairing does (`TopCat.singularKronecker_coefficient_naturality`). In particular a class with
values in `ULift ℤ`, such as Tau Ceti's Euler classes, and its image in integral cohomology under
`TopCat.uliftIntegralCohomologyIso` have the same evaluation, read through `ULift.down`.

## Main results

* `TauCeti.HomologicalOrientation.evalFundamentalClass_singularCohomologyValueMap`:
  `⟨g_* c, f_*[N]⟩ = g ⟨c, f_*[N]⟩`.
* `TauCeti.HomologicalOrientation.evalFundamentalClass_uliftIntegralCohomologyIso_hom`: the
  evaluation of the integral class of `c` is the evaluation of `c`, read in `ℤ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1 (the Kronecker pairing) and Section 3.3 (fundamental classes).
-/

public section

open CategoryTheory Module

namespace TauCeti.HomologicalOrientation

variable {N E : Type} [TopologicalSpace N] [T2Space N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E N]
  [CompactSpace N] {n : ℕ} (o : HomologicalOrientation N E n) (hn : finrank ℝ E = n)
  {X : Type} [TopologicalSpace X]

/-- **Evaluation on a fundamental class commutes with a change of cochain values**: for
`g : M ⟶ M'` and `c ∈ Hⁿ(X; M)`, `⟨g_* c, f_*[N]⟩ = g ⟨c, f_*[N]⟩`. -/
theorem evalFundamentalClass_singularCohomologyValueMap {M M' : ModuleCat.{0} ℤ} (g : M ⟶ M')
    (f : C(N, X))
    (c : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ M n) :
    o.evalFundamentalClass hn M' f
        ((TopCat.of X).singularCohomologyValueMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ g n c) =
      g.hom (o.evalFundamentalClass hn M f c) := by
  rw [evalFundamentalClass_apply, evalFundamentalClass_apply,
    TopCat.singularKronecker_coefficient_naturality, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- A class `c ∈ Hⁿ(X; ULift ℤ)` and its image in integral cohomology under
`TopCat.uliftIntegralCohomologyIso` have the same evaluation on `f_*[N]`, read in `ℤ`. -/
theorem evalFundamentalClass_uliftIntegralCohomologyIso_hom (f : C(N, X))
    (c : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n) :
    o.evalFundamentalClass hn (ModuleCat.of ℤ ℤ) f
        (((TopCat.of X).uliftIntegralCohomologyIso n).hom c) =
      (o.evalFundamentalClass hn (ModuleCat.of ℤ (ULift.{0} ℤ)) f c).down := by
  rw [TopCat.uliftIntegralCohomologyIso_hom, evalFundamentalClass_singularCohomologyValueMap,
    uliftIntIso_hom_apply]

end TauCeti.HomologicalOrientation

end
