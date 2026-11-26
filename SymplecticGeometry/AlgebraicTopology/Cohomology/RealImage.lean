/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.ChangeOfValues
public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralChains
public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import Mathlib.Algebra.Category.ModuleCat.Algebra
import SymplecticGeometry.AlgebraicTopology.Cohomology.FundamentalClass

/-!
# The real image of an integral cohomology class

Tau Ceti's integral classes, such as `TauCeti.complexEulerClass`, live in
`Hⁿ(X; ULift ℤ)`, the cohomology of integral chains with values in `ULift ℤ`, while the de Rham
homomorphism `TauCeti.deRhamHom` lands in `Hⁿ(X; ℝ)`, computed from real chains. The real image
`TopCat.singularCohomologyRealImage` joins the two: it changes the values along the cast
`TauCeti.intToRealCoeff : ULift ℤ → ℝ` (`TopCat.singularCohomologyValueMap`), and then reads the
class, computed from integral chains with values in `ℝ`, as a class of `Hⁿ(X; ℝ)` through the
inverse of `TopCat.singularCohomologyIntChainsIso ℝ`. As that comparison is an isomorphism of
abelian groups, the real image is `ℤ`-linear, with target `Hⁿ(X; ℝ)` read as an abelian group.

## Main definitions

* `TopCat.singularCohomologyRealImage`: the real image `Hⁿ(X; ULift ℤ) → Hⁿ(X; ℝ)`.

## Main results

* `TopCat.singularCohomologyRealImage_comp_singularCohomologyIntChainsIso_hom`: computed from
  integral chains, the real image is the change of values along `ℤ → ℝ`.
* `TopCat.singularCohomologyRealImage_naturality`: the real image commutes with the maps induced
  by continuous maps.
* `TauCeti.HomologicalOrientation.evalFundamentalClass_singularCohomologyRealImage`: the
  evaluation with values in `ℝ` of the real image of `c` on `f_*[N]`, read through integral
  chains, is the cast of the evaluation of `c`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1 (change of coefficients) and Section 3.3 (fundamental classes).
-/

public section

noncomputable section

open CategoryTheory Module TauCeti

namespace TopCat

variable (X : TopCat.{0}) (n : ℕ)

/-- The **real image** of an integral class: the map `Hⁿ(X; ULift ℤ) → Hⁿ(X; ℝ)` of abelian
groups that casts the values of integral cocycles to `ℝ`, and reads the result, a class computed
from integral chains, as a class computed from real chains. -/
def singularCohomologyRealImage :
    X.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{0} ℤ)) n ⟶
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℝ)).obj
        (X.singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) n) :=
  X.singularCohomologyValueMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ intToRealCoeff n ≫
    (X.singularCohomologyIntChainsIso ℝ n).inv

/-- The real image is the change of values along `ℤ → ℝ` followed by the inverse comparison of
cohomology computed from integral chains with real cohomology. -/
theorem singularCohomologyRealImage_def :
    X.singularCohomologyRealImage n =
      X.singularCohomologyValueMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ intToRealCoeff n ≫
        (X.singularCohomologyIntChainsIso ℝ n).inv :=
  (rfl)

/-- Read through integral chains, the real image of a class is its change of values along
`ℤ → ℝ`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem singularCohomologyRealImage_comp_singularCohomologyIntChainsIso_hom :
    X.singularCohomologyRealImage n ≫ (X.singularCohomologyIntChainsIso ℝ n).hom =
      X.singularCohomologyValueMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ intToRealCoeff n := by
  rw [singularCohomologyRealImage_def, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {X} in
/-- **Naturality of the real image**: for a continuous map `f : X ⟶ Y`, the real image of the
pull-back `f^* c` of an integral class is the pull-back of the real image of `c`. -/
@[reassoc, elementwise]
theorem singularCohomologyRealImage_naturality {Y : TopCat.{0}} (f : X ⟶ Y) :
    TopCat.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ)
        (M := ModuleCat.of ℤ (ULift.{0} ℤ)) f n ≫ X.singularCohomologyRealImage n =
      Y.singularCohomologyRealImage n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℝ)).map
          (TopCat.singularCohomologyMap (R := ModuleCat.of ℝ ℝ) (k := ℝ)
            (M := ModuleCat.of ℝ ℝ) f n) := by
  rw [singularCohomologyRealImage_def, singularCohomologyRealImage_def, ← Category.assoc,
    Iso.comp_inv_eq, Category.assoc, Category.assoc,
    singularCohomologyIntChainsIso_hom_naturality, Iso.inv_hom_id_assoc,
    singularCohomologyValueMap_naturality]

end TopCat

namespace TauCeti.HomologicalOrientation

variable {N E : Type} [TopologicalSpace N] [T2Space N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E N]
  [CompactSpace N] {n : ℕ} (o : HomologicalOrientation N E n) (hn : finrank ℝ E = n)
  {X : Type} [TopologicalSpace X]

/-- **Evaluation of the real image on a fundamental class**: for an integral class
`c ∈ Hⁿ(X; ULift ℤ)` and `f : N → X` from a compact oriented `n`-manifold, the real image of `c`,
read through integral chains, evaluates on `f_*[N]` to the cast to `ℝ` of `⟨c, f_*[N]⟩`. -/
theorem evalFundamentalClass_singularCohomologyRealImage (f : C(N, X))
    (c : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n) :
    o.evalFundamentalClass hn (ModuleCat.of ℤ ℝ) f
        (((TopCat.of X).singularCohomologyIntChainsIso ℝ n).hom
          ((TopCat.of X).singularCohomologyRealImage n c)) =
      ((o.evalFundamentalClass hn (ModuleCat.of ℤ (ULift.{0} ℤ)) f c).down : ℝ) := by
  rw [TopCat.singularCohomologyRealImage_comp_singularCohomologyIntChainsIso_hom_apply,
    evalFundamentalClass_singularCohomologyValueMap, intToRealCoeff_apply]

end TauCeti.HomologicalOrientation

end
