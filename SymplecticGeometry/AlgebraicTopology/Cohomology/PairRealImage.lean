/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.PairChangeOfCoefficients
public import SymplecticGeometry.AlgebraicTopology.Cohomology.PairIntegralChains
public import SymplecticGeometry.AlgebraicTopology.Cohomology.RealImage

/-!
# The real image of an integral cohomology class of a pair

For a topological pair `P = (X, A)`, the real image
`TopPair.singularCohomologyRealImage : Hⁿ(X, A; ULift ℤ) ⟶ F (Hⁿ(X, A; ℝ))`, with `F` the
restriction of scalars along `ℤ → ℝ`, is the counterpart for pairs of
`TopCat.singularCohomologyRealImage` (`RealImage.lean`). It changes the values of integral
relative cocycles along the cast `TauCeti.intToRealCoeff : ULift ℤ → ℝ`
(`TopPair.singularCohomologyValueMap`), and then reads the class, computed from integral chains
with values in `ℝ`, as a class computed from real chains, through the inverse of
`TopPair.singularCohomologyIntChainsIso ℝ` (`PairIntegralChains.lean`).

## Main definitions

* `TopPair.singularCohomologyRealImage`: the real image `Hⁿ(X, A; ULift ℤ) → Hⁿ(X, A; ℝ)`.

## Main results

* `TopPair.singularCohomologyRealImage_comp_singularCohomologyIntChainsIso_hom`: computed from
  integral chains, the real image is the change of values along `ℤ → ℝ`.
* `TopPair.singularCohomologyRealImage_naturality`: the real image commutes with the maps
  induced by maps of pairs.
* `TopPair.singularCohomologyπ_singularCohomologyRealImage`: the real image commutes with the
  map `TopPair.singularCohomologyπ` from the cohomology of the pair to that of `X`.

The proofs follow those of `TopCat.singularCohomologyRealImage_naturality` and its neighbours,
with the lemmas for pairs of `PairChangeOfCoefficients.lean` and `PairIntegralChains.lean` in
place of those for spaces.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1.
-/

public section

noncomputable section

open CategoryTheory TauCeti

namespace TopPair

variable (P : TopPair.{0}) (n : ℕ)

/-- The **real image** of an integral class of a pair `(X, A)`: the map
`Hⁿ(X, A; ULift ℤ) → Hⁿ(X, A; ℝ)` of abelian groups that casts the values of integral relative
cocycles to `ℝ`, and reads the result, a class computed from integral chains, as a class
computed from real chains. -/
def singularCohomologyRealImage :
    P.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{0} ℤ)) n ⟶
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℝ)).obj
        (P.singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) n) :=
  P.singularCohomologyValueMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ intToRealCoeff n ≫
    (P.singularCohomologyIntChainsIso ℝ n).inv

/-- The real image of a pair is the change of values along `ℤ → ℝ` followed by the inverse
comparison of cohomology computed from integral chains with real cohomology. -/
theorem singularCohomologyRealImage_def :
    P.singularCohomologyRealImage n =
      P.singularCohomologyValueMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ intToRealCoeff n ≫
        (P.singularCohomologyIntChainsIso ℝ n).inv :=
  (rfl)

/-- Read through integral chains, the real image of a class of a pair is its change of values
along `ℤ → ℝ`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem singularCohomologyRealImage_comp_singularCohomologyIntChainsIso_hom :
    P.singularCohomologyRealImage n ≫ (P.singularCohomologyIntChainsIso ℝ n).hom =
      P.singularCohomologyValueMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ intToRealCoeff n := by
  rw [singularCohomologyRealImage_def, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {P} in
/-- **Naturality of the real image of a pair**: for a map of pairs `f : P ⟶ P'`, the real image
of the pull-back `f^* c` of an integral class is the pull-back of the real image of `c`. -/
@[reassoc, elementwise]
theorem singularCohomologyRealImage_naturality {P' : TopPair.{0}} (f : P ⟶ P') :
    TopPair.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ)
        (M := ModuleCat.of ℤ (ULift.{0} ℤ)) f n ≫ P.singularCohomologyRealImage n =
      P'.singularCohomologyRealImage n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℝ)).map
          (TopPair.singularCohomologyMap (R := ModuleCat.of ℝ ℝ) (k := ℝ)
            (M := ModuleCat.of ℝ ℝ) f n) := by
  rw [singularCohomologyRealImage_def, singularCohomologyRealImage_def, ← Category.assoc,
    Iso.comp_inv_eq, Category.assoc, Category.assoc,
    singularCohomologyIntChainsIso_hom_naturality, Iso.inv_hom_id_assoc,
    singularCohomologyValueMap_naturality]

/-- The real image commutes with the map from the cohomology of a pair `(X, A)` to that of `X`:
sending an integral class of the pair to `X` and taking its real image there
(`TopCat.singularCohomologyRealImage`) is taking its real image as a class of the pair and then
sending that to `X`. -/
@[reassoc, elementwise]
theorem singularCohomologyπ_singularCohomologyRealImage :
    P.singularCohomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{0} ℤ)) n ≫
        P.fst.singularCohomologyRealImage n =
      P.singularCohomologyRealImage n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℝ)).map
          (P.singularCohomologyπ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) n) := by
  rw [TopCat.singularCohomologyRealImage_def, singularCohomologyRealImage_def, ← Category.assoc,
    Iso.comp_inv_eq, Category.assoc, Category.assoc,
    singularCohomologyπ_singularCohomologyIntChainsIso_hom, Iso.inv_hom_id_assoc,
    singularCohomologyπ_singularCohomologyValueMap]

end TopPair

end
