/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.ChangeOfValues
public import SymplecticGeometry.AlgebraicTopology.Cohomology.FundamentalClass
public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralChains
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.RestrictScalars

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
* `TopCat.chainComplexMap_f_singularCochainComplexIntChainsIso_hom_f`: read through integral
  chains, a real cochain takes on an integral chain its value on the chain with its coefficients
  cast to `ℝ`, for chains of any simplicial set over the singular one.
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


variable {X} in
/-- **Restricting a real cochain to integral chains.** For a map `j : S ⟶ toSSet X` of simplicial
sets and a real cochain `ψ` of `X`, the cochain `ψ` read through integral chains, on the image
under `j` of a chain of `S` with coefficients `ULift ℤ`, is `ψ` on the image under `j` of the
chain with its coefficients cast to `ℝ` (`SSet.restrictScalarsChainMap` along
`TauCeti.intToRealCoeff`). -/
theorem chainComplexMap_f_singularCochainComplexIntChainsIso_hom_f {S : SSet.{0}}
    (j : S ⟶ toSSet.obj X) (p : ℕ)
    (ψ : ((toSSet.obj X).chainComplex (ModuleCat.of ℝ ℝ)).X p ⟶ ModuleCat.of ℝ ℝ) :
    (SSet.chainComplexMap j (ModuleCat.of ℤ (ULift.{0} ℤ))).f p ≫
        (X.singularCochainComplexIntChainsIso ℝ).hom.f p ψ =
      (SSet.restrictScalarsChainMap (algebraMap ℤ ℝ) (N := ModuleCat.of ℝ ℝ)
        (intToRealCoeff ≫ (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℝ) ℝ).inv)
          S).f p ≫ (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℝ)).map
            ((SSet.chainComplexMap j (ModuleCat.of ℝ ℝ)).f p ≫ ψ) ≫
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℝ) ℝ).hom := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  ext a
  refine (ConcreteCategory.congr_hom (SSet.ι_chainComplexMap_f_assoc (f := j) (x := σ)
    (R := ModuleCat.of ℤ (ULift.{0} ℤ))
      (h := (X.singularCochainComplexIntChainsIso ℝ).hom.f p ψ)) a).trans ?_
  refine (X.singularCochainComplexIntChainsIso_hom_f_apply_ιChainComplex ℝ _ ψ a).trans ?_
  rw [SSet.ιChainComplex_restrictScalarsChainMap_f_assoc, ← Functor.map_comp_assoc,
    SSet.ι_chainComplexMap_f_assoc, Functor.map_comp, Category.assoc, ← smul_eq_mul, ← map_smul,
    ← map_smul,
    smul_eq_mul, mul_one]
  -- The identifications of `ℝ` with the restricted `ℝ`-module `ℝ`, and restrictions of scalars of
  -- morphisms, are the identity on elements, but their evaluation lemmas are stated for the
  -- underlying types, which `rw` does not identify with the carriers here.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ModuleCat.restrictScalarsAlgebraMapIso_hom_apply,
    ModuleCat.restrictScalars.map_apply (algebraMap ℤ ℝ),
    ModuleCat.restrictScalars.map_apply (algebraMap ℤ ℝ),
    ModuleCat.restrictScalarsAlgebraMapIso_inv_apply, intToRealCoeff_apply,
    ModuleCat.restrictScalars.map_apply (algebraMap ℤ ℝ)]

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
