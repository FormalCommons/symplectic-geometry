/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Manifold
public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
import TauCeti.Geometry.Manifold.Topology

/-!
# Evaluation on a fundamental class and change of cochain values

Tau Ceti's `TauCeti.HomologicalOrientation.evalFundamentalClass` evaluates a class of
`Hⁿ(X; M)` on the image `f_*[N]` of the fundamental class of a compact oriented `n`-manifold,
with values in the coefficient module `M`. This file shows that the evaluation commutes with a
change of cochain values `g : M ⟶ M'` (`TopCat.singularCohomologyValueMap`), since the Kronecker
pairing does (`TopCat.singularKronecker_coefficient_naturality`). In particular a class with
values in `ULift ℤ`, such as Tau Ceti's Euler classes, and its image in integral cohomology under
`TopCat.uliftIntegralCohomologyIso` have the same evaluation, read through `ULift.down`.

On a compact connected oriented manifold `N` itself, evaluation on `[N]` is a bijection
`Hⁿ(N; L) → L` for every abelian group `L`, with no injectivity hypothesis on `L` as in Tau Ceti's
`TauCeti.HomologicalOrientation.evalFundamentalClass_id_bijective`. The evaluation factors as the
cap product `c ↦ [N] ⌢ c` into `H₀(N; L)` followed by the augmentation `H₀(N; L) → L`
(`TopCat.singularCap_comp_singularHomology₀ε`). The first map is bijective by Poincaré duality
(`TauCeti.HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`), and the second
because a connected manifold is path connected.

## Main results

* `TauCeti.HomologicalOrientation.evalFundamentalClass_singularCohomologyValueMap`:
  `⟨g_* c, f_*[N]⟩ = g ⟨c, f_*[N]⟩`.
* `TauCeti.HomologicalOrientation.evalFundamentalClass_uliftIntegralCohomologyIso_hom`: the
  evaluation of the integral class of `c` is the evaluation of `c`, read in `ℤ`.
* `TauCeti.HomologicalOrientation.evalFundamentalClass_id_eq_singularHomology₀ε`:
  `⟨c, [N]⟩ = ε([N] ⌢ c)`.
* `TauCeti.HomologicalOrientation.evalFundamentalClass_id_bijective'`: for `N` connected and any
  abelian group `L`, `c ↦ ⟨c, [N]⟩` is a bijection `Hⁿ(N; L) → L`, and
  `TauCeti.HomologicalOrientation.evalFundamentalClass_id_injective`: two classes of `Hⁿ(N; L)`
  with the same evaluation on `[N]` are equal.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1 (the Kronecker pairing) and Section 3.3 (fundamental classes, the cap product and
  Poincaré duality, Theorem 3.30).
-/

public section

open CategoryTheory MonoidalCategory Module
open scoped Manifold

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

-- The cap product over `ℤ` uses the `ℤ`-linear monoidal structure of a preadditive category, as in
-- `TauCeti.HomologicalOrientation.bijective_singularCapAddHom_fundamentalClass`.
attribute [local instance] MonoidalPreadditive.monoidalLinearInt

/-- **Evaluation on the fundamental class through the cap product**: for `c ∈ Hⁿ(N; L)`,
`⟨c, [N]⟩` is the augmentation of the cap product `[N] ⌢ c ∈ H₀(N; L)`. -/
theorem evalFundamentalClass_id_eq_singularHomology₀ε (L : ModuleCat.{0} ℤ)
    (c : (TopCat.of N).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L n) :
    o.evalFundamentalClass hn L (ContinuousMap.id N) c =
      ((TopCat.of N).singularHomology₀ε L).hom
        (((TopCat.of N).singularCap ℤ (ρ_ _).inv (ρ_ L).hom n 0 n (add_zero n) c).hom
          (o.fundamentalClass hn)) := by
  rw [evalFundamentalClass_apply, mapFundamentalClass_id,
    ← TopCat.singularCap_comp_singularHomology₀ε (TopCat.of N) ℤ n (add_zero n) c,
    ModuleCat.hom_comp]
  -- `fundamentalClass` lives in the homology of the singular simplicial set, the source of the
  -- cap product in `singularHomologyFunctor`; the two agree by definition.
  exact LinearMap.comp_apply _ _ _

/-- **Evaluation on the fundamental class is an isomorphism in top degree.** For a compact
connected oriented `n`-manifold `N` and any abelian group `L`, the map `Hⁿ(N; L) → L`,
`c ↦ ⟨c, [N]⟩`, is bijective. -/
theorem evalFundamentalClass_id_bijective' [ConnectedSpace N] (L : ModuleCat.{0} ℤ) :
    Function.Bijective (o.evalFundamentalClass hn L (ContinuousMap.id N)) := by
  have : PathConnectedSpace N := 𝓘(ℝ, E).pathConnectedSpace N
  have h := (ConcreteCategory.bijective_of_isIso ((TopCat.of N).singularHomology₀ε L)).comp
    (o.bijective_singularCapAddHom_fundamentalClass hn L n 0 (add_zero n))
  convert h using 1
  funext c
  exact (o.evalFundamentalClass_id_eq_singularHomology₀ε hn L c).trans
    (congrArg _ (TopCat.singularCapAddHom_apply ..).symm)

/-- **Classes of top degree are determined by their evaluation on the fundamental class**: on a
compact connected oriented `n`-manifold `N`, two classes of `Hⁿ(N; L)`, for any abelian group `L`,
with the same value on `[N]` are equal. -/
theorem evalFundamentalClass_id_injective [ConnectedSpace N] (L : ModuleCat.{0} ℤ) :
    Function.Injective (o.evalFundamentalClass hn L (ContinuousMap.id N)) :=
  (o.evalFundamentalClass_id_bijective' hn L).1

end TauCeti.HomologicalOrientation

end
