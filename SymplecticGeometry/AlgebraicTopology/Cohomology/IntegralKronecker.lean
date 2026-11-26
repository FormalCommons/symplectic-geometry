/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
public import TauCeti.AlgebraicTopology.Cohomology.CrossProduct

/-!
# The Kronecker pairing of integral cohomology with integral homology

For a space `X` and `n : ℕ`, this file defines the `ℤ`-valued pairing
`⟨-, -⟩ : Hⁿ(X; ℤ) × Hₙ(X; ℤ) → ℤ` on Tau Ceti's integral cohomology `TopCat.integralCohomology`:
a class `a` is carried by `TopCat.integralCohomologyEquiv` to cohomology with chain coefficients
and values the unit object `ℤ` of `ModuleCat ℤ`, and evaluated there on homology by Tau Ceti's
Kronecker map `TopCat.singularKronecker`. The Kronecker map is taken with the `ℤ`-linear structure
`ModuleCat.instLinear` of a category of modules, the one with which Tau Ceti states its lemmas on
it; instance search on `ModuleCat ℤ` would find `CategoryTheory.Linear.preadditiveIntLinear`
instead. Fixing the structure inside the definition lets statements about the pairing of integral
classes be written without naming it.

## Main definitions and results

* `TopCat.integralKronecker`: the pairing, `ℤ`-linear in the class and in the homology class,
  with `TopCat.integralKronecker_def` and `TopCat.integralKronecker_apply` giving it through
  `TopCat.integralCohomologyEquiv` and `TopCat.singularKronecker`.
* `TopCat.integralKronecker_eq_singularKronecker`: the pairing is the Kronecker map of the class
  itself, with chain coefficients `ULift ℤ`, after the change of coefficients of homology along
  `TauCeti.integralCoeffIso`; this is Tau Ceti's `TopCat.singularKronecker_integralCohomologyEquiv`.
* `TopCat.integralKronecker_naturality`: `⟨f^* a, x⟩ = ⟨a, f_* x⟩` for a continuous map `f`.
* `TopCat.integralKronecker_integralCup_fst_snd_singularHomologyCross`: for classes `a` of `X` and
  `b` of `Y`, `⟨pr₁^* a ⌣ pr₂^* b, x × y⟩ = ⟨a, x⟩ ⟨b, y⟩` on a homology cross product, from Tau
  Ceti's `TopCat.singularKronecker_singularCup_fst_snd_singularHomologyCross`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (the Kronecker
  pairing) and Section 3.B (cross products).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology TauCeti

namespace TopCat

/-- **The Kronecker pairing of integral cohomology**, `Hⁿ(X; ℤ) →ₗ[ℤ] (Hₙ(X; ℤ) →ₗ[ℤ] ℤ)`: the
value `⟨a, x⟩` of an integral class `a` on a homology class `x` with coefficients `ℤ`. It is Tau
Ceti's Kronecker map `TopCat.singularKronecker`, for the `ℤ`-linear structure
`ModuleCat.instLinear`, applied to the image of `a` under `TopCat.integralCohomologyEquiv`
(`TopCat.integralKronecker_apply`). -/
def integralKronecker (X : TopCat.{0}) (n : ℕ) :
    X.integralCohomology n →ₗ[ℤ]
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (𝟙_ (ModuleCat.{0} ℤ))).obj X →ₗ[ℤ]
        ℤ) :=
  ModuleCat.homLinearEquiv.toLinearMap ∘ₗ
    (@TopCat.singularKronecker _ _ _ _ (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ)) X ℤ _
      ModuleCat.instLinear n) ∘ₗ (X.integralCohomologyEquiv n).toLinearMap

/-- The pairing `TopCat.integralKronecker` is `TopCat.integralCohomologyEquiv`, followed by the
Kronecker map `TopCat.singularKronecker` for the structure `ModuleCat.instLinear` and by
`ModuleCat.homLinearEquiv`, which reads a morphism of `ModuleCat ℤ` as a linear map. -/
theorem integralKronecker_def (X : TopCat.{0}) (n : ℕ) :
    X.integralKronecker n =
      ModuleCat.homLinearEquiv.toLinearMap ∘ₗ
        (@TopCat.singularKronecker _ _ _ _ (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ)) X ℤ _
          ModuleCat.instLinear n) ∘ₗ (X.integralCohomologyEquiv n).toLinearMap :=
  (rfl)

/- Tau Ceti's lemmas on the Kronecker map, and the target of `TopCat.integralCohomologyEquiv`,
use the structure `ModuleCat.instLinear`; instance search would otherwise find
`CategoryTheory.Linear.preadditiveIntLinear`, which integral cohomology and its pull-backs
carry, and which those name explicitly. -/
attribute [local instance high] ModuleCat.instLinear

/-- The pairing `TopCat.integralKronecker` is the Kronecker map `TopCat.singularKronecker` of the
class read through `TopCat.integralCohomologyEquiv`. -/
theorem integralKronecker_apply (X : TopCat.{0}) (n : ℕ) (a : X.integralCohomology n)
    (x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (𝟙_ (ModuleCat.{0} ℤ))).obj X) :
    X.integralKronecker n a x = X.singularKronecker ℤ n (X.integralCohomologyEquiv n a) x :=
  (rfl)

/-- The pairing `TopCat.integralKronecker` on the image of a class under the inverse of
`TopCat.integralCohomologyEquiv` is the Kronecker map of that class. -/
theorem integralKronecker_integralCohomologyEquiv_symm (X : TopCat.{0}) (n : ℕ)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) n)
    (x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (𝟙_ (ModuleCat.{0} ℤ))).obj X) :
    X.integralKronecker n ((X.integralCohomologyEquiv n).symm a) x =
      X.singularKronecker ℤ n a x := by
  rw [integralKronecker_apply, LinearEquiv.apply_symm_apply]

/-- **The pairing of the class itself**: `⟨a, x⟩` is the Kronecker map of the integral class `a`,
with chain coefficients `ULift ℤ` and the `ℤ`-linear structure
`CategoryTheory.Linear.preadditiveIntLinear` of integral cohomology, on the image of `x` under the
change of coefficients `Hₙ(X; ℤ) ≅ Hₙ(X; ULift ℤ)` along `TauCeti.integralCoeffIso`. -/
theorem integralKronecker_eq_singularKronecker (X : TopCat.{0}) (n : ℕ)
    (a : X.integralCohomology n)
    (x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (𝟙_ (ModuleCat.{0} ℤ))).obj X) :
    X.integralKronecker n a x =
      @TopCat.singularKronecker _ _ _ _ (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ ℤ) X ℤ _
        Linear.preadditiveIntLinear n a
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).map integralCoeffIso.inv).app X x) := by
  rw [integralKronecker_apply, singularKronecker_integralCohomologyEquiv,
    ConcreteCategory.comp_apply]

/-- **Naturality of the integral Kronecker pairing**, `⟨f^* a, x⟩ = ⟨a, f_* x⟩`: for a continuous
map `f : X ⟶ Y`, the pull-back of an integral class of `Y` takes on a homology class of `X` the
value of the class on the push-forward. -/
theorem integralKronecker_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : Y.integralCohomology n)
    (x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (𝟙_ (ModuleCat.{0} ℤ))).obj X) :
    X.integralKronecker n
        (@TopCat.singularCohomologyMap _ _ _ _ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ _
          Linear.preadditiveIntLinear (ModuleCat.of ℤ ℤ) X Y f n a) x =
      Y.integralKronecker n a
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (𝟙_ (ModuleCat.{0} ℤ))).map f x) := by
  rw [integralKronecker_apply, integralKronecker_apply, integralCohomologyEquiv_naturality,
    singularKronecker_naturality, ConcreteCategory.comp_apply]

/-- **The integral cup product of pull-backs along the projections on a cross product.** For
integral classes `a ∈ Hᵖ(X; ℤ)`, `b ∈ H^q(Y; ℤ)` and homology classes `x ∈ Hₚ(X; ℤ)`,
`y ∈ H_q(Y; ℤ)`, let `x × y ∈ Hₙ(X × Y; ℤ)` be the homology cross product, read with coefficients
`ℤ` instead of `ℤ ⊗ ℤ` through the left unitor. Then `⟨pr₁^* a ⌣ pr₂^* b, x × y⟩ = ⟨a, x⟩ ⟨b, y⟩`,
the cup product being `TopCat.integralCup`. -/
theorem integralKronecker_integralCup_fst_snd_singularHomologyCross (X Y : TopCat.{0})
    {p q n : ℕ} (h : p + q = n) (a : X.integralCohomology p) (b : Y.integralCohomology q)
    (x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj (𝟙_ (ModuleCat.{0} ℤ))).obj X)
    (y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (𝟙_ (ModuleCat.{0} ℤ))).obj Y) :
    (X ⊗ Y).integralKronecker n ((X ⊗ Y).integralCup p q n h
        (@TopCat.singularCohomologyMap _ _ _ _ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ _
          Linear.preadditiveIntLinear (ModuleCat.of ℤ ℤ) (X ⊗ Y) X (fst X Y) p a)
        (@TopCat.singularCohomologyMap _ _ _ _ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ _
          Linear.preadditiveIntLinear (ModuleCat.of ℤ ℤ) (X ⊗ Y) Y (snd X Y) q b))
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).map (λ_ (𝟙_ (ModuleCat.{0} ℤ))).hom).app
        (X ⊗ Y) (singularHomologyCross X Y (𝟙_ (ModuleCat.{0} ℤ)) (𝟙_ (ModuleCat.{0} ℤ)) p q n h
          (x ⊗ₜ y))) =
      X.integralKronecker p a x * Y.integralKronecker q b y := by
  obtain ⟨a, rfl⟩ := (X.integralCohomologyEquiv p).symm.surjective a
  obtain ⟨b, rfl⟩ := (Y.integralCohomologyEquiv q).symm.surjective b
  rw [← integralCohomologyEquiv_symm_naturality, ← integralCohomologyEquiv_symm_naturality,
    ← integralCohomologyEquiv_symm_singularCup, integralKronecker_integralCohomologyEquiv_symm,
    integralKronecker_integralCohomologyEquiv_symm, integralKronecker_integralCohomologyEquiv_symm]
  exact singularKronecker_singularCup_fst_snd_singularHomologyCross X Y h a b x y

end TopCat

end
