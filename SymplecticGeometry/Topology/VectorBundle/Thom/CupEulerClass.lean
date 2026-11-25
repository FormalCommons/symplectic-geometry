/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
public import SymplecticGeometry.LinearAlgebra.Complex.Finrank
public import SymplecticGeometry.Topology.VectorBundle.Thom.ChangeOfCoefficients
public import TauCeti.Topology.VectorBundle.Thom.Gysin
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars

/-!
# Cup product with the Euler class when the complement of the zero section is acyclic

Let `E → B` be a real vector bundle, `E₀` the complement of its zero section
(`TauCeti.zeroSectionCompl`), and `u ∈ Hⁿ(E, E₀; K)` a relative class whose Thom map
`a ↦ π^*a ⌣ u` (`TauCeti.thomMap`) is bijective, as it is for a Thom class over a compact base
(`TauCeti.bijective_thomMap_of_compactSpace`). Write `e(u) = TauCeti.eulerClass … u` for its Euler
class. For `p + n = m`, the cup product `a ↦ a ⌣ e(u) : Hᵖ(B; M) → Hᵐ(B; M)` sits in the Gysin
sequence

`Hᵐ⁻¹(E₀; M) ⟶ Hᵖ(B; M) ⟶ Hᵐ(B; M) ⟶ Hᵐ(E₀; M)`,

so it is injective when `Hᵐ⁻¹(E₀; M)` vanishes and surjective when `Hᵐ(E₀; M)` vanishes. The
injectivity needs only an injective Thom map, through the exact sequence of the pair `(E, E₀)`
(`TauCeti.exact_singularCohomologyδ_eulerClass`), and the surjectivity only a surjective one,
through the exactness of the Gysin sequence at `Hᵐ(B; M)`. Applied to the tautological line
over `ℂPⁿ`, whose complement of the zero section is `ℂⁿ⁺¹ ∖ {0}`, this is the inductive step for
the powers of the hyperplane class.

Over a compact base, the bijectivity also holds in integral cohomology for a Thom class with
values `ULift ℤ` (`TauCeti.bijective_integralCup_eulerClass`), hence for the Euler class of an
oriented real vector bundle (`TauCeti.VectorBundleOrientation.bijective_integralCup_eulerClass`)
and for the Euler class `TauCeti.complexEulerClass` of the real bundle underlying a complex one,
with its canonical orientation (`TauCeti.bijective_integralCup_complexEulerClass`). Tau Ceti
writes these classes, and the Thom classes they come from, with chain coefficients and
values `ULift ℤ` and the structure `CategoryTheory.Linear.preadditiveIntLinear` of `ModuleCat ℤ`,
while its Thom map takes chain coefficients and values `ℤ` and the structure
`ModuleCat.instLinear`. The changes of coefficients of `ChangeOfCoefficients.lean` carry the Thom
class to one with coefficients `ℤ` and its Euler class along, and the inverse of Tau Ceti's
`TopCat.integralCohomologyEquiv` and `TopCat.uliftIntegralCohomologyIso` carry the result to
`TopCat.integralCohomology`.

## Main results

* `TauCeti.injective_singularCup_eulerClass`: injectivity, if `Hᵐ⁻¹(E₀; M)` vanishes.
* `TauCeti.surjective_singularCup_eulerClass`: surjectivity, if `Hᵐ(E₀; M)` vanishes.
* `TauCeti.bijective_singularCup_eulerClass`: bijectivity, if both vanish.
* `TauCeti.bijective_integralCup_eulerClass`: the bijectivity in integral cohomology, for a Thom
  class with values `ULift ℤ` over a compact base.
* `TauCeti.VectorBundleOrientation.bijective_integralCup_eulerClass`: the same for the Euler class
  of an oriented real vector bundle.
* `TauCeti.bijective_integralCup_complexEulerClass`: the bijectivity for the Euler class of a
  complex vector bundle, in integral cohomology.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12, Theorem 12.2 (the Gysin sequence), and §14 (the canonical orientation
  of a complex vector bundle).
-/

public section

open Bundle CategoryTheory Limits MonoidalCategory

universe w

namespace TauCeti

section Real

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K] {M : ModuleCat.{w} K}

/-- **Cup product with the Euler class is injective** if the cohomology of the complement `E₀` of
the zero section vanishes one degree below the target: for `u ∈ Hⁿ(E, E₀; K)` whose Thom map is
injective in degree `p`, `p + n = m = l + 1`, and `Hˡ(E₀; M) = 0`, the map
`a ↦ a ⌣ e(u) : Hᵖ(B; M) → Hᵐ(B; M)` is injective. -/
theorem injective_singularCup_eulerClass {n p l m : ℕ} (hl : l + 1 = m) (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Injective (thomMap F E M n p m h u))
    (hE : IsZero ((thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M l)) :
    Function.Injective
      (((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h).flip
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u)) := by
  have := ModuleCat.subsingleton_of_isZero hE
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ hu ?_
  rw [LinearMap.flip_apply, ← eulerClass_thomMap] at ha
  obtain ⟨y, hy⟩ := (exact_singularCohomologyδ_eulerClass _ K M F E l m hl _).1 ha
  rw [map_zero, ← hy, Subsingleton.elim y 0, map_zero]

/-- **Cup product with the Euler class is surjective** if the cohomology of the complement `E₀` of
the zero section vanishes in the target degree: for `u ∈ Hⁿ(E, E₀; K)` whose Thom map is
surjective in degree `p`, `p + n = m`, and `Hᵐ(E₀; M) = 0`, the map
`a ↦ a ⌣ e(u) : Hᵖ(B; M) → Hᵐ(B; M)` is surjective. -/
theorem surjective_singularCup_eulerClass {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Surjective (thomMap F E M n p m h u))
    (hE : IsZero ((thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M m)) :
    Function.Surjective
      (((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h).flip
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u)) := by
  have := ModuleCat.subsingleton_of_isZero hE
  exact fun y ↦
    (exact_singularCup_eulerClass_singularCohomologyMap F E M h u hu y).1 (Subsingleton.elim _ _)

/-- **Cup product with the Euler class is bijective** if the cohomology of the complement `E₀` of
the zero section vanishes in the target degree and one below it: for `u ∈ Hⁿ(E, E₀; K)` whose
Thom map is bijective in degree `p`, `p + n = m = l + 1`, and `Hˡ(E₀; M) = Hᵐ(E₀; M) = 0`, the map
`a ↦ a ⌣ e(u) : Hᵖ(B; M) → Hᵐ(B; M)` is bijective. -/
theorem bijective_singularCup_eulerClass {n p l m : ℕ} (hl : l + 1 = m) (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n p m h u))
    (hEl : IsZero ((thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M l))
    (hEm : IsZero ((thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M m)) :
    Function.Bijective
      (((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h).flip
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u)) :=
  ⟨injective_singularCup_eulerClass hl h u hu.1 hEl,
    surjective_singularCup_eulerClass h u hu.2 hEm⟩

end Real

section Integral

open Module

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **The Gysin step in integral cohomology**: for a Thom class `U ∈ Hᵈ(E, E₀; ULift ℤ)` of a real
vector bundle `E → B` of rank `d` over a compact base, `p + d = m = l + 1`, and
`Hˡ(E₀; ℤ) = Hᵐ(E₀; ℤ) = 0`, the map `a ↦ a ⌣ e(U) : Hᵖ(B; ℤ) → Hᵐ(B; ℤ)` is bijective, where
the Euler class `e(U)` is read in integral cohomology through
`TopCat.uliftIntegralCohomologyIso`. The rank is any `d` equal to `finrank ℝ F`, so that `U` can
live in the degree that its Euler class is used in. -/
theorem bijective_integralCup_eulerClass [CompactSpace B] {d p l m : ℕ}
    (hd : finrank ℝ F = d) (hl : l + 1 = m) (h : p + d = m)
    (U : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) d)
    (hU : IsThomClass F E (hd ▸ U))
    (hEl : IsZero ((thomPair F E).snd.integralCohomology l))
    (hEm : IsZero ((thomPair F E).snd.integralCohomology m)) :
    Function.Bijective fun a : (TopCat.of B).integralCohomology p ↦
      (TopCat.of B).integralCup p d m h a ((TopCat.uliftIntegralCohomologyIso _ d).hom
        (eulerClass _ ℤ _ F E d U)) := by
  subst hd
  -- The Thom class with chain coefficients and values `ℤ`, for the linear structure
  -- `ModuleCat.instLinear` that `TauCeti.thomMap` uses.
  have hU' := ((hU.singularCohomologyValueMap uliftIntIso).singularCohomologyChainCoefficientMap
      integralCoeffIso.symm).singularCohomologyLinearCongr (L₂ := ModuleCat.instLinear)
    (Subsingleton.elim _ _)
  have hzero (n : ℕ) (hn : IsZero ((thomPair F E).snd.integralCohomology n)) :=
    hn.of_iso (((thomPair F E).snd.integralCohomologyEquiv n).symm).toModuleIso
  have hbij := bijective_singularCup_eulerClass (M := 𝟙_ (ModuleCat.{0} ℤ)) hl h _
    (bijective_thomMap_of_compactSpace _ p m h hU') (hzero l hEl) (hzero m hEm)
  rw [← unitors_equal] at hbij
  -- Carry the Euler class of the new Thom class back to that of `U`.
  have h₁ := eulerClass_comp_singularCohomologyChainCoefficientMap_apply (F := F) (E := E) ℤ
    (ModuleCat.of ℤ ℤ) integralCoeffIso.symm.hom (finrank ℝ F)
  have h₂ := eulerClass_comp_singularCohomologyValueMap_apply (F := F) (E := E)
    (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ uliftIntIso.hom (finrank ℝ F)
  rw [← LinearEquiv.symm_apply_apply ((TopCat.of B).integralCohomologyEquiv _)
      ((TopCat.uliftIntegralCohomologyIso _ _).hom (eulerClass _ ℤ _ F E _ U)),
    TopCat.integralCohomologyEquiv_apply, TopCat.uliftIntegralCohomologyIso_hom, h₂, h₁]
  -- The values are written `ModuleCat.of ℤ ℤ` in `hbij` and `𝟙_ (ModuleCat ℤ)`, which Mathlib
  -- defines to be it, in the goal, so `rw` cannot carry one to the other; `exact` matches them.
  refine (TopCat.bijective_integralCup_integralCohomologyEquiv_symm_iff _ p _ m h _).2 ?_
  convert hbij using 4
  exact congrArg _ (singularCohomologyLinearCongr_eulerClass (F := F) (E := E) _ _ _ _ _)

namespace VectorBundleOrientation

/-- **Cup product with the Euler class of an oriented vector bundle is bijective** if the integral
cohomology of the complement `E₀` of the zero section vanishes in the target degree and one below
it: for an orientation `o` of a real vector bundle `E → B` of rank `n + 1` over a compact base,
`p + (n + 1) = m = l + 1`, and `Hˡ(E₀; ℤ) = Hᵐ(E₀; ℤ) = 0`, the map
`a ↦ a ⌣ e(E, o) : Hᵖ(B; ℤ) → Hᵐ(B; ℤ)` is bijective, where the Euler class
`TauCeti.VectorBundleOrientation.eulerClass` is read in integral cohomology through
`TopCat.uliftIntegralCohomologyIso`. -/
theorem bijective_integralCup_eulerClass [CompactSpace B] {n : ℕ}
    (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1) {p l m : ℕ}
    (hl : l + 1 = m) (h : p + (n + 1) = m)
    (hEl : IsZero ((TopCat.of (zeroSectionCompl F E)).integralCohomology l))
    (hEm : IsZero ((TopCat.of (zeroSectionCompl F E)).integralCohomology m)) :
    Function.Bijective fun a : (TopCat.of B).integralCohomology p ↦
      (TopCat.of B).integralCup p (n + 1) m h a
        ((TopCat.uliftIntegralCohomologyIso _ _).hom (o.eulerClass hF)) := by
  rw [eulerClass_def]
  exact TauCeti.bijective_integralCup_eulerClass hF hl h _ (o.isThomClass_thomClass hF) hEl hEm

end VectorBundleOrientation

end Integral

section Complex

open Module

variable {B : Type} [TopologicalSpace B]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]

open scoped VectorBundle.ComplexToReal

/-- **Cup product with the Euler class of a complex vector bundle is bijective** if the integral
cohomology of the complement `E₀` of the zero section vanishes in the target degree and one below
it: for a complex vector bundle `E → B` of complex rank `r + 1` over a compact base,
`p + 2r + 2 = m = l + 1`, and `Hˡ(E₀; ℤ) = Hᵐ(E₀; ℤ) = 0`, the map
`a ↦ a ⌣ e(E_ℝ) : Hᵖ(B; ℤ) → Hᵐ(B; ℤ)` is bijective, where `e(E_ℝ)` is
`TauCeti.complexEulerClass`, read in integral cohomology through
`TopCat.uliftIntegralCohomologyIso`. -/
theorem bijective_integralCup_complexEulerClass [CompactSpace B] {r : ℕ}
    (hF : finrank ℂ F = r + 1) {p l m : ℕ} (hl : l + 1 = m) (h : p + (2 * r + 2) = m)
    (hEl : IsZero ((TopCat.of (zeroSectionCompl F E)).integralCohomology l))
    (hEm : IsZero ((TopCat.of (zeroSectionCompl F E)).integralCohomology m)) :
    Function.Bijective fun a : (TopCat.of B).integralCohomology p ↦
      (TopCat.of B).integralCup p (2 * r + 2) m h a
        ((TopCat.uliftIntegralCohomologyIso _ _).hom (complexEulerClass F E hF)) := by
  rw [complexEulerClass_def]
  exact VectorBundleOrientation.bijective_integralCup_eulerClass _
    (SymplecticGeometry.finrank_real_of_finrank_complex_eq_add_one hF) hl h hEl hEm

end Complex

end TauCeti

end
