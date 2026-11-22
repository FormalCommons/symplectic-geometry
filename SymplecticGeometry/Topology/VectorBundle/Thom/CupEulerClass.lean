/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Thom.Gysin

/-!
# Cup product with the Euler class when the complement of the zero section is acyclic

Let `E → B` be a real vector bundle, `E₀` the complement of its zero section
(`TauCeti.zeroSectionCompl`), and `u ∈ Hⁿ(E, E₀; K)` a relative class whose Thom map
`a ↦ π^*a ⌣ u` (`TauCeti.thomMap`) is bijective, as it is for a Thom class over a compact base
(`TauCeti.bijective_thomMap_of_compactSpace`). Write `e(u) = TauCeti.eulerClass … u` for its Euler
class. For `p + n = m`, the cup product `a ↦ a ⌣ e(u) : Hᵖ(B; M) → Hᵐ(B; M)` sits in the Gysin
sequence

`Hᵐ⁻¹(E₀; M) ⟶ Hᵖ(B; M) ⟶ Hᵐ(B; M) ⟶ Hᵐ(E₀; M)`,

so it is injective when `Hᵐ⁻¹(E₀; M)` vanishes and surjective when `Hᵐ(E₀; M)` vanishes. Applied
to the tautological line over `ℂPⁿ`, whose complement of the zero section is `ℂⁿ⁺¹ ∖ {0}`, this
is the inductive step for the powers of the hyperplane class.

## Main results

* `TauCeti.injective_singularCup_eulerClass`: injectivity, if `Hᵐ⁻¹(E₀; M)` vanishes.
* `TauCeti.surjective_singularCup_eulerClass`: surjectivity, if `Hᵐ(E₀; M)` vanishes.
* `TauCeti.bijective_singularCup_eulerClass`: bijectivity, if both vanish.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12, Theorem 12.2 (the Gysin sequence).
-/

public section

open Bundle CategoryTheory Limits MonoidalCategory

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K] {M : ModuleCat.{w} K}

/-- **Cup product with the Euler class is injective** if the cohomology of the complement `E₀` of
the zero section vanishes one degree below the target: for `u ∈ Hⁿ(E, E₀; K)` whose Thom map is
bijective in degree `p`, `p + n = m = l + 1`, and `Hˡ(E₀; M) = 0`, the map
`a ↦ a ⌣ e(u) : Hᵖ(B; M) → Hᵐ(B; M)` is injective. -/
theorem injective_singularCup_eulerClass {n p l m : ℕ} (hl : l + 1 = m) (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n p m h u))
    (hE : IsZero ((thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M l)) :
    Function.Injective
      (((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h).flip
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u)) := by
  have := ModuleCat.subsingleton_of_isZero hE
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
  obtain ⟨y, rfl⟩ := (exact_gysinδ_singularCup_eulerClass F E M hl h u hu a).1 ha
  rw [Subsingleton.elim y 0, map_zero]

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
  ⟨injective_singularCup_eulerClass hl h u hu hEl,
    surjective_singularCup_eulerClass h u hu.2 hEm⟩

end TauCeti

end
