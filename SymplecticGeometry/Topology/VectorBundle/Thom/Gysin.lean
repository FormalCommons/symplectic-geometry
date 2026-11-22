/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Thom.Isomorphism

/-!
# The Gysin sequence of a real vector bundle

This file is a part of Tau Ceti's file `TauCeti/Topology/VectorBundle/Thom/Gysin.lean`, copied
from Tau Ceti's main branch at commit `aa1b4e9e2a`, which the pinned version of Tau Ceti does not
have. It contains the Gysin connecting map `TauCeti.gysinδ` and the three exactness statements of
the Gysin sequence of the complement `E₀` of the zero section. The changes are these:

* The section `Sphere` (the Gysin sequence of the sphere bundle) and the three vanishing lemmas
  at the end of the section `Gysin`
  (`singularCohomologyMap_zeroSectionComplProjHom_singularCup_eulerClass`,
  `gysinδ_singularCohomologyMap_zeroSectionComplProjHom`, `singularCup_gysinδ_eulerClass`) are
  left out, and so is the import of `TauCeti.Topology.VectorBundle.SphereBundle.Basic`, which only
  the sphere bundle needs.
* `TauCeti.eulerClass_thomMap` and the exact sequence of the Thom pair with the base in place of
  the total space come from `SymplecticGeometry.Topology.VectorBundle.Thom.Isomorphism` and
  `SymplecticGeometry.Topology.VectorBundle.EulerClass`, the copies of Tau Ceti's main branch.
* This docstring omits Tau Ceti's account of the sphere bundle.

Let `E → B` be a real vector bundle with Thom pair `(E, E₀)`, `E₀` the complement of the zero
section, and let `π₀ : E₀ → B` be the restriction of the projection
(`TauCeti.zeroSectionComplProjHom`). The projection `π : E → B` is a homotopy equivalence with
homotopy inverse the zero section, so replacing `Hᵐ(E)` by `Hᵐ(B)` in the long exact sequence of
the pair `(E, E₀)` gives the exact sequence

`⋯ ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(B) ⟶ Hᵐ(E₀) ⟶ Hᵐ⁺¹(E, E₀) ⟶ Hᵐ⁺¹(B) ⟶ ⋯`

whose maps out of relative cohomology are the Euler class maps `TauCeti.eulerClass`, for
arbitrary coefficients and in every degree
(`TauCeti.exact_eulerClass_singularCohomologyMap_zeroSectionComplProjHom`,
`TauCeti.exact_singularCohomologyMap_zeroSectionComplProjHom_singularCohomologyδ`,
`TauCeti.exact_singularCohomologyδ_eulerClass`, in `TauCeti.Topology.VectorBundle.EulerClass`).

For a relative class `u ∈ Hⁿ(E, E₀; K)` the Euler class map sends the image `π^*a ⌣ u` of
`a ∈ Hᵖ(B; M)` under the Thom map `TauCeti.thomMap` to `a ⌣ e(u)`
(`TauCeti.eulerClass_thomMap`). When the Thom map of `u` is bijective (this is the Thom
isomorphism, which holds for a Thom class by Milnor and Stasheff, Theorem 10.4, and is not proved
in this file), it identifies `Hᵖ⁺ⁿ(E, E₀; M)` with `Hᵖ(B; M)`, and the sequence above becomes the
**Gysin sequence**

`⋯ ⟶ Hᵖ(B) ⟶ Hᵖ⁺ⁿ(B) ⟶ Hᵖ⁺ⁿ(E₀) ⟶ Hᵖ⁺¹(B) ⟶ Hᵖ⁺ⁿ⁺¹(B) ⟶ ⋯`,

whose maps are the cup product `a ↦ a ⌣ e(u)` with the Euler class, the pullback along `π₀`, and
the Gysin connecting map `TauCeti.gysinδ`, the connecting morphism of the pair followed by the
inverse of the Thom map (`TauCeti.exact_singularCup_eulerClass_singularCohomologyMap`,
`TauCeti.exact_singularCohomologyMap_gysinδ`, `TauCeti.exact_gysinδ_singularCup_eulerClass`). Each
statement asks for the bijectivity, or only the surjectivity, of the Thom map in the single degree
that it uses. Below the rank, where these degrees do not exist, the sequences of the Thom pair
above apply directly.

## Main definitions

* `TauCeti.gysinδ`: the Gysin connecting map `Hˡ(E₀; M) ⟶ H^q(B; M)`, `l + 1 = q + n`.

## Main results

* `TauCeti.exact_singularCup_eulerClass_singularCohomologyMap`,
  `TauCeti.exact_singularCohomologyMap_gysinδ`, `TauCeti.exact_gysinδ_singularCup_eulerClass`:
  the Gysin sequence of a class whose Thom map is bijective.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12, Theorem 12.2 (the Gysin sequence) and its proof.
* A. Hatcher, *Algebraic Topology*, Section 4.D, the Gysin sequence following Corollary 4D.11.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory
universe w

namespace TauCeti

section GysinMap

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **The Gysin connecting map** `Hˡ(E₀; M) ⟶ H^q(B; M)` of a class `u ∈ Hⁿ(E, E₀; K)` whose
Thom map is bijective in degree `q`, for `l + 1 = m` and `q + n = m`: the connecting morphism
`Hˡ(E₀; M) ⟶ Hᵐ(E, E₀; M)` of the pair `(E, E₀)` followed by the inverse of the Thom map. It is
characterized by `TauCeti.thomMap_gysinδ`. -/
def gysinδ {n q l m : ℕ} (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u)) :
    (thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M l →ₗ[K]
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K M q :=
  (LinearEquiv.ofBijective _ hu).symm.toLinearMap ∘ₗ
    ((thomPair F E).singularCohomologyδ (ModuleCat.of K K) K M l m hl).hom

/-- The Thom map sends the Gysin connecting map to the connecting morphism of the pair `(E, E₀)`:
`π^*(gysinδ y) ⌣ u = δ y`. -/
@[simp]
theorem thomMap_gysinδ {n q l m : ℕ} (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u))
    (y : (thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M l) :
    thomMap F E M n q m h u (gysinδ F E M hl h u hu y) =
      (thomPair F E).singularCohomologyδ (ModuleCat.of K K) K M l m hl y :=
  (LinearEquiv.ofBijective _ hu).apply_symm_apply _

/-- The Gysin connecting map is the unique map whose image under the Thom map is the connecting
morphism of the pair `(E, E₀)`. -/
theorem gysinδ_eq_iff {n q l m : ℕ} (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u))
    (y : (thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M l)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M q) :
    gysinδ F E M hl h u hu y = a ↔
      thomMap F E M n q m h u a =
        (thomPair F E).singularCohomologyδ (ModuleCat.of K K) K M l m hl y :=
  ⟨fun ha ↦ ha ▸ thomMap_gysinδ F E M hl h u hu y,
    fun ha ↦ hu.1 ((thomMap_gysinδ F E M hl h u hu y).trans ha.symm)⟩

end GysinMap

section Gysin

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **Exactness of the Gysin sequence at `Hᵐ(B)`**: if the Thom map of `u ∈ Hⁿ(E, E₀; K)` is
surjective in degree `p`, then `Hᵖ(B; M) ⟶ Hᵐ(B; M) ⟶ Hᵐ(E₀; M)`, the cup product `a ↦ a ⌣ e(u)`
with the Euler class followed by the pullback along `π₀ : E₀ → B`, is exact, for `p + n = m`. -/
theorem exact_singularCup_eulerClass_singularCohomologyMap {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Surjective (thomMap F E M n p m h u)) :
    Function.Exact
      (((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h).flip
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u))
      (TopCat.singularCohomologyMap (zeroSectionComplProjHom F E) m) := by
  intro y
  rw [exact_eulerClass_singularCohomologyMap_zeroSectionComplProjHom _ K M F E m y]
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ⟨thomMap F E M n p m h u a, ?_⟩⟩
  · obtain ⟨a, rfl⟩ := hu x
    exact ⟨a, (eulerClass_thomMap F E h u a).symm.trans hx⟩
  · exact (eulerClass_thomMap F E h u a).trans ha

/-- **Exactness of the Gysin sequence at `Hˡ(E₀)`**: if the Thom map of `u ∈ Hⁿ(E, E₀; K)` is
bijective in degree `q`, then `Hˡ(B; M) ⟶ Hˡ(E₀; M) ⟶ H^q(B; M)`, the pullback along
`π₀ : E₀ → B` followed by the Gysin connecting map, is exact, for `l + 1 = q + n`. -/
theorem exact_singularCohomologyMap_gysinδ {n q l m : ℕ} (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u)) :
    Function.Exact (TopCat.singularCohomologyMap (zeroSectionComplProjHom F E) l)
      (gysinδ F E M hl h u hu) := by
  intro y
  rw [← exact_singularCohomologyMap_zeroSectionComplProjHom_singularCohomologyδ _ K M F E l m hl y,
    gysinδ_eq_iff, map_zero, eq_comm]

/-- **Exactness of the Gysin sequence at `H^q(B)`**: if the Thom map of `u ∈ Hⁿ(E, E₀; K)` is
bijective in degree `q`, then `Hˡ(E₀; M) ⟶ H^q(B; M) ⟶ Hᵐ(B; M)`, the Gysin connecting map
followed by the cup product `a ↦ a ⌣ e(u)` with the Euler class, is exact, for `l + 1 = m` and
`q + n = m`. -/
theorem exact_gysinδ_singularCup_eulerClass {n q l m : ℕ} (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u)) :
    Function.Exact (gysinδ F E M hl h u hu)
      (((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom q n m h).flip
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u)) := by
  intro a
  rw [LinearMap.flip_apply, ← eulerClass_thomMap,
    exact_singularCohomologyδ_eulerClass _ K M F E l m hl]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, (gysinδ_eq_iff F E M hl h u hu y a).2 hy.symm⟩,
    fun ⟨y, hy⟩ ↦ ⟨y, ((gysinδ_eq_iff F E M hl h u hu y a).1 hy).symm⟩⟩

end Gysin

end TauCeti
