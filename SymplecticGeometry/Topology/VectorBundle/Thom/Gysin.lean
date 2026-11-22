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
have. It contains only `TauCeti.exact_singularCup_eulerClass_singularCohomologyMap`, the
exactness of the Gysin sequence of the complement `E₀` of the zero section at the cohomology of
the base. The changes are these:

* The section `GysinMap` (`TauCeti.gysinδ`, `TauCeti.thomMap_gysinδ`, `TauCeti.gysinδ_eq_iff`)
  and, from the section `Gysin`, the exactness statements
  `TauCeti.exact_singularCohomologyMap_gysinδ` and `TauCeti.exact_gysinδ_singularCup_eulerClass`
  are left out, since the library uses none of them.
* The section `Sphere` (the Gysin sequence of the sphere bundle) and the three vanishing lemmas
  at the end of the section `Gysin`
  (`singularCohomologyMap_zeroSectionComplProjHom_singularCup_eulerClass`,
  `gysinδ_singularCohomologyMap_zeroSectionComplProjHom`, `singularCup_gysinδ_eulerClass`) are
  left out, and so is the import of `TauCeti.Topology.VectorBundle.SphereBundle.Basic`, which only
  the sphere bundle needs.
* `TauCeti.eulerClass_thomMap` and the exact sequence of the Thom pair with the base in place of
  the total space come from `SymplecticGeometry.Topology.VectorBundle.Thom.Isomorphism` and
  `SymplecticGeometry.Topology.VectorBundle.EulerClass`, the copies of Tau Ceti's main branch.
* This docstring keeps only what concerns the declaration copied: it omits Tau Ceti's account of
  the sphere bundle, of the Gysin connecting map and of the two exactness statements left out,
  together with their entries under *Main definitions* and *Main results*, and it cites only the
  one exactness lemma of the Thom pair that this file uses.

Let `E → B` be a real vector bundle with Thom pair `(E, E₀)`, `E₀` the complement of the zero
section, and let `π₀ : E₀ → B` be the restriction of the projection
(`TauCeti.zeroSectionComplProjHom`). The projection `π : E → B` is a homotopy equivalence with
homotopy inverse the zero section, so replacing `Hᵐ(E)` by `Hᵐ(B)` in the long exact sequence of
the pair `(E, E₀)` gives the exact sequence

`⋯ ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(B) ⟶ Hᵐ(E₀) ⟶ Hᵐ⁺¹(E, E₀) ⟶ Hᵐ⁺¹(B) ⟶ ⋯`

whose maps out of relative cohomology are the Euler class maps `TauCeti.eulerClass`, for
arbitrary coefficients and in every degree
(`TauCeti.exact_eulerClass_singularCohomologyMap_zeroSectionComplProjHom` is its exactness at
`Hᵐ(B)`).

For a relative class `u ∈ Hⁿ(E, E₀; K)` the Euler class map sends the image `π^*a ⌣ u` of
`a ∈ Hᵖ(B; M)` under the Thom map `TauCeti.thomMap` to `a ⌣ e(u)`
(`TauCeti.eulerClass_thomMap`). When the Thom map of `u` is surjective in degree `p`, it follows
that `Hᵖ(B) ⟶ Hᵖ⁺ⁿ(B) ⟶ Hᵖ⁺ⁿ(E₀)`, the cup product `a ↦ a ⌣ e(u)` with the Euler class followed
by the pullback along `π₀`, is exact: a piece of the **Gysin sequence**.

## Main results

* `TauCeti.exact_singularCup_eulerClass_singularCohomologyMap`: exactness of the Gysin sequence
  at `Hᵖ⁺ⁿ(B)` for a class whose Thom map is surjective in degree `p`.

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

end Gysin

end TauCeti
