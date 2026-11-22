/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Thom.Isomorphism
public import SymplecticGeometry.Topology.VectorBundle.EulerClass

/-!
# The Euler class map on the image of the Thom map

This file is a part of Tau Ceti's file `TauCeti/Topology/VectorBundle/Thom/Isomorphism.lean`,
copied from Tau Ceti's main branch at commit `aa1b4e9e2a`, which the pinned version of Tau Ceti
does not yet have. It contains only `TauCeti.eulerClass_thomMap`; the rest of Tau Ceti's file is in
the pinned version, which this file imports. The code is unchanged; the lemmas of Tau Ceti's
`TauCeti/Topology/VectorBundle/EulerClass.lean` that its proof uses and the pinned version lacks
come from `SymplecticGeometry.Topology.VectorBundle.EulerClass`, the copy of Tau Ceti's main
branch.

For a real vector bundle, the Euler class map `TauCeti.eulerClass` sends the image `Φ_u(a)` of
`a` under the Thom map to the cup product `a ⌣ e(u)` of `a` with the Euler class of `u`
(`TauCeti.eulerClass_thomMap`).

## Main results

* `TauCeti.eulerClass_thomMap`: the Euler class map sends `Φ_u(a)` to `a ⌣ e(u)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Module Set

universe w

namespace TauCeti

section EulerClass

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K] {M : ModuleCat.{w} K}

/-- **The Euler class map on the image of the Thom map**: for `u ∈ Hⁿ(E, E₀; K)` and
`a ∈ Hᵖ(B; M)`, the Euler class of `π^*a ⌣ u` is `a ⌣ e(u)`, the cup product of `a` with the Euler
class of `u`. -/
theorem eulerClass_thomMap {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    eulerClass (ModuleCat.of K K) K M F E m (thomMap F E M n p m h u a) =
      (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h a
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u) := by
  rw [eulerClass_def, eulerClass_def, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    thomMap_apply, TopPair.singularCohomologyπ_singularCup, ← TopCat.singularCup_naturality,
    ← ConcreteCategory.comp_apply,
    singularCohomologyMap_thomPairProj_comp_singularCohomologyMap_zeroSectionHom,
    ConcreteCategory.id_apply]
  -- The two sides differ only in writing the chain coefficients `K` as `𝟙_ (ModuleCat K)`.
  rfl

end EulerClass

end TauCeti
