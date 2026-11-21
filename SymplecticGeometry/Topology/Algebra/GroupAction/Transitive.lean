/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Group.OpenMapping
public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.Topology.Algebra.GroupAction.Transitive

/-!
# Orbit–stabilizer homeomorphism for σ-compact groups

Let a σ-compact topological group `G` act continuously and transitively on a Hausdorff Baire
space `X`. Then for every `b : X` the orbit map `g ↦ g • b` is open (Mathlib's
`isOpenMap_smul_of_sigmaCompact`), so the orbit–stabilizer bijection
`G ⧸ MulAction.stabilizer G b ≃ X` is a homeomorphism. This complements Tau Ceti's
`TauCeti.quotientStabilizerHomeomorph`, which instead assumes the quotient compact.

## Main definitions

* `MulAction.quotientStabilizerHomeomorphOfSigmaCompact`: the homeomorphism
  `G ⧸ MulAction.stabilizer G b ≃ₜ X`, with underlying equivalence Tau Ceti's
  `TauCeti.quotientStabilizerEquiv`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.5.
-/

public section

namespace MulAction

variable (G : Type*) {X : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace X]
  [MulAction G X] [IsTopologicalGroup G] [SigmaCompactSpace G] [BaireSpace X] [T2Space X]
  [ContinuousSMul G X] [IsPretransitive G X]

/-- For a σ-compact group acting continuously and transitively on a Hausdorff Baire space `X`,
the quotient of `G` by the stabilizer of `b` is homeomorphic to `X`, the coset of `g` going to
`g • b`. -/
noncomputable def quotientStabilizerHomeomorphOfSigmaCompact (b : X) :
    G ⧸ stabilizer G b ≃ₜ X :=
  (TauCeti.quotientStabilizerEquiv G b).toHomeomorphOfContinuousOpen
    (TauCeti.continuous_quotientStabilizerEquiv G b (continuous_id.smul continuous_const))
    (by
      rw [QuotientGroup.isOpenQuotientMap_mk.isOpenMap_iff]
      convert isOpenMap_smul_of_sigmaCompact (G := G) b using 1
      ext g
      exact TauCeti.quotientStabilizerEquiv_mk G b g)

/-- The underlying equivalence is the algebraic orbit–stabilizer equivalence. -/
@[simp]
theorem quotientStabilizerHomeomorphOfSigmaCompact_toEquiv (b : X) :
    (quotientStabilizerHomeomorphOfSigmaCompact G b).toEquiv =
      TauCeti.quotientStabilizerEquiv G b :=
  (rfl)

/-- The orbit–stabilizer homeomorphism sends the coset of `g` to `g • b`. -/
@[simp]
theorem quotientStabilizerHomeomorphOfSigmaCompact_mk (b : X) (g : G) :
    quotientStabilizerHomeomorphOfSigmaCompact G b (QuotientGroup.mk g) = g • b :=
  TauCeti.quotientStabilizerEquiv_mk G b g

/-- The orbit–stabilizer homeomorphism is equivariant for the left actions of `G`. -/
@[simp]
theorem quotientStabilizerHomeomorphOfSigmaCompact_smul (b : X) (g : G)
    (q : G ⧸ stabilizer G b) :
    quotientStabilizerHomeomorphOfSigmaCompact G b (g • q) =
      g • quotientStabilizerHomeomorphOfSigmaCompact G b q :=
  TauCeti.quotientStabilizerEquiv_smul G b g q

end MulAction

end
