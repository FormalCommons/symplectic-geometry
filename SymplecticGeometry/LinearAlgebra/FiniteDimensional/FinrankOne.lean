/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Modules of rank one given by a `Fact`

A module `V` whose rank one is recorded as the instance `Fact (Module.finrank K V = 1)` gets two
instances here: it is finite-dimensional over a division ring `K`, and its rank is that of `K`
itself over any ring with the strong rank condition. The second is the hypothesis
`Fact (finrank K K = finrank K V)` that a frame bundle with model fibre `K` asks of a bundle with
model fibre `V`.

Mathlib's `FiniteDimensional.of_fact_finrank_eq_succ` is a lemma and not an instance because its
`n` cannot be inferred; its rank-two case `FiniteDimensional.of_fact_finrank_eq_two` is a lemma
that callers enable with a local instance attribute. For rank one there is no `n` to infer, so
both instances here are global. A search for `FiniteDimensional K V` or for
`Fact (finrank K K = finrank K V)` then also looks for `Fact (finrank K V = 1)`, an instance
search that fails at once where no such fact is in context; both conclusions are propositions,
so the instances create no diamond.

## Main definitions

* `FiniteDimensional.of_fact_finrank_eq_one`: a module of rank one is finite-dimensional.
* `Module.fact_finrank_self_eq_of_fact_finrank_eq_one`: a module of rank one has the rank of the
  ring.
-/

public section

open Module

/-- A module of rank one, the rank given by a `Fact`, is finite-dimensional. -/
instance FiniteDimensional.of_fact_finrank_eq_one {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Fact (finrank K V = 1)] : FiniteDimensional K V :=
  .of_fact_finrank_eq_succ 0

/-- A module of rank one, the rank given by a `Fact`, has the rank of the ring itself. -/
instance Module.fact_finrank_self_eq_of_fact_finrank_eq_one {K V : Type*} [Semiring K]
    [StrongRankCondition K] [AddCommMonoid V] [Module K V] [Fact (finrank K V = 1)] :
    Fact (finrank K K = finrank K V) :=
  ⟨by rw [finrank_self, Fact.out (p := finrank K V = 1)]⟩

end
