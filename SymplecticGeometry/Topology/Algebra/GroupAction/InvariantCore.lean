/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Sets.Opens
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The invariant core of an open set, and actions on invariant open sets

Let a compact space `G` act jointly continuously on a space `X`, and let `U` be an open set. The
points of `X` whose whole orbit lies in `U` form an open set (Tau Ceti's
`TauCeti.isOpen_setOf_forall_smul_mem`). For an action of a monoid it is the largest invariant
subset of `U`. This file bundles it as `TopologicalSpace.Opens.invariantCore G U`.

An open set `U` that is invariant under the action of a monoid `G` carries the restricted action,
`TopologicalSpace.Opens.mulActionOfForallSMulMem`. The invariant core always is invariant, so it
carries this action as an instance.

## Main definitions

* `TopologicalSpace.Opens.invariantCore G U`: the points whose orbit lies in `U`, as an open set.
* `TopologicalSpace.Opens.mulActionOfForallSMulMem`: the action of `G` on an invariant open set.

## Main results

* `TopologicalSpace.Opens.invariantCore_le`: the invariant core lies in `U`.
* `TopologicalSpace.Opens.smul_mem_invariantCore`: the invariant core is invariant.
* `TopologicalSpace.Opens.subset_invariantCore`: it contains every invariant subset of `U`.
-/

public section

namespace TopologicalSpace.Opens

section Core

variable (G : Type*) {X : Type*} [TopologicalSpace G] [CompactSpace G] [TopologicalSpace X]

/-- For a jointly continuous action of a compact space `G` on `X`, the points of an open set `U`
whose whole orbit lies in `U`, as an open set. -/
def invariantCore [SMul G X] [ContinuousSMul G X] (U : Opens X) : Opens X where
  carrier := {x | ∀ g : G, g • x ∈ U}
  is_open' := TauCeti.isOpen_setOf_forall_smul_mem U.isOpen

variable {G}

@[simp]
theorem mem_invariantCore [SMul G X] [ContinuousSMul G X] {U : Opens X} {x : X} :
    x ∈ U.invariantCore G ↔ ∀ g : G, g • x ∈ U :=
  (Iff.rfl)

theorem coe_invariantCore [SMul G X] [ContinuousSMul G X] (U : Opens X) :
    (U.invariantCore G : Set X) = {x | ∀ g : G, g • x ∈ U} :=
  (rfl)

variable [Monoid G] [MulAction G X] [ContinuousSMul G X] {U : Opens X}

/-- The invariant core of `U` lies in `U`. -/
theorem invariantCore_le (U : Opens X) : U.invariantCore G ≤ U := fun x hx ↦ by
  simpa using hx 1

/-- The invariant core is invariant. -/
theorem smul_mem_invariantCore {x : X} (hx : x ∈ U.invariantCore G) (g : G) :
    g • x ∈ U.invariantCore G := fun h ↦ by
  simpa [mul_smul] using hx (h * g)

/-- Every invariant subset of `U` lies in the invariant core of `U`. -/
theorem subset_invariantCore {s : Set X} (hs : ∀ g : G, ∀ x ∈ s, g • x ∈ s) (hsU : s ⊆ U) :
    s ⊆ U.invariantCore G := fun x hx g ↦ hsU (hs g x hx)

/-- An invariant open set is its own invariant core. -/
theorem invariantCore_eq_self (hU : ∀ g : G, ∀ x ∈ U, g • x ∈ U) : U.invariantCore G = U :=
  le_antisymm (invariantCore_le U) (subset_invariantCore hU le_rfl)

end Core

section Action

variable {G X : Type*} [Monoid G] [MulAction G X] [TopologicalSpace X] {U : Opens X}

/-- The action of a monoid `G` on an open set `U` that `G` maps into itself, by the action on
`X`. -/
abbrev mulActionOfForallSMulMem (hU : ∀ g : G, ∀ x ∈ U, g • x ∈ U) : MulAction G U where
  smul g x := ⟨g • (x : X), hU g x x.property⟩
  one_smul x := Subtype.ext (one_smul G (x : X))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : X))

theorem coe_smul_mulActionOfForallSMulMem (hU : ∀ g : G, ∀ x ∈ U, g • x ∈ U) (g : G) (x : U) :
    letI := mulActionOfForallSMulMem hU
    ((g • x : U) : X) = g • (x : X) :=
  (rfl)

variable [TopologicalSpace G] [CompactSpace G] [ContinuousSMul G X]

/-- The invariant core of an open set carries the restricted action. -/
instance : MulAction G (U.invariantCore G) :=
  mulActionOfForallSMulMem fun _ _ hx ↦ smul_mem_invariantCore hx _

@[simp]
theorem coe_smul_invariantCore (g : G) (x : U.invariantCore G) :
    ((g • x : U.invariantCore G) : X) = g • (x : X) :=
  (rfl)

end Action

end TopologicalSpace.Opens

end
