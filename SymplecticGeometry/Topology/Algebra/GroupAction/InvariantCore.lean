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

Let a compact space `G` act jointly continuously on a space `X`, and let `U` be an open set. Tau
Ceti bundles the points of `X` whose whole orbit lies in `U` as an open set,
`TopologicalSpace.Opens.invariantCore G U`, and lets a monoid act on it. This file adds the
description of its underlying set, the inclusion of a set that every `g • ·` maps into `U`, and
the restricted action on any open set that a monoid `G` maps into itself,
`TopologicalSpace.Opens.mulActionOfForallSMulMem`.

The restricted action `mulActionOfForallSMulMem` is Tau Ceti's
`ContRepresentation.mulActionOpens` for an arbitrary monoid action in place of a continuous linear
representation, with the same proofs of the action laws.

## Main definitions

* `TopologicalSpace.Opens.mulActionOfForallSMulMem`: the action of `G` on an invariant open set.

## Main results

* `TopologicalSpace.Opens.subset_invariantCore`: a set that every `g • ·` maps into `U`, such as an
  invariant subset of `U`, lies in the invariant core.
-/

public section

namespace TopologicalSpace.Opens

section Core

variable {G : Type*} {X : Type*} [TopologicalSpace G] [CompactSpace G] [TopologicalSpace X]
  [SMul G X] [ContinuousSMul G X]

theorem coe_invariantCore (U : Opens X) :
    (U.invariantCore G : Set X) = {x | ∀ g : G, g • x ∈ U} :=
  Set.ext fun _ ↦ mem_invariantCore

/-- A set lies in the invariant core of `U` once every `g • ·` maps it into `U`. -/
theorem subset_invariantCore {U : Opens X} {s : Set X} (hs : ∀ g : G, ∀ x ∈ s, g • x ∈ U) :
    s ⊆ U.invariantCore G := fun x hx ↦ mem_invariantCore.2 fun g ↦ hs g x hx

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

end Action

end TopologicalSpace.Opens

end
