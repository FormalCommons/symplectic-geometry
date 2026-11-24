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

The invariant core and its API follow Tau Ceti's `Submodule.invariantCore`, carried over from
submodules to open sets, and the proofs of `invariantCore_le`, `smul_mem_invariantCore`,
`le_invariantCore_iff`, `invariantCore_mono` and `invariantCore_eq_self_iff` take the steps of
the lemmas of the same names there. The restricted action `mulActionOfForallSMulMem` is Tau Ceti's
`ContRepresentation.mulActionOpens` for an arbitrary monoid action in place of a continuous linear
representation, with the same proofs of the action laws.

## Main definitions

* `TopologicalSpace.Opens.invariantCore G U`: the points whose orbit lies in `U`, as an open set.
* `TopologicalSpace.Opens.mulActionOfForallSMulMem`: the action of `G` on an invariant open set.

## Main results

* `TopologicalSpace.Opens.subset_invariantCore`: a set that every `g • ·` maps into `U`, such as an
  invariant subset of `U`, lies in the invariant core.
* `TopologicalSpace.Opens.le_invariantCore_iff`: an open set lies in the invariant core of `U`
  exactly when every `g • ·` maps it into `U`.
* `TopologicalSpace.Opens.invariantCore_le`: the invariant core lies in `U`.
* `TopologicalSpace.Opens.smul_mem_invariantCore`: the invariant core is invariant.
* `TopologicalSpace.Opens.invariantCore_eq_self_iff`: `U` is its own invariant core exactly when
  it is invariant.
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

section SMul

variable [SMul G X] [ContinuousSMul G X] {U : Opens X}

/-- A set lies in the invariant core of `U` once every `g • ·` maps it into `U`. -/
theorem subset_invariantCore {s : Set X} (hs : ∀ g : G, ∀ x ∈ s, g • x ∈ U) :
    s ⊆ U.invariantCore G := fun x hx g ↦ hs g x hx

/-- An open set lies in the invariant core of `U` exactly when every `g • ·` maps it into `U`. -/
theorem le_invariantCore_iff {V : Opens X} :
    V ≤ U.invariantCore G ↔ ∀ g : G, ∀ x ∈ V, g • x ∈ U :=
  ⟨fun h g _ hx ↦ mem_invariantCore.1 (h hx) g, subset_invariantCore⟩

variable (G) in
/-- Taking invariant cores preserves inclusions of open sets. -/
theorem invariantCore_mono : Monotone (invariantCore G : Opens X → Opens X) :=
  fun _ _ h ↦ le_invariantCore_iff.2 fun g _ hx ↦ h (mem_invariantCore.1 hx g)

end SMul

variable [Monoid G] [MulAction G X] [ContinuousSMul G X] {U : Opens X}

/-- The invariant core of `U` lies in `U`. -/
theorem invariantCore_le (U : Opens X) : U.invariantCore G ≤ U := fun x hx ↦ by
  simpa using hx 1

/-- The invariant core is invariant. -/
theorem smul_mem_invariantCore {x : X} (hx : x ∈ U.invariantCore G) (g : G) :
    g • x ∈ U.invariantCore G := fun h ↦ by
  simpa [mul_smul] using hx (h * g)

/-- An open set is its own invariant core exactly when it is invariant. -/
theorem invariantCore_eq_self_iff : U.invariantCore G = U ↔ ∀ g : G, ∀ x ∈ U, g • x ∈ U :=
  (invariantCore_le U).ge_iff_eq.symm.trans le_invariantCore_iff

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
