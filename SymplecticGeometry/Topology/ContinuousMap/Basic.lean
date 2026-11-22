/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Corestriction of bundled continuous maps

A complement to Mathlib's `Mathlib/Topology/ContinuousMap/Basic.lean`.

## Main definitions

* `ContinuousMap.codRestrict`: a continuous map `f : C(α, β)` whose values lie in a set
  `s : Set β`, seen as a continuous map `C(α, s)`. It bundles `Set.codRestrict` with
  `Continuous.codRestrict`.

## Main results

* `ContinuousMap.subtypeVal_comp_codRestrict`: followed by the inclusion of `s`, the
  corestriction of `f` is `f`.
* `ContinuousMap.comp_codRestrict`: precomposing a corestriction with `g` gives the
  corestriction of `f.comp g`.

This follows Mathlib's corestrictions of other bundled maps, such as
`BoundedContinuousFunction.codRestrict` and `ContinuousLinearMap.codRestrict`.
-/

public section

namespace ContinuousMap

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The corestriction of a continuous map `f : C(α, β)` to a set `s` that contains all its
values, as a continuous map `C(α, s)`. -/
def codRestrict (f : C(α, β)) (s : Set β) (h : ∀ x, f x ∈ s) : C(α, s) where
  toFun := s.codRestrict f h
  continuous_toFun := f.continuous.codRestrict h

variable (f : C(α, β)) (s : Set β) (h : ∀ x, f x ∈ s)

theorem coe_codRestrict : ⇑(f.codRestrict s h) = s.codRestrict f h :=
  (rfl)

theorem codRestrict_apply (x : α) : f.codRestrict s h x = ⟨f x, h x⟩ :=
  (rfl)

@[simp]
theorem coe_codRestrict_apply (x : α) : (f.codRestrict s h x : β) = f x :=
  (rfl)

/-- Followed by the inclusion of `s`, the corestriction of `f` to `s` is `f`. -/
@[simp]
theorem subtypeVal_comp_codRestrict : (subtypeVal s).comp (f.codRestrict s h) = f :=
  (rfl)

/-- Precomposing the corestriction of `f` with `g` gives the corestriction of `f.comp g`. -/
@[simp]
theorem comp_codRestrict {γ : Type*} [TopologicalSpace γ] (g : C(γ, α)) :
    (f.codRestrict s h).comp g = (f.comp g).codRestrict s (fun x ↦ h (g x)) :=
  (rfl)

end ContinuousMap

end
