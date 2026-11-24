/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.ContinuousMap.CodRestrict

/-!
# Corestriction of bundled continuous maps

A complement to Tau Ceti's `TauCeti/Topology/ContinuousMap/CodRestrict.lean`, which defines
`ContinuousMap.codRestrict`: a continuous map `f : C(α, β)` whose values lie in a set
`s : Set β`, seen as a continuous map `C(α, s)`.

## Main results

* `ContinuousMap.coe_codRestrict` and `ContinuousMap.codRestrict_apply`: the corestriction of
  `f` is `Set.codRestrict` of `f`, as a function and at each point.
* `ContinuousMap.comp_codRestrict`: precomposing a corestriction with `g` gives the
  corestriction of `f.comp g`.
-/

public section

namespace ContinuousMap

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
  (f : C(α, β)) (s : Set β) (h : ∀ x, f x ∈ s)

theorem codRestrict_apply (x : α) : f.codRestrict s h x = ⟨f x, h x⟩ :=
  Subtype.ext (coe_codRestrict_apply f s h x)

theorem coe_codRestrict : ⇑(f.codRestrict s h) = s.codRestrict f h :=
  funext (codRestrict_apply f s h)

/-- Precomposing the corestriction of `f` with `g` gives the corestriction of `f.comp g`. -/
@[simp]
theorem comp_codRestrict {γ : Type*} [TopologicalSpace γ] (g : C(γ, α)) :
    (f.codRestrict s h).comp g = (f.comp g).codRestrict s (fun x ↦ h (g x)) :=
  ext fun x ↦ Subtype.ext (by simp)

end ContinuousMap

end
