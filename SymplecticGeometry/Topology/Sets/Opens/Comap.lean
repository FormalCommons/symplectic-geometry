/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Sets.Opens

/-!
# Open sets of an open subspace

For open sets `U ≤ W` of `X`, the set `U` read as an open set of the subspace `W` (its preimage
under the inclusion `W → X`) is mapped back onto `U` by the inclusion of `W`
(`TopologicalSpace.Opens.range_val_comp_val_comap`).
-/

public section

namespace TopologicalSpace.Opens

variable {X : Type*} [TopologicalSpace X]

/-- For open sets `U ≤ W` of `X`, the composite of the inclusions `U ∩ W → W → X`, where `U ∩ W`
is `U` read as an open set of `W`, has range `U`. -/
theorem range_val_comp_val_comap {U W : Opens X} (hUW : U ≤ W) :
    Set.range ((Subtype.val : W → X) ∘
      (Subtype.val : Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ U → W)) = U := by
  ext x
  simpa using fun hx ↦ hUW hx

end TopologicalSpace.Opens

end
