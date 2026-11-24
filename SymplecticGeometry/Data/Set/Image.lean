/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Set.Image

/-!
# Ranges of composites

Supplements to `Mathlib/Data/Set/Image.lean`.

## Main results

* `Set.range_comp_eq_range_inter_of_range_eq_preimage`: if `range c = f ⁻¹' t`, then
  `range (f ∘ c) = range f ∩ t`.
-/

public section

namespace Set

/-- If the range of `c` is the preimage of `t` under `f`, then the range of `f ∘ c` is the part of
`t` in the range of `f`. -/
theorem range_comp_eq_range_inter_of_range_eq_preimage {α β γ : Type*} {f : β → γ}
    {c : α → β} {t : Set γ} (h : range c = f ⁻¹' t) : range (f ∘ c) = range f ∩ t := by
  rw [range_comp, h, image_preimage_eq_range_inter]

end Set

end
