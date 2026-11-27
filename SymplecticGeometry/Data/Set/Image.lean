/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Prod

/-!
# Ranges and images of composites

Supplements to `Mathlib/Data/Set/Image.lean`.

## Main results

* `Set.range_comp_eq_range_inter_of_range_eq_preimage`: if `range c = f ⁻¹' t`, then
  `range (f ∘ c) = range f ∩ t`.
* `Set.image_inter_image_eq_prod_singleton`: if `e (f s) = (g s, b)` whenever `f s ∈ S`, then
  `e` maps `S ∩ f '' J` onto `(g '' (J ∩ f ⁻¹' S)) ×ˢ {b}`.
-/

public section

namespace Set

/-- If the range of `c` is the preimage of `t` under `f`, then the range of `f ∘ c` is the part of
`t` in the range of `f`. -/
theorem range_comp_eq_range_inter_of_range_eq_preimage {α β γ : Type*} {f : β → γ}
    {c : α → β} {t : Set γ} (h : range c = f ⁻¹' t) : range (f ∘ c) = range f ∩ t := by
  rw [range_comp, h, image_preimage_eq_range_inter]

/-- If a map `e : X → A × B` sends `f s` to `(g s, b)` whenever `f s` lies in `S`, then for every
`J` it maps the part of `f '' J` in `S` onto `(g '' (J ∩ f ⁻¹' S)) ×ˢ {b}`. -/
theorem image_inter_image_eq_prod_singleton {X N A B : Type*} {e : X → A × B} {S : Set X}
    {f : N → X} {g : N → A} {b : B} (hg : ∀ s ∈ f ⁻¹' S, e (f s) = (g s, b)) (J : Set N) :
    e '' (S ∩ f '' J) = (g '' (J ∩ f ⁻¹' S)) ×ˢ {b} := by
  rw [inter_comm, ← image_inter_preimage, image_image, prod_singleton, image_image]
  exact image_congr fun s hs => hg s hs.2

end Set

end
