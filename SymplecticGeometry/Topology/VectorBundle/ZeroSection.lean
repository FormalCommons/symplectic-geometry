/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.ZeroSection

/-!
# The complement of a point of the zero section

Set identities relating Tau Ceti's set of nonzero vectors `TauCeti.zeroSectionCompl F E` of a
bundle `E → B` to the complement of a single point `0_b` of the zero section. They use only that
the fibres have a zero: no topology or linear structure.

## Main results

* `TauCeti.zeroSectionCompl_union_compl_preimage_singleton`: the nonzero vectors together with
  the points off the fibre over `b` form the complement of `0_b`.
* `TauCeti.zeroSectionCompl_subset_compl_singleton_zeroSection`: the nonzero vectors lie off
  `0_b`.
-/

public section

open Bundle Set

namespace TauCeti

variable {B : Type*} (F : Type*) (E : B → Type*) [∀ b, Zero (E b)]

variable {F E} in
/-- The points of the total space that are nonzero vectors or lie off the fibre over `b` are
the points other than the zero vector `0_b`. -/
theorem zeroSectionCompl_union_compl_preimage_singleton (b : B) :
    zeroSectionCompl F E ∪ (π F E ⁻¹' {b})ᶜ = {zeroSection F E b}ᶜ := by
  ext ⟨b', v⟩
  simp only [mem_union, mem_zeroSectionCompl, mem_compl_iff, mem_preimage, mem_singleton_iff,
    zeroSection, TotalSpace.mk.injEq, not_and]
  constructor
  · rintro (hv | hb) rfl
    exacts [fun h ↦ hv (eq_of_heq h), (hb rfl).elim]
  · intro h
    by_cases hb : b' = b
    · subst hb
      exact Or.inl fun hv ↦ h rfl (heq_of_eq hv)
    · exact Or.inr hb

/-- The nonzero vectors of a bundle lie in the complement of the point `0_b` of the zero
section. -/
theorem zeroSectionCompl_subset_compl_singleton_zeroSection (b : B) :
    zeroSectionCompl F E ⊆ {zeroSection F E b}ᶜ := by
  rw [zeroSectionCompl_eq_compl_range]
  exact compl_subset_compl.2 (singleton_subset_iff.2 (mem_range_self b))

end TauCeti

end
