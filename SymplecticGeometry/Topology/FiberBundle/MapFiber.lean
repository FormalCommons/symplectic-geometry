/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.FiberBundle.MapFiber

/-!
# Fibres of a restricted map

For a map `proj : P → B`, a set `t ⊆ B` and a point `b ∈ t`, the fibre over `b` of the restriction
`t.restrictPreimage proj : proj ⁻¹' t → t` is homeomorphic to the fibre of `proj` over `b`
(`TauCeti.MapFiber.restrictPreimageHomeomorph`): both are the points of `P` that `proj` sends to
`b`.
-/

public section

open Set

namespace TauCeti.MapFiber

variable {P B : Type*} [TopologicalSpace P]

/-- The fibre over `b ∈ t` of the restriction of `proj : P → B` over `t` is homeomorphic to the
fibre of `proj` over `b`, by forgetting that its points lie over `t`. -/
def restrictPreimageHomeomorph (proj : P → B) (t : Set B) (b : t) :
    MapFiber (t.restrictPreimage proj) b ≃ₜ MapFiber proj b where
  toFun z := ⟨z.val.val, congrArg Subtype.val z.property⟩
  invFun z := ⟨⟨z.val, (z.property.symm ▸ b.property : proj z.val ∈ t)⟩, Subtype.ext z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _

@[simp]
theorem coe_restrictPreimageHomeomorph_apply (proj : P → B) (t : Set B) (b : t)
    (z : MapFiber (t.restrictPreimage proj) b) :
    (restrictPreimageHomeomorph proj t b z : P) = z.val.val :=
  (rfl)

@[simp]
theorem coe_coe_restrictPreimageHomeomorph_symm_apply (proj : P → B) (t : Set B) (b : t)
    (z : MapFiber proj b) :
    (((restrictPreimageHomeomorph proj t b).symm z : proj ⁻¹' t) : P) = z.val :=
  (rfl)

end TauCeti.MapFiber

end
