/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quotients by preimages along a surjection

A surjective homomorphism `f : G →* H` identifies the quotient of `G` by the preimage of a normal
subgroup `M` of `H` with `H ⧸ M`. This is the first isomorphism theorem for the composite of `f`
with the quotient map of `M`, whose kernel is `M.comap f`.

## Main results

* `QuotientGroup.quotientComapMulEquivOfSurjective`: `G ⧸ M.comap f ≃* H ⧸ M` for a surjective
  `f : G →* H`.
* `QuotientGroup.quotientComapMulEquivOfSurjective_mk`: it sends the class of `g` to the class of
  `f g`.
-/

public section

namespace QuotientGroup

variable {G H : Type*} [Group G] [Group H]

/-- A surjective homomorphism `f : G →* H` induces `G ⧸ M.comap f ≃* H ⧸ M` for every normal
subgroup `M` of `H`. -/
noncomputable def quotientComapMulEquivOfSurjective (f : G →* H) (hf : Function.Surjective f)
    (M : Subgroup H) [M.Normal] : G ⧸ M.comap f ≃* H ⧸ M :=
  (quotientMulEquivOfEq (by rw [← MonoidHom.comap_ker, ker_mk'])).trans
    (quotientKerEquivOfSurjective ((mk' M).comp f) ((mk'_surjective M).comp hf))

/-- `QuotientGroup.quotientComapMulEquivOfSurjective f hf M` sends the class of `g` to the class
of `f g`. -/
@[simp]
theorem quotientComapMulEquivOfSurjective_mk (f : G →* H) (hf : Function.Surjective f)
    (M : Subgroup H) [M.Normal] (g : G) :
    quotientComapMulEquivOfSurjective f hf M (g : G ⧸ M.comap f) = (f g : H ⧸ M) :=
  (rfl)

end QuotientGroup

end
