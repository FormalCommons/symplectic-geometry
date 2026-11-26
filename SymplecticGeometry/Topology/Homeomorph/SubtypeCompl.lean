/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Set.Subset
public import Mathlib.Topology.Homeomorph.Lemmas
import SymplecticGeometry.Topology.Homeomorph.HomeomorphImage

/-!
# The complement of a set inside a subspace

For a subspace `t` of a topological space `X` and a set `D` of points of `t`, the complement of
`D` in `t`, a subspace of the subspace `t`, is homeomorphic to the subspace `t \ D` of `X`
(`Homeomorph.Set.subtypeCompl`). The homeomorphism sends each point to itself, as the coercion
lemmas `Homeomorph.Set.subtypeCompl_apply_coe` and
`Homeomorph.Set.coe_coe_subtypeCompl_symm_apply` say. For `D = {a}`, it identifies the space
obtained by removing `a` from `t` with `t \ {a}`.

## Main definitions

* `Homeomorph.Set.subtypeCompl`: for `D : Set t`, the homeomorphism `Dᶜ ≃ₜ t \ D`.
-/

public section

open Set Topology

namespace Homeomorph.Set

variable {X : Type*} [TopologicalSpace X] {t : Set X}

/-- For a subspace `t` of `X` and `D : Set t`, the complement of `D` in `t` is homeomorphic to
the subspace `t \ D` of `X`, by the map that sends a point to itself. -/
noncomputable def subtypeCompl (D : Set t) : (Dᶜ : Set t) ≃ₜ ↥(t \ Subtype.val '' D) :=
  (IsEmbedding.subtypeVal.homeomorphImage Dᶜ).trans (Homeomorph.setCongr image_val_compl)

@[simp]
theorem subtypeCompl_apply_coe (D : Set t) (z : (Dᶜ : Set t)) :
    (subtypeCompl D z : X) = z := by
  simp [subtypeCompl, Homeomorph.setCongr]

@[simp]
theorem coe_coe_subtypeCompl_symm_apply (D : Set t) (z : ↥(t \ Subtype.val '' D)) :
    (((subtypeCompl D).symm z : t) : X) = z := by
  simp [subtypeCompl, Homeomorph.setCongr, IsEmbedding.apply_homeomorphImage_symm_apply]

end Homeomorph.Set

end
