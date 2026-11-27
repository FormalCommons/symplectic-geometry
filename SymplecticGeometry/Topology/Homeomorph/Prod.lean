/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Defs
import SymplecticGeometry.Logic.Equiv.Prod

/-!
# Homeomorphisms of a product given fibre by fibre

A homeomorphism `Φ` of `X × F` of the form `Φ q = (q.1, g q)`, such as
`Φ (p, v) = (p, χ p v)` for a family `χ` of maps of `F`, has an inverse that preserves the first
coordinate (`Homeomorph.fst_symm_apply_of_apply_eq_prodMk`). This is
`Equiv.fst_symm_apply_of_forall_fst_apply` for `Φ`, with the inverse written as the
homeomorphism `Φ.symm` rather than as `Φ.toEquiv.symm`, so that it can be passed where a
hypothesis on `Φ.symm` is expected.
-/

public section

namespace Homeomorph

/-- A homeomorphism of `X × F` of the form `q ↦ (q.1, g q)` has an inverse that preserves the
first coordinate. -/
theorem fst_symm_apply_of_apply_eq_prodMk {X F : Type*} [TopologicalSpace X] [TopologicalSpace F]
    {Φ : X × F ≃ₜ X × F} {g : X × F → F} (hg : ∀ q, Φ q = (q.1, g q)) (q : X × F) :
    (Φ.symm q).1 = q.1 := by
  rw [← coe_symm_toEquiv]
  exact Equiv.fst_symm_apply_of_forall_fst_apply (by simp [hg]) q

end Homeomorph

end
