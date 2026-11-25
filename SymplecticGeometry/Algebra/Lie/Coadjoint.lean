/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint

/-!
# The coadjoint stabilizer of a linear functional

For a linear functional `ν` on a Lie algebra `L`, this file characterizes the coadjoint stabilizer
`L_ν = lieAnnihilator R L ν` by the bracket: `ξ ∈ L_ν` exactly when `ν ⁅ξ, η⁆ = 0` for every `η`,
or equivalently when `ν ⁅η, ξ⁆ = 0` for every `η`. Both follow from Tau Ceti's
`Module.Dual.ker_kirillovForm`.

## Main results

* `Module.Dual.mem_lieAnnihilator_iff`: `ξ ∈ L_ν ↔ ∀ η, ν ⁅ξ, η⁆ = 0`.
* `Module.Dual.mem_lieAnnihilator_iff'`: `ξ ∈ L_ν ↔ ∀ η, ν ⁅η, ξ⁆ = 0`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
-/

public section

open TauCeti

namespace Module.Dual

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (ν : Dual R L)

/-- An element `ξ` lies in the coadjoint stabilizer of `ν` exactly when `ν ⁅ξ, η⁆ = 0` for every
`η`. -/
theorem mem_lieAnnihilator_iff {ξ : L} :
    ξ ∈ (lieAnnihilator R L ν).toSubmodule ↔ ∀ η : L, ν ⁅ξ, η⁆ = 0 := by
  rw [← ν.ker_kirillovForm, LinearMap.mem_ker, LinearMap.ext_iff]
  simp

/-- An element `ξ` lies in the coadjoint stabilizer of `ν` exactly when `ν ⁅η, ξ⁆ = 0` for every
`η`. -/
theorem mem_lieAnnihilator_iff' {ξ : L} :
    ξ ∈ (lieAnnihilator R L ν).toSubmodule ↔ ∀ η : L, ν ⁅η, ξ⁆ = 0 := by
  rw [ν.mem_lieAnnihilator_iff]
  refine forall_congr' fun η ↦ ?_
  rw [← lie_skew, map_neg, neg_eq_zero]

end Module.Dual

end
