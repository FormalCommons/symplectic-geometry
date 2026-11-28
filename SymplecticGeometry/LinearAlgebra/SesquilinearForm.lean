/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Alternating sesquilinear maps

An alternating sesquilinear map `B` satisfies `B y x = -B x y`, so `B - Bᵀ` is twice `B`. This
identity holds with no hypothesis on the scalars: the factor `2` is a natural number. Where `2`
is invertible, it says that the skew part `½ (B - Bᵀ)` of an alternating form is the form itself.

## Main results

* `LinearMap.IsAlt.sub_flip_eq_two_smul`: for an alternating `B`, `B - B.flip = 2 • B`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.5
-/

public section

namespace LinearMap

variable {R R₁ M M₁ : Type*} [CommSemiring R] [AddCommGroup M] [Module R M] [CommSemiring R₁]
  [AddCommMonoid M₁] [Module R₁ M₁] {I : R₁ →+* R} {B : M₁ →ₛₗ[I] M₁ →ₛₗ[I] M}

/-- An alternating sesquilinear map minus its transpose is twice the map. -/
theorem IsAlt.sub_flip_eq_two_smul (H : B.IsAlt) : B - B.flip = 2 • B := by
  ext x y
  simp [two_nsmul, ← H.neg x y]

end LinearMap

end
