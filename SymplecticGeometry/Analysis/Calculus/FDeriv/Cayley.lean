/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.NoncommRing
import TauCeti.Analysis.Calculus.FDeriv.Mul

/-!
# The derivative of the inverse Cayley transform

In a normed algebra `R` over a nontrivially normed field with summable geometric series, for
instance the continuous endomorphisms of a Banach space, the map `x ↦ A (1 + x) (1 - x)⁻¹` is
differentiable at every `C` with `1 - C` invertible, with derivative
`Ẋ ↦ 2 A (1 - C)⁻¹ Ẋ (1 - C)⁻¹`. With `A` a complex structure `J₀`, this map is the inverse
Cayley transform at `J₀`, and this computes its differential.

The proof is that of Tau Ceti's `TauCeti.hasFDerivAt_cayleyParam`, which differentiates
the other Cayley parametrization `η ↦ (1 + η)⁻¹ j (1 + η)`: the product rule, and Tau Ceti's
`HasFDerivAt.ringInverse` for the inverse.

## Main results

* `SymplecticGeometry.hasFDerivAt_mul_one_add_ringInverse`: the derivative of
  `x ↦ A (1 + x) (1 - x)⁻¹`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], §2.5 (the Cayley transform).
-/

public section

open ContinuousLinearMap

namespace SymplecticGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {R : Type*} [NormedRing R]
  [HasSummableGeomSeries R] [NormedAlgebra 𝕜 R]

/-- At a point `C` with `1 - C` invertible, the map `x ↦ A (1 + x) (1 - x)⁻¹` has derivative
`Ẋ ↦ 2 A (1 - C)⁻¹ Ẋ (1 - C)⁻¹`. -/
theorem hasFDerivAt_mul_one_add_ringInverse (A : R) {C : R} (hC : IsUnit (1 - C)) :
    HasFDerivAt (fun x : R => A * (1 + x) * Ring.inverse (1 - x))
      ((2 : 𝕜) • mulLeftRight 𝕜 R (A * Ring.inverse (1 - C)) (Ring.inverse (1 - C))) C := by
  obtain ⟨u, hu⟩ := hC
  have hR : (1 - C) * Ring.inverse (1 - C) = 1 := by
    rw [← hu, Ring.inverse_unit, Units.mul_inv]
  have hinv : HasFDerivAt (fun x : R => Ring.inverse (1 - x)) _ C :=
    ((hasFDerivAt_id (𝕜 := 𝕜) C).const_sub 1).ringInverse ⟨u, hu⟩
  have hmul : HasFDerivAt (fun x : R => A * (1 + x))
      ((ContinuousLinearMap.mul 𝕜 R A).comp (ContinuousLinearMap.id 𝕜 R)) C :=
    (ContinuousLinearMap.mul 𝕜 R A).hasFDerivAt.comp C ((hasFDerivAt_id C).const_add 1)
  refine (hmul.mul' hinv).congr_fderiv (ContinuousLinearMap.ext fun X => ?_)
  have hX : X * Ring.inverse (1 - C) =
      (1 - C) * Ring.inverse (1 - C) * X * Ring.inverse (1 - C) := by
    rw [hR, one_mul]
  simp only [add_apply, smul_apply, comp_apply, neg_apply, mulLeftRight_apply, id_apply, id_eq,
    smul_eq_mul, op_smul_eq_mul, neg_mul, mul_neg, neg_neg, two_smul, mul_apply']
  rw [mul_assoc A X, hX]
  noncomm_ring

end SymplecticGeometry

end
