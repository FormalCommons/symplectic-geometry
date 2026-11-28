/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Normed.Algebra.CayleyChart

/-!
# The derivative of the inverse Cayley transform

In a normed algebra `R` over a nontrivially normed field with summable geometric series, for
instance the continuous endomorphisms of a Banach space, the map `x ↦ A (1 + x) (1 - x)⁻¹` is
differentiable at every `C` with `1 - C` invertible, with derivative
`Ẋ ↦ 2 A (1 - C)⁻¹ Ẋ (1 - C)⁻¹`. With `A` a complex structure `J₀`, this map is the inverse
Cayley transform at `J₀`, and this computes its differential.

The map is `x ↦ A * cayleyCoord 1 (-x)`, so the result follows by the chain rule from Tau Ceti's
`TauCeti.hasFDerivAt_cayleyCoord_one`, the derivative of the Cayley coordinate at the base
point `1`.

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
  have h := (ContinuousLinearMap.mul 𝕜 R A).hasFDerivAt.comp C
    ((TauCeti.hasFDerivAt_cayleyCoord_one (𝕜 := 𝕜) (x := -C)
      (by rwa [← sub_eq_add_neg])).comp C (hasFDerivAt_id C).neg)
  refine (h.congr_of_eventuallyEq (.of_forall fun x => ?_)).congr_fderiv ?_
  · simp only [Function.comp_apply, mul_apply', TauCeti.cayleyCoord_def, sub_neg_eq_add,
      ← sub_eq_add_neg, mul_assoc]
  · ext X
    simp only [comp_apply, mul_apply', neg_apply, smul_apply, mulLeftRight_apply, id_apply,
      ← sub_eq_add_neg, neg_mul, mul_neg, neg_smul, smul_neg, neg_neg, mul_smul_comm, mul_assoc]

end SymplecticGeometry

end
