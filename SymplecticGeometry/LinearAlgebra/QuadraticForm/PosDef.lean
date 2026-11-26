/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.LinearAlgebra.QuadraticForm.PosDef

/-!
# Sublevel sets of positive definite quadratic forms

For a quadratic form `Q` on a real module, the set `{v | Q v ≤ 1}` is the ellipsoid of `Q` when
`Q` is positive definite. This file shows that this set determines a positive definite form, and
computes its image under a linear equivalence.

## Main results

* `QuadraticMap.PosDef.eq_of_setOfPred_le_one_eq`: if `Q` is positive definite and
  `{v | Q v ≤ 1} = {v | Q' v ≤ 1}`, then `Q = Q'`.
* `QuadraticMap.image_setOfPred_le_one`: `e '' {v | Q v ≤ 1} = {w | Q (e.symm w) ≤ 1}`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.4
-/

public section

namespace QuadraticMap

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- A positive definite quadratic form is determined by its sublevel set `{v | Q v ≤ 1}`: any
quadratic form `Q'` with the same sublevel set equals `Q`. Only `Q` is assumed positive
definite. -/
theorem PosDef.eq_of_setOfPred_le_one_eq {Q Q' : QuadraticForm ℝ M} (hQ : Q.PosDef)
    (h : {v | Q v ≤ 1} = {v | Q' v ≤ 1}) : Q = Q' := by
  -- On the ray through `v`, the condition `Q (√u • v) ≤ 1` reads `u * Q v ≤ 1`.
  have key (v : M) (u : ℝ) (hu : 0 ≤ u) : u * Q v ≤ 1 ↔ u * Q' v ≤ 1 := by
    have hv := Set.ext_iff.1 h (Real.sqrt u • v)
    simpa [QuadraticMap.map_smul, Real.mul_self_sqrt hu] using hv
  ext v
  by_cases hv : v = 0
  · simp [hv]
  have hpos : 0 < Q v := hQ v hv
  have hle : Q' v ≤ Q v := by
    have := (key v (Q v)⁻¹ (inv_nonneg.2 hpos.le)).1 (by rw [inv_mul_cancel₀ hpos.ne'])
    rwa [inv_mul_le_iff₀ hpos, mul_one] at this
  refine le_antisymm ?_ hle
  rcases le_or_gt (Q' v) 0 with h0 | h0
  · have := (key v (2 / Q v) (by positivity)).2
      (by nlinarith [show 0 ≤ 2 / Q v by positivity])
    rw [div_mul_cancel₀ _ hpos.ne'] at this
    norm_num at this
  · have := (key v (Q' v)⁻¹ (inv_nonneg.2 h0.le)).2 (by rw [inv_mul_cancel₀ h0.ne'])
    rwa [inv_mul_le_iff₀ h0, mul_one] at this

end QuadraticMap

namespace QuadraticMap

variable {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] [LE N] [One N]

/-- The image of the sublevel set `{v | Q v ≤ 1}` under a linear equivalence `e` is the sublevel
set of the transported form `Q.comp e.symm`. -/
theorem image_setOfPred_le_one (Q : QuadraticMap R M N) (e : M ≃ₗ[R] P) :
    e '' {v | Q v ≤ 1} = {w | Q.comp (e.symm : P →ₗ[R] M) w ≤ 1} := by
  rw [e.image_eq_preimage_symm]
  rfl

end QuadraticMap

end
