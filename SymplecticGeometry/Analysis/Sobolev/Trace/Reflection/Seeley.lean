/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Reflection.Seeley
import SymplecticGeometry.Analysis.Sobolev.Trace.Reflection.HalfSpace

/-!
# Seeley's moment identities as sums

Facts about Tau Ceti's Seeley coefficients `TauCeti.HalfSpaceExtension.seeleyCoeff`, stated with
`HasSum`, so that they need no completeness of the target space.

* `hasSum_seeleyCoeff_mul_neg_pow`: the moment identities `∑ₖ aₖ (-2 ^ k) ^ n = 1`, combining
  Tau Ceti's `summable_seeleyCoeff_mul_neg_pow` and `tsum_seeleyCoeff_mul_neg_pow`.
* `hasSum_seeleyCoeff_smul_compContinuousLinearMap_timeScale`: a continuous multilinear map `A`
  on `ℝ × E` is the sum of the `aₖ A (timeScale (-2 ^ k) ·, …)`. Its proof follows Tau Ceti's
  `tsum_seeleyCoeff_smul_compContinuousLinearMap_timeScale`, which assumes the target complete.
* `hasSum_seeleyCoeff_smul_timeScale_of_fst_eq_zero` and
  `hasSum_seeleyCoeff_smul_compContinuousLinearMap_timeScale_of_fst_eq_zero`: at a point of
  time `0`, Seeley's sums of the values of a function, and of the dilated coefficients of a
  formal multilinear series, give back the value and the coefficient there.

## References

* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

public section

namespace TauCeti.HalfSpaceExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Seeley's moment identities as sums: `∑ₖ aₖ (-2 ^ k) ^ n` sums to `1` for every `n`. -/
theorem hasSum_seeleyCoeff_mul_neg_pow (n : ℕ) :
    HasSum (fun k ↦ seeleyCoeff k * (-(2 : ℝ) ^ k) ^ n) 1 :=
  (summable_seeleyCoeff_mul_neg_pow n).hasSum_iff.mpr (tsum_seeleyCoeff_mul_neg_pow n)

/-- The moment identities for multilinear maps: `∑ₖ aₖ A (timeScale (-2 ^ k) ·, …)` sums to
`A`. Unlike Tau Ceti's `tsum_seeleyCoeff_smul_compContinuousLinearMap_timeScale`, this needs no
completeness of `F`. -/
theorem hasSum_seeleyCoeff_smul_compContinuousLinearMap_timeScale {m : ℕ}
    (A : (ℝ × E) [×m]→L[ℝ] F) :
    HasSum (fun k ↦ seeleyCoeff k •
      A.compContinuousLinearMap (fun _ ↦ timeScale (E := E) (-2 ^ k))) A := by
  classical
  let B : Finset (Fin m) → (ℝ × E) [×m]→L[ℝ] F := fun s ↦ A.compContinuousLinearMap fun i ↦
    if i ∈ s then (ContinuousLinearMap.inl ℝ ℝ E).comp (ContinuousLinearMap.fst ℝ ℝ E)
    else (ContinuousLinearMap.inr ℝ ℝ E).comp (ContinuousLinearMap.snd ℝ ℝ E)
  have hB (a : ℝ) :
      A.compContinuousLinearMap (fun _ ↦ timeScale (E := E) a) = ∑ s, a ^ s.card • B s := by
    ext v
    simp only [B, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      sum_apply, smul_apply,
      map_timeScale_eq_sum_pow_card_smul]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    congr 2
    funext i
    by_cases hi : i ∈ s <;> simp [hi]
  have hA : A = ∑ s, B s := by
    have h1 : A.compContinuousLinearMap (fun _ ↦ timeScale (E := E) 1) = A := by
      ext v
      simp
    simpa using ((hB 1).symm.trans h1).symm
  have hsum : HasSum (fun k ↦ ∑ s, (seeleyCoeff k * (-2 ^ k) ^ s.card) • B s) (∑ s, B s) :=
    hasSum_sum fun s _ ↦ by
      simpa using (hasSum_seeleyCoeff_mul_neg_pow s.card).smul_const (B s)
  rw [← hA] at hsum
  convert hsum using 2 with k
  rw [hB, Finset.smul_sum]
  simp_rw [smul_smul]

/-- At time `0`, Seeley's sum `∑ₖ aₖ h (timeScale (-2 ^ k) z)` sums to `h z`. -/
theorem hasSum_seeleyCoeff_smul_timeScale_of_fst_eq_zero (h : ℝ × E → F) {z : ℝ × E}
    (hz : z.1 = 0) : HasSum (fun k ↦ seeleyCoeff k • h (timeScale (-2 ^ k) z)) (h z) := by
  simp_rw [timeScale_of_fst_eq_zero hz]
  simpa using (hasSum_seeleyCoeff_mul_neg_pow 0).smul_const (h z)

/-- At time `0`, Seeley's sum of the dilated coefficients of order `m` of a series `p` sums to
`p z m`. -/
theorem hasSum_seeleyCoeff_smul_compContinuousLinearMap_timeScale_of_fst_eq_zero
    (p : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) F) {z : ℝ × E} (hz : z.1 = 0) (m : ℕ) :
    HasSum (fun k ↦ seeleyCoeff k •
      (p (timeScale (-2 ^ k) z) m).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k))
      (p z m) := by
  simp_rw [timeScale_of_fst_eq_zero hz]
  exact hasSum_seeleyCoeff_smul_compContinuousLinearMap_timeScale (p z m)

end TauCeti.HalfSpaceExtension

end
