/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The jet norm of a function at a point

For a function `f : E → F` between normed spaces over `𝕜`, a point `z` and an order `r`, the
`r`-jet norm `SymplecticGeometry.jetNormAt 𝕜 r f z` is the sum, over the orders `j ≤ r`, of the
norms `‖iteratedFDeriv 𝕜 j f z‖` of the derivatives of `f` at `z`.

## Main results

* `SymplecticGeometry.jetNormAt_nonneg` and `SymplecticGeometry.jetNormAt_mono`: the jet norm is
  nonnegative and monotone in the order.
* `SymplecticGeometry.jetNormAt_zero`: the jet norm of order `0` is `‖f z‖`.
* `SymplecticGeometry.jetNormAt_add_le`: the triangle inequality, for functions that are `C^r`
  at `z`, from Mathlib's `iteratedFDeriv_add_apply`.
* `SymplecticGeometry.jetNormAt_smul`: the jet norm of `c • f` is `‖c‖` times that of `f`, for every
  `f`, from Mathlib's `ContinuousLinearEquiv.iteratedFDeriv_comp_left`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4
-/

public section

namespace SymplecticGeometry

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The **`r`-jet norm** of `f` at `z`: the sum, over the orders `j ≤ r`, of the norms of the
`j`-th derivatives `iteratedFDeriv 𝕜 j f z`. -/
noncomputable def jetNormAt (r : ℕ) (f : E → F) (z : E) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), ‖iteratedFDeriv 𝕜 j f z‖

theorem jetNormAt_def (r : ℕ) (f : E → F) (z : E) :
    jetNormAt 𝕜 r f z = ∑ j ∈ Finset.range (r + 1), ‖iteratedFDeriv 𝕜 j f z‖ :=
  (rfl)

variable {𝕜}

theorem jetNormAt_nonneg (r : ℕ) (f : E → F) (z : E) : 0 ≤ jetNormAt 𝕜 r f z := by
  rw [jetNormAt_def]
  positivity

/-- The jet norm grows with the order. -/
theorem jetNormAt_mono (f : E → F) (z : E) : Monotone fun r ↦ jetNormAt 𝕜 r f z :=
  fun r r' hr ↦ Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (by omega)) fun _ _ _ ↦ norm_nonneg _

/-- The jet norm of order `0` is the norm of the value. -/
@[simp]
theorem jetNormAt_zero (f : E → F) (z : E) : jetNormAt 𝕜 0 f z = ‖f z‖ := by
  rw [jetNormAt_def, Finset.sum_range_one, norm_iteratedFDeriv_zero]

/-- The zero function has jet norm `0`. -/
@[simp]
theorem jetNormAt_zero_fun (r : ℕ) (z : E) : jetNormAt 𝕜 r (0 : E → F) z = 0 := by
  simp [jetNormAt_def]

@[simp]
theorem jetNormAt_neg (r : ℕ) (f : E → F) (z : E) :
    jetNormAt 𝕜 r (-f) z = jetNormAt 𝕜 r f z := by
  simp only [jetNormAt_def, iteratedFDeriv_neg_apply, norm_neg]

/-- The **triangle inequality for jet norms**, for functions of class `C^r` at `z`. -/
theorem jetNormAt_add_le {r : ℕ} {f g : E → F} {z : E} (hf : ContDiffAt 𝕜 r f z)
    (hg : ContDiffAt 𝕜 r g z) :
    jetNormAt 𝕜 r (f + g) z ≤ jetNormAt 𝕜 r f z + jetNormAt 𝕜 r g z := by
  simp only [jetNormAt_def, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  have hjr : (j : WithTop ℕ∞) ≤ r := by
    exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [iteratedFDeriv_add_apply (hf.of_le hjr) (hg.of_le hjr)]
  exact norm_add_le _ _

/-- The jet norm of a scalar multiple `c • f` is `‖c‖` times that of `f`, for every `f`. -/
@[simp]
theorem jetNormAt_smul {R : Type*} [NormedField R] [NormedSpace R F] [SMulCommClass 𝕜 R F]
    (r : ℕ) (f : E → F) (z : E) (c : R) :
    jetNormAt 𝕜 r (c • f) z = ‖c‖ * jetNormAt 𝕜 r f z := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [jetNormAt_def]
  -- For `c ≠ 0`, multiplication by `c` is a continuous linear equivalence over `𝕜`, and iterated
  -- derivatives commute with it with no smoothness assumption.
  let L : F ≃L[𝕜] F := .ofContinuousLinearMap (c • .id 𝕜 F) (c⁻¹ • .id 𝕜 F)
    (by ext; simp [smul_smul, mul_inv_cancel₀ hc]) (by ext; simp [smul_smul, inv_mul_cancel₀ hc])
  have hL : c • f = L ∘ f := by ext; simp [L]
  simp only [jetNormAt_def, Finset.mul_sum, hL, L.iteratedFDeriv_comp_left]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have : L.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDeriv 𝕜 j f z) =
      c • iteratedFDeriv 𝕜 j f z := by
    ext; simp [L]
  rw [this, norm_smul]

end SymplecticGeometry

end
