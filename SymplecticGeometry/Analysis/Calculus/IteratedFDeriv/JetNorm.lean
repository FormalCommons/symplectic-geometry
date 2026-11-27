/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.ContDiff.Bounds

/-!
# The jet norm of a function at a point

For a function `f : E → F` between normed spaces over `𝕜`, a point `z` and an order `r`, the
`r`-jet norm `SymplecticGeometry.jetNormAt 𝕜 r f z` is the sum, over the orders `j ≤ r`, of the
norms `‖iteratedFDeriv 𝕜 j f z‖` of the derivatives of `f` at `z`.

## Main results

* `iteratedFDeriv_const_smul_apply_of_field`: the iterated derivative of `c • f` is `c` times
  that of `f`, with no smoothness assumption, from Mathlib's
  `ContinuousLinearEquiv.iteratedFDeriv_comp_left` applied to `ContinuousLinearEquiv.smulLeft`.
* `SymplecticGeometry.jetNormAt_nonneg` and `SymplecticGeometry.jetNormAt_mono`: the jet norm is
  nonnegative and monotone in the order.
* `SymplecticGeometry.norm_iteratedFDeriv_le_jetNormAt`: each derivative of order at most `r` is
  bounded in norm by the `r`-jet norm.
* `SymplecticGeometry.jetNormAt_zero`: the jet norm of order `0` is `‖f z‖`.
* `SymplecticGeometry.jetNormAt_congr_of_eventuallyEq`: the jet norm at `z` depends only on the
  germ of the function at `z`.
* `SymplecticGeometry.jetNormAt_add_le`: the triangle inequality, for functions that are `C^r`
  at `z`, from Mathlib's `iteratedFDeriv_add_apply`.
* `SymplecticGeometry.jetNormAt_smul`: the jet norm of `c • f` is `‖c‖` times that of `f`, for every
  `f`.
* `SymplecticGeometry.jetNormAt_smul_le`: the Leibniz bound on the jet norm of a product
  `fun y ↦ f y • g y` of functions that are `C^r` at `z`, from Tau Ceti's
  `TauCeti.norm_iteratedFDeriv_smul_le_of_isOpen` on an open neighbourhood of `z`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4
-/

public section

open scoped Topology

/-- The iterated derivative of `c • f` is `c` times that of `f`, for every `f`, when `c` lies in a
normed field: unlike `iteratedFDeriv_const_smul_apply`, no smoothness of `f` is assumed. -/
theorem iteratedFDeriv_const_smul_apply_of_field {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {R : Type*} [NormedField R] [NormedSpace R F] [SMulCommClass 𝕜 R F]
    (i : ℕ) (f : E → F) (x : E) (c : R) :
    iteratedFDeriv 𝕜 i (c • f) x = c • iteratedFDeriv 𝕜 i f x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  -- `ContinuousLinearEquiv.smulLeft` asks for `SMulCommClass Rˣ 𝕜 F`.
  have := SMulCommClass.symm 𝕜 R F
  -- For `c ≠ 0`, multiplication by `c` is a continuous linear equivalence over `𝕜`, and iterated
  -- derivatives commute with such a map with no smoothness assumption.
  have hL : c • f = ContinuousLinearEquiv.smulLeft (R₁ := 𝕜) (Units.mk0 c hc) ∘ f := by
    ext; simp
  rw [hL, ContinuousLinearEquiv.iteratedFDeriv_comp_left]
  ext; simp

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

/-- Each derivative of order `j ≤ r` is bounded in norm by the `r`-jet norm. -/
theorem norm_iteratedFDeriv_le_jetNormAt {j r : ℕ} (hj : j ≤ r) (f : E → F) (z : E) :
    ‖iteratedFDeriv 𝕜 j f z‖ ≤ jetNormAt 𝕜 r f z := by
  rw [jetNormAt_def]
  exact Finset.single_le_sum (f := fun l ↦ ‖iteratedFDeriv 𝕜 l f z‖)
    (fun _ _ ↦ norm_nonneg _) (Finset.mem_range_succ_iff.2 hj)

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

/-- The jet norm at `z` depends only on the germ of the function at `z`. -/
theorem jetNormAt_congr_of_eventuallyEq (r : ℕ) {f g : E → F} {z : E} (h : f =ᶠ[𝓝 z] g) :
    jetNormAt 𝕜 r f z = jetNormAt 𝕜 r g z := by
  simp only [jetNormAt_def, (h.iteratedFDeriv 𝕜 _).eq_of_nhds]

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
  simp [jetNormAt_def, Finset.mul_sum, iteratedFDeriv_const_smul_apply_of_field, norm_smul]

/-- The **Leibniz bound for jet norms**: for functions `f` and `g` that are `C^r` at `z`, the
`r`-jet norm of `fun y ↦ f y • g y` at `z` is at most `(r + 1) * 2 ^ r` times the product of
the `r`-jet norms of `f` and `g`. -/
theorem jetNormAt_smul_le {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
    [IsScalarTower 𝕜 𝕜' F] {r : ℕ} {f : E → 𝕜'} {g : E → F} {z : E} (hf : ContDiffAt 𝕜 r f z)
    (hg : ContDiffAt 𝕜 r g z) :
    jetNormAt 𝕜 r (fun y ↦ f y • g y) z ≤
      (r + 1) * 2 ^ r * jetNormAt 𝕜 r f z * jetNormAt 𝕜 r g z := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv, hgv⟩ := hg.contDiffOn le_rfl (by simp)
  set t := interior (u ∩ v)
  have ht : IsOpen t := isOpen_interior
  have hzt : z ∈ t := mem_interior_iff_mem_nhds.2 (Filter.inter_mem hu hv)
  have hft : ContDiffOn 𝕜 r f t := hfu.mono (interior_subset.trans Set.inter_subset_left)
  have hgt : ContDiffOn 𝕜 r g t := hgv.mono (interior_subset.trans Set.inter_subset_right)
  have hf₀ := jetNormAt_nonneg (𝕜 := 𝕜) r f z
  have hg₀ := jetNormAt_nonneg (𝕜 := 𝕜) r g z
  have key (j : ℕ) (hj : j ≤ r) : ‖iteratedFDeriv 𝕜 j (fun y ↦ f y • g y) z‖ ≤
      2 ^ r * (jetNormAt 𝕜 r f z * jetNormAt 𝕜 r g z) := by
    refine (TauCeti.norm_iteratedFDeriv_smul_le_of_isOpen ht hft hgt hzt
      (by exact_mod_cast hj)).trans ?_
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i f z‖ *
          ‖iteratedFDeriv 𝕜 (j - i) g z‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (jetNormAt 𝕜 r f z * jetNormAt 𝕜 r g z) := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hi' := Finset.mem_range_succ_iff.1 hi
          rw [mul_assoc]
          gcongr
          · exact norm_iteratedFDeriv_le_jetNormAt (by omega) f z
          · exact norm_iteratedFDeriv_le_jetNormAt (by omega) g z
      _ = 2 ^ j * (jetNormAt 𝕜 r f z * jetNormAt 𝕜 r g z) := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow,
            Nat.cast_ofNat]
      _ ≤ 2 ^ r * (jetNormAt 𝕜 r f z * jetNormAt 𝕜 r g z) := by
          gcongr
          norm_num
  rw [jetNormAt_def]
  calc ∑ j ∈ Finset.range (r + 1), ‖iteratedFDeriv 𝕜 j (fun y ↦ f y • g y) z‖
      ≤ ∑ _j ∈ Finset.range (r + 1), 2 ^ r * (jetNormAt 𝕜 r f z * jetNormAt 𝕜 r g z) :=
        Finset.sum_le_sum fun j hj ↦ key j (Finset.mem_range_succ_iff.1 hj)
    _ = (r + 1) * 2 ^ r * jetNormAt 𝕜 r f z * jetNormAt 𝕜 r g z := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end SymplecticGeometry

end
