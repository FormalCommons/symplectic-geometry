/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Bounds
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear

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
* `SymplecticGeometry.continuous_jetNormAt`: the `r`-jet norm of a `C^r` function is continuous.
* `SymplecticGeometry.jetNormAt_zero`: the jet norm of order `0` is `‖f z‖`.
* `SymplecticGeometry.jetNormAt_congr_of_eventuallyEq`: the jet norm at `z` depends only on the
  germ of the function at `z`.
* `SymplecticGeometry.jetNormAt_add_le`: the triangle inequality, for functions that are `C^r`
  at `z`, from Mathlib's `iteratedFDeriv_add_apply`.
* `SymplecticGeometry.jetNormAt_smul`: the jet norm of `c • f` is `‖c‖` times that of `f`, for every
  `f`.
* `SymplecticGeometry.jetNormAt_succ`: the `(r + 1)`-jet norm of `f` is `‖f z‖` plus the `r`-jet
  norm of `fderiv 𝕜 f`, from Mathlib's `norm_iteratedFDeriv_fderiv`.
* `SymplecticGeometry.jetNormAt_const`: the jet norm of a constant function.
* `SymplecticGeometry.jetNormAt_le_of_norm_iteratedFDeriv_succ_le`: a bound of the `r`-jet norm
  from a common bound of the derivatives of orders `1` to `r`, and its form
  `SymplecticGeometry.jetNormAt_le_mul_one_add_norm_of_norm_iteratedFDeriv_succ_le`, a constant
  times `1 + ‖f z‖`, and `SymplecticGeometry.jetNormAt_fderiv_le_of_norm_iteratedFDeriv_succ_le`,
  the bound of the `r`-jet norm of `fderiv 𝕜 f` by those of orders `1` to `r + 1`.
* `SymplecticGeometry.jetNormAt_continuousLinearMap_le`: the `r`-jet norm of a continuous linear
  map `L` at `z` is at most `‖L z‖ + ‖L‖`, so at most `1 + ‖z‖` if `‖L‖ ≤ 1`
  (`SymplecticGeometry.jetNormAt_continuousLinearMap_le_one_add_norm`).
* `SymplecticGeometry.jetNormAt_comp_fst`: the jet norm of `f ∘ Prod.fst` at `p` is that of `f`
  at `p.1`, from Tau Ceti's `Prod.norm_iteratedFDeriv_comp_fst`.
* `SymplecticGeometry.jetNormAt_comp_left_le`: the jet norm of `L ∘ f`, for a continuous linear
  map `L`, is at most `‖L‖` times that of `f`, from Mathlib's
  `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`.
* `SymplecticGeometry.jetNormAt_comp_const_smul_le`: for `‖a‖ ≤ 1`, the jet norm of
  `z ↦ f (a • z)` at `z` is at most that of `f` at `a • z`, from Tau Ceti's
  `TauCeti.norm_iteratedFDeriv_comp_const_smul`.
* `SymplecticGeometry.jetNormAt_comp_le`: for `f` of class `C^r` at `z` and `g` of class `C^r` at
  `f z`, the jet norm of `g ∘ f` at `z` is at most
  `(r + 1)! * jetNormAt 𝕜 r g (f z) * max 1 (jetNormAt 𝕜 r f z) ^ r`, from Tau Ceti's
  `TauCeti.norm_iteratedFDeriv_comp_le_of_contDiffAt` (the Faà di Bruno bound at a point).
* `SymplecticGeometry.jetNormAt_bilinear_le`: for a continuous bilinear map `B` and `f`, `g` of
  class `C^r` at `z`, the jet norm of `w ↦ B (f w) (g w)` at `z` is at most
  `2 ^ r * ‖B‖ * jetNormAt 𝕜 r f z * jetNormAt 𝕜 r g z`, from Tau Ceti's
  `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_contDiffAt` (the Leibniz bound at a
  point).
* `SymplecticGeometry.jetNormAt_fun_smul_le`: the Leibniz bound on the jet norm of a product
  `fun y ↦ f y • g y` of functions that are `C^r` at `z`, from `jetNormAt_bilinear_le` applied to
  `ContinuousLinearMap.lsmul`.

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

/-- The `r`-jet norm of a `C^r` function is a continuous function of the point. -/
theorem continuous_jetNormAt {r : ℕ} {f : E → F} (hf : ContDiff 𝕜 r f) :
    Continuous (jetNormAt 𝕜 r f) := by
  simp only [funext (jetNormAt_def 𝕜 r f)]
  exact continuous_finsetSum _ fun l hl ↦ (hf.continuous_iteratedFDeriv (by
    exact_mod_cast Finset.mem_range_succ_iff.mp hl)).norm

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

/-- The `(r + 1)`-jet norm of `f` at `z` is the norm of `f z` plus the `r`-jet norm of
`fderiv 𝕜 f` at `z`. -/
theorem jetNormAt_succ (r : ℕ) (f : E → F) (z : E) :
    jetNormAt 𝕜 (r + 1) f z = ‖f z‖ + jetNormAt 𝕜 r (fderiv 𝕜 f) z := by
  simp only [jetNormAt_def, Finset.sum_range_succ' _ (r + 1), norm_iteratedFDeriv_zero,
    norm_iteratedFDeriv_fderiv, add_comm ‖f z‖]

/-- A constant function has jet norm the norm of its value. -/
@[simp]
theorem jetNormAt_const (r : ℕ) (c : F) (z : E) :
    jetNormAt 𝕜 r (fun _ : E ↦ c) z = ‖c‖ := by
  rw [jetNormAt_def, Finset.sum_range_succ']
  simp [iteratedFDeriv_const_of_ne]

/-- If the derivatives of `f` at `z` of orders `1` to `r` have norm at most `C`, the `r`-jet norm
of `f` at `z` is at most `‖f z‖ + r * C`. -/
theorem jetNormAt_le_of_norm_iteratedFDeriv_succ_le {r : ℕ} {f : E → F} {z : E} {C : ℝ}
    (h : ∀ j < r, ‖iteratedFDeriv 𝕜 (j + 1) f z‖ ≤ C) :
    jetNormAt 𝕜 r f z ≤ ‖f z‖ + r * C := by
  rw [jetNormAt_def, Finset.sum_range_succ', norm_iteratedFDeriv_zero, add_comm ‖f z‖]
  gcongr
  calc ∑ j ∈ Finset.range r, ‖iteratedFDeriv 𝕜 (j + 1) f z‖
      ≤ ∑ _j ∈ Finset.range r, C := Finset.sum_le_sum fun j hj ↦ h j (Finset.mem_range.1 hj)
    _ = r * C := by simp

/-- If the derivatives of orders `1` to `r` of `f` at `z` have norm at most `C`, the `r`-jet norm
of `f` at `z` is at most `(1 + r * |C|) * (1 + ‖f z‖)`. -/
theorem jetNormAt_le_mul_one_add_norm_of_norm_iteratedFDeriv_succ_le {r : ℕ} {f : E → F} {z : E}
    {C : ℝ} (h : ∀ j < r, ‖iteratedFDeriv 𝕜 (j + 1) f z‖ ≤ C) :
    jetNormAt 𝕜 r f z ≤ (1 + r * |C|) * (1 + ‖f z‖) := by
  have h' := jetNormAt_le_of_norm_iteratedFDeriv_succ_le (C := |C|) fun j hj ↦
    (h j hj).trans (le_abs_self C)
  nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) (abs_nonneg C))
    (norm_nonneg (f z))]

/-- If the derivatives of orders `1` to `r + 1` of `f` at `z` have norm at most `C`, the `r`-jet
norm of `fderiv 𝕜 f` at `z` is at most `(r + 1) * |C|`. -/
theorem jetNormAt_fderiv_le_of_norm_iteratedFDeriv_succ_le {r : ℕ} {f : E → F} {z : E} {C : ℝ}
    (h : ∀ j < r + 1, ‖iteratedFDeriv 𝕜 (j + 1) f z‖ ≤ C) :
    jetNormAt 𝕜 r (fderiv 𝕜 f) z ≤ (r + 1) * |C| := by
  have h' := jetNormAt_le_of_norm_iteratedFDeriv_succ_le (C := |C|) fun j hj ↦
    (h j hj).trans (le_abs_self C)
  rw [jetNormAt_succ] at h'
  push_cast at h'
  linarith [norm_nonneg (f z)]

/-- The `r`-jet norm of a continuous linear map `L` at `z` is at most `‖L z‖ + ‖L‖`: its
derivatives of order two or more vanish. -/
theorem jetNormAt_continuousLinearMap_le (L : E →L[𝕜] F) (r : ℕ) (z : E) :
    jetNormAt 𝕜 r L z ≤ ‖L z‖ + ‖L‖ := by
  cases r with
  | zero => simp
  | succ r =>
    rw [jetNormAt_succ, funext fun x ↦ L.fderiv (x := x), jetNormAt_const]

/-- The `r`-jet norm at `z` of a continuous linear map `L` of operator norm at most `1` is at most
`1 + ‖z‖`. -/
theorem jetNormAt_continuousLinearMap_le_one_add_norm {L : E →L[𝕜] F} (hL : ‖L‖ ≤ 1) (r : ℕ)
    (z : E) : jetNormAt 𝕜 r L z ≤ 1 + ‖z‖ := by
  have := L.le_opNorm z
  have := mul_le_mul_of_nonneg_right hL (norm_nonneg z)
  linarith [jetNormAt_continuousLinearMap_le L r z]

/-- The jet norm of a scalar multiple `c • f` is `‖c‖` times that of `f`, for every `f`. -/
@[simp]
theorem jetNormAt_smul {R : Type*} [NormedField R] [NormedSpace R F] [SMulCommClass 𝕜 R F]
    (r : ℕ) (f : E → F) (z : E) (c : R) :
    jetNormAt 𝕜 r (c • f) z = ‖c‖ * jetNormAt 𝕜 r f z := by
  simp [jetNormAt_def, Finset.mul_sum, iteratedFDeriv_const_smul_apply_of_field, norm_smul]

section Bounds

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

open scoped Nat

/-- The jet norm of `f ∘ Prod.fst` at `p` is the jet norm of `f` at `p.1`. -/
@[simp]
theorem jetNormAt_comp_fst (r : ℕ) (f : E → F) (p : E × G) :
    jetNormAt 𝕜 r (f ∘ Prod.fst) p = jetNormAt 𝕜 r f p.1 := by
  simp only [jetNormAt_def, Prod.norm_iteratedFDeriv_comp_fst]

/-- The jet norm of `L ∘ f`, for a continuous linear map `L` and a map `f` that is `C^r` at `z`,
is at most `‖L‖` times the jet norm of `f`. -/
theorem jetNormAt_comp_left_le (L : F →L[𝕜] G) {r : ℕ} {f : E → F} {z : E}
    (hf : ContDiffAt 𝕜 r f z) :
    jetNormAt 𝕜 r (L ∘ f) z ≤ ‖L‖ * jetNormAt 𝕜 r f z := by
  simp only [jetNormAt_def, Finset.mul_sum]
  exact Finset.sum_le_sum fun j hj ↦ L.norm_iteratedFDeriv_comp_left hf
    (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))

/-- The jet norm of the rescaling `z ↦ f (a • z)` at `z` is at most that of `f` at `a • z`, when
`‖a‖ ≤ 1`, for every `f`. -/
theorem jetNormAt_comp_const_smul_le (r : ℕ) (f : E → F) {a : 𝕜} (ha : ‖a‖ ≤ 1) (z : E) :
    jetNormAt 𝕜 r (fun z ↦ f (a • z)) z ≤ jetNormAt 𝕜 r f (a • z) := by
  simp only [jetNormAt_def, TauCeti.norm_iteratedFDeriv_comp_const_smul]
  exact Finset.sum_le_sum fun j _ ↦
    mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ha)

/-- The **jet norm of a composition**: if `f` is `C^r` at `z` and `g` is `C^r` at `f z`, the
`r`-jet norm of `g ∘ f` at `z` is at most `(r + 1)!` times the `r`-jet norm of `g` at `f z` times
`max 1 (jetNormAt 𝕜 r f z) ^ r`. -/
theorem jetNormAt_comp_le {r : ℕ} {g : F → G} {f : E → F} {z : E}
    (hg : ContDiffAt 𝕜 r g (f z)) (hf : ContDiffAt 𝕜 r f z) :
    jetNormAt 𝕜 r (g ∘ f) z ≤
      (r + 1)! * jetNormAt 𝕜 r g (f z) * max 1 (jetNormAt 𝕜 r f z) ^ r := by
  set D := max 1 (jetNormAt 𝕜 r f z)
  have hD : 1 ≤ D := le_max_left _ _
  have hC := jetNormAt_nonneg (𝕜 := 𝕜) r g (f z)
  rw [jetNormAt_def]
  calc ∑ j ∈ Finset.range (r + 1), ‖iteratedFDeriv 𝕜 j (g ∘ f) z‖
      ≤ ∑ _j ∈ Finset.range (r + 1), (r ! * jetNormAt 𝕜 r g (f z) * D ^ r : ℝ) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        refine (TauCeti.norm_iteratedFDeriv_comp_le_of_contDiffAt (D := D)
          (hg.of_le (by exact_mod_cast hjr)) (hf.of_le (by exact_mod_cast hjr))
          (fun i hi ↦ norm_iteratedFDeriv_le_jetNormAt (hi.trans hjr) g (f z))
          (fun i hi₁ hi ↦ ?_)).trans ?_
        · calc ‖iteratedFDeriv 𝕜 i f z‖ ≤ jetNormAt 𝕜 r f z :=
                norm_iteratedFDeriv_le_jetNormAt (hi.trans hjr) f z
            _ ≤ D := le_max_right _ _
            _ ≤ D ^ i := le_self_pow₀ hD (by omega)
        · gcongr
    _ = (r + 1)! * jetNormAt 𝕜 r g (f z) * D ^ r := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.factorial_succ]
        push_cast
        ring

/-- The **jet norm of a bilinear combination**: for a continuous bilinear map `B` and maps `f`,
`g` that are `C^r` at `z`, the `r`-jet norm of `w ↦ B (f w) (g w)` at `z` is at most
`2 ^ r * ‖B‖` times the product of the `r`-jet norms of `f` and `g` at `z`. -/
theorem jetNormAt_bilinear_le (B : F →L[𝕜] G →L[𝕜] H) {r : ℕ} {f : E → F} {g : E → G} {z : E}
    (hf : ContDiffAt 𝕜 r f z) (hg : ContDiffAt 𝕜 r g z) :
    jetNormAt 𝕜 r (fun w ↦ B (f w) (g w)) z ≤
      2 ^ r * ‖B‖ * jetNormAt 𝕜 r f z * jetNormAt 𝕜 r g z := by
  set a : ℕ → ℝ := fun i ↦ ‖iteratedFDeriv 𝕜 i f z‖
  set b : ℕ → ℝ := fun i ↦ ‖iteratedFDeriv 𝕜 i g z‖
  have ha : ∀ i, 0 ≤ a i := fun _ ↦ norm_nonneg _
  have hb : ∀ i, 0 ≤ b i := fun _ ↦ norm_nonneg _
  simp only [jetNormAt_def]
  calc ∑ n ∈ Finset.range (r + 1), ‖iteratedFDeriv 𝕜 n (fun w ↦ B (f w) (g w)) z‖
      ≤ ∑ n ∈ Finset.range (r + 1), ‖B‖ * ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * a i * b (n - i) := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        have hnr : n ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
        exact B.norm_iteratedFDeriv_le_of_bilinear_of_contDiffAt hf hg (by exact_mod_cast hnr)
    _ ≤ ∑ n ∈ Finset.range (r + 1), ‖B‖ * ∑ i ∈ Finset.range (n + 1),
          2 ^ r * (a i * b (n - i)) := by
        refine Finset.sum_le_sum fun n hn ↦ mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ ↦ ?_) (norm_nonneg B)
        have hc : (n.choose i : ℝ) ≤ 2 ^ r := by
          exact_mod_cast (Nat.choose_le_two_pow n i).trans
            (Nat.pow_le_pow_right two_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)))
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hc (mul_nonneg (ha i) (hb _))
    _ = 2 ^ r * ‖B‖ * ∑ m ∈ Finset.range (r + 1), a m * ∑ k ∈ Finset.range (r + 1 - m), b k := by
        simp_rw [← Finset.mul_sum, Finset.sum_range_diag_flip (r + 1) fun m k ↦ a m * b k,
          ← Finset.mul_sum]
        ring
    _ ≤ 2 ^ r * ‖B‖ * ∑ m ∈ Finset.range (r + 1), a m * ∑ k ∈ Finset.range (r + 1), b k := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ ↦ ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by omega)) fun k _ _ ↦ hb k) (ha m)
    _ = 2 ^ r * ‖B‖ * (∑ m ∈ Finset.range (r + 1), a m) * ∑ k ∈ Finset.range (r + 1), b k := by
        rw [← Finset.sum_mul]
        ring

/-- The **Leibniz bound for jet norms**: for functions `f` and `g` that are `C^r` at `z`, the
`r`-jet norm of `fun y ↦ f y • g y` at `z` is at most `2 ^ r` times the product of the `r`-jet
norms of `f` and `g`. -/
theorem jetNormAt_fun_smul_le {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {r : ℕ} {f : E → 𝕜'} {g : E → F} {z : E}
    (hf : ContDiffAt 𝕜 r f z) (hg : ContDiffAt 𝕜 r g z) :
    jetNormAt 𝕜 r (fun y ↦ f y • g y) z ≤ 2 ^ r * jetNormAt 𝕜 r f z * jetNormAt 𝕜 r g z := by
  have h := jetNormAt_bilinear_le (ContinuousLinearMap.lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] F →L[𝕜] F) hf hg
  simp only [ContinuousLinearMap.lsmul_apply] at h
  refine h.trans ?_
  have := jetNormAt_nonneg (𝕜 := 𝕜) r f z
  have := jetNormAt_nonneg (𝕜 := 𝕜) r g z
  -- The bilinear map `lsmul` has norm at most `1`.
  calc 2 ^ r * ‖(ContinuousLinearMap.lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] F →L[𝕜] F)‖ * jetNormAt 𝕜 r f z *
        jetNormAt 𝕜 r g z
      ≤ 2 ^ r * 1 * jetNormAt 𝕜 r f z * jetNormAt 𝕜 r g z := by
        gcongr
        exact ContinuousLinearMap.opNorm_lsmul_le
    _ = 2 ^ r * jetNormAt 𝕜 r f z * jetNormAt 𝕜 r g z := by ring

end Bounds
end SymplecticGeometry

end
