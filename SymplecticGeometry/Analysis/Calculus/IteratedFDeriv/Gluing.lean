/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.NhdsSet

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Algebra.Support
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.JetNorm

/-!
# Gluing maps that agree to a given order

Let `ρ i`, for `i` in a finite set `s`, be real `C^r` functions with `tsupport (ρ i) ⊆ U i`,
summing to `1` near a point `z`, and let `g i` be maps that are `C^r` on the open sets `U i`.
The glued map `G = fun y ↦ ∑ i ∈ s, ρ i y • g i y` is the usual way to patch local maps
together with a partition of unity; for a locally finite one, `G` is a finite sum of this form
near each point. This file compares `G` with a map `f` that is `C^r` at `z`. Near `z`, we
have `G - f = ∑ i ∈ s, ρ i • (g i - f)`, so Leibniz's rule bounds the derivatives of `G - f` by
those of the `ρ i` and of the `g i - f`. In particular, if every `g i - f` has
`‖D^l (g i - f)‖ ≤ C * w ^ (N + 1 - l)`, for a weight `0 ≤ w ≤ 1` (such as the norm of the
imaginary part on `EuclideanSpace ℂ ι'`), then so has `G - f`, with another constant.

## Main results

* `SymplecticGeometry.sum_smul_sub_eventuallyEq`: along a filter on which the `ρ i` sum to `1`,
  `G - f` is the sum of the `ρ i • (g i - f)`;
* `SymplecticGeometry.norm_iteratedFDeriv_sum_smul_sub_le`: the bound at one point, with an
  explicit constant;
* `SymplecticGeometry.exists_norm_iteratedFDeriv_sum_smul_sub_le`: the bound near a compact set,
  for a weight with `0 ≤ w ≤ 1` near it;
* `SymplecticGeometry.iteratedFDeriv_sum_smul_sub_eq_zero`: if every `g i - f` has vanishing
  derivatives of order at most `j` at `z`, so has `G - f`;
* `SymplecticGeometry.sum_smul_apply_eq`: if every `g i` has the value of `f` at `z`, so has `G`;
* `SymplecticGeometry.fderiv_sum_smul_eq`: if every `g i` has the value and the derivative of `f`
  at `z`, then `G` has the derivative of `f` at `z`.

These are the gluing steps of the proof of Proposition 5.55 of [CieliebakEliashberg2012], where
local maps that agree with each other to order `N + 1` along the real points are patched with a
partition of unity. The Leibniz bound is Tau Ceti's
`TauCeti.norm_iteratedFDeriv_smul_le_of_isOpen`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Filter Set Topology

namespace SymplecticGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} {s : Finset ι} {ρ : ι → E → ℝ} {g : ι → E → F} {U : ι → Set E}
  {f : E → F} {V : Set E} {r : ℕ}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Along a filter on which the `ρ i` eventually sum to `1`, the glued map minus `f` is
eventually the sum of the `ρ i • (g i - f)`. -/
theorem sum_smul_sub_eventuallyEq {l : Filter E} (hsum : ∀ᶠ y in l, ∑ i ∈ s, ρ i y = 1) :
    ((fun y ↦ ∑ i ∈ s, ρ i y • g i y) - f) =ᶠ[l]
      fun y ↦ ∑ i ∈ s, ρ i y • (g i - f) y := by
  filter_upwards [hsum] with y hy
  simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hy, one_smul]

/-- The iterated derivative of order `j ≤ r` of the glued map `∑ i ∈ s, ρ i • g i` minus `f`,
at a point `z` near which the `ρ i` sum to `1` and where `f` is `C^r`, is at most
`s.card * 2 ^ j * B * C * w ^ (N + 1 - j)`, if `0 ≤ w ≤ 1`, the derivatives of order at most
`j` of the `ρ i` are at most `B` at `z`, and those of order `l ≤ j` of `g i - f` are at most
`C * w ^ (N + 1 - l)` at `z` whenever `z ∈ U i`. -/
theorem norm_iteratedFDeriv_sum_smul_sub_le (hU : ∀ i ∈ s, IsOpen (U i))
    (hρ : ∀ i ∈ s, ContDiff ℝ r (ρ i)) (hρU : ∀ i ∈ s, tsupport (ρ i) ⊆ U i)
    (hg : ∀ i ∈ s, ContDiffOn ℝ r (g i) (U i)) {z : E} (hf : ContDiffAt ℝ r f z)
    (hsum : ∀ᶠ y in 𝓝 z, ∑ i ∈ s, ρ i y = 1)
    {N j : ℕ} (hj : j ≤ r) {w B C : ℝ} (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) (hC : 0 ≤ C)
    (hρB : ∀ i ∈ s, ∀ l ≤ j, ‖iteratedFDeriv ℝ l (ρ i) z‖ ≤ B)
    (hgC : ∀ i ∈ s, z ∈ U i → ∀ l ≤ j,
      ‖iteratedFDeriv ℝ l (g i - f) z‖ ≤ C * w ^ (N + 1 - l)) :
    ‖iteratedFDeriv ℝ j ((fun y ↦ ∑ i ∈ s, ρ i y • g i y) - f) z‖ ≤
      s.card * 2 ^ j * B * C * w ^ (N + 1 - j) := by
  have hj' : (j : WithTop ℕ∞) ≤ r := by exact_mod_cast hj
  -- An open set around `z` on which `f` is `C^r`.
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  have hzV : z ∈ interior u := mem_interior_iff_mem_nhds.mpr hu
  replace hfu := hfu.mono interior_subset
  -- Each term `ρ i • (g i - f)` obeys the bound without the factor `s.card`.
  have key : ∀ i ∈ s, ‖iteratedFDeriv ℝ j (fun y ↦ ρ i y • (g i - f) y) z‖ ≤
      2 ^ j * B * C * w ^ (N + 1 - j) := by
    intro i hi
    have hB : 0 ≤ B := (norm_nonneg _).trans (hρB i hi 0 (Nat.zero_le _))
    by_cases hzi : z ∈ U i
    · have hO : IsOpen (U i ∩ interior u) := (hU i hi).inter isOpen_interior
      refine (TauCeti.norm_iteratedFDeriv_smul_le_of_isOpen hO
        ((hρ i hi).contDiffOn.of_le hj') ((((hg i hi).mono inter_subset_left).sub
          (hfu.mono inter_subset_right)).of_le hj') ⟨hzi, hzV⟩ le_rfl).trans ?_
      calc ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (ρ i) z‖ *
            ‖iteratedFDeriv ℝ (j - l) (g i - f) z‖
          ≤ ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * (B * (C * w ^ (N + 1 - j))) := by
            refine Finset.sum_le_sum fun l hl ↦ ?_
            have hl : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
            rw [mul_assoc]
            gcongr
            · exact hρB i hi l hl
            · refine (hgC i hi hzi (j - l) (Nat.sub_le j l)).trans ?_
              exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hw₀ hw₁ (by omega)) hC
        _ = 2 ^ j * B * C * w ^ (N + 1 - j) := by
            rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
            push_cast
            ring
    · have hzt : z ∉ tsupport (fun y ↦ ρ i y • (g i - f) y) :=
        fun h ↦ hzi (hρU i hi (tsupport_smul_subset_left _ _ h))
      rw [Function.notMem_support.mp fun h ↦ hzt (support_iteratedFDeriv_subset j h), norm_zero]
      positivity
  -- Near `z`, the glued map minus `f` is the sum of these terms, each of them `C^r` at `z`.
  have hterm : ∀ i ∈ s, ContDiffAt ℝ j (fun y ↦ ρ i y • (g i - f) y) z := by
    intro i hi
    have h₁ := (hg i hi).contDiff_smul_of_tsupport_subset (hU i hi) (hρ i hi).contDiffOn
      (hρU i hi)
    have h₂ := (hρ i hi).contDiffAt.smul hf
    refine ((h₁.contDiffAt.sub h₂).of_le hj').congr_of_eventuallyEq (Eventually.of_forall ?_)
    intro y
    simp [smul_sub]
  rw [((sum_smul_sub_eventuallyEq hsum).iteratedFDeriv ℝ j).eq_of_nhds,
    iteratedFDeriv_fun_sum_apply hterm]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum key).trans_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Near a compact set `K`, the glued map `∑ i ∈ s, ρ i • g i` minus `f` has the bounds
`‖D^j (G - f)‖ ≤ C' * w ^ (N + 1 - j)`, for `j ≤ r`, if every `g i - f` has them with a constant
`C` near `K` on `U i ∩ V`. Here the `ρ i` are `C^r` with `tsupport (ρ i) ⊆ U i` and sum to `1`
near `K`, and `w` is a weight with `0 ≤ w ≤ 1` near `K`. The bounds hold at the points of `V`
near `K`. -/
theorem exists_norm_iteratedFDeriv_sum_smul_sub_le (hU : ∀ i ∈ s, IsOpen (U i))
    (hV : IsOpen V) (hρ : ∀ i ∈ s, ContDiff ℝ r (ρ i)) (hρU : ∀ i ∈ s, tsupport (ρ i) ⊆ U i)
    (hg : ∀ i ∈ s, ContDiffOn ℝ r (g i) (U i)) (hf : ContDiffOn ℝ r f V)
    {K : Set E} (hK : IsCompact K) (hsum : ∀ᶠ y in 𝓝ˢ K, ∑ i ∈ s, ρ i y = 1)
    {w : E → ℝ} (hw : ∀ᶠ y in 𝓝ˢ K, 0 ≤ w y ∧ w y ≤ 1) {N : ℕ} {C : ℝ}
    (hgC : ∀ᶠ y in 𝓝ˢ K, ∀ i ∈ s, y ∈ U i → y ∈ V → ∀ l ≤ r,
      ‖iteratedFDeriv ℝ l (g i - f) y‖ ≤ C * w y ^ (N + 1 - l)) :
    ∃ C', ∀ᶠ y in 𝓝ˢ K, y ∈ V → ∀ j ≤ r,
      ‖iteratedFDeriv ℝ j ((fun y ↦ ∑ i ∈ s, ρ i y • g i y) - f) y‖ ≤
        C' * w y ^ (N + 1 - j) := by
  -- A bound on the derivatives of the `ρ i` near `K`.
  set Φ : E → ℝ := fun y ↦ ∑ i ∈ s, jetNormAt ℝ r (ρ i) y
  have hΦ : Continuous Φ := continuous_finsetSum _ fun i hi ↦ continuous_jetNormAt (hρ i hi)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  have hΦM : ∀ᶠ y in 𝓝ˢ K, Φ y < max M 0 + 1 :=
    (isOpen_lt hΦ continuous_const).mem_nhdsSet.mpr fun y hy ↦
      (le_abs_self _).trans_lt ((hM y hy).trans_lt (by
        have := le_max_left M 0
        linarith))
  refine ⟨s.card * 2 ^ r * (max M 0 + 1) * max C 0, ?_⟩
  filter_upwards [hsum.eventually_nhdsSet, hΦM, hw, hgC] with y hys hyΦ hyw hyC hyV j hj
  have hB : ∀ i ∈ s, ∀ l ≤ j, ‖iteratedFDeriv ℝ l (ρ i) y‖ ≤ max M 0 + 1 := fun i hi l hl ↦
    ((norm_iteratedFDeriv_le_jetNormAt (hl.trans hj) _ _).trans
      (Finset.single_le_sum (fun i _ ↦ jetNormAt_nonneg r (ρ i) y) hi)).trans hyΦ.le
  refine (norm_iteratedFDeriv_sum_smul_sub_le (N := N) hU hρ hρU hg
    (hf.contDiffAt (hV.mem_nhds hyV)) hys hj hyw.1 hyw.2 (le_max_right C 0) hB
    fun i hi hyi l hl ↦ (hyC i hi hyi hyV l (hl.trans hj)).trans ?_).trans ?_
  · gcongr
    · exact pow_nonneg hyw.1 _
    · exact le_max_left C 0
  · have : (2 : ℝ) ^ j ≤ 2 ^ r := pow_le_pow_right₀ one_le_two hj
    have := hyw.1
    have : 0 ≤ max M 0 := le_max_right M 0
    gcongr

/-- If every `g i - f`, for `z ∈ U i`, has vanishing derivatives of order at most `j` at `z`,
for `j ≤ r`, then so has the glued map `∑ i ∈ s, ρ i • g i` minus `f`, at a point `z` where
`f` is `C^r` and near which the `ρ i` sum to `1`. -/
theorem iteratedFDeriv_sum_smul_sub_eq_zero (hU : ∀ i ∈ s, IsOpen (U i))
    (hρ : ∀ i ∈ s, ContDiff ℝ r (ρ i)) (hρU : ∀ i ∈ s, tsupport (ρ i) ⊆ U i)
    (hg : ∀ i ∈ s, ContDiffOn ℝ r (g i) (U i)) {z : E} (hf : ContDiffAt ℝ r f z)
    (hsum : ∀ᶠ y in 𝓝 z, ∑ i ∈ s, ρ i y = 1) {j : ℕ} (hj : j ≤ r)
    (hgz : ∀ i ∈ s, z ∈ U i → ∀ l ≤ j, iteratedFDeriv ℝ l (g i - f) z = 0) :
    iteratedFDeriv ℝ j ((fun y ↦ ∑ i ∈ s, ρ i y • g i y) - f) z = 0 := by
  have h := norm_iteratedFDeriv_sum_smul_sub_le (N := 0) (w := 0) (C := 0)
    (B := ∑ i ∈ s, jetNormAt ℝ j (ρ i) z) hU hρ hρU hg hf hsum hj le_rfl zero_le_one le_rfl
    (fun i hi l hl ↦ (norm_iteratedFDeriv_le_jetNormAt hl _ _).trans
      (Finset.single_le_sum (fun i _ ↦ jetNormAt_nonneg j (ρ i) z) hi))
    fun i hi hzi l hl ↦ by simp [hgz i hi hzi l hl]
  simpa using h

omit [NormedSpace ℝ E] in
/-- If every `g i`, for `z ∈ U i`, has the value of `f` at `z`, then so has the glued map
`∑ i ∈ s, ρ i • g i`, at a point `z` where the `ρ i` sum to `1`. -/
theorem sum_smul_apply_eq (hρU : ∀ i ∈ s, tsupport (ρ i) ⊆ U i) {z : E}
    (hsum : ∑ i ∈ s, ρ i z = 1) (hg₀ : ∀ i ∈ s, z ∈ U i → g i z = f z) :
    ∑ i ∈ s, ρ i z • g i z = f z := by
  calc ∑ i ∈ s, ρ i z • g i z = ∑ i ∈ s, ρ i z • f z := by
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        by_cases hzi : z ∈ U i
        · rw [hg₀ i hi hzi]
        · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hzi (hρU i hi h), zero_smul, zero_smul]
    _ = f z := by rw [← Finset.sum_smul, hsum, one_smul]

/-- If every `g i`, for `z ∈ U i`, has the value and the derivative of `f` at `z`, then the
glued map `∑ i ∈ s, ρ i • g i` has the derivative of `f` at `z`, at a point `z` where `f` is
`C^1` and near which the `ρ i` sum to `1`. -/
theorem fderiv_sum_smul_eq (hU : ∀ i ∈ s, IsOpen (U i))
    (hρ : ∀ i ∈ s, ContDiff ℝ 1 (ρ i)) (hρU : ∀ i ∈ s, tsupport (ρ i) ⊆ U i)
    (hg : ∀ i ∈ s, ContDiffOn ℝ 1 (g i) (U i)) {z : E} (hf : ContDiffAt ℝ 1 f z)
    (hsum : ∀ᶠ y in 𝓝 z, ∑ i ∈ s, ρ i y = 1)
    (hg₀ : ∀ i ∈ s, z ∈ U i → g i z = f z)
    (hg₁ : ∀ i ∈ s, z ∈ U i → fderiv ℝ (g i) z = fderiv ℝ f z) :
    fderiv ℝ (fun y ↦ ∑ i ∈ s, ρ i y • g i y) z = fderiv ℝ f z := by
  have hfz : DifferentiableAt ℝ f z := hf.differentiableAt one_ne_zero
  have hgz : ∀ i ∈ s, z ∈ U i → ∀ l ≤ 1, iteratedFDeriv ℝ l (g i - f) z = 0 := by
    intro i hi hzi l hl
    have hgi : DifferentiableAt ℝ (g i) z :=
      ((hg i hi).contDiffAt ((hU i hi).mem_nhds hzi)).differentiableAt one_ne_zero
    interval_cases l
    · rw [← norm_eq_zero, norm_iteratedFDeriv_zero, Pi.sub_apply, hg₀ i hi hzi, sub_self,
        norm_zero]
    · rw [← norm_eq_zero, norm_iteratedFDeriv_one, fderiv_sub hgi hfz, hg₁ i hi hzi, sub_self,
        norm_zero]
  have h₁ := iteratedFDeriv_sum_smul_sub_eq_zero hU hρ hρU hg hf hsum le_rfl hgz
  have hG : DifferentiableAt ℝ (fun y ↦ ∑ i ∈ s, ρ i y • g i y) z := by
    refine DifferentiableAt.fun_sum fun i hi ↦ ?_
    exact ((hg i hi).contDiff_smul_of_tsupport_subset (hU i hi) (hρ i hi).contDiffOn
      (hρU i hi)).differentiable one_ne_zero z
  rwa [← norm_eq_zero, norm_iteratedFDeriv_one, fderiv_sub hG hfz, norm_eq_zero,
    sub_eq_zero] at h₁

end SymplecticGeometry

end
