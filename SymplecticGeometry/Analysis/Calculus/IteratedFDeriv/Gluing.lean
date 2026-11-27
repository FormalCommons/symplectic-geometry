/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.NhdsSet

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Algebra.Support
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import SymplecticGeometry.Geometry.Manifold.PartitionOfUnity
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
  at `z`, then `G` has the derivative of `f` at `z`;
* `SymplecticGeometry.exists_contDiff_glue_of_norm_iteratedFDeriv_sub_le`: the global gluing
  along a closed set `S` that need not be compact. Maps `g i`, smooth on open sets `U i` that
  cover `S`, agreeing in value and derivative on `S` and pairwise to order `N + 1` near the
  compact subsets of `S`, glue to one smooth map with the same value and derivative on `S` that
  agrees with each `g i` to order `N + 1` near the compact subsets of `S ∩ U i`. The map is
  `∑ᶠ i, ρ i • g i` for a smooth partition of unity on a closed neighbourhood of `S`; near a
  compact set it is a finite sum, and a cutoff equal to `1` near the compact set confines the
  supports of the finitely many terms to where the pairwise bounds hold, so that
  `exists_norm_iteratedFDeriv_sum_smul_sub_le` applies.

These are the gluing steps of the proof of Proposition 5.55 of [CieliebakEliashberg2012], where
local maps that agree with each other to order `N + 1` along the real points are patched with a
partition of unity. The Leibniz bound is Tau Ceti's
`TauCeti.norm_iteratedFDeriv_smul_le_of_isOpen`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

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

section Global

/-! ### Gluing along a closed set with a partition of unity -/

variable [FiniteDimensional ℝ E]

/-- The bound step of `exists_contDiff_glue_of_norm_iteratedFDeriv_sub_le`, for the glued map of
a smooth partition of unity on a neighbourhood `s` of `S`. -/
private theorem exists_norm_iteratedFDeriv_finsum_smul_sub_le {S s : Set E}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) E s) (hρ : ρ.IsSubordinate U) (hSs : S ⊆ interior s)
    (hU : ∀ i, IsOpen (U i)) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
    {w : E → ℝ} (hw : Continuous w) (hw₀ : ∀ y, 0 ≤ w y) (hwS : ∀ y ∈ S, w y = 0) {N r : ℕ}
    (hpair : ∀ i j K, IsCompact K → K ⊆ S ∩ U i ∩ U j → ∃ C, ∀ᶠ y in 𝓝ˢ K, ∀ l ≤ r,
      ‖iteratedFDeriv ℝ l (g i - g j) y‖ ≤ C * w y ^ (N + 1 - l))
    (i₀ : ι) {K : Set E} (hK : IsCompact K) (hKS : K ⊆ S ∩ U i₀) :
    ∃ C, ∀ᶠ y in 𝓝ˢ K, ∀ l ≤ r, ‖iteratedFDeriv ℝ l
      ((fun y ↦ ∑ᶠ i, ρ i y • g i y) - g i₀) y‖ ≤ C * w y ^ (N + 1 - l) := by
  classical
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  obtain ⟨t, ht⟩ := ρ.exists_finset_finsum_smul_eq_sum_of_isCompact (F := F) hK'
  -- The pairwise bounds near the parts of `K` in the supports of the `ρ j`.
  have hpair' : ∀ j, ∃ C, ∀ᶠ y in 𝓝ˢ (K ∩ tsupport (ρ j)), ∀ l ≤ r,
      ‖iteratedFDeriv ℝ l (g j - g i₀) y‖ ≤ C * w y ^ (N + 1 - l) := fun j ↦
    hpair j i₀ _ (hK.inter_right (isClosed_tsupport _)) fun y hy ↦
      ⟨⟨(hKS hy.1).1, hρ j hy.2⟩, (hKS hy.1).2⟩
  choose C hC using hpair'
  set P : ι → Set E := fun j ↦ {y | ∀ l ≤ r,
    ‖iteratedFDeriv ℝ l (g j - g i₀) y‖ ≤ C j * w y ^ (N + 1 - l)}
  have hP : ∀ j, K ∩ tsupport (ρ j) ⊆ interior (P j) := fun j ↦
    subset_interior_iff_mem_nhdsSet.2 (hC j)
  -- An open neighbourhood of `K` on which every `ρ j`, `j ∈ t`, is supported where the
  -- pairwise bound holds.
  set O : Set E := interior K' ∩ interior s ∩ U i₀ ∩ {y | w y < 1} ∩
    ⋂ j ∈ t, (interior (P j) ∪ (tsupport (ρ j))ᶜ)
  have hO : IsOpen O := (((isOpen_interior.inter isOpen_interior).inter (hU i₀)).inter
    (isOpen_lt hw continuous_const)).inter (isOpen_biInter_finset fun j _ ↦
      isOpen_interior.union (isClosed_tsupport _).isOpen_compl)
  have hKO : K ⊆ O := fun y hy ↦ ⟨⟨⟨⟨hKK' hy, hSs (hKS hy).1⟩, (hKS hy).2⟩, by
    simp [hwS y (hKS hy).1]⟩, mem_iInter₂.2 fun j _ ↦ by
      by_cases hyj : y ∈ tsupport (ρ j)
      · exact Or.inl (hP j ⟨hy, hyj⟩)
      · exact Or.inr hyj⟩
  obtain ⟨ψ, hψ, -, hψ1, -, hψO⟩ := hK.exists_contDiff_cutoff hO hKO
  set Q : Set E := interior (ψ ⁻¹' {1}) ∩ O
  have hQ : IsOpen Q := isOpen_interior.inter hO
  have hKQ : K ⊆ Q := subset_inter hψ1 hKO
  have hQK' : ∀ y ∈ Q, y ∈ K' := fun y hy ↦ interior_subset hy.2.1.1.1.1
  have hQs : ∀ y ∈ Q, y ∈ s := fun y hy ↦ interior_subset hy.2.1.1.1.2
  have hQψ : ∀ y ∈ Q, ψ y = 1 := fun y hy ↦ interior_subset hy.1
  -- The cut-off partition `ψ * ρ j`, `j ∈ t`, glues the same map near `K`.
  have hsupp : ∀ j ∈ t, tsupport (fun y ↦ ψ y * ρ j y) ⊆ U j ∩ interior (P j) := by
    intro j hj y hy
    have hyO := hψO (tsupport_mul_subset_left hy)
    have hyj : y ∈ tsupport (ρ j) := tsupport_mul_subset_right hy
    refine ⟨hρ j hyj, ?_⟩
    rcases mem_iInter₂.1 hyO.2 j hj with h | h
    · exact h
    · exact absurd hyj h
  have hr : ((r : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  obtain ⟨C', hC'⟩ := exists_norm_iteratedFDeriv_sum_smul_sub_le (s := t) (N := N)
    (C := ∑ j ∈ t, max (C j) 0) (w := w) (ρ := fun j y ↦ ψ y * ρ j y)
    (U := fun j ↦ U j ∩ interior (P j)) (g := g) (f := g i₀) (V := U i₀)
    (fun j _ ↦ (hU j).inter isOpen_interior) (hU i₀)
    (fun j _ ↦ (hψ.mul (ρ j).contMDiff.contDiff).of_le hr) hsupp
    (fun j _ ↦ ((hg j).mono inter_subset_left).of_le hr) ((hg i₀).of_le hr) hK
    (mem_nhdsSet_iff_forall.2 fun y hy ↦ mem_of_superset (hQ.mem_nhds (hKQ hy))
      fun z hz ↦ by
        rw [mem_ofPred_eq, ← Finset.mul_sum, (ht z (hQK' z hz)).2 (hQs z hz), hQψ z hz, mul_one])
    (mem_nhdsSet_iff_forall.2 fun y hy ↦ mem_of_superset (hO.mem_nhds (hKO hy))
      fun z hz ↦ ⟨hw₀ z, hz.1.2.le⟩)
    (Eventually.of_forall fun y j hj hy _ l hl ↦ (interior_subset hy.2 l hl).trans
      (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans
        (Finset.single_le_sum (fun j _ ↦ le_max_right (C j) 0) hj)) (pow_nonneg (hw₀ y) _)))
  refine ⟨C', ?_⟩
  filter_upwards [hC', (hU i₀).mem_nhdsSet.2 fun y hy ↦ (hKS hy).2,
    hQ.mem_nhdsSet.2 hKQ] with y hy hyU hyQ l hl
  have heq : ((fun y ↦ ∑ᶠ i, ρ i y • g i y) - g i₀) =ᶠ[𝓝 y]
      ((fun y ↦ ∑ j ∈ t, (ψ y * ρ j y) • g j y) - g i₀) :=
    mem_of_superset (hQ.mem_nhds hyQ) fun z hz ↦ by
      simp only [mem_ofPred_eq, Pi.sub_apply, (ht z (hQK' z hz)).1 (g · z), hQψ z hz, one_mul]
  rw [(heq.iteratedFDeriv ℝ l).eq_of_nhds]
  exact hy hyU l hl

/-- **Gluing local maps that agree to order `N + 1` along a closed set.** Let `S` be a closed
subset of a finite-dimensional real space `E`, covered by open sets `U i`, and let `g i : E → F`
be smooth on `U i`. Let `w ≥ 0` be a continuous weight vanishing on `S`. Suppose that the `g i`
agree in value and derivative at the points of `S` where they are defined, and that near every
compact `K ⊆ S ∩ U i ∩ U j` the derivatives of order `l ≤ r` of `g i - g j` are bounded by a
constant times `w ^ (N + 1 - l)`. Then there is a smooth map `G : E → F` with the value and the
derivative of `g i` at each point of `S ∩ U i`, and such that near every compact
`K ⊆ S ∩ U i` the derivatives of order `l ≤ r` of `G - g i` have bounds of the same form. -/
theorem exists_contDiff_glue_of_norm_iteratedFDeriv_sub_le {S : Set E} (hS : IsClosed S)
    (hU : ∀ i, IsOpen (U i)) (hSU : S ⊆ ⋃ i, U i) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
    (hgS : ∀ i j, ∀ z ∈ S ∩ U i ∩ U j, g i z = g j z ∧ fderiv ℝ (g i) z = fderiv ℝ (g j) z)
    {w : E → ℝ} (hw : Continuous w) (hw₀ : ∀ y, 0 ≤ w y) (hwS : ∀ y ∈ S, w y = 0) {N r : ℕ}
    (hpair : ∀ i j K, IsCompact K → K ⊆ S ∩ U i ∩ U j → ∃ C, ∀ᶠ y in 𝓝ˢ K, ∀ l ≤ r,
      ‖iteratedFDeriv ℝ l (g i - g j) y‖ ≤ C * w y ^ (N + 1 - l)) :
    ∃ G : E → F, ContDiff ℝ ∞ G ∧
      (∀ i, ∀ z ∈ S ∩ U i, G z = g i z ∧ fderiv ℝ G z = fderiv ℝ (g i) z) ∧
      ∀ i K, IsCompact K → K ⊆ S ∩ U i → ∃ C, ∀ᶠ y in 𝓝ˢ K, ∀ l ≤ r,
        ‖iteratedFDeriv ℝ l (G - g i) y‖ ≤ C * w y ^ (N + 1 - l) := by
  -- A smooth partition of unity on a closed neighbourhood of `S` inside `⋃ i, U i`.
  obtain ⟨u, hu, hSu, hus⟩ := normal_exists_closure_subset hS (isOpen_iUnion hU) hSU
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_closure U hU
    hus
  have hSs : S ⊆ interior (closure u) := hSu.trans (hu.subset_interior_iff.2 subset_closure)
  refine ⟨fun y ↦ ∑ᶠ i, ρ i y • g i y, ?_, fun i z hz ↦ ?_,
    fun i K hK hKS ↦ exists_norm_iteratedFDeriv_finsum_smul_sub_le ρ hρ hSs hU hg hw hw₀ hwS
      hpair i hK hKS⟩
  · refine contMDiff_iff_contDiff.1 (ρ.contMDiff_finsum_smul (n := ⊤) fun i y hy ↦ ?_)
    exact ((hg i).contDiffAt ((hU i).mem_nhds (hρ i hy))).contMDiffAt
  -- Near `z`, the glued map is a finite sum.
  obtain ⟨K', hK', hzK'⟩ := exists_compact_mem_nhds z
  obtain ⟨t, ht⟩ := ρ.exists_finset_finsum_smul_eq_sum_of_isCompact (F := F) hK'
  have hn : K' ∩ interior (closure u) ∈ 𝓝 z :=
    inter_mem hzK' (isOpen_interior.mem_nhds (hSs hz.1))
  have heq : (fun y ↦ ∑ᶠ i, ρ i y • g i y) =ᶠ[𝓝 z] fun y ↦ ∑ j ∈ t, ρ j y • g j y :=
    mem_of_superset hn fun y hy ↦ (ht y hy.1).1 (g · y)
  have hsum : ∀ᶠ y in 𝓝 z, ∑ j ∈ t, ρ j y = 1 :=
    mem_of_superset hn fun y hy ↦ (ht y hy.1).2 (interior_subset hy.2)
  have hgi : ContDiffAt ℝ ∞ (g i) z := (hg i).contDiffAt ((hU i).mem_nhds hz.2)
  have h1 : ((1 : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hagree : ∀ j ∈ t, z ∈ U j → g j z = g i z ∧ fderiv ℝ (g j) z = fderiv ℝ (g i) z :=
    fun j _ hzj ↦ hgS j i z ⟨⟨hz.1, hzj⟩, hz.2⟩
  refine ⟨?_, ?_⟩
  · exact heq.eq_of_nhds.trans <| sum_smul_apply_eq (fun j _ ↦ hρ j) hsum.self_of_nhds
      fun j hj hzj ↦ (hagree j hj hzj).1
  · rw [heq.fderiv_eq]
    exact fderiv_sum_smul_eq (fun j _ ↦ hU j) (fun j _ ↦ (ρ j).contMDiff.contDiff.of_le h1)
      (fun j _ ↦ hρ j) (fun j _ ↦ (hg j).of_le h1) (hgi.of_le h1) hsum
      (fun j hj hzj ↦ (hagree j hj hzj).1) fun j hj hzj ↦ (hagree j hj hzj).2

end Global

end SymplecticGeometry

end
