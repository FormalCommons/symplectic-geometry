/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SymplecticGeometry.Analysis.Calculus.ContDiff.FTaylorSeries
public import SymplecticGeometry.Analysis.Normed.Group.FunctionSeries
public import SymplecticGeometry.Analysis.Sobolev.Trace.Reflection.Seeley

/-!
# Seeley's extension

Seeley's operator extends a function on `[0, ∞)` to `ℝ`: for `t < 0` it takes the value
`∑ₖ aₖ χ (-2 ^ k t) f (-2 ^ k t)`, where `aₖ` is Tau Ceti's
`TauCeti.HalfSpaceExtension.seeleyCoeff k` and `χ = seeleyCutoff` is a smooth
cutoff equal to `1` on `(-∞, 1/2]` and to `0` on `[3/4, ∞)`. For each `t < 0` only finitely many
terms are nonzero, and only values of `f` on `(0, 3/4)` enter, so the operator is linear and
commutes with every linear map. Applying it at both ends of `[0, 1]`, the second time after the
reflection `t ↦ 1 - t`, extends functions on `[0, 1]`. Both operators are bundled as `ℝ`-linear
maps on `ℝ → F`, `seeleyExtendLinearMap` and `seeleyIccExtendLinearMap`.

The main results say that the extension of a family `f (·, x)` that is smooth on
`Ici 0 ×ˢ U` (respectively `Icc 0 1 ×ˢ U`) is smooth on `univ ×ˢ U`, where `U` is an open set
of a normed space or, more generally, the intersection `C ∩ O` of a convex set `C` with unique
differentials and an open set `O`, such as the range of a model with corners cut by an open set.
The proof needs only that each point of `U` has convex neighbourhoods in `U`, and that `U` has
unique differentials, so that Taylor series within `Ici 0 ×ˢ U` are determined. No completeness
of the target space is needed, unlike for Tau Ceti's
`TauCeti.HalfSpaceExtension.seeleyExtension` on all of `ℝ × E`, whose cutoff is also different.

The proof follows Tau Ceti's `TauCeti.HalfSpaceExtension.contDiff_halfSpaceReflection`, with
Seeley's infinite sum in place of Hestenes' finite one: the Taylor series of the terms
`aₖ (χ f) (timeScale (-2 ^ k) z)` on the lower half are bounded by `|aₖ| (2 ^ k) ^ m` times a
local bound of the derivatives of `χ f`, so by Tau Ceti's `summable_abs_seeleyCoeff_mul_pow` their
sums converge locally uniformly (`HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn_of_convex`);
at `t = 0` the moment identities `hasSum_seeleyCoeff_smul_compContinuousLinearMap_timeScale`, from
`tsum_seeleyCoeff_mul_neg_pow` and `map_timeScale_eq_sum_pow_card_smul`, make the limit series
agree with that of `f`, as Tau Ceti's
`sum_higherReflectionCoeff_smul_compContinuousLinearMap_timeScale` does for a finite sum; and the
two series glue across `t = 0` by `HasFTaylorSeriesUpToOn.union`. The uniform convergence uses
`tendstoUniformlyOn_finsetSum_of_hasSum`, which needs no completeness.

## Main definitions

* `SymplecticGeometry.seeleyCutoff`: the cutoff `χ`.
* `SymplecticGeometry.seeleyExtend`: Seeley's extension from `[0, ∞)`.
* `SymplecticGeometry.seeleyIccExtend`: Seeley's extension from `[0, 1]`.

## Main results

* `SymplecticGeometry.contDiffOn_seeleyExtend`, `SymplecticGeometry.contDiffOn_seeleyIccExtend`:
  the extensions of smooth families are smooth.
* `SymplecticGeometry.contDiffOn_seeleyExtend_of_convex`,
  `SymplecticGeometry.contDiffOn_seeleyIccExtend_of_convex`: the same for parameters in `C ∩ O`.
* `SymplecticGeometry.contDiff_seeleyExtend`: the extension of a function smooth on `[0, ∞)` is
  smooth.
* `SymplecticGeometry.exists_contDiffOn_eqOn_Icc_prod`: a family smooth on `Icc a b ×ˢ U` agrees
  there with one smooth on `univ ×ˢ U`.
* `SymplecticGeometry.exists_contDiff_eqOn_of_contDiffOn_halfSpace`: a function smooth on a
  relatively open part of the half-space `0 ≤ t` of `ℝ × E` agrees near a boundary point with one
  smooth on `ℝ × E`; the `C^∞` counterpart of Tau Ceti's finite-order
  `TauCeti.HalfSpaceExtension.exists_local_contDiff_extension_halfSpace`.

## References

* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

public section

open Set Filter
open scoped Topology ContDiff

namespace SymplecticGeometry

open TauCeti.HalfSpaceExtension

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### The cutoff -/

/-- The smooth cutoff of Seeley's extension: `1` on `(-∞, 1/2]` and `0` on `[3/4, ∞)`. -/
noncomputable def seeleyCutoff (s : ℝ) : ℝ :=
  Real.smoothTransition (3 - 4 * s)

theorem seeleyCutoff_def (s : ℝ) : seeleyCutoff s = Real.smoothTransition (3 - 4 * s) := (rfl)

/-- The cutoff is `1` up to `1/2`. -/
theorem seeleyCutoff_eq_one_of_le {s : ℝ} (hs : s ≤ 1 / 2) : seeleyCutoff s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The cutoff is `0` from `3/4` on. -/
theorem seeleyCutoff_eq_zero_of_le {s : ℝ} (hs : 3 / 4 ≤ s) : seeleyCutoff s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The cutoff is smooth. -/
theorem contDiff_seeleyCutoff : ContDiff ℝ ∞ seeleyCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))

/-! ### The extension -/

/-- Seeley's extension of `f` from `[0, ∞)` to `ℝ`: `f t` for `t ≥ 0`, and
`∑ₖ aₖ χ (-2 ^ k t) f (-2 ^ k t)` for `t < 0`. Only the values of `f` on `[0, 1]` enter the
second case. -/
noncomputable def seeleyExtend (f : ℝ → F) (t : ℝ) : F :=
  if 0 ≤ t then f t
  else ∑' k, seeleyCoeff k • seeleyCutoff (-2 ^ k * t) • f (-2 ^ k * t)

theorem seeleyExtend_def (f : ℝ → F) (t : ℝ) :
    seeleyExtend f t = if 0 ≤ t then f t
      else ∑' k, seeleyCoeff k • seeleyCutoff (-2 ^ k * t) • f (-2 ^ k * t) := (rfl)

@[simp]
theorem seeleyExtend_of_nonneg (f : ℝ → F) {t : ℝ} (ht : 0 ≤ t) : seeleyExtend f t = f t := by
  simp [seeleyExtend_def, ht]

@[simp]
theorem seeleyExtend_of_neg (f : ℝ → F) {t : ℝ} (ht : t < 0) :
    seeleyExtend f t = ∑' k, seeleyCoeff k • seeleyCutoff (-2 ^ k * t) • f (-2 ^ k * t) := by
  simp [seeleyExtend_def, not_le.mpr ht]

/-- For `t < 0` the dilated times `-2 ^ k t` eventually exceed any bound. -/
private theorem exists_forall_lt_neg_two_pow_mul {t : ℝ} (ht : t < 0) (c : ℝ) :
    ∃ N : ℕ, ∀ k, N ≤ k → c < -2 ^ k * t := by
  have h : Tendsto (fun k : ℕ ↦ (2 : ℝ) ^ k * -t) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const (neg_pos.2 ht)
  simpa using (h.eventually_gt_atTop c).exists_forall_of_atTop

/-- For `t < 0`, the cutoff vanishes at `-2 ^ k t` for all large `k`. -/
theorem exists_seeleyCutoff_eq_zero {t : ℝ} (ht : t < 0) :
    ∃ N : ℕ, ∀ k, N ≤ k → seeleyCutoff (-2 ^ k * t) = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_lt_neg_two_pow_mul ht (3 / 4)
  exact ⟨N, fun k hk ↦ seeleyCutoff_eq_zero_of_le (hN k hk).le⟩

/-- For `t < 0`, Seeley's sum is the finite sum up to any `N` from which on the cutoff vanishes
at `-2 ^ k t`. -/
theorem seeleyExtend_eq_sum (f : ℝ → F) {t : ℝ} (ht : t < 0) {N : ℕ}
    (hN : ∀ k, N ≤ k → seeleyCutoff (-2 ^ k * t) = 0) :
    seeleyExtend f t =
      ∑ k ∈ Finset.range N, seeleyCoeff k • seeleyCutoff (-2 ^ k * t) • f (-2 ^ k * t) := by
  rw [seeleyExtend_of_neg f ht]
  refine tsum_eq_sum fun k hk ↦ ?_
  rw [hN k (by simpa using hk), zero_smul, smul_zero]

/-- For `t < 0`, Seeley's sum depends only on the values of `f` on `(0, 1)`. -/
theorem seeleyExtend_congr_of_neg {f g : ℝ → F} (hfg : EqOn f g (Ioo 0 1)) {t : ℝ}
    (ht : t < 0) : seeleyExtend f t = seeleyExtend g t := by
  obtain ⟨N, hN⟩ := exists_seeleyCutoff_eq_zero ht
  rw [seeleyExtend_eq_sum f ht hN, seeleyExtend_eq_sum g ht hN]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : -2 ^ k * t < 3 / 4
  · rw [hfg ⟨by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) k], by linarith⟩]
  · rw [seeleyCutoff_eq_zero_of_le (not_lt.mp hk), zero_smul, zero_smul]

theorem seeleyExtend_congr {f g : ℝ → F} (h : EqOn f g (Ici 0)) :
    seeleyExtend f = seeleyExtend g := by
  funext t
  rcases le_or_gt 0 t with ht | ht
  · rw [seeleyExtend_of_nonneg _ ht, seeleyExtend_of_nonneg _ ht, h ht]
  · exact seeleyExtend_congr_of_neg (h.mono fun _ hs ↦ le_of_lt hs.1) ht

theorem seeleyExtend_add (f g : ℝ → F) :
    seeleyExtend (f + g) = seeleyExtend f + seeleyExtend g := by
  funext t
  rcases le_or_gt 0 t with ht | ht
  · simp [seeleyExtend_of_nonneg _ ht]
  · obtain ⟨N, hN⟩ := exists_seeleyCutoff_eq_zero ht
    simp only [Pi.add_apply, seeleyExtend_eq_sum _ ht hN, smul_add, Finset.sum_add_distrib]

theorem seeleyExtend_smul (c : ℝ) (f : ℝ → F) :
    seeleyExtend (c • f) = c • seeleyExtend f := by
  funext t
  rcases le_or_gt 0 t with ht | ht
  · simp [seeleyExtend_of_nonneg _ ht]
  · obtain ⟨N, hN⟩ := exists_seeleyCutoff_eq_zero ht
    simp only [Pi.smul_apply, seeleyExtend_eq_sum _ ht hN, Finset.smul_sum, smul_comm c]

variable (F) in
/-- Seeley's extension `seeleyExtend`, as an `ℝ`-linear map on functions `ℝ → F`. -/
noncomputable def seeleyExtendLinearMap : (ℝ → F) →ₗ[ℝ] (ℝ → F) where
  toFun := seeleyExtend
  map_add' := seeleyExtend_add
  map_smul' := seeleyExtend_smul

@[simp]
theorem coe_seeleyExtendLinearMap : ⇑(seeleyExtendLinearMap F) = seeleyExtend := (rfl)

@[simp]
theorem seeleyExtend_zero : seeleyExtend (0 : ℝ → F) = 0 := by
  rw [← coe_seeleyExtendLinearMap, map_zero]

/-- Seeley's extension commutes with linear maps. -/
theorem _root_.LinearMap.map_seeleyExtend (L : F →ₗ[ℝ] G) (f : ℝ → F) (t : ℝ) :
    L (seeleyExtend f t) = seeleyExtend (L ∘ f) t := by
  rcases le_or_gt 0 t with ht | ht
  · simp [seeleyExtend_of_nonneg _ ht]
  · obtain ⟨N, hN⟩ := exists_seeleyCutoff_eq_zero ht
    simp only [seeleyExtend_eq_sum _ ht hN, map_sum, map_smul, Function.comp_apply]

/-- Seeley's extension of `f` from `[0, 1]` to `ℝ`: `seeleyExtend f` for `t ≤ 1/2`, and the
extension of `s ↦ f (1 - s)` at `1 - t` for `t > 1/2`. -/
noncomputable def seeleyIccExtend (f : ℝ → F) (t : ℝ) : F :=
  if t ≤ 1 / 2 then seeleyExtend f t else seeleyExtend (fun s ↦ f (1 - s)) (1 - t)

theorem seeleyIccExtend_def (f : ℝ → F) (t : ℝ) :
    seeleyIccExtend f t =
      if t ≤ 1 / 2 then seeleyExtend f t else seeleyExtend (fun s ↦ f (1 - s)) (1 - t) := (rfl)

@[simp]
theorem seeleyIccExtend_of_mem (f : ℝ → F) {t : ℝ} (h : t ∈ Icc 0 1) :
    seeleyIccExtend f t = f t := by
  rw [seeleyIccExtend_def]
  split_ifs with ht
  · exact seeleyExtend_of_nonneg f h.1
  · rw [seeleyExtend_of_nonneg _ (by linarith [h.2]), sub_sub_cancel]

/-- For `t < 1`, `seeleyIccExtend f t = seeleyExtend f t`. -/
theorem seeleyIccExtend_of_lt_one (f : ℝ → F) {t : ℝ} (ht : t < 1) :
    seeleyIccExtend f t = seeleyExtend f t := by
  rw [seeleyIccExtend_def]
  split_ifs with h
  · rfl
  · rw [seeleyExtend_of_nonneg _ (by linarith), seeleyExtend_of_nonneg _ (by linarith),
      sub_sub_cancel]

/-- For `t > 0`, `seeleyIccExtend f t` is the extension of `s ↦ f (1 - s)` at `1 - t`. -/
theorem seeleyIccExtend_of_pos (f : ℝ → F) {t : ℝ} (ht : 0 < t) :
    seeleyIccExtend f t = seeleyExtend (fun s ↦ f (1 - s)) (1 - t) := by
  rw [seeleyIccExtend_def]
  split_ifs with h
  · rw [seeleyExtend_of_nonneg _ ht.le, seeleyExtend_of_nonneg _ (by linarith), sub_sub_cancel]
  · rfl

theorem seeleyIccExtend_congr {f g : ℝ → F} (h : EqOn f g (Icc 0 1)) :
    seeleyIccExtend f = seeleyIccExtend g := by
  have h' : EqOn (fun s ↦ f (1 - s)) (fun s ↦ g (1 - s)) (Icc 0 1) :=
    fun s hs ↦ h ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hext {f g : ℝ → F} (h : EqOn f g (Icc 0 1)) {t : ℝ} (ht : t ≤ 1) :
      seeleyExtend f t = seeleyExtend g t := by
    rcases le_or_gt 0 t with h0 | h0
    · rw [seeleyExtend_of_nonneg _ h0, seeleyExtend_of_nonneg _ h0, h ⟨h0, ht⟩]
    · exact seeleyExtend_congr_of_neg (h.mono Ioo_subset_Icc_self) h0
  funext t
  rw [seeleyIccExtend_def, seeleyIccExtend_def]
  split_ifs with ht
  · exact hext h (by linarith)
  · exact hext h' (by linarith)

theorem seeleyIccExtend_add (f g : ℝ → F) :
    seeleyIccExtend (f + g) = seeleyIccExtend f + seeleyIccExtend g := by
  funext t
  simp only [seeleyIccExtend_def, Pi.add_apply]
  split_ifs
  · exact congrFun (seeleyExtend_add f g) t
  · exact congrFun (seeleyExtend_add (fun s ↦ f (1 - s)) (fun s ↦ g (1 - s))) (1 - t)

theorem seeleyIccExtend_smul (c : ℝ) (f : ℝ → F) :
    seeleyIccExtend (c • f) = c • seeleyIccExtend f := by
  funext t
  simp only [seeleyIccExtend_def, Pi.smul_apply]
  split_ifs
  · exact congrFun (seeleyExtend_smul c f) t
  · exact congrFun (seeleyExtend_smul c (fun s ↦ f (1 - s))) (1 - t)

variable (F) in
/-- Seeley's extension from `[0, 1]`, `seeleyIccExtend`, as an `ℝ`-linear map on functions
`ℝ → F`. -/
noncomputable def seeleyIccExtendLinearMap : (ℝ → F) →ₗ[ℝ] (ℝ → F) where
  toFun := seeleyIccExtend
  map_add' := seeleyIccExtend_add
  map_smul' := seeleyIccExtend_smul

@[simp]
theorem coe_seeleyIccExtendLinearMap : ⇑(seeleyIccExtendLinearMap F) = seeleyIccExtend := (rfl)

@[simp]
theorem seeleyIccExtend_zero : seeleyIccExtend (0 : ℝ → F) = 0 := by
  rw [← coe_seeleyIccExtendLinearMap, map_zero]

/-- Seeley's extension from `[0, 1]` commutes with linear maps. -/
theorem _root_.LinearMap.map_seeleyIccExtend (L : F →ₗ[ℝ] G) (f : ℝ → F) (t : ℝ) :
    L (seeleyIccExtend f t) = seeleyIccExtend (L ∘ f) t := by
  simp only [seeleyIccExtend_def]
  split_ifs
  · exact L.map_seeleyExtend f t
  · exact L.map_seeleyExtend (fun s ↦ f (1 - s)) (1 - t)

/-! ### Smoothness -/

section Smooth

variable {C O : Set E} {h : ℝ × E → F}

/-- A sequence whose terms at a point of negative time vanish once the dilated time exceeds `1`
has finite support, so it is summable. -/
private theorem summable_of_fst_neg {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    {z : ℝ × E} (hz : z.1 < 0) {c : ℕ → X}
    (hc : ∀ k, 1 < (timeScale (E := E) (-2 ^ k) z).1 → c k = 0) : Summable c := by
  obtain ⟨N, hN⟩ := exists_forall_lt_neg_two_pow_mul hz 1
  refine summable_of_ne_finset_zero (s := Finset.range N) fun k hk ↦ hc k ?_
  simpa using hN k (by simpa using hk)

/-- If `h` vanishes for times at least `1`, so does its Taylor series for times beyond `1`. -/
private theorem ftaylorSeriesWithin_eq_zero (h1 : ∀ z : ℝ × E, 1 ≤ z.1 → h z = 0)
    {s : Set (ℝ × E)} {z : ℝ × E} (hz : 1 < z.1) (m : ℕ) :
    ftaylorSeriesWithin ℝ h s z m = 0 := by
  have hev : h =ᶠ[𝓝[s] z] (0 : ℝ × E → F) := eventually_nhdsWithin_of_eventually_nhds <|
    eventually_of_mem ((isOpen_lt continuous_const continuous_fst).mem_nhds hz)
      fun y hy ↦ h1 y (le_of_lt hy)
  simp only [ftaylorSeriesWithin]
  rw [hev.iteratedFDerivWithin_eq (h1 z hz.le), iteratedFDerivWithin_zero, Pi.zero_apply]

/-- The Taylor coefficients of `h` of each order are bounded on `Ici 0 ×ˢ (C ∩ ball x₀ r)` for
some `r` with `ball x₀ r ⊆ O`, when `h` vanishes for times at least `1`. -/
private theorem exists_bound_ftaylorSeriesWithin (hC : UniqueDiffOn ℝ C) (hO : IsOpen O)
    (hh : ContDiffOn ℝ ∞ h (Ici 0 ×ˢ (C ∩ O))) (h1 : ∀ z : ℝ × E, 1 ≤ z.1 → h z = 0) (m : ℕ)
    {x₀ : E} (hx₀ : x₀ ∈ C ∩ O) :
    ∃ r > 0, ∃ M, 0 ≤ M ∧ Metric.ball x₀ r ⊆ O ∧ ∀ z : ℝ × E, 0 ≤ z.1 → z.2 ∈ C →
      z.2 ∈ Metric.ball x₀ r → ‖ftaylorSeriesWithin ℝ h (Ici 0 ×ˢ (C ∩ O)) z m‖ ≤ M := by
  set p := ftaylorSeriesWithin ℝ h (Ici 0 ×ˢ (C ∩ O)) with hp_def
  have hc : ContinuousOn (fun z ↦ p z m) (Ici 0 ×ˢ (C ∩ O)) :=
    (hh.ftaylorSeriesWithin ((uniqueDiffOn_Ici 0).prod (hC.inter hO))).cont m
      (by exact_mod_cast le_top)
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ {x₀}) := isCompact_Icc.prod isCompact_singleton
  have hKs : Icc (0 : ℝ) 1 ×ˢ {x₀} ⊆ Ici 0 ×ˢ (C ∩ O) :=
    prod_mono Icc_subset_Ici_self (singleton_subset_iff.mpr hx₀)
  obtain ⟨K, hKb⟩ := hK.exists_bound_of_continuousOn (hc.mono hKs)
  obtain ⟨u, hu, hpre⟩ := continuousOn_iff'.1 hc {A | ‖A‖ < K + 1}
    (isOpen_lt continuous_norm continuous_const)
  have hKu : Icc (0 : ℝ) 1 ×ˢ {x₀} ⊆ u := fun z hz ↦ by
    have hz' : z ∈ (fun z ↦ p z m) ⁻¹' {A | ‖A‖ < K + 1} ∩ Ici 0 ×ˢ (C ∩ O) :=
      ⟨(hKb z hz).trans_lt (lt_add_one K), hKs hz⟩
    rw [hpre] at hz'
    exact hz'.1
  obtain ⟨V, W, -, hW, hV, hW₀, hVW⟩ := generalized_tube_lemma isCompact_Icc isCompact_singleton
    hu hKu
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 (hW.inter hO) x₀ ⟨hW₀ rfl, hx₀.2⟩
  refine ⟨r, hr, max (K + 1) 0, le_max_right _ _, fun x hx ↦ (hrW hx).2,
    fun z hz₀ hzC hz ↦ ?_⟩
  rcases le_or_gt z.1 1 with hz₁ | hz₁
  · have hzu : z ∈ u ∩ Ici 0 ×ˢ (C ∩ O) :=
      ⟨hVW ⟨hV ⟨hz₀, hz₁⟩, (hrW hz).1⟩, hz₀, hzC, (hrW hz).2⟩
    rw [← hpre] at hzu
    exact hzu.1.le.trans (le_max_left _ _)
  · rw [hp_def, ftaylorSeriesWithin_eq_zero h1 hz₁, norm_zero]
    exact le_max_right _ _

/-- Seeley's sum `∑ₖ aₖ h (timeScale (-2 ^ k) z)` has, on the lower half of `univ ×ˢ (C ∩ O)`,
the Taylor series whose coefficients are the corresponding sums of the dilated coefficients of
`h`. -/
private theorem hasFTaylorSeriesUpToOn_seeleySum (hCc : Convex ℝ C) (hC : UniqueDiffOn ℝ C)
    (hO : IsOpen O) (hh : ContDiffOn ℝ ∞ h (Ici 0 ×ˢ (C ∩ O)))
    (h1 : ∀ z : ℝ × E, 1 ≤ z.1 → h z = 0) :
    HasFTaylorSeriesUpToOn ∞ (fun z ↦ ∑' k, seeleyCoeff k • h (timeScale (-2 ^ k) z))
      (fun z m ↦ ∑' k, seeleyCoeff k •
        (ftaylorSeriesWithin ℝ h (Ici 0 ×ˢ (C ∩ O)) (timeScale (-2 ^ k) z)
          m).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k))
      (Iic 0 ×ˢ (C ∩ O)) := by
  set p := ftaylorSeriesWithin ℝ h (Ici 0 ×ˢ (C ∩ O)) with hp_def
  have hp : HasFTaylorSeriesUpToOn ∞ h p (Ici 0 ×ˢ (C ∩ O)) :=
    hh.ftaylorSeriesWithin ((uniqueDiffOn_Ici 0).prod (hC.inter hO))
  have hval {z : ℝ × E} (hz : z ∈ Iic 0 ×ˢ (C ∩ O)) :
      Summable fun k ↦ seeleyCoeff k • h (timeScale (-2 ^ k) z) := by
    rcases hz.1.lt_or_eq with hz₀ | hz₀
    · exact summable_of_fst_neg hz₀ fun k hk ↦ by rw [h1 _ hk.le, smul_zero]
    · exact (hasSum_seeleyCoeff_smul_timeScale_of_fst_eq_zero h hz₀).summable
  have hcoef (m : ℕ) {z : ℝ × E} (hz : z ∈ Iic 0 ×ˢ (C ∩ O)) :
      Summable fun k ↦ seeleyCoeff k •
        (p (timeScale (-2 ^ k) z) m).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k) := by
    rcases hz.1.lt_or_eq with hz₀ | hz₀
    · refine summable_of_fst_neg hz₀ fun k hk ↦ ?_
      rw [hp_def, ftaylorSeriesWithin_eq_zero h1 hk]
      ext v
      simp
    · exact (hasSum_seeleyCoeff_smul_compContinuousLinearMap_timeScale_of_fst_eq_zero p hz₀
        m).summable
  have hnhds {z : ℝ × E} {r : ℝ} (hr : 0 < r) :
      Iic 0 ×ˢ (C ∩ Metric.ball z.2 r) ∈ 𝓝[Iic 0 ×ˢ (C ∩ O)] z :=
    mem_nhdsWithin.2 ⟨univ ×ˢ Metric.ball z.2 r, isOpen_univ.prod Metric.isOpen_ball,
      ⟨trivial, Metric.mem_ball_self hr⟩, fun y hy ↦ ⟨hy.2.1, hy.2.2.1, hy.1.2⟩⟩
  refine HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn_of_convex (l := atTop)
    (fᵢ := fun S z ↦ ∑ k ∈ S, seeleyCoeff k • h (timeScale (-2 ^ k) z))
    (qᵢ := fun S z m ↦ ∑ k ∈ S, seeleyCoeff k •
      (p (timeScale (-2 ^ k) z) m).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k))
    (fun z hz ↦ ?_) (fun S ↦ ?_) (fun m _ ↦ ?_) (fun z hz ↦ (hval hz).hasSum)
  · obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO z.2 hz.2.2
    exact ⟨Iic 0 ×ˢ (C ∩ Metric.ball z.2 r),
      prod_mono subset_rfl (inter_subset_inter_right _ hrO),
      (convex_Iic 0).prod (hCc.inter (convex_ball _ _)), hnhds hr⟩
  · exact HasFTaylorSeriesUpToOn.sum fun k _ ↦
      ((hp.compContinuousLinearMap (timeScale (-2 ^ k))).const_smul (seeleyCoeff k)).mono
        fun z hz ↦ ⟨mem_upperHalfSpace.1 (timeScale_neg_two_pow_mem_upperHalfSpace k hz.1),
          by simpa using hz.2⟩
  · refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun z hz ↦ ?_
    obtain ⟨r, hr, M, hM₀, hrO, hM⟩ := exists_bound_ftaylorSeriesWithin hC hO hh h1 m hz.2
    refine ⟨_, hnhds hr, tendstoUniformlyOn_finsetSum_of_hasSum
      (fun y hy ↦ (hcoef m ⟨hy.1, hy.2.1, hrO hy.2.2⟩).hasSum)
      ((summable_abs_seeleyCoeff_mul_pow m).mul_right M) fun k y hy ↦ ?_⟩
    have hτ : ‖timeScale (E := E) (-2 ^ k)‖ ≤ 2 ^ k := by
      refine (norm_timeScale_le _).trans_eq ?_
      rw [abs_neg, abs_pow, abs_two, max_eq_left (one_le_pow₀ one_le_two)]
    have hy' := mem_upperHalfSpace.1 (timeScale_neg_two_pow_mem_upperHalfSpace (E := E) k hy.1)
    calc _ = |seeleyCoeff k| * ‖(p (timeScale (-2 ^ k) y) m).compContinuousLinearMap
          fun _ ↦ timeScale (E := E) (-2 ^ k)‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |seeleyCoeff k| * (M * ∏ _i : Fin m, (2 : ℝ) ^ k) := by
        gcongr
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        gcongr with i
        exact hM _ hy' (by simpa using hy.2.1) (by simpa using hy.2.2)
      _ = |seeleyCoeff k| * ((2 : ℝ) ^ k) ^ m * M := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- The function equal to `h` for nonnegative times and to Seeley's sum of `h` for negative
times is smooth on `univ ×ˢ (C ∩ O)`. -/
private theorem contDiffOn_seeleyGlue (hCc : Convex ℝ C) (hC : UniqueDiffOn ℝ C) (hO : IsOpen O)
    (hh : ContDiffOn ℝ ∞ h (Ici 0 ×ˢ (C ∩ O))) (h1 : ∀ z : ℝ × E, 1 ≤ z.1 → h z = 0) :
    ContDiffOn ℝ ∞ (fun z ↦ if 0 ≤ z.1 then h z
      else ∑' k, seeleyCoeff k • h (timeScale (-2 ^ k) z)) (univ ×ˢ (C ∩ O)) := by
  set p := ftaylorSeriesWithin ℝ h (Ici 0 ×ˢ (C ∩ O))
  have hp : HasFTaylorSeriesUpToOn ∞ h p (Ici 0 ×ˢ (C ∩ O)) :=
    hh.ftaylorSeriesWithin ((uniqueDiffOn_Ici 0).prod (hC.inter hO))
  have hq := hasFTaylorSeriesUpToOn_seeleySum hCc hC hO hh h1
  let r : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) F := fun z m ↦ if 0 ≤ z.1 then p z m
    else ∑' k, seeleyCoeff k • (p (timeScale (-2 ^ k) z) m).compContinuousLinearMap
      (fun _ ↦ timeScale (-2 ^ k))
  have hs : HasFTaylorSeriesUpToOn ∞ (fun z ↦ if 0 ≤ z.1 then h z
      else ∑' k, seeleyCoeff k • h (timeScale (-2 ^ k) z)) r (Ici 0 ×ˢ (C ∩ O)) :=
    (hp.congr fun z hz ↦ by simp only [mem_Ici.mp hz.1, ↓reduceIte]).congr_series
      fun m _ z hz ↦ by simp only [r, mem_Ici.mp hz.1, ↓reduceIte]
  have ht : HasFTaylorSeriesUpToOn ∞ (fun z ↦ if 0 ≤ z.1 then h z
      else ∑' k, seeleyCoeff k • h (timeScale (-2 ^ k) z)) r (Iic 0 ×ˢ (C ∩ O)) := by
    refine (hq.congr fun z hz ↦ ?_).congr_series fun m _ z hz ↦ ?_
    · split_ifs with h0
      · exact (hasSum_seeleyCoeff_smul_timeScale_of_fst_eq_zero h
          (le_antisymm hz.1 h0)).tsum_eq.symm
      · rfl
    · simp only [r]
      split_ifs with h0
      · exact (hasSum_seeleyCoeff_smul_compContinuousLinearMap_timeScale_of_fst_eq_zero p
          (le_antisymm hz.1 h0) m).tsum_eq
      · rfl
  have hcl {a : Set ℝ} (ha : IsClosed a) : closure (a ×ˢ (C ∩ O)) ⊆ a ×ˢ univ :=
    closure_minimal (prod_mono subset_rfl (subset_univ _)) (ha.prod isClosed_univ)
  have hunion := hs.union ht (fun z hz ↦ ⟨(hcl isClosed_Ici hz.1).1, hz.2.2⟩)
    (fun z hz ↦ ⟨(hcl isClosed_Iic hz.1).1, hz.2.2⟩)
  rw [← union_prod, Ici_union_Iic] at hunion
  exact hunion.contDiffOn

/-- Multiplying by the cutoff turns a family smooth on `Icc 0 1 ×ˢ U` into one smooth on
`Ici 0 ×ˢ U` that vanishes for times at least `3/4`. -/
private theorem contDiffOn_seeleyCutoff_smul {f : ℝ × E → F} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f (Icc 0 1 ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun z ↦ seeleyCutoff z.1 • f z) (Ici 0 ×ˢ U) := by
  intro z hz
  rcases lt_or_ge z.1 1 with hz₁ | hz₁
  · have hfz : ContDiffWithinAt ℝ ∞ f (Ici 0 ×ˢ U) z := by
      refine (contDiffWithinAt_inter ((isOpen_lt continuous_fst continuous_const).mem_nhds
        hz₁)).1 ((hf z ⟨⟨hz.1, hz₁.le⟩, hz.2⟩).mono fun y hy ↦ ⟨⟨hy.1.1, hy.2.le⟩, hy.1.2⟩)
    exact ((contDiff_seeleyCutoff.comp contDiff_fst).contDiffWithinAt).smul hfz
  · refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_ |>.contDiffWithinAt
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds
      (show (3 / 4 : ℝ) < z.1 by linarith)] with y hy
    rw [seeleyCutoff_eq_zero_of_le (le_of_lt hy), zero_smul]

/-- The extension of a family smooth on `Icc 0 1 ×ˢ (C ∩ O)` is smooth on `Iio 1 ×ˢ (C ∩ O)`. -/
private theorem contDiffOn_seeleyExtend_Iio (hCc : Convex ℝ C) (hC : UniqueDiffOn ℝ C)
    (hO : IsOpen O) {f : ℝ × E → F} (hf : ContDiffOn ℝ ∞ f (Icc 0 1 ×ˢ (C ∩ O))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E ↦ seeleyExtend (fun s ↦ f (s, z.2)) z.1)
      (Iio 1 ×ˢ (C ∩ O)) := by
  refine contDiffOn_of_locally_contDiffOn fun z _ ↦ ?_
  rcases lt_or_ge z.1 (1 / 2) with hz | hz
  · refine ⟨Iio (1 / 2) ×ˢ univ, isOpen_Iio.prod isOpen_univ, ⟨hz, trivial⟩, ?_⟩
    have h1 (y : ℝ × E) (hy : 1 ≤ y.1) : seeleyCutoff y.1 • f y = 0 := by
      rw [seeleyCutoff_eq_zero_of_le (by linarith), zero_smul]
    refine ((contDiffOn_seeleyGlue hCc hC hO (contDiffOn_seeleyCutoff_smul hf) h1).mono
      fun y (hy : y ∈ Iio 1 ×ˢ (C ∩ O) ∩ Iio (1 / 2) ×ˢ univ) ↦ ⟨trivial, hy.1.2⟩).congr
      fun y hy ↦ ?_
    rw [seeleyExtend_def]
    split_ifs with h0
    · rw [seeleyCutoff_eq_one_of_le hy.2.1.le, one_smul]
    · simp [timeScale_apply]
  · refine ⟨Ioi 0 ×ˢ univ, isOpen_Ioi.prod isOpen_univ,
      ⟨show (0 : ℝ) < z.1 by linarith, trivial⟩, ?_⟩
    refine (hf.mono fun y (hy : y ∈ Iio 1 ×ˢ (C ∩ O) ∩ Ioi 0 ×ˢ univ) ↦
      ⟨⟨le_of_lt hy.2.1, le_of_lt hy.1.1⟩, hy.1.2⟩).congr fun y hy ↦ ?_
    rw [seeleyExtend_of_nonneg _ (le_of_lt hy.2.1)]

/-- **Seeley's extension theorem**, with parameters in a convex set with unique differentials cut
by an open set: if `f` is smooth on `Ici 0 ×ˢ (C ∩ O)`, then
`(t, x) ↦ seeleyExtend (f (·, x)) t` is smooth on `univ ×ˢ (C ∩ O)`. -/
theorem contDiffOn_seeleyExtend_of_convex {f : ℝ × E → F} {C O : Set E} (hCc : Convex ℝ C)
    (hC : UniqueDiffOn ℝ C) (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f (Ici 0 ×ˢ (C ∩ O))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ seeleyExtend (fun s ↦ f (s, p.2)) p.1)
      (univ ×ˢ (C ∩ O)) := by
  refine contDiffOn_of_locally_contDiffOn fun z _ ↦ ?_
  rcases lt_or_ge z.1 1 with hz | hz
  · refine ⟨Iio 1 ×ˢ univ, isOpen_Iio.prod isOpen_univ, ⟨hz, trivial⟩, ?_⟩
    exact (contDiffOn_seeleyExtend_Iio hCc hC hO
      (hf.mono (prod_mono Icc_subset_Ici_self subset_rfl))).mono
      fun y (hy : y ∈ univ ×ˢ (C ∩ O) ∩ Iio 1 ×ˢ univ) ↦ ⟨hy.2.1, hy.1.2⟩
  · refine ⟨Ioi 0 ×ˢ univ, isOpen_Ioi.prod isOpen_univ,
      ⟨show (0 : ℝ) < z.1 by linarith, trivial⟩, ?_⟩
    refine (hf.mono fun y (hy : y ∈ univ ×ˢ (C ∩ O) ∩ Ioi 0 ×ˢ univ) ↦
      ⟨le_of_lt hy.2.1, hy.1.2⟩).congr fun y hy ↦ ?_
    rw [seeleyExtend_of_nonneg _ (le_of_lt hy.2.1)]

/-- **Seeley's extension theorem**, with parameters: if `f` is smooth on `Ici 0 ×ˢ U` for an
open `U`, then `(t, x) ↦ seeleyExtend (f (·, x)) t` is smooth on `univ ×ˢ U`. -/
theorem contDiffOn_seeleyExtend {f : ℝ × E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (Ici 0 ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ seeleyExtend (fun s ↦ f (s, p.2)) p.1) (univ ×ˢ U) := by
  rw [← univ_inter U] at hf ⊢
  exact contDiffOn_seeleyExtend_of_convex convex_univ uniqueDiffOn_univ hU hf

/-- **Seeley's extension theorem**: if `f : ℝ → F` is smooth on `[0, ∞)`, then
`seeleyExtend f` is smooth on `ℝ`. -/
theorem contDiff_seeleyExtend {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Ici 0)) :
    ContDiff ℝ ∞ (seeleyExtend f) := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ f p.1) (Ici 0 ×ˢ univ) :=
    hf.comp contDiff_fst.contDiffOn fun p hp ↦ hp.1
  have hg := contDiffOn_seeleyExtend isOpen_univ h
  rw [univ_prod_univ, contDiffOn_univ] at hg
  exact hg.comp (contDiff_id.prodMk contDiff_const : ContDiff ℝ ∞ fun t : ℝ ↦ (t, (0 : ℝ)))

/-- **Seeley's extension theorem** on `[0, 1]`, with parameters in a convex set with unique
differentials cut by an open set: if `f` is smooth on `Icc 0 1 ×ˢ (C ∩ O)`, then
`(t, x) ↦ seeleyIccExtend (f (·, x)) t` is smooth on `univ ×ˢ (C ∩ O)`. -/
theorem contDiffOn_seeleyIccExtend_of_convex {f : ℝ × E → F} {C O : Set E} (hCc : Convex ℝ C)
    (hC : UniqueDiffOn ℝ C) (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f (Icc 0 1 ×ˢ (C ∩ O))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ seeleyIccExtend (fun s ↦ f (s, p.2)) p.1)
      (univ ×ˢ (C ∩ O)) := by
  refine contDiffOn_of_locally_contDiffOn fun z _ ↦ ?_
  rcases lt_or_ge z.1 1 with hz | hz
  · refine ⟨Iio 1 ×ˢ univ, isOpen_Iio.prod isOpen_univ, ⟨hz, trivial⟩, ?_⟩
    refine ((contDiffOn_seeleyExtend_Iio hCc hC hO hf).mono
      fun y (hy : y ∈ univ ×ˢ (C ∩ O) ∩ Iio 1 ×ˢ univ) ↦ ⟨hy.2.1, hy.1.2⟩).congr
      fun y hy ↦ seeleyIccExtend_of_lt_one _ hy.2.1
  · refine ⟨Ioi 0 ×ˢ univ, isOpen_Ioi.prod isOpen_univ,
      ⟨show (0 : ℝ) < z.1 by linarith, trivial⟩, ?_⟩
    have hf' : ContDiffOn ℝ ∞ (fun q : ℝ × E ↦ f (1 - q.1, q.2)) (Icc 0 1 ×ˢ (C ∩ O)) :=
      hf.comp ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd).contDiffOn
        fun q hq ↦ ⟨⟨by linarith [hq.1.2], by linarith [hq.1.1]⟩, hq.2⟩
    refine ((contDiffOn_seeleyExtend_Iio hCc hC hO hf').comp
      ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd).contDiffOn
      fun y (hy : y ∈ univ ×ˢ (C ∩ O) ∩ Ioi 0 ×ˢ univ) ↦
        ⟨show 1 - y.1 < 1 by linarith [mem_Ioi.mp hy.2.1], hy.1.2⟩).congr fun y hy ↦ ?_
    exact seeleyIccExtend_of_pos _ hy.2.1

/-- **Seeley's extension theorem** on `[0, 1]`, with parameters: if `f` is smooth on
`Icc 0 1 ×ˢ U` for an open `U`, then `(t, x) ↦ seeleyIccExtend (f (·, x)) t` is smooth on
`univ ×ˢ U`. -/
theorem contDiffOn_seeleyIccExtend {f : ℝ × E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (Icc 0 1 ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ seeleyIccExtend (fun s ↦ f (s, p.2)) p.1) (univ ×ˢ U) := by
  rw [← univ_inter U] at hf ⊢
  exact contDiffOn_seeleyIccExtend_of_convex convex_univ uniqueDiffOn_univ hU hf

/-- Seeley's extension on an interval `[a, b]`, `a < b`, with parameters: a function smooth on
`Icc a b ×ˢ U`, for an open `U`, agrees on `Icc a b ×ˢ U` with a function smooth on
`univ ×ˢ U`. -/
theorem exists_contDiffOn_eqOn_Icc_prod {f : ℝ × E → F} {U : Set E} {a b : ℝ} (hab : a < b)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ U)) :
    ∃ g : ℝ × E → F, ContDiffOn ℝ ∞ g (univ ×ˢ U) ∧ EqOn g f (Icc a b ×ˢ U) := by
  have hc : 0 < b - a := sub_pos.2 hab
  have hf' : ContDiffOn ℝ ∞ (fun q : ℝ × E ↦ f (a + (b - a) * q.1, q.2)) (Icc 0 1 ×ˢ U) :=
    hf.comp ((contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd).contDiffOn
      fun q hq ↦ ⟨⟨by nlinarith [hq.1.1], by nlinarith [hq.1.2]⟩, hq.2⟩
  refine ⟨fun p ↦ seeleyIccExtend (fun s ↦ f (a + (b - a) * s, p.2)) ((p.1 - a) / (b - a)),
    (contDiffOn_seeleyIccExtend hU hf').comp
      (((contDiff_fst.sub contDiff_const).div_const _).prodMk contDiff_snd).contDiffOn
      fun p hp ↦ ⟨trivial, hp.2⟩, fun p hp ↦ ?_⟩
  have hmem : (p.1 - a) / (b - a) ∈ Icc 0 1 :=
    ⟨div_nonneg (by linarith [hp.1.1]) hc.le, (div_le_one hc).2 (by linarith [hp.1.2])⟩
  simp only [seeleyIccExtend_of_mem _ hmem]
  rw [mul_div_cancel₀ _ hc.ne', add_sub_cancel]

/-- **Seeley's extension near a boundary point of the half-space `0 ≤ t` of `ℝ × E`.** A function
smooth on the part of an open set `U` where `0 ≤ t` agrees, near a point `(0, x₀)` of `U` and on
that part, with a function smooth on all of `ℝ × E`. -/
theorem exists_contDiff_eqOn_of_contDiffOn_halfSpace [HasContDiffBump E] {f : ℝ × E → F}
    {U : Set (ℝ × E)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f (U ∩ {z | 0 ≤ z.1})) {x₀ : E}
    (hx₀ : (0, x₀) ∈ U) :
    ∃ g : ℝ × E → F, ContDiff ℝ ∞ g ∧
      ∃ V, IsOpen V ∧ (0, x₀) ∈ V ∧ EqOn g f (V ∩ {z | 0 ≤ z.1}) := by
  -- A box `Ioo (-a) a ×ˢ B` around `(0, x₀)` inside `U`.
  have hUn : U ∈ 𝓝 ((0 : ℝ), x₀) := hU.mem_nhds hx₀
  rw [nhds_prod_eq] at hUn
  obtain ⟨u, hu, B', hB', huB⟩ := mem_prod_iff.1 hUn
  obtain ⟨B, hBB', hB, hx₀B⟩ := mem_nhds_iff.1 hB'
  obtain ⟨a, ha, hau⟩ := Metric.mem_nhds_iff.1 hu
  have hsub : Icc 0 (a / 2) ×ˢ B ⊆ U ∩ {z | 0 ≤ z.1} := fun z hz ↦
    ⟨huB ⟨hau (by rw [Real.ball_eq_Ioo]; constructor <;> linarith [hz.1.1, hz.1.2]),
      hBB' hz.2⟩, hz.1.1⟩
  obtain ⟨g₀, hg₀, hg₀f⟩ := exists_contDiffOn_eqOn_Icc_prod (half_pos ha) hB (hf.mono hsub)
  -- `g₀` is already smooth on `univ ×ˢ B`, so a cut-off in the `E` direction suffices.
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.1 hB x₀ hx₀B
  let ρ : ContDiffBump x₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨fun z ↦ ρ z.2 • g₀ z, ?_, Prod.fst ⁻¹' Iio (a / 2) ∩ Prod.snd ⁻¹' Metric.ball x₀ (r / 4),
    (isOpen_Iio.preimage continuous_fst).inter (Metric.isOpen_ball.preimage continuous_snd),
    ⟨half_pos ha, Metric.mem_ball_self (by positivity)⟩, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
    by_cases hz : z.2 ∈ Metric.ball x₀ r
    · exact (ρ.contDiff.comp contDiff_snd).contDiffAt.smul
        (hg₀.contDiffAt ((isOpen_univ.prod hB).mem_nhds ⟨mem_univ _, hrB hz⟩))
    · refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
      have hz' : z.2 ∈ (Metric.closedBall x₀ (r / 2))ᶜ := fun h ↦
        hz (Metric.closedBall_subset_ball (by linarith) h)
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hz')] with z' hz''
      rw [ρ.zero_of_le_dist (le_of_lt (by simpa using hz'')), zero_smul]
  · rintro z ⟨⟨hza, hzb⟩, hz0⟩
    have hzB : z.2 ∈ B := hrB (Metric.ball_subset_ball (by linarith) hzb)
    simp only
    rw [ρ.one_of_mem_closedBall (Metric.ball_subset_closedBall hzb), one_smul]
    exact hg₀f ⟨⟨hz0, le_of_lt hza⟩, hzB⟩

end Smooth

end SymplecticGeometry

end
