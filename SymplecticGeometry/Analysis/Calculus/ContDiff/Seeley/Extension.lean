/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Analysis.Sobolev.Trace.Reflection.HalfSpace
public import SymplecticGeometry.Analysis.Calculus.ContDiff.Seeley.Coefficients

/-!
# Seeley's extension

Seeley's operator extends a function on `[0, ∞)` to `ℝ`: for `t < 0` it takes the value
`∑ₖ aₖ χ (-2 ^ k t) f (-2 ^ k t)`, where `aₖ = seeleyCoeff k` and `χ = seeleyCutoff` is a smooth
cutoff equal to `1` on `(-∞, 1/2]` and to `0` on `[3/4, ∞)`. For each `t < 0` only finitely many
terms are nonzero, and only values of `f` on `(0, 3/4)` enter, so the operator is linear and
commutes with every linear map. Applying it at both ends of `[0, 1]`, the second time after the
reflection `t ↦ 1 - t`, extends functions on `[0, 1]`.

The main results say that the extension of a family `f (·, x)` that is smooth on
`Ici 0 ×ˢ U` (respectively `Icc 0 1 ×ˢ U`), for `U` open in a normed space, is smooth on
`univ ×ˢ U`. No completeness of the target space is needed.

The proof follows Tau Ceti's `TauCeti.HalfSpaceExtension.contDiff_halfSpaceReflection`, with
Seeley's infinite sum in place of Hestenes' finite one: the Taylor series of the terms
`aₖ (χ f) (timeScale (-2 ^ k) z)` on the lower half are bounded by `|aₖ| 2 ^ (k m)` times a local
bound of the derivatives of `χ f`, so by `summable_seeleyCoeff_mul_pow` their sums converge locally
uniformly (`HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn_of_convex`); at `t = 0` the
moment identities `tsum_seeleyCoeff_mul_neg_two_pow` and `map_timeScale_eq_sum_pow_card_smul`
make the limit series agree with that of `f`; and the two series glue across `t = 0` as in
`HasFTaylorSeriesUpToOn.union_of_isClosed`, here for sets closed only relative to their union.
The uniform convergence uses `tendstoUniformlyOn_finsetSum_of_hasSum`, whose proof adapts
Mathlib's `tendstoUniformlyOn_tsum` to sums that exist without completeness.

## Main definitions

* `SymplecticGeometry.seeleyCutoff`: the cutoff `χ`.
* `SymplecticGeometry.seeleyExtend`: Seeley's extension from `[0, ∞)`.
* `SymplecticGeometry.seeleyIccExtend`: Seeley's extension from `[0, 1]`.

## Main results

* `SymplecticGeometry.contDiffOn_seeleyExtend`, `SymplecticGeometry.contDiffOn_seeleyIccExtend`:
  the extensions of smooth families are smooth.

## References

* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

public section

open Set Filter
open scoped Topology ContDiff

section General

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {f : E → F}
  {p : E → FormalMultilinearSeries 𝕜 E F} {s t : Set E}

/-- Taylor series on two sets glue to their union when each set is closed relative to the
union. -/
theorem HasFTaylorSeriesUpToOn.union (hs : HasFTaylorSeriesUpToOn n f p s)
    (ht : HasFTaylorSeriesUpToOn n f p t) (hst : closure s ∩ t ⊆ s) (hts : closure t ∩ s ⊆ t) :
    HasFTaylorSeriesUpToOn n f p (s ∪ t) := by
  have key : ∀ x ∈ s ∪ t, (x ∈ s ∨ x ∉ closure s) ∧ (x ∈ t ∨ x ∉ closure t) := by
    rintro x (hx | hx)
    · exact ⟨.inl hx, (em (x ∈ closure t)).imp (fun h ↦ hts ⟨h, hx⟩) id⟩
    · exact ⟨(em (x ∈ closure s)).imp (fun h ↦ hst ⟨h, hx⟩) id, .inl hx⟩
  constructor
  · rintro x (hx | hx)
    exacts [hs.zero_eq x hx, ht.zero_eq x hx]
  · intro m hm x hx
    obtain ⟨h₁, h₂⟩ := key x hx
    apply HasFDerivWithinAt.union
    · rcases h₁ with h | h
      exacts [hs.fderivWithin m hm x h, .of_notMem_closure h]
    · rcases h₂ with h | h
      exacts [ht.fderivWithin m hm x h, .of_notMem_closure h]
  · intro m hm x hx
    obtain ⟨h₁, h₂⟩ := key x hx
    apply ContinuousWithinAt.union
    · rcases h₁ with h | h
      exacts [hs.cont m hm x h, continuousWithinAt_of_notMem_closure h]
    · rcases h₂ with h | h
      exacts [ht.cont m hm x h, continuousWithinAt_of_notMem_closure h]

end General

/-- Weierstrass' test for a series of functions whose sums exist: the partial sums converge
uniformly on `s` when the terms are bounded on `s` by a summable sequence. Unlike
`tendstoUniformlyOn_tsum`, this needs no completeness of the target. -/
theorem tendstoUniformlyOn_finsetSum_of_hasSum {α β G : Type*} [NormedAddCommGroup G]
    {f : α → β → G} {g : β → G} {u : α → ℝ} {s : Set β}
    (hg : ∀ x ∈ s, HasSum (fun n ↦ f n x) (g x)) (hu : Summable u)
    (hfu : ∀ n, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun t x ↦ ∑ n ∈ t, f n x) g atTop s := by
  refine Metric.tendstoUniformlyOn_iff.2 fun ε εpos ↦ ?_
  filter_upwards [(tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos] with t ht x hx
  have htail : HasSum (fun n : {n // n ∉ t} ↦ f n x) (g x - ∑ n ∈ t, f n x) :=
    (t.hasSum_compl_iff (f := fun n ↦ f n x)).2 (by rw [sub_add_cancel]; exact hg x hx)
  rw [dist_eq_norm]
  exact (htail.norm_le_of_bounded (hu.subtype _).hasSum fun n ↦ hfu n x hx).trans_lt ht

namespace TauCeti.HalfSpaceExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The time dilation by `a` has operator norm at most `max |a| 1`. -/
theorem norm_timeScale_le (a : ℝ) : ‖timeScale (E := E) a‖ ≤ max |a| 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z ↦ ?_
  rw [timeScale_apply, Prod.norm_def, Prod.norm_def, norm_mul, Real.norm_eq_abs]
  refine max_le ?_ ?_
  · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _) (by positivity)
  · calc ‖z.2‖ = 1 * ‖z.2‖ := (one_mul _).symm
      _ ≤ _ := mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg _) (by positivity)

/-- The time dilations fix the points of time `0`. -/
theorem timeScale_of_fst_eq_zero {z : ℝ × E} (hz : z.1 = 0) (a : ℝ) :
    timeScale a z = z := by
  ext <;> simp [hz]

end TauCeti.HalfSpaceExtension

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

theorem seeleyExtend_of_nonneg (f : ℝ → F) {t : ℝ} (ht : 0 ≤ t) : seeleyExtend f t = f t := by
  simp [seeleyExtend_def, ht]

/-- For `t < 0` the dilated times `-2 ^ k t` eventually exceed any bound. -/
private theorem exists_forall_lt_neg_two_pow_mul {t : ℝ} (ht : t < 0) (c : ℝ) :
    ∃ N : ℕ, ∀ k, N ≤ k → c < -2 ^ k * t := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (c / -t) (one_lt_two : (1 : ℝ) < 2)
  refine ⟨N, fun k hk ↦ ?_⟩
  have h2 : (2 : ℝ) ^ N ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hk
  rw [div_lt_iff₀ (by linarith)] at hN
  nlinarith

/-- For `t < 0`, the cutoff vanishes at `-2 ^ k t` for all large `k`. -/
private theorem exists_seeleyCutoff_eq_zero {t : ℝ} (ht : t < 0) :
    ∃ N : ℕ, ∀ k, N ≤ k → seeleyCutoff (-2 ^ k * t) = 0 := by
  obtain ⟨N, hN⟩ := exists_forall_lt_neg_two_pow_mul ht (3 / 4)
  exact ⟨N, fun k hk ↦ seeleyCutoff_eq_zero_of_le (hN k hk).le⟩

/-- For `t < 0`, Seeley's sum is a finite sum. -/
private theorem seeleyExtend_eq_sum (f : ℝ → F) {t : ℝ} (ht : t < 0) {N : ℕ}
    (hN : ∀ k, N ≤ k → seeleyCutoff (-2 ^ k * t) = 0) :
    seeleyExtend f t =
      ∑ k ∈ Finset.range N, seeleyCoeff k • seeleyCutoff (-2 ^ k * t) • f (-2 ^ k * t) := by
  simp only [seeleyExtend_def, not_le.mpr ht, ↓reduceIte]
  refine tsum_eq_sum fun k hk ↦ ?_
  rw [hN k (by simpa using hk), zero_smul, smul_zero]

/-- For `t < 0`, Seeley's sum depends only on the values of `f` on `(0, 1)`. -/
private theorem seeleyExtend_congr_of_neg {f g : ℝ → F} (hfg : EqOn f g (Ioo 0 1)) {t : ℝ}
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

theorem seeleyIccExtend_of_mem (f : ℝ → F) {t : ℝ} (h : t ∈ Icc 0 1) :
    seeleyIccExtend f t = f t := by
  rw [seeleyIccExtend_def]
  split_ifs with ht
  · exact seeleyExtend_of_nonneg f h.1
  · rw [seeleyExtend_of_nonneg _ (by linarith [h.2]), sub_sub_cancel]

/-- For `t < 1`, `seeleyIccExtend f t = seeleyExtend f t`. -/
private theorem seeleyIccExtend_of_lt_one (f : ℝ → F) {t : ℝ} (ht : t < 1) :
    seeleyIccExtend f t = seeleyExtend f t := by
  rw [seeleyIccExtend_def]
  split_ifs with h
  · rfl
  · rw [seeleyExtend_of_nonneg _ (by linarith), seeleyExtend_of_nonneg _ (by linarith),
      sub_sub_cancel]

/-- For `t > 0`, `seeleyIccExtend f t` is the extension of `s ↦ f (1 - s)` at `1 - t`. -/
private theorem seeleyIccExtend_of_pos (f : ℝ → F) {t : ℝ} (ht : 0 < t) :
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

/-- Seeley's extension from `[0, 1]` commutes with linear maps. -/
theorem _root_.LinearMap.map_seeleyIccExtend (L : F →ₗ[ℝ] G) (f : ℝ → F) (t : ℝ) :
    L (seeleyIccExtend f t) = seeleyIccExtend (L ∘ f) t := by
  simp only [seeleyIccExtend_def]
  split_ifs
  · exact L.map_seeleyExtend f t
  · exact L.map_seeleyExtend (fun s ↦ f (1 - s)) (1 - t)

/-! ### Smoothness -/

section Smooth

variable {U : Set E} {h : ℝ × E → F}

/-- The moment identities for multilinear maps: `∑ₖ aₖ A (timeScale (-2 ^ k) ·, …)` sums to
`A`. -/
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
    hasSum_sum fun s _ ↦ by simpa using (hasSum_seeleyCoeff_mul_neg_two_pow s.card).smul_const (B s)
  rw [← hA] at hsum
  convert hsum using 2 with k
  rw [hB, Finset.smul_sum]
  simp_rw [smul_smul]

/-- The dilations by `-2 ^ k` map the lower half of `univ ×ˢ U` to its upper half. -/
private theorem timeScale_mem_Ici_prod {z : ℝ × E} (hz : z ∈ Iic 0 ×ˢ U) (k : ℕ) :
    timeScale (-2 ^ k) z ∈ Ici 0 ×ˢ U := by
  rw [timeScale_apply]
  exact ⟨mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 (pow_nonneg zero_le_two k)) hz.1, hz.2⟩

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

/-- The Taylor coefficients of `h` of each order are bounded on `Ici 0 ×ˢ ball x₀ r` for some
`r`, when `h` vanishes for times at least `1`. -/
private theorem exists_bound_ftaylorSeriesWithin (hU : IsOpen U)
    (hh : ContDiffOn ℝ ∞ h (Ici 0 ×ˢ U)) (h1 : ∀ z : ℝ × E, 1 ≤ z.1 → h z = 0) (m : ℕ)
    {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ r > 0, ∃ M, 0 ≤ M ∧ Metric.ball x₀ r ⊆ U ∧ ∀ z : ℝ × E, 0 ≤ z.1 →
      z.2 ∈ Metric.ball x₀ r → ‖ftaylorSeriesWithin ℝ h (Ici 0 ×ˢ U) z m‖ ≤ M := by
  set p := ftaylorSeriesWithin ℝ h (Ici 0 ×ˢ U) with hp_def
  have hc : ContinuousOn (fun z ↦ p z m) (Ici 0 ×ˢ U) :=
    (hh.ftaylorSeriesWithin ((uniqueDiffOn_Ici 0).prod hU.uniqueDiffOn)).cont m
      (by exact_mod_cast le_top)
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ {x₀}) := isCompact_Icc.prod isCompact_singleton
  have hKs : Icc (0 : ℝ) 1 ×ˢ {x₀} ⊆ Ici 0 ×ˢ U :=
    prod_mono Icc_subset_Ici_self (singleton_subset_iff.mpr hx₀)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono hKs)
  obtain ⟨u, hu, hpre⟩ := continuousOn_iff'.1 hc {A | ‖A‖ < C + 1}
    (isOpen_lt continuous_norm continuous_const)
  have hKu : Icc (0 : ℝ) 1 ×ˢ {x₀} ⊆ u := fun z hz ↦ by
    have hz' : z ∈ (fun z ↦ p z m) ⁻¹' {A | ‖A‖ < C + 1} ∩ Ici 0 ×ˢ U :=
      ⟨(hC z hz).trans_lt (lt_add_one C), hKs hz⟩
    rw [hpre] at hz'
    exact hz'.1
  obtain ⟨V, W, -, hW, hV, hW₀, hVW⟩ := generalized_tube_lemma isCompact_Icc isCompact_singleton
    hu hKu
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 (hW.inter hU) x₀ ⟨hW₀ rfl, hx₀⟩
  refine ⟨r, hr, max (C + 1) 0, le_max_right _ _, fun x hx ↦ (hrW hx).2, fun z hz₀ hz ↦ ?_⟩
  rcases le_or_gt z.1 1 with hz₁ | hz₁
  · have hzu : z ∈ u ∩ Ici 0 ×ˢ U := ⟨hVW ⟨hV ⟨hz₀, hz₁⟩, (hrW hz).1⟩, hz₀, (hrW hz).2⟩
    rw [← hpre] at hzu
    exact hzu.1.le.trans (le_max_left _ _)
  · rw [hp_def, ftaylorSeriesWithin_eq_zero h1 hz₁, norm_zero]
    exact le_max_right _ _

/-- Seeley's sum `∑ₖ aₖ h (timeScale (-2 ^ k) z)` has, on the lower half of `univ ×ˢ U`, the
Taylor series whose coefficients are the corresponding sums of the dilated coefficients of `h`. -/
private theorem hasFTaylorSeriesUpToOn_seeleySum (hU : IsOpen U)
    (hh : ContDiffOn ℝ ∞ h (Ici 0 ×ˢ U)) (h1 : ∀ z : ℝ × E, 1 ≤ z.1 → h z = 0) :
    HasFTaylorSeriesUpToOn ∞ (fun z ↦ ∑' k, seeleyCoeff k • h (timeScale (-2 ^ k) z))
      (fun z m ↦ ∑' k, seeleyCoeff k •
        (ftaylorSeriesWithin ℝ h (Ici 0 ×ˢ U) (timeScale (-2 ^ k) z) m).compContinuousLinearMap
          fun _ ↦ timeScale (-2 ^ k))
      (Iic 0 ×ˢ U) := by
  set p := ftaylorSeriesWithin ℝ h (Ici 0 ×ˢ U) with hp_def
  have hp : HasFTaylorSeriesUpToOn ∞ h p (Ici 0 ×ˢ U) :=
    hh.ftaylorSeriesWithin ((uniqueDiffOn_Ici 0).prod hU.uniqueDiffOn)
  have hval {z : ℝ × E} (hz : z ∈ Iic 0 ×ˢ U) :
      Summable fun k ↦ seeleyCoeff k • h (timeScale (-2 ^ k) z) := by
    rcases hz.1.lt_or_eq with hz₀ | hz₀
    · exact summable_of_fst_neg hz₀ fun k hk ↦ by rw [h1 _ hk.le, smul_zero]
    · simp_rw [timeScale_of_fst_eq_zero hz₀]
      exact (by simpa using (hasSum_seeleyCoeff_mul_neg_two_pow 0).smul_const (h z) :
        HasSum (fun k ↦ seeleyCoeff k • h z) (h z)).summable
  have hcoef (m : ℕ) {z : ℝ × E} (hz : z ∈ Iic 0 ×ˢ U) :
      Summable fun k ↦ seeleyCoeff k •
        (p (timeScale (-2 ^ k) z) m).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k) := by
    rcases hz.1.lt_or_eq with hz₀ | hz₀
    · refine summable_of_fst_neg hz₀ fun k hk ↦ ?_
      rw [hp_def, ftaylorSeriesWithin_eq_zero h1 hk]
      ext v
      simp
    · simp_rw [timeScale_of_fst_eq_zero hz₀]
      exact (hasSum_seeleyCoeff_smul_compContinuousLinearMap_timeScale (p z m)).summable
  have hnhds {z : ℝ × E} {r : ℝ} (hr : 0 < r) :
      Iic 0 ×ˢ Metric.ball z.2 r ∈ 𝓝[Iic 0 ×ˢ U] z :=
    mem_nhdsWithin.2 ⟨univ ×ˢ Metric.ball z.2 r, isOpen_univ.prod Metric.isOpen_ball,
      ⟨trivial, Metric.mem_ball_self hr⟩, fun y hy ↦ ⟨hy.2.1, hy.1.2⟩⟩
  refine HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn_of_convex (l := atTop)
    (fᵢ := fun S z ↦ ∑ k ∈ S, seeleyCoeff k • h (timeScale (-2 ^ k) z))
    (qᵢ := fun S z m ↦ ∑ k ∈ S, seeleyCoeff k •
      (p (timeScale (-2 ^ k) z) m).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k))
    (fun z hz ↦ ?_) (fun S ↦ ?_) (fun m _ ↦ ?_) (fun z hz ↦ (hval hz).hasSum)
  · obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z.2 hz.2
    exact ⟨Iic 0 ×ˢ Metric.ball z.2 r, prod_mono subset_rfl hrU,
      (convex_Iic 0).prod (convex_ball _ _), hnhds hr⟩
  · exact HasFTaylorSeriesUpToOn.sum fun k _ ↦
      ((hp.compContinuousLinearMap (timeScale (-2 ^ k))).const_smul (seeleyCoeff k)).mono
        fun z hz ↦ timeScale_mem_Ici_prod hz k
  · refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun z hz ↦ ?_
    obtain ⟨r, hr, M, hM₀, hrU, hM⟩ := exists_bound_ftaylorSeriesWithin hU hh h1 m hz.2
    refine ⟨_, hnhds hr, tendstoUniformlyOn_finsetSum_of_hasSum
      (fun y hy ↦ (hcoef m ⟨hy.1, hrU hy.2⟩).hasSum)
      ((summable_seeleyCoeff_mul_pow m).mul_right M) fun k y hy ↦ ?_⟩
    have hτ : ‖timeScale (E := E) (-2 ^ k)‖ ≤ 2 ^ k := by
      refine (norm_timeScale_le _).trans_eq ?_
      rw [abs_neg, abs_pow, abs_two, max_eq_left (one_le_pow₀ one_le_two)]
    have hy' := timeScale_mem_Ici_prod (k := k) ⟨hy.1, hrU hy.2⟩
    calc _ = |seeleyCoeff k| * ‖(p (timeScale (-2 ^ k) y) m).compContinuousLinearMap
          fun _ ↦ timeScale (E := E) (-2 ^ k)‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |seeleyCoeff k| * (M * ∏ _i : Fin m, (2 : ℝ) ^ k) := by
        gcongr
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        gcongr with i
        exact hM _ hy'.1 (by simpa using hy.2)
      _ = |seeleyCoeff k| * 2 ^ (k * m) * M := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
        ring

/-- The function equal to `h` for nonnegative times and to Seeley's sum of `h` for negative
times is smooth on `univ ×ˢ U`. -/
private theorem contDiffOn_seeleyGlue (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h (Ici 0 ×ˢ U))
    (h1 : ∀ z : ℝ × E, 1 ≤ z.1 → h z = 0) :
    ContDiffOn ℝ ∞ (fun z ↦ if 0 ≤ z.1 then h z
      else ∑' k, seeleyCoeff k • h (timeScale (-2 ^ k) z)) (univ ×ˢ U) := by
  set p := ftaylorSeriesWithin ℝ h (Ici 0 ×ˢ U)
  have hp : HasFTaylorSeriesUpToOn ∞ h p (Ici 0 ×ˢ U) :=
    hh.ftaylorSeriesWithin ((uniqueDiffOn_Ici 0).prod hU.uniqueDiffOn)
  have hq := hasFTaylorSeriesUpToOn_seeleySum hU hh h1
  have hval {z : ℝ × E} (hz : z.1 = 0) :
      ∑' k, seeleyCoeff k • h (timeScale (-2 ^ k) z) = h z := by
    simp_rw [timeScale_of_fst_eq_zero hz]
    exact (by simpa using (hasSum_seeleyCoeff_mul_neg_two_pow 0).smul_const (h z) :
      HasSum (fun k ↦ seeleyCoeff k • h z) (h z)).tsum_eq
  have hcoef {z : ℝ × E} (hz : z.1 = 0) (m : ℕ) :
      ∑' k, seeleyCoeff k • (p (timeScale (-2 ^ k) z) m).compContinuousLinearMap
        (fun _ ↦ timeScale (-2 ^ k)) = p z m := by
    simp_rw [timeScale_of_fst_eq_zero hz]
    exact (hasSum_seeleyCoeff_smul_compContinuousLinearMap_timeScale (p z m)).tsum_eq
  let r : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) F := fun z m ↦ if 0 ≤ z.1 then p z m
    else ∑' k, seeleyCoeff k • (p (timeScale (-2 ^ k) z) m).compContinuousLinearMap
      (fun _ ↦ timeScale (-2 ^ k))
  have hs : HasFTaylorSeriesUpToOn ∞ (fun z ↦ if 0 ≤ z.1 then h z
      else ∑' k, seeleyCoeff k • h (timeScale (-2 ^ k) z)) r (Ici 0 ×ˢ U) :=
    (hp.congr fun z hz ↦ by simp only [mem_Ici.mp hz.1, ↓reduceIte]).congr_series
      fun m _ z hz ↦ by simp only [r, mem_Ici.mp hz.1, ↓reduceIte]
  have ht : HasFTaylorSeriesUpToOn ∞ (fun z ↦ if 0 ≤ z.1 then h z
      else ∑' k, seeleyCoeff k • h (timeScale (-2 ^ k) z)) r (Iic 0 ×ˢ U) := by
    refine (hq.congr fun z hz ↦ ?_).congr_series fun m _ z hz ↦ ?_
    · split_ifs with h0
      · exact (hval (le_antisymm hz.1 h0)).symm
      · rfl
    · simp only [r]
      split_ifs with h0
      · exact hcoef (le_antisymm hz.1 h0) m
      · rfl
  have hcl {a : Set ℝ} (ha : IsClosed a) : closure (a ×ˢ U) ⊆ a ×ˢ univ :=
    closure_minimal (prod_mono subset_rfl (subset_univ U)) (ha.prod isClosed_univ)
  have hunion := hs.union ht (fun z hz ↦ ⟨(hcl isClosed_Ici hz.1).1, hz.2.2⟩)
    (fun z hz ↦ ⟨(hcl isClosed_Iic hz.1).1, hz.2.2⟩)
  rw [← union_prod, Ici_union_Iic] at hunion
  exact hunion.contDiffOn

/-- Multiplying by the cutoff turns a family smooth on `Icc 0 1 ×ˢ U` into one smooth on
`Ici 0 ×ˢ U` that vanishes for times at least `3/4`. -/
private theorem contDiffOn_seeleyCutoff_smul {f : ℝ × E → F}
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

/-- The extension of a family smooth on `Icc 0 1 ×ˢ U` is smooth on `Iio 1 ×ˢ U`. -/
private theorem contDiffOn_seeleyExtend_Iio (hU : IsOpen U) {f : ℝ × E → F}
    (hf : ContDiffOn ℝ ∞ f (Icc 0 1 ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E ↦ seeleyExtend (fun s ↦ f (s, z.2)) z.1) (Iio 1 ×ˢ U) := by
  refine contDiffOn_of_locally_contDiffOn fun z _ ↦ ?_
  rcases lt_or_ge z.1 (1 / 2) with hz | hz
  · refine ⟨Iio (1 / 2) ×ˢ univ, isOpen_Iio.prod isOpen_univ, ⟨hz, trivial⟩, ?_⟩
    have h1 (y : ℝ × E) (hy : 1 ≤ y.1) : seeleyCutoff y.1 • f y = 0 := by
      rw [seeleyCutoff_eq_zero_of_le (by linarith), zero_smul]
    refine ((contDiffOn_seeleyGlue hU (contDiffOn_seeleyCutoff_smul hf) h1).mono
      fun y (hy : y ∈ Iio 1 ×ˢ U ∩ Iio (1 / 2) ×ˢ univ) ↦ ⟨trivial, hy.1.2⟩).congr fun y hy ↦ ?_
    rw [seeleyExtend_def]
    split_ifs with h0
    · rw [seeleyCutoff_eq_one_of_le hy.2.1.le, one_smul]
    · simp [timeScale_apply]
  · refine ⟨Ioi 0 ×ˢ univ, isOpen_Ioi.prod isOpen_univ,
      ⟨show (0 : ℝ) < z.1 by linarith, trivial⟩, ?_⟩
    refine (hf.mono fun y (hy : y ∈ Iio 1 ×ˢ U ∩ Ioi 0 ×ˢ univ) ↦
      ⟨⟨le_of_lt hy.2.1, le_of_lt hy.1.1⟩, hy.1.2⟩).congr fun y hy ↦ ?_
    rw [seeleyExtend_of_nonneg _ (le_of_lt hy.2.1)]

/-- **Seeley's extension theorem**, with parameters: if `f` is smooth on `Ici 0 ×ˢ U` for an
open `U`, then `(t, x) ↦ seeleyExtend (f (·, x)) t` is smooth on `univ ×ˢ U`. -/
theorem contDiffOn_seeleyExtend {f : ℝ × E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (Ici 0 ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ seeleyExtend (fun s ↦ f (s, p.2)) p.1) (univ ×ˢ U) := by
  refine contDiffOn_of_locally_contDiffOn fun z _ ↦ ?_
  rcases lt_or_ge z.1 1 with hz | hz
  · refine ⟨Iio 1 ×ˢ univ, isOpen_Iio.prod isOpen_univ, ⟨hz, trivial⟩, ?_⟩
    exact (contDiffOn_seeleyExtend_Iio hU (hf.mono (prod_mono Icc_subset_Ici_self subset_rfl))).mono
      fun y (hy : y ∈ univ ×ˢ U ∩ Iio 1 ×ˢ univ) ↦ ⟨hy.2.1, hy.1.2⟩
  · refine ⟨Ioi 0 ×ˢ univ, isOpen_Ioi.prod isOpen_univ,
      ⟨show (0 : ℝ) < z.1 by linarith, trivial⟩, ?_⟩
    refine (hf.mono fun y (hy : y ∈ univ ×ˢ U ∩ Ioi 0 ×ˢ univ) ↦
      ⟨le_of_lt hy.2.1, hy.1.2⟩).congr fun y hy ↦ ?_
    rw [seeleyExtend_of_nonneg _ (le_of_lt hy.2.1)]

/-- **Seeley's extension theorem** on `[0, 1]`, with parameters: if `f` is smooth on
`Icc 0 1 ×ˢ U` for an open `U`, then `(t, x) ↦ seeleyIccExtend (f (·, x)) t` is smooth on
`univ ×ˢ U`. -/
theorem contDiffOn_seeleyIccExtend {f : ℝ × E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (Icc 0 1 ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ seeleyIccExtend (fun s ↦ f (s, p.2)) p.1) (univ ×ˢ U) := by
  refine contDiffOn_of_locally_contDiffOn fun z _ ↦ ?_
  rcases lt_or_ge z.1 1 with hz | hz
  · refine ⟨Iio 1 ×ˢ univ, isOpen_Iio.prod isOpen_univ, ⟨hz, trivial⟩, ?_⟩
    refine ((contDiffOn_seeleyExtend_Iio hU hf).mono
      fun y (hy : y ∈ univ ×ˢ U ∩ Iio 1 ×ˢ univ) ↦ ⟨hy.2.1, hy.1.2⟩).congr
      fun y hy ↦ seeleyIccExtend_of_lt_one _ hy.2.1
  · refine ⟨Ioi 0 ×ˢ univ, isOpen_Ioi.prod isOpen_univ,
      ⟨show (0 : ℝ) < z.1 by linarith, trivial⟩, ?_⟩
    have hf' : ContDiffOn ℝ ∞ (fun q : ℝ × E ↦ f (1 - q.1, q.2)) (Icc 0 1 ×ˢ U) :=
      hf.comp ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd).contDiffOn
        fun q hq ↦ ⟨⟨by linarith [hq.1.2], by linarith [hq.1.1]⟩, hq.2⟩
    refine ((contDiffOn_seeleyExtend_Iio hU hf').comp
      ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd).contDiffOn
      fun y (hy : y ∈ univ ×ˢ U ∩ Ioi 0 ×ˢ univ) ↦
        ⟨show 1 - y.1 < 1 by linarith [mem_Ioi.mp hy.2.1], hy.1.2⟩).congr fun y hy ↦ ?_
    exact seeleyIccExtend_of_pos _ hy.2.1

end Smooth

end SymplecticGeometry

end
