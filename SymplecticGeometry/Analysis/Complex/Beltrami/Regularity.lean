/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Complex.Beltrami.CkHolder
public import TauCeti.Analysis.Complex.Beltrami.Isothermal
public import TauCeti.Analysis.Complex.Beltrami.Transition
public import TauCeti.Analysis.Holder.Rescaling
public import TauCeti.Geometry.Symplectic.Cayley.Smooth
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Complex.Conformal.PseudoHyperbolic
import TauCeti.Analysis.Holder.JetBounds

/-!
# Planar isothermal charts of class `C^m`, and smooth ones

Let `J` be a field of almost complex structures on the plane. This file shows that the regularity
of `J` passes to its isothermal charts, the charts `e` whose derivative carries `J` to
multiplication by `i`: `de_z (J z v) = i · de_z v`.

* If `J` is of class `C^m` at `c`, with `1 ≤ m`, and tame at `c`, then `c` has an isothermal chart
  of class `C^m` with invertible derivative
  (`TauCeti.Beltrami.exists_contDiffOn_isothermal_chart_of_contDiffAt`).
* If `J` is smooth and tame on an open set `U`, then every point of `U` has a smooth isothermal
  chart with source in `U` (`TauCeti.Beltrami.exists_smooth_isothermal_chart_of_contDiffOn`).

The first result follows the proof of Tau Ceti's `TauCeti.Beltrami.exists_isothermal_chart`,
with the space `C^{k,α}` in place of the Hölder space `C^{0,α}`, where `m = k + 1`. The scalar
Beltrami coefficient `μ` of `J` is `C^m` at `c`. Normalized at `c` by the real-linear map
`L = TauCeti.Beltrami.linearEquiv (μ c)` and read at `c + L⁻¹ x`, it becomes a coefficient `ν`
that vanishes at `0` and whose `k`-th derivative is Lipschitz, hence Hölder, near `0`
(`ContDiffAt.exists_ball_holderOnWith_iteratedFDeriv`). Cut off and rescaled, `ν` has a small
`C^{k,α}` norm (`TauCeti.eventually_exists_ckHolderSpace_cutoff_rescale`), so the structure of the
rescaled coefficient has a chart of class `C^{k+1}`
(`TauCeti.Beltrami.exists_isComplexLinear_contDiff_chart`). That chart, read through
`z ↦ ε⁻¹ L (z - c)` on the unit disc, is the isothermal chart; its equation follows from
`TauCeti.Beltrami.isComplexLinear_comp_linearMap_iff`. The private steps
`exists_rescaled_coefficient_of_contDiffAt` and `exists_chart_comp_affine_of_contDiffOn` are the
analogues, of class `C^m`, of the private steps `exists_rescaled_coefficient` and
`exists_chart_comp_affine` of Tau Ceti's `TauCeti.Beltrami.exists_isothermal_chart`.

The second result takes Tau Ceti's `C¹` chart
(`TauCeti.Beltrami.exists_isothermal_chart_of_contDiffAt`), restricted to `U`. Since every point
of its source has isothermal charts of every finite order, by the first result, the chart is
smooth (`TauCeti.Beltrami.contDiffOn_infty_of_fderiv_comp`).

## Main results

* `ContDiffAt.exists_ball_holderOnWith_iteratedFDeriv`: a map of class `C^{k+1}` at `x` is
  `C^{k+1}` on a ball around `x`, with a Hölder `k`-th derivative there.
* `TauCeti.Beltrami.exists_contDiffOn_isothermal_chart_of_contDiffAt`: isothermal charts of class
  `C^m` for a field of structures of class `C^m` at a point.
* `TauCeti.Beltrami.exists_smooth_isothermal_chart_of_contDiffOn`: smooth isothermal charts for a
  smooth field of structures on an open set.

## References

* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter V.
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B and Appendix E.
-/

public section

open Complex Metric Set Filter
open scoped ComplexConjugate NNReal Topology ContDiff

/-- Let `α ≤ 1`. A map of class `C^{k+1}` at `x` is of class `C^{k+1}` on some ball around `x`
on which its `k`-th derivative is `α`-Hölder. -/
theorem ContDiffAt.exists_ball_holderOnWith_iteratedFDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {k : ℕ} (hf : ContDiffAt ℝ (k + 1) f x) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ ρ > 0, ∃ H : ℝ≥0, ContDiffOn ℝ (k + 1) f (ball x ρ) ∧
      HolderOnWith H α (iteratedFDeriv ℝ k f) (ball x ρ) := by
  obtain ⟨r, hr, A, hA⟩ := (show ContDiffAt ℝ (k + 1 : ℕ) f x by exact_mod_cast hf
    ).exists_ball_bound_iteratedFDeriv
  obtain ⟨r', hr', hr'f⟩ := Metric.eventually_nhds_iff_ball.mp (hf.eventually (by simp))
  have hρ : 0 < min r r' := lt_min hr hr'
  have hC : ContDiffOn ℝ (k + 1) f (ball x (min r r')) := fun y hy ↦
    (hr'f y (ball_subset_ball (min_le_right _ _) hy)).contDiffWithinAt
  have hb (i : ℕ) (hi : i ≤ k + 1) (y) (hy : y ∈ ball x (min r r')) :
      ‖iteratedFDeriv ℝ i f y‖ ≤ A.toNNReal :=
    (hA i hi y (ball_subset_ball (min_le_left _ _) hy)).trans (Real.le_coe_toNNReal A)
  exact ⟨_, hρ, _, hC, ContDiffOn.holderOnWith_iteratedFDeriv_of_lt (k := k + 1) (j := k)
    (by exact_mod_cast hC) isOpen_ball (convex_ball _ _) (by omega) hα
    (hb k (by omega)) (hb (k + 1) le_rfl)⟩

namespace TauCeti.Beltrami

/-- **Normalized and rescaled coefficient of class `C^{k+1}`.** Let `μ` be `C^{k+1}` at `c`
with `‖μ c‖ < 1`, write `a = μ c`, and let `M` be a real-linear map, `0 < α ≤ 1` and `0 < ρ`.
For every `δ > 0` there are `ε > 0` and a `C^{k,α}` function `f` vanishing off
`closedBall 0 2`, of norm less than `δ`, that on the unit disc is the coefficient
`(μ - a) / (1 - conj a μ)` read at `z = c + M (ε w)`, with `z ∈ ball c ρ`. -/
private theorem exists_rescaled_coefficient_of_contDiffAt {k : ℕ} {α : ℝ≥0} (hα0 : 0 < α)
    (hα1 : α ≤ 1) {μ : ℂ → ℂ} {c : ℂ} (hμ : ContDiffAt ℝ (k + 1) μ c) (hμc : ‖μ c‖ < 1)
    (M : ℂ →L[ℝ] ℂ) {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > (0 : ℝ), ∃ f ∈ supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall 0 2),
      ‖f‖ < δ ∧ ∀ w ∈ ball (0 : ℂ) 1, c + M (ε • w) ∈ ball c ρ ∧
        f w = (μ (c + M (ε • w)) - μ c) / (1 - conj (μ c) * μ (c + M (ε • w))) := by
  set a := μ c
  set g : ℂ → ℂ := fun x ↦ c + M x
  have hg0 : g 0 = c := by simp [g]
  have hg : ContDiff ℝ ∞ g := contDiff_const.add M.contDiff
  -- The normalized coefficient read through `g` is `C^{k+1}` at `0` and vanishes there.
  set ν : ℂ → ℂ := fun x ↦ (μ (g x) - a) / (1 - conj a * μ (g x))
  have hμg : ContDiffAt ℝ (k + 1) (fun x ↦ μ (g x)) 0 :=
    (hg0 ▸ hμ).comp 0 (hg.contDiffAt.of_le (by exact_mod_cast le_top))
  have hden : ContDiffAt ℝ (k + 1) (fun x ↦ 1 - conj a * μ (g x)) 0 :=
    contDiffAt_const.sub ((contDiffAt_const (c := conj a)).mul hμg)
  have hden0 : 1 - conj a * μ (g 0) ≠ 0 := by
    rw [hg0]
    exact one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one hμc.le hμc
  have hν : ContDiffAt ℝ (k + 1) ν 0 := by
    have := (hμg.sub (contDiffAt_const (c := a))).mul (hden.inv hden0)
    simp only [div_eq_mul_inv, ν]
    exact this
  have hν0 : ν 0 = 0 := by simp [ν, hg0, a]
  obtain ⟨ρ₁, hρ₁, H, hνC, hνH⟩ := hν.exists_ball_holderOnWith_iteratedFDeriv hα1
  -- Near `0`, the point `g x` stays in `ball c ρ`.
  obtain ⟨ρ₂, hρ₂, hρ₂g⟩ := Metric.mem_nhds_iff.mp (hg.continuous.continuousAt.preimage_mem_nhds
    (by rw [hg0]; exact isOpen_ball.mem_nhds (mem_ball_self hρ)))
  -- Rescale with a bump equal to `1` on the unit disc and supported in the disc of radius `2`.
  let χ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hsmall := eventually_exists_ckHolderSpace_cutoff_rescale (F := ℂ) (ℓ := k) hα0 hα1 hρ₁
    (hνC.of_le (by exact_mod_cast le_self_add)) hνH hν0 (χ.contDiff (n := k + 1))
    χ.hasCompactSupport hδ
  obtain ⟨ε, ⟨⟨f, hf, hfχ, hfδ⟩, hε⟩⟩ :=
    ((hsmall.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hρ₂)).exists
  refine ⟨ε, hε.1, f, by rwa [χ.tsupport_eq] at hf, hfδ, fun w hw ↦ ⟨hρ₂g ?_, ?_⟩⟩
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hε.1.le]
    calc ε * ‖w‖ ≤ ε * 1 := by gcongr; exacts [hε.1.le, (mem_ball_zero_iff.mp hw).le]
      _ < ρ₂ := by rw [mul_one]; exact hε.2
  · rw [hfχ, χ.one_of_mem_closedBall (ball_subset_closedBall hw), one_smul]

/-- **Reading a chart of class `C^n` through an affine map.** Let `e` be an open partial
homeomorphism of class `C^n`, `n ≠ 0`, on its source, with invertible derivative there. For a
real-linear isomorphism `L`, `ε ≠ 0` and `c`, there is an open partial homeomorphism `E` whose
source is the set of `z` with `ε⁻¹ L (z - c) ∈ e.source ∩ ball 0 1`, of class `C^n` on its
source, whose derivative at such `z` is that of `e` at `ε⁻¹ L (z - c)` composed with `ε⁻¹ L`,
and is invertible. (It is `z ↦ e (ε⁻¹ L (z - c))`.) -/
private theorem exists_chart_comp_affine_of_contDiffOn {n : WithTop ℕ∞} (hn : n ≠ 0)
    {e : OpenPartialHomeomorph ℂ ℂ} (he : ContDiffOn ℝ n e e.source)
    (hinv : ∀ w ∈ e.source, (fderiv ℝ e w).IsInvertible) (L : ℂ ≃L[ℝ] ℂ) {ε : ℝ}
    (hε : ε ≠ 0) (c : ℂ) :
    ∃ E : OpenPartialHomeomorph ℂ ℂ,
      (∀ z, z ∈ E.source ↔ ε⁻¹ • L (z - c) ∈ e.source ∧ ε⁻¹ • L (z - c) ∈ ball (0 : ℂ) 1) ∧
      ContDiffOn ℝ n E E.source ∧ (∀ z ∈ E.source, (fderiv ℝ E z).IsInvertible) ∧
      ∀ z ∈ E.source, fderiv ℝ E z =
        (fderiv ℝ e (ε⁻¹ • L (z - c))).comp (ε⁻¹ • (L : ℂ →L[ℝ] ℂ)) := by
  set T : ℂ →L[ℝ] ℂ := ε⁻¹ • (L : ℂ →L[ℝ] ℂ)
  have hT (z : ℂ) : T z = ε⁻¹ • L z := by simp [T]
  let R : ℂ ≃ₜ ℂ := (Homeomorph.subRight c).trans
    (L.toHomeomorph.trans (Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε)))
  set E := R.toOpenPartialHomeomorph.trans (e.restrOpen (ball 0 1) isOpen_ball)
  have hE : ⇑E = fun z ↦ e (T (z - c)) := by
    ext z
    simp [E, R, hT]
  have hEs (z : ℂ) : z ∈ E.source ↔ T (z - c) ∈ e.source ∧ T (z - c) ∈ ball (0 : ℂ) 1 := by
    simp [E, R, hT]
  have hdE (z : ℂ) (hz : z ∈ E.source) : fderiv ℝ E z = (fderiv ℝ e (T (z - c))).comp T := by
    have hd : DifferentiableAt ℝ e (T (z - c)) :=
      (he.differentiableOn hn _ ((hEs z).mp hz).1).differentiableAt
        (e.open_source.mem_nhds ((hEs z).mp hz).1)
    rw [hE]
    exact (hd.hasFDerivAt.comp z (T.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c))).fderiv
  have hTinv : T.IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := ε • (L.symm : ℂ →L[ℝ] ℂ)) ?_ ?_ <;>
    · ext z
      simp [T, hε]
  refine ⟨E, fun z ↦ by rw [hEs, hT], ?_, fun z hz ↦ ?_, fun z hz ↦ by rw [hdE z hz, hT]⟩
  · rw [hE]
    exact he.comp (T.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn
      fun z hz ↦ ((hEs z).mp hz).1
  · rw [hdE z hz]
    exact (hinv _ ((hEs z).mp hz).1).comp hTinv

/-- **Isothermal charts of class `C^m`.** Let `1 ≤ m` and let `J` be a field of almost complex
structures on the plane that is of class `C^m` at `c` in the operator norm and tame at `c`. Then
`c` has an isothermal chart of class `C^m`: an open partial homeomorphism `e` whose source
contains `c`, which is of class `C^m` on its source with invertible derivative there, and in
which `J` is multiplication by `i`: `de_z (J z v) = i · de_z v`. -/
theorem exists_contDiffOn_isothermal_chart_of_contDiffAt {m : ℕ} (hm : 1 ≤ m)
    {J : ℂ → AlmostComplexStructure ℂ} {c : ℂ}
    (hJ : ContDiffAt ℝ m (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap) c)
    (hJc : stdComplexSymplecticForm.Tames (J c)) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ ContDiffOn ℝ m e e.source ∧
      (∀ z ∈ e.source, (fderiv ℝ e z).IsInvertible) ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- The scalar coefficient `μ` of `J` is `C^{k+1}` at `c`, and is that of `J` near `c`.
  set μ : ℂ → ℂ := fun z ↦ (AlmostComplexStructure.ofComplexModule ℂ).cayley (J z) 1
  have hμ : ContDiffAt ℝ (k + 1 : ℕ) μ c := contMDiffAt_iff_contDiffAt.mp
    ((stdComplexSymplecticForm_tames.contMDiffAt_cayley hJc hJ.contMDiffAt).clm_apply
      (contMDiffAt_const (c := (1 : ℂ))))
  obtain ⟨ρ, hρ, hρJ⟩ := Metric.eventually_nhds_iff_ball.mp
    (SymplecticForm.Tames.eventually_of_continuousAt hJ.continuousAt hJc)
  have hμJ (z : ℂ) (hz : z ∈ ball c ρ) : μ z = (coefficientEquiv ⟨J z, hρJ z hz⟩).val :=
    (coefficientEquiv_apply (J z) (hρJ z hz)).symm
  have hc : c ∈ ball c ρ := mem_ball_self hρ
  set a := μ c
  have ha : ‖a‖ < 1 := by
    have := (coefficientEquiv ⟨J c, hρJ c hc⟩).property
    rwa [← hμJ c hc] at this
  have ha' : Complex.normSq a ≠ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  set L := linearEquiv a ha'
  -- Normalize by `L`, rescale, and take the chart of the rescaled coefficient.
  have hα0 : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hα1 : (1 / 2 : ℝ≥0) < 1 := by norm_num
  obtain ⟨δ, hδ, hchart⟩ := exists_isComplexLinear_contDiff_chart k hα0 hα1 (0 : ℂ) two_pos
  obtain ⟨ε, hε, f, hf, hfδ, hfw⟩ := exists_rescaled_coefficient_of_contDiffAt (k := k) (μ := μ)
    hα0 hα1.le (by exact_mod_cast hμ) ha (L.symm : ℂ →L[ℝ] ℂ) hρ (lt_min hδ one_pos)
  have hf1 (w : ℂ) : ‖f w‖ < 1 :=
    (f.norm_apply_le w).trans_lt (hfδ.trans_le (min_le_right _ _))
  set Jf : ℂ → AlmostComplexStructure ℂ := fun w ↦ (coefficientEquiv.symm ⟨f w, hf1 w⟩).val
  have hJf (w : ℂ) : stdComplexSymplecticForm.Tames (Jf w) := (coefficientEquiv.symm _).property
  obtain ⟨e, he0, -, heC, heinv, helin⟩ := hchart Jf (fun w _ ↦ hJf w) f hf
    (fun w _ ↦ by simp [Jf]) (hfδ.trans_le (min_le_left _ _))
  -- Read that chart through `z ↦ ε⁻¹ L (z - c)` on the unit disc.
  obtain ⟨E, hEs, hEC, hEinv, hdE⟩ := exists_chart_comp_affine_of_contDiffOn (by simp) heC heinv
    L hε.ne' c
  -- The point of the source read at `w = ε⁻¹ L (z - c)` is `z` again.
  have hz (z : ℂ) : c + (L.symm : ℂ →L[ℝ] ℂ) (ε • ε⁻¹ • L (z - c)) = z := by
    simp [hε.ne']
  have hsrc (z : ℂ) (hzE : z ∈ E.source) : z ∈ ball c ρ := by
    have := (hfw _ ((hEs z).mp hzE).2).1
    rwa [hz] at this
  refine ⟨E, (hEs c).mpr (by simpa using he0), by exact_mod_cast hEC, hEinv, fun z hzE v ↦ ?_⟩
  rw [hdE z hzE]
  have hzρ := hsrc z hzE
  have hfz := (hfw _ ((hEs z).mp hzE).2).2
  rw [hz] at hfz
  set w := ε⁻¹ • L (z - c)
  -- At `w`, the chart is complex linear for `Jf w`, whose coefficient is the normalized
  -- coefficient of `J z`.
  have hlin : IsComplexLinear (Jf w).toLinearMap
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (fderiv ℝ e w).toLinearMap :=
    isComplexLinear_iff.mpr (LinearMap.ext fun v ↦ by simpa using helin w ((hEs z).mp hzE).1 v)
  have hμz : ‖μ z‖ ≤ 1 := by
    rw [hμJ z hzρ]
    exact (coefficientEquiv _).property.le
  have hcoef : (coefficientEquiv ⟨Jf w, hJf w⟩).val *
      (1 - conj a * (coefficientEquiv ⟨J z, hρJ z hzρ⟩).val) =
        (coefficientEquiv ⟨J z, hρJ z hzρ⟩).val - a := by
    have hJfw : (coefficientEquiv ⟨Jf w, hJf w⟩).val = f w := by simp [Jf]
    rw [hJfw, hfz, ← hμJ z hzρ]
    exact div_mul_cancel₀ _ (one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one hμz ha)
  have hkey := ((isComplexLinear_comp_linearMap_iff (J z) (Jf w) (hρJ z hzρ) (hJf w) hcoef
    (fderiv ℝ e w)).mpr hlin).apply v
  have hkey' : fderiv ℝ e w (linearMap a (J z v)) = I * fderiv ℝ e w (linearMap a v) := by
    simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_comp, AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul] using hkey
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.map_smul_of_tower, ContinuousLinearEquiv.coe_coe, L,
    linearEquiv_apply, linearMap_apply] at hkey' ⊢
  rw [hkey', Complex.real_smul, Complex.real_smul]
  ring

/-- **Smooth isothermal charts.** Let `J` be a field of almost complex structures on the plane
that is smooth on an open set `U` in the operator norm and tame at every point of `U`. Then every
`c ∈ U` has a smooth isothermal chart: an open partial homeomorphism `e` whose source contains
`c` and lies in `U`, which is smooth on its source with invertible derivative there, and in which
`J` is multiplication by `i`: `de_z (J z v) = i · de_z v`. -/
theorem exists_smooth_isothermal_chart_of_contDiffOn {J : ℂ → AlmostComplexStructure ℂ}
    {U : Set ℂ} (hU : IsOpen U)
    (hJ : ContDiffOn ℝ ∞ (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap) U)
    (hJU : ∀ z ∈ U, stdComplexSymplecticForm.Tames (J z)) {c : ℂ} (hc : c ∈ U) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ (∀ z ∈ e.source, (fderiv ℝ e z).IsInvertible) ∧
      ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
  have hJat (z : ℂ) (hz : z ∈ U) (m : ℕ) :
      ContDiffAt ℝ m (fun z ↦ LinearMap.toContinuousLinearMap (J z).toLinearMap) z :=
    (hJ.contDiffAt (hU.mem_nhds hz)).of_le (by exact_mod_cast le_top)
  -- Tau Ceti's `C¹` chart at `c`, restricted to `U`.
  obtain ⟨e₁, hc₁, hC₁, -, hinv₁, hlin₁⟩ := exists_isothermal_chart_of_contDiffAt
    (α := 1 / 2) (by norm_num) (by norm_num) (hJat c hc 1) (hJU c hc)
  set e := e₁.restrOpen U hU
  have he : ⇑e = e₁ := e₁.coe_restrOpen hU
  have hes : e.source = e₁.source ∩ U := e₁.restrOpen_source U hU
  have hlin : ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
    rw [he, hes]
    exact fun z hz ↦ hlin₁ z hz.1
  refine ⟨e, by rw [hes]; exact ⟨hc₁, hc⟩, by rw [hes]; exact inter_subset_right, ?_,
    by rw [he, hes]; exact fun z hz ↦ hinv₁ z hz.1, hlin⟩
  -- Around each point there are isothermal charts of every finite order, so `e` is smooth.
  refine contDiffOn_infty_of_fderiv_comp (J := fun z ↦ LinearMap.toContinuousLinearMap
    (J z).toLinearMap) ?_ hlin fun z hz m ↦ ?_
  · rw [he, hes]
    exact (hC₁.differentiableOn one_ne_zero).mono inter_subset_left
  · have hzU : z ∈ U := by rw [hes] at hz; exact hz.2
    obtain ⟨e', hz', hC', hinv', hlin'⟩ := exists_contDiffOn_isothermal_chart_of_contDiffAt
      (le_max_right m 1) (hJat z hzU _) (hJU z hzU)
    exact ⟨e', hz', hC'.of_le (by exact_mod_cast le_max_left m 1), hinv', hlin'⟩

end TauCeti.Beltrami

end
