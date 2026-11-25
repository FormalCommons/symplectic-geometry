/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Holonomic approximation in coordinates: conventions and wiggling

This file starts the coordinate treatment of holonomic approximation, following
[EliashbergMishachev2002], Chapter 3. The model is
`D := (Fin m → ℝ) × (Fin k → ℝ)`, with the core directions first and the transverse directions
second, and with sup norms, so that the cube `Iᵐ` is `Metric.closedBall (0 : Fin m → ℝ) 1` and
no cube needs a definition.

A formal section (a first jet over `D` with values in a normed space `F`) is a pair of maps
`f : D → F` and `G : D → D →L[ℝ] F`. It is holonomic on `s` when `∀ x ∈ s, fderiv ℝ f x = G x`.
Neither notion gets a definition: statements carry the two maps and this equation.

The file proves the one-dimensional *wiggling* lemma, the zig-zag diffeotopy that both
[EliashbergMishachev2002], §3.2, and the handle-core argument of [McDuffSalamon2017], Lemma 7.3.2,
use: a compactly supported diffeotopy that moves points by less than a given `δ`, stays in the
`δ`-neighbourhood of a compact set `K`, and on `K` itself pushes each point in a transverse
direction by `r sin (N u)`, where `u` is a core coordinate. As `N` grows the image of a segment
along that core coordinate oscillates more and more often between the heights `± r`, so its
length in the transverse direction is as large as wanted.

## Main results

* `IsMIntegralCurve.norm_sub_le_mul`: an integral curve of a field bounded by `C` on a real
  normed space moves by at most `C t` in time `t`.
* `SymplecticGeometry.exists_diffeotopy_apply_eq_add_smul`: on a finite-dimensional real normed
  space, for a compact `K`, a vector `e` with `‖e‖ < δ` and a smooth `g` with `|g| ≤ 1` that is
  constant along `e`, there is a diffeotopy supported in a compact subset of the
  `δ`-neighbourhood of `K`, moving points by at most `t ‖e‖` at time `t`, and acting on `K` by
  `x ↦ x + (t * g x) • e`.
* `SymplecticGeometry.exists_wiggling_diffeotopy`: the zig-zag on `D`.

The diffeotopy is the flow of the cut-off vector field `φ g e`, built with Tau Ceti's
`TauCeti.compactlySupportedFlowDiffeotopy`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- An integral curve, on a real normed space with its standard model, of a vector field bounded
by `C` moves by at most `C t` in time `t ≥ 0`. -/
theorem _root_.IsMIntegralCurve.norm_sub_le_mul {v : E → E} {γ : ℝ → E}
    (hγ : IsMIntegralCurve (I := 𝓘(ℝ, E)) γ v) {C : ℝ} (hC : ∀ y, ‖v y‖ ≤ C) {t : ℝ}
    (ht : 0 ≤ t) : ‖γ t - γ 0‖ ≤ C * t := by
  have hd : ∀ s, HasDerivAt γ (v (γ s)) s := fun s ↦ by
    have : HasFDerivAt γ (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v (γ s))) s :=
      HasMFDerivAt.hasFDerivAt (hγ s)
    simpa using this.hasDerivAt
  simpa using norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s _ ↦ (hd s).hasDerivWithinAt) (fun s _ ↦ hC (γ s)) t ⟨ht, le_rfl⟩

/-- **Pushing a compact set along a direction.** On a finite-dimensional real normed space, let
`K` be compact, `e` a vector with `‖e‖ < δ`, and `g` a smooth function with `|g| ≤ 1` that is
constant along `e`. Then there is a smooth diffeotopy `h` that is the identity off a compact subset
of the `δ`-neighbourhood of `K`, moves every point by at most `t ‖e‖` at time `t`, and sends each
`x ∈ K` at time `t` to `x + (t * g x) • e`. -/
theorem exists_diffeotopy_apply_eq_add_smul {K : Set E} (hK : IsCompact K) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (hg1 : ∀ x, |g x| ≤ 1) {e : E} (hge : ∀ x (s : ℝ), g (x + s • e) = g x)
    {δ : ℝ} (he : ‖e‖ < δ) :
    ∃ h : TauCeti.Diffeotopy 𝓘(ℝ, E) ∞ E,
      (∃ C, IsCompact C ∧ C ⊆ thickening δ K ∧ ∀ t, ∀ x ∉ C, h (t, x) = x) ∧
      (∀ t x, ‖h (t, x) - x‖ ≤ (t : ℝ) * ‖e‖) ∧
      ∀ t, ∀ x ∈ K, h (t, x) = x + ((t : ℝ) * g x) • e := by
  -- The cut-off `φ` is `1` on the `ρ`-neighbourhood of `K` and vanishes off the
  -- `ρ'`-neighbourhood, with `‖e‖ < ρ < ρ' < δ`.
  set ρ := (2 * ‖e‖ + δ) / 3
  set ρ' := (‖e‖ + 2 * δ) / 3
  have hρ : ‖e‖ < ρ := by simp only [ρ]; linarith
  have hρρ' : ρ < ρ' := by simp only [ρ, ρ']; linarith
  have hρ'δ : ρ' < δ := by simp only [ρ']; linarith
  have hρ0 : 0 < ρ := (norm_nonneg e).trans_lt hρ
  obtain ⟨φ, hφ0, hφ1, hφI⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, E) (n := ⊤)
    (isOpen_thickening (δ := ρ') (E := K)).isClosed_compl (isClosed_cthickening (δ := ρ) (E := K))
    (disjoint_compl_left_iff_subset.mpr
      (cthickening_subset_thickening' (hρ0.trans hρρ') hρρ' K))
  have hφ : ContDiff ℝ ∞ φ := contMDiff_iff_contDiff.mp φ.contMDiff
  set v : E → E := fun y ↦ (φ y * g y) • e
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr ((hφ.mul hg).smul contDiff_const)
  have hC : IsCompact (cthickening ρ' K) := hK.cthickening
  have hzero : ∀ y ∉ cthickening ρ' K, v y = 0 := fun y hy ↦ by
    have : φ y = 0 := hφ0 fun h ↦ hy (thickening_subset_cthickening _ _ h)
    simp [v, this]
  have hn : (1 : ℕ∞) ≤ ⊤ := le_top
  have hv1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) E)) := hv.of_le (by simp)
  have hcomplete := TauCeti.isCompleteVectorField_of_isCompact_of_eq_zero_off hv1 hC hzero
  have hγ : ∀ x, IsMIntegralCurve (I := 𝓘(ℝ, E)) (maximalIntegralCurve v x) v := fun x ↦
    TauCeti.isMIntegralCurve_maximalIntegralCurve_of_eq_univ hv1
      (hcomplete.maximalIntegralCurveInterval_eq_univ x)
  -- Tau Ceti states the next two facts for fields valued in tangent spaces; `v` is `E`-valued,
  -- so `simp` and `rw` do not find them, and they are restated for `v`.
  have h0 : ∀ x, maximalIntegralCurve (I := 𝓘(ℝ, E)) v x 0 = x := fun x ↦
    maximalIntegralCurve_zero
  have happ : ∀ (t : unitInterval) x,
      TauCeti.compactlySupportedFlowDiffeotopy hn hv hC hzero 1 (t, x) =
        maximalIntegralCurve v x t := fun t x ↦
    (TauCeti.compactlySupportedFlowDiffeotopy_apply hn hv hC hzero 1 (t, x)).trans
      (by rw [one_mul])
  refine ⟨TauCeti.compactlySupportedFlowDiffeotopy hn hv hC hzero 1, ⟨_, hC,
    cthickening_subset_thickening' (hρ0.trans (hρρ'.trans hρ'δ)) hρ'δ K, fun t x hx ↦
      TauCeti.compactlySupportedFlowDiffeotopy_apply_of_eq_zero hn hv hC hzero 1 (hzero x hx) t⟩,
    fun t x ↦ ?_, fun t x hx ↦ ?_⟩
  · -- The field is bounded by `‖e‖`, so points move at speed at most `‖e‖`.
    rw [happ]
    have hbound : ∀ y, ‖v y‖ ≤ ‖e‖ := fun y ↦ by
      have h1 : |φ y| ≤ 1 := abs_le.mpr ⟨by linarith [(hφI y).1], (hφI y).2⟩
      simp only [v, norm_smul, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (norm_nonneg e)
        (by nlinarith [abs_nonneg (φ y), abs_nonneg (g y), hg1 y])
    have := (hγ x).norm_sub_le_mul hbound t.property.1
    rwa [h0, mul_comm] at this
  · -- Near `K` the field is the constant `g x • e` along the line through `x`, so the line is
    -- the integral curve for times in `(-ε, 1 + ε)`.
    rw [happ]
    set ε := (ρ - ‖e‖) / (‖e‖ + 1)
    have hε : 0 < ε := div_pos (by linarith) (by positivity)
    have hεe : (1 + ε) * ‖e‖ < ρ := by
      have : ε * ‖e‖ < ρ - ‖e‖ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg e]
      linarith
    have hline : IsMIntegralCurveOn (I := 𝓘(ℝ, E)) (fun s : ℝ ↦ x + (s * g x) • e) v
        (Ioo (-ε) (1 + ε)) := by
      intro s hs
      have hmem : x + (s * g x) • e ∈ cthickening ρ K := by
        refine mem_cthickening_of_dist_le _ x _ _ hx ?_
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul]
        have hs' : |s| ≤ 1 + ε := abs_le.mpr ⟨by linarith [hs.1], hs.2.le⟩
        calc |s| * |g x| * ‖e‖ ≤ (1 + ε) * 1 * ‖e‖ := by
              gcongr
              exact hg1 x
          _ ≤ ρ := by linarith
      have hvs : v (x + (s * g x) • e) = g x • e := by
        simp only [v, hφ1 hmem, hge, Pi.one_apply, one_mul]
      have hd : HasDerivAt (fun s : ℝ ↦ x + (s * g x) • e) (g x • e) s := by
        simpa using (((hasDerivAt_id s).mul_const (g x)).smul_const e).const_add x
      rw [hvs]
      exact (hd.hasFDerivAt.hasMFDerivAt).hasMFDerivWithinAt
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0)
      ⟨by linarith, by linarith⟩ hv1 ((hγ x).isMIntegralCurveOn _) hline
      (by rw [h0]; simp)
    exact heq ⟨by linarith [t.property.1], by linarith [t.property.2]⟩

/-- **The wiggling lemma.** On `D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms, let `K` be compact,
`i` a core direction, `j` a transverse direction, `0 ≤ r < δ` and `N : ℝ`. There is a smooth
diffeotopy `h` of `D` that is the identity off a compact subset of the `δ`-neighbourhood of `K`,
moves every point by less than `δ`, and sends each `(u, v) ∈ K` at time `t` to
`(u, v + t r sin (N uᵢ) eⱼ)`. Taking `N` large makes the image of a segment along the `i`-th core
direction zig-zag between the transverse heights `± r` as often as wanted. -/
theorem exists_wiggling_diffeotopy {m k : ℕ} {K : Set ((Fin m → ℝ) × (Fin k → ℝ))}
    (hK : IsCompact K) (i : Fin m) (j : Fin k) {r δ : ℝ} (hr : 0 ≤ r) (hrδ : r < δ) (N : ℝ) :
    ∃ h : TauCeti.Diffeotopy 𝓘(ℝ, (Fin m → ℝ) × (Fin k → ℝ)) ∞ ((Fin m → ℝ) × (Fin k → ℝ)),
      (∃ C, IsCompact C ∧ C ⊆ thickening δ K ∧ ∀ t, ∀ x ∉ C, h (t, x) = x) ∧
      (∀ t x, dist (h (t, x)) x < δ) ∧
      ∀ t, ∀ x ∈ K, h (t, x) = (x.1, x.2 + Pi.single j ((t : ℝ) * r * Real.sin (N * x.1 i))) := by
  set e : (Fin m → ℝ) × (Fin k → ℝ) := (0, Pi.single j r)
  have hne : ‖e‖ = r := by
    have h2 : ‖e‖ = ‖(Pi.single j r : Fin k → ℝ)‖ := by simp [e]
    rw [h2, ← coe_nnNorm, Pi.nnNorm_single, coe_nnNorm, Real.norm_of_nonneg hr]
  have hg : ContDiff ℝ ∞ fun x : (Fin m → ℝ) × (Fin k → ℝ) ↦ Real.sin (N * x.1 i) :=
    by fun_prop
  obtain ⟨h, hsupp, hsmall, hK'⟩ := exists_diffeotopy_apply_eq_add_smul hK hg
    (fun x ↦ Real.abs_sin_le_one _) (e := e) (fun x s ↦ by simp [e]) (hne ▸ hrδ)
  refine ⟨h, hsupp, fun t x ↦ ?_, fun t x hx ↦ ?_⟩
  · rw [dist_eq_norm]
    calc ‖h (t, x) - x‖ ≤ (t : ℝ) * ‖e‖ := hsmall t x
      _ ≤ 1 * r := by rw [hne]; gcongr; exact t.property.2
      _ < δ := by linarith
  · rw [hK' t x hx]
    ext l
    · simp [e]
    · simp only [e, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_ne l j with rfl | hl
      · simp; ring
      · simp [hl]

end SymplecticGeometry

end
