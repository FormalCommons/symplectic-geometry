/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Diffeomorphism.Diffeotopy.Flow
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Diffeotopies that push a compact set along a direction

On a finite-dimensional real normed space `E`, take a compact set `K`, a vector `e` and a smooth
function `g` with `|g| ≤ 1` that is constant along `e` at the points of `K`. This file builds a
compactly supported diffeotopy that, at time `t`, moves each point `x ∈ K` to `x + (t g(x)) • e`,
moves no point by more than `t ‖e‖`, and is supported in a compact subset of any given
neighbourhood `thickening δ K` with `‖e‖ < δ`. It moves every point along the line through it in
the direction `e`, and fixes the zeros of `g`.

The diffeotopy is Tau Ceti's `TauCeti.compactlySupportedFlowDiffeotopy` of the field
`y ↦ (φ y * g y) • e`, where `φ` is a smooth cut-off equal to `1` near `K`. Near `K` the field is
constant along the lines `s ↦ x + s • (g x • e)`, so these lines are its flow lines there.
Everywhere the field is a multiple of `e`, so the quotient map `E → E ⧸ ℝ ∙ e` is constant along
its flow lines; and the field vanishes wherever `g` does.

## Main results

* `SymplecticGeometry.maximalIntegralCurve_eqOn_add_smul`: if a `C¹` vector field equals the
  constant `c` along the line `s ↦ x + s • c` for `s` in an open interval around `0`, then its
  maximal integral curve through `x` is that line on the interval.
* `SymplecticGeometry.exists_diffeotopy_apply_eq_add_smul`: the diffeotopy described above.

The proofs adapt two proofs of Tau Ceti to a compact set and a profile `g`:
`TauCeti.eventually_exists_diffeotopy_final_apply_eq`, which takes the compactly supported flow
diffeotopy of a cut-off constant field, and
`TauCeti.maximalIntegralCurve_bumpChartField_extChartAt_symm`, which identifies the flow line of
such a field with a straight segment by uniqueness of integral curves.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia
  (1965), §4, Homogeneity Lemma.
-/

public section

open Set Metric
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If a `C¹` vector field `v` on a real normed space equals the constant `c` at the points
`x + s • c` for `s ∈ (a, b)`, an interval containing `0`, then the maximal integral curve of `v`
through `x` is `s ↦ x + s • c` on `(a, b)`. -/
theorem maximalIntegralCurve_eqOn_add_smul {v : E → E}
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) E)))
    {x c : E} {a b : ℝ} (h0 : (0 : ℝ) ∈ Ioo a b) (hvc : ∀ s ∈ Ioo a b, v (x + s • c) = c) :
    EqOn (maximalIntegralCurve (I := 𝓘(ℝ, E)) v x) (fun s ↦ x + s • c) (Ioo a b) := by
  have hline : IsMIntegralCurveOn (I := 𝓘(ℝ, E)) (fun s : ℝ ↦ x + s • c) v (Ioo a b) :=
    TauCeti.isMIntegralCurveOn_iff_isIntegralCurveOn.2 fun s hs ↦ by
      simpa [hvc s hs] using (((hasDerivAt_id s).smul_const c).const_add x).hasDerivWithinAt
  exact hline.eqOn_maximalIntegralCurve hv h0 (by simp)

variable [FiniteDimensional ℝ E]

/-- **Pushing a compact set along a direction.** On a finite-dimensional real normed space, let
`K` be compact, `e` a vector with `‖e‖ < δ`, and `g` a smooth function with `|g| ≤ 1` such that
`g (x + s • e) = g x` for `x ∈ K` and every real `s`. Then there is a smooth diffeotopy `h` that is
the identity off a compact subset of the `δ`-neighbourhood of `K`, moves every point by at most
`t ‖e‖` at time `t`, and sends each `x ∈ K` at time `t` to `x + (t * g x) • e`. Moreover every
point moves only along the line through it in the direction `e`, and the zeros of `g` stay put. -/
theorem exists_diffeotopy_apply_eq_add_smul {K : Set E} (hK : IsCompact K) {g : E → ℝ}
    (hg : ContDiff ℝ ∞ g) (hg1 : ∀ x, |g x| ≤ 1) {e : E}
    (hge : ∀ x ∈ K, ∀ s : ℝ, g (x + s • e) = g x) {δ : ℝ} (he : ‖e‖ < δ) :
    ∃ h : TauCeti.Diffeotopy 𝓘(ℝ, E) ∞ E,
      (∃ C, IsCompact C ∧ C ⊆ thickening δ K ∧ ∀ t, ∀ x ∉ C, h (t, x) = x) ∧
      (∀ t x, ‖h (t, x) - x‖ ≤ (t : ℝ) * ‖e‖) ∧
      (∀ t, ∀ x ∈ K, h (t, x) = x + ((t : ℝ) * g x) • e) ∧
      (∀ t x, h (t, x) - x ∈ ℝ ∙ e) ∧
      ∀ t x, g x = 0 → h (t, x) = x := by
  -- The cut-off `φ` is `1` on the `ρ`-neighbourhood of `K` and vanishes off the
  -- `ρ'`-neighbourhood, with `‖e‖ < ρ < ρ' < δ`.
  set ρ := (2 * ‖e‖ + δ) / 3
  set ρ' := (‖e‖ + 2 * δ) / 3
  have hρ : ‖e‖ < ρ := by simp only [ρ]; linarith
  have hρ' : ρ < ρ' := by simp only [ρ, ρ']; linarith
  have hρ'δ : ρ' < δ := by simp only [ρ']; linarith
  have hρ0 : 0 < ρ := (norm_nonneg e).trans_lt hρ
  obtain ⟨φ, hφ, hφI, hφs, hφ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    isOpen_thickening isClosed_cthickening (cthickening_subset_thickening' (hρ0.trans hρ') hρ' K)
  set v : E → E := fun y ↦ (φ y * g y) • e
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr ((hφ.mul hg).smul contDiff_const)
  have hv1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun y ↦ (⟨y, v y⟩ : TangentBundle 𝓘(ℝ, E) E)) := hv.of_le (by simp)
  have hC : IsCompact (cthickening ρ' K) := hK.cthickening
  have hzero : ∀ y ∉ cthickening ρ' K, v y = 0 := fun y hy ↦ by
    have : φ y = 0 := by
      rw [← Function.notMem_support, hφs]
      exact fun h ↦ hy (thickening_subset_cthickening _ _ h)
    simp [v, this]
  have hn : (1 : ℕ∞) ≤ ⊤ := le_top
  refine ⟨TauCeti.compactlySupportedFlowDiffeotopy hn hv hC hzero 1, ⟨_, hC,
    cthickening_subset_thickening' (hρ0.trans (hρ'.trans hρ'δ)) hρ'δ K, fun t x hx ↦
      TauCeti.compactlySupportedFlowDiffeotopy_apply_of_eq_zero hn hv hC hzero 1 (hzero x hx) t⟩,
    fun t x ↦ ?_, fun t x hx ↦ ?_, fun t x ↦ ?_, fun t x hgx ↦ ?_⟩
  · -- The field is bounded by `‖e‖`, so points move at speed at most `‖e‖`.
    have hbound : ∀ y, ‖v y‖ ≤ ‖e‖ := fun y ↦ by
      have h1 : |φ y| ≤ 1 := abs_le.mpr ⟨by linarith [(hφI ⟨y, rfl⟩).1], (hφI ⟨y, rfl⟩).2⟩
      simp only [v, norm_smul, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (norm_nonneg e)
        (by nlinarith [abs_nonneg (φ y), abs_nonneg (g y), hg1 y])
    simpa using norm_compactlySupportedFlowDiffeotopy_sub_le hn hv hC hzero zero_le_one hbound t x
  · -- Near `K` the field is the constant `g x • e` along the line through `x`, for times in
    -- `(-ε, 1 + ε)`.
    set ε := (ρ - ‖e‖) / (‖e‖ + 1)
    have hε : 0 < ε := div_pos (by linarith) (by positivity)
    have hεe : (1 + ε) * ‖e‖ < ρ := by
      have : ε * ‖e‖ < ρ - ‖e‖ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg e]
      linarith
    have hvc : ∀ s ∈ Ioo (-ε) (1 + ε), v (x + s • g x • e) = g x • e := fun s hs ↦ by
      have hmem : x + s • g x • e ∈ cthickening ρ K := by
        refine mem_cthickening_of_dist_le _ x _ _ hx ?_
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul, Real.norm_eq_abs,
          Real.norm_eq_abs, ← mul_assoc]
        have hs' : |s| ≤ 1 + ε := abs_le.mpr ⟨by linarith [hs.1], hs.2.le⟩
        calc |s| * |g x| * ‖e‖ ≤ (1 + ε) * 1 * ‖e‖ := by gcongr; exact hg1 x
          _ ≤ ρ := by linarith
      simp only [v]
      rw [(hφ1 _).1 hmem, one_mul, smul_smul, hge x hx]
    simp only [TauCeti.compactlySupportedFlowDiffeotopy_apply hn hv hC hzero 1 (t, x), one_mul]
    rw [maximalIntegralCurve_eqOn_add_smul hv1 ⟨by linarith, by linarith⟩ hvc
      ⟨by linarith [t.property.1], by linarith [t.property.2]⟩, mul_smul]
  · -- The field is a multiple of `e`, so the quotient map onto `E ⧸ ℝ ∙ e` is constant along
    -- its flow lines. The closedness of `ℝ ∙ e` is the instance that makes the quotient a normed
    -- space, which `map_compactlySupportedFlowDiffeotopy` asks of its target.
    have : IsClosed ((ℝ ∙ e : Submodule ℝ E) : Set E) := Submodule.isClosed_of_finiteDimensional _
    have := map_compactlySupportedFlowDiffeotopy hn hv hC hzero 1 (ℝ ∙ e).mkQL
      (fun y ↦ by simp [v]) t x
    simpa [Submodule.Quotient.eq] using this
  · -- The zeros of `g` are zeros of the field, so they stay put. The `show` states the equation
    -- in `E`, where `simp` proves it; the lemma asks for it in the tangent space at `x`, which is
    -- `E` by definition.
    exact TauCeti.compactlySupportedFlowDiffeotopy_apply_of_eq_zero hn hv hC hzero 1
      (show v x = 0 by simp [v, hgx]) t

end SymplecticGeometry

end
