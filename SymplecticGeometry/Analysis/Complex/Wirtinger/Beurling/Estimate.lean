/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Beurling.Cauchy
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.Wirtinger.Lp
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.UnifTight
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.FDerivApply
import SymplecticGeometry.Analysis.Complex.Wirtinger.Basic
import SymplecticGeometry.Analysis.Complex.Wirtinger.Commutator
import SymplecticGeometry.Analysis.Normed.Operator.ComplexLinearPart
import SymplecticGeometry.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The `L²` estimate for `∂̄ + μ ∂` in the plane, and its higher orders

For maps `v` from the plane to a complex Hilbert space, the `L²` Beurling transform has norm at
most one and sends `∂̄v` to `∂v`, so `‖∂v‖₂ ≤ ‖∂̄v‖₂`. A coefficient `μ` with `‖μ‖ ≤ m`
almost everywhere then changes `∂̄` by a term of norm at most `m ‖∂̄v‖₂`, which gives
`(1 - m) ‖∂̄v‖₂ ≤ ‖∂̄v + μ ∂v‖₂`; for `m < 1` this bounds `∂̄v` by `∂̄v + μ ∂v`.

## Main results

* `TauCeti.eLpNorm_wirtingerDeriv_le_eLpNorm_conjWirtingerDeriv`: `‖∂u‖₂ ≤ ‖∂̄u‖₂` for a Schwartz
  function `u`, from `TauCeti.beurlingL2_toLp_conjWirtingerDerivCLM` and
  `TauCeti.norm_beurlingL2_le`.
* `TauCeti.eLpNorm_conjWirtingerDeriv_le_of_norm_le`: the estimate for `∂̄ + μ ∂` on Schwartz
  functions.
* `TauCeti.HasWeakFDerivOn.eLpNorm_complexLinearPart_le_eLpNorm_complexAntilinearPart` and
  `TauCeti.HasWeakFDerivOn.eLpNorm_complexAntilinearPart_le_of_norm_le`: the same two estimates
  for a compactly supported `v` with a weak derivative `D ∈ L²`, where `∂v` and `∂̄v` are the
  complex-linear and complex-antilinear parts of `D`. Mollification reduces them to the
  Schwartz case.
* `ContDiff.eLpNorm_conjWirtingerDeriv_le_of_norm_le` and `ContDiff.eLpNorm_fderiv_le_of_norm_le`:
  for a compactly supported `C¹` map `v` and a coefficient with `‖μ‖ ≤ m` only on the support
  of `v`, the estimate `(1 - m) ‖∂̄v‖₂ ≤ ‖∂̄v + μ ∂v‖₂` and, for `m < 1`, the bound
  `‖Dv‖₂ ≤ 2 (1 - m)⁻¹ ‖∂̄v + μ ∂v‖₂` of the whole derivative. They follow from the previous two
  results, applied to the classical derivative (Tau Ceti's `ContDiffOn.hasWeakFDerivOn_fderiv`)
  and to the coefficient `μ` cut off outside the support of `v`, where `∂v` vanishes. The bound
  of `Dv` by `∂v` and `∂̄v` is Tau Ceti's `TauCeti.eLpNorm_wirtingerPartsCLM_le`, through
  `TauCeti.fderiv_eq_wirtingerPartsCLM`.
* `TauCeti.exists_sum_eLpNorm_iteratedFDeriv_le_of_norm_le`: the estimate at every order. For
  `μ` smooth near a compact set `K` with `‖μ‖ ≤ m < 1` on `K`, the `L²` norms of the derivatives
  of order at most `k + 1` of a smooth `v` supported in `K` are bounded by a constant times those
  of order at most `k` of `∂̄v + μ ∂v` and of `v`. The proof is an induction on `k`, starting from
  `ContDiff.eLpNorm_fderiv_le_of_norm_le`. The step applies the order-`k` estimate to the
  partial derivatives `∂₁v` and `∂_I v`, rewrites `∂̄ + μ ∂` of them by the commutator
  `TauCeti.conjWirtingerDeriv_fderiv_apply_add_smul_wirtingerDeriv`, bounds its lower-order term
  by `TauCeti.exists_eLpNorm_iteratedFDeriv_fderiv_smul_wirtingerDeriv_le`, and returns to `v`
  by `ContDiff.eLpNorm_iteratedFDeriv_succ_le_add_fderiv_apply_one_I`. A cutoff reduces it to a
  coefficient smooth on the whole plane.

The absorption step is `MeasureTheory.one_sub_mul_eLpNorm_le_eLpNorm_add_smul`, and the passage
to the limit `MeasureTheory.eLpNorm_le_eLpNorm_of_tendsto`, with Tau Ceti's
`MeasureTheory.tendsto_eLpNorm_comp_sub_comp_of_tendsto` for the convergence of `∂` and `∂̄` of
the mollified maps.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B (the Beurling transform on `L²`; derivatives of higher order from the estimate
  applied to partial derivatives).
-/

public section

open MeasureTheory Complex Filter Topology ContinuousLinearMap
open scoped ENNReal NNReal SchwartzMap Convolution ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **`‖∂u‖₂ ≤ ‖∂̄u‖₂` on Schwartz functions**: the `L²` Beurling transform, which has norm at most
one, sends `∂̄u` to `∂u`. -/
theorem eLpNorm_wirtingerDeriv_le_eLpNorm_conjWirtingerDeriv (u : 𝓢(ℂ, F)) :
    eLpNorm (fun z ↦ wirtingerDeriv (⇑u) z 1) 2 volume ≤
      eLpNorm (fun z ↦ conjWirtingerDeriv (⇑u) z 1) 2 volume := by
  have hle : ‖(SchwartzMap.wirtingerDerivCLM F u).toLp 2‖ ≤
      ‖(SchwartzMap.conjWirtingerDerivCLM F u).toLp 2‖ := by
    rw [← beurlingL2_toLp_conjWirtingerDerivCLM]
    exact ((beurlingL2 F).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_beurlingL2_le (F := F)))
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp] at hle
  rw [← funext (SchwartzMap.wirtingerDerivCLM_apply u),
    ← funext (SchwartzMap.conjWirtingerDerivCLM_apply u)]
  exact (ENNReal.toReal_le_toReal ((SchwartzMap.memLp _ 2 volume).eLpNorm_ne_top)
      ((SchwartzMap.memLp _ 2 volume).eLpNorm_ne_top)).1 hle

/-- **The estimate for `∂̄ + μ ∂` on Schwartz functions**: if `‖μ‖ ≤ m` almost everywhere, then
`(1 - m) ‖∂̄u‖₂ ≤ ‖∂̄u + μ ∂u‖₂`. -/
theorem eLpNorm_conjWirtingerDeriv_le_of_norm_le (u : 𝓢(ℂ, F)) {μ : ℂ → ℂ}
    (hμ : AEStronglyMeasurable μ volume) {m : ℝ≥0} (hμm : ∀ᵐ z, ‖μ z‖ ≤ m) :
    (1 - (m : ℝ≥0∞)) * eLpNorm (fun z ↦ conjWirtingerDeriv (⇑u) z 1) 2 volume ≤
      eLpNorm (fun z ↦ conjWirtingerDeriv (⇑u) z 1 + μ z • wirtingerDeriv (⇑u) z 1) 2 volume := by
  have hm₁ := SchwartzMap.memLp (SchwartzMap.conjWirtingerDerivCLM F u) 2 volume
  rw [funext (SchwartzMap.conjWirtingerDerivCLM_apply u)] at hm₁
  exact one_sub_mul_eLpNorm_le_eLpNorm_add_smul one_le_two hμ hμm
    (eLpNorm_wirtingerDeriv_le_eLpNorm_conjWirtingerDeriv u) hm₁.eLpNorm_ne_top

/-- **`‖∂v‖₂ ≤ ‖∂̄v‖₂` for compactly supported `W^{1,2}` maps.** If `D` is a weak derivative of a
compactly supported `v` on the plane and `D ∈ L²`, then the `L²` norm of its complex-linear part
`∂v` is at most that of its complex-antilinear part `∂̄v`. -/
theorem HasWeakFDerivOn.eLpNorm_complexLinearPart_le_eLpNorm_complexAntilinearPart
    {v : ℂ → F} {D : ℂ → ℂ →L[ℝ] F} (h : HasWeakFDerivOn volume ⊤ v D)
    (hv : HasCompactSupport v) (hD : MemLp D 2 volume) :
    eLpNorm (fun z ↦ (D z).complexLinearPart 1) 2 volume ≤
      eLpNorm (fun z ↦ (D z).complexAntilinearPart 1) 2 volume := by
  have hvl : LocallyIntegrable v volume := locallyIntegrableOn_univ.1 h.locallyIntegrableOn
  have hDl : LocallyIntegrable D volume := hD.locallyIntegrable one_le_two
  -- Mollify `v` by Tau Ceti's shrinking normalized bumps.
  let φ : ℕ → ContDiffBump (0 : ℂ) := ContDiffBump.shrinking one_pos
  let w : ℕ → ℂ → F := fun n ↦ v ⋆[(lsmul ℝ ℝ).flip, volume] (φ n).normed volume
  have hw (n : ℕ) : ContDiff ℝ ∞ (w n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_right _ hvl (φ n).contDiff_normed
  have hwc (n : ℕ) : HasCompactSupport (w n) := hv.convolution _ (φ n).hasCompactSupport_normed
  have hdw (n : ℕ) : fderiv ℝ (w n) = (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] D := by
    ext1 z
    rw [h.fderiv_convolution_right hvl hDl _ (φ n).contDiff_normed (φ n).hasCompactSupport_normed
      z fun _ _ ↦ trivial, convolution_flip]
  have hconv :=
    tendsto_eLpNorm_normed_convolution_sub (by norm_num) (ContDiffBump.tendsto_rOut_shrinking
      (c := (0 : ℂ)) one_pos) hD
  have hdm (n : ℕ) : MemLp (fderiv ℝ (w n)) 2 volume :=
    ((hw n).continuous_fderiv (by simp)).memLp_of_hasCompactSupport ((hwc n).fderiv (𝕜 := ℝ))
  have hconv' : Tendsto (fun n ↦ eLpNorm (fderiv ℝ (w n) - D) 2 volume) atTop (𝓝 0) := by
    simpa only [hdw] using hconv
  -- A continuous `P` with `‖P A‖ ≤ ‖A‖` keeps the convergence of `D w n → D`.
  have hlim (P : (ℂ →L[ℝ] F) → F) (hPc : Continuous P) (hPn : ∀ A, ‖P A‖ ≤ ‖A‖) :
      Tendsto (fun n ↦ eLpNorm (P ∘ fderiv ℝ (w n) - P ∘ D) 2 volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_comp_sub_comp_of_tendsto one_le_two (by norm_num) hPc hPn hdm hD hconv'
  refine eLpNorm_le_eLpNorm_of_tendsto one_le_two
    (a' := fun n z ↦ (fderiv ℝ (w n) z).complexLinearPart 1)
    (b' := fun n z ↦ (fderiv ℝ (w n) z).complexAntilinearPart 1) (.of_forall fun n ↦ ?_)
    (hlim (fun A ↦ A.complexLinearPart 1)
      ((continuous_eval_const 1).comp continuous_complexLinearPart)
      fun A ↦ (norm_complexLinearPart_apply_le A 1).trans_eq (by rw [norm_one, mul_one]))
    (hlim (fun A ↦ A.complexAntilinearPart 1)
      ((continuous_eval_const 1).comp continuous_complexAntilinearPart)
      fun A ↦ (norm_complexAntilinearPart_apply_le A 1).trans_eq (by rw [norm_one, mul_one]))
  have hcoe : ⇑((hwc n).toSchwartzMap (hw n)) = w n :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have := eLpNorm_wirtingerDeriv_le_eLpNorm_conjWirtingerDeriv ((hwc n).toSchwartzMap (hw n))
  simpa only [hcoe, wirtingerDeriv_eq_complexLinearPart,
    conjWirtingerDeriv_eq_complexAntilinearPart] using this

/-- **The estimate for `∂̄ + μ ∂` on compactly supported `W^{1,2}` maps.** If `D ∈ L²` is a weak
derivative of a compactly supported `v` on the plane and `‖μ‖ ≤ m` almost everywhere, then
`(1 - m) ‖∂̄v‖₂ ≤ ‖∂̄v + μ ∂v‖₂`, where `∂v` and `∂̄v` are the complex-linear and
complex-antilinear parts of `D`. -/
theorem HasWeakFDerivOn.eLpNorm_complexAntilinearPart_le_of_norm_le
    {v : ℂ → F} {D : ℂ → ℂ →L[ℝ] F} (h : HasWeakFDerivOn volume ⊤ v D)
    (hv : HasCompactSupport v) (hD : MemLp D 2 volume) {μ : ℂ → ℂ}
    (hμ : AEStronglyMeasurable μ volume) {m : ℝ≥0} (hμm : ∀ᵐ z, ‖μ z‖ ≤ m) :
    (1 - (m : ℝ≥0∞)) * eLpNorm (fun z ↦ (D z).complexAntilinearPart 1) 2 volume ≤
      eLpNorm (fun z ↦ (D z).complexAntilinearPart 1 + μ z • (D z).complexLinearPart 1) 2
        volume := by
  have hQ : MemLp (fun z ↦ (D z).complexAntilinearPart 1) 2 volume :=
    hD.of_le (((continuous_eval_const 1).comp
      continuous_complexAntilinearPart).comp_aestronglyMeasurable hD.aestronglyMeasurable)
      (.of_forall fun z ↦ by
        simpa using norm_complexAntilinearPart_apply_le (D z) 1)
  exact one_sub_mul_eLpNorm_le_eLpNorm_add_smul one_le_two hμ hμm
    (h.eLpNorm_complexLinearPart_le_eLpNorm_complexAntilinearPart hv hD)
    hQ.eLpNorm_ne_top

/-- **The estimate for `∂̄ + μ ∂` on compactly supported `C¹` maps.** If `v` is a compactly
supported `C¹` map on the plane and `‖μ‖ ≤ m` on the topological support of `v`, then
`(1 - m) ‖∂̄v‖₂ ≤ ‖∂̄v + μ ∂v‖₂`. Off the support of `v` the coefficient `μ` is arbitrary, since
`∂v` vanishes there. -/
theorem _root_.ContDiff.eLpNorm_conjWirtingerDeriv_le_of_norm_le {v : ℂ → F}
    (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) {μ : ℂ → ℂ}
    (hμ : AEStronglyMeasurable μ (volume.restrict (tsupport v))) {m : ℝ≥0}
    (hμm : ∀ z ∈ tsupport v, ‖μ z‖ ≤ m) :
    (1 - (m : ℝ≥0∞)) * eLpNorm (fun z ↦ conjWirtingerDeriv v z 1) 2 volume ≤
      eLpNorm (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1) 2 volume := by
  have hν : AEStronglyMeasurable ((tsupport v).indicator μ) volume :=
    (aestronglyMeasurable_indicator_iff (isClosed_tsupport v).measurableSet).2 hμ
  have hνm : ∀ᵐ z, ‖(tsupport v).indicator μ z‖ ≤ m := .of_forall fun z ↦ by
    by_cases hz : z ∈ tsupport v
    · simpa [Set.indicator_of_mem hz] using hμm z hz
    · simp [Set.indicator_of_notMem hz]
  have heq := conjWirtingerDeriv_add_smul_wirtingerDeriv_congr (v := v)
    (Set.eqOn_indicator (f := μ)) 1
  have hD : MemLp (fderiv ℝ v) 2 volume :=
    (hv.continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport (hc.fderiv (𝕜 := ℝ))
  have := (hv.contDiffOn (s := Set.univ)).hasWeakFDerivOn_fderiv (μ := volume) (Ω := ⊤)
    |>.eLpNorm_complexAntilinearPart_le_of_norm_le hc hD hν hνm
  simpa only [← wirtingerDeriv_eq_complexLinearPart, ← conjWirtingerDeriv_eq_complexAntilinearPart,
    heq] using this

/-- **The bound of the whole derivative by `∂̄ + μ ∂`.** If `v` is a compactly supported `C¹` map
on the plane and `‖μ‖ ≤ m < 1` on the topological support of `v`, then
`‖Dv‖₂ ≤ 2 (1 - m)⁻¹ ‖∂̄v + μ ∂v‖₂`. -/
theorem _root_.ContDiff.eLpNorm_fderiv_le_of_norm_le {v : ℂ → F}
    (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v) {μ : ℂ → ℂ}
    (hμ : AEStronglyMeasurable μ (volume.restrict (tsupport v))) {m : ℝ≥0} (hm : m < 1)
    (hμm : ∀ z ∈ tsupport v, ‖μ z‖ ≤ m) :
    eLpNorm (fderiv ℝ v) 2 volume ≤ 2 * (1 - (m : ℝ≥0∞))⁻¹ *
      eLpNorm (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1) 2 volume := by
  have hdv : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hD : MemLp (fderiv ℝ v) 2 volume := hdv.memLp_of_hasCompactSupport (hc.fderiv (𝕜 := ℝ))
  have hw : Continuous fun z ↦ wirtingerDeriv v z 1 := hv.continuous_wirtingerDeriv_apply 1
  have hcw : Continuous fun z ↦ conjWirtingerDeriv v z 1 :=
    hv.continuous_conjWirtingerDeriv_apply 1
  have hle : eLpNorm (fun z ↦ wirtingerDeriv v z 1) 2 volume ≤
      eLpNorm (fun z ↦ conjWirtingerDeriv v z 1) 2 volume := by
    simpa only [← wirtingerDeriv_eq_complexLinearPart,
      ← conjWirtingerDeriv_eq_complexAntilinearPart] using
      (hv.contDiffOn (s := Set.univ)).hasWeakFDerivOn_fderiv (μ := volume) (Ω := ⊤)
        |>.eLpNorm_complexLinearPart_le_eLpNorm_complexAntilinearPart hc hD
  have hm₀ : (1 - (m : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt (by exact_mod_cast hm)).ne'
  have habs : eLpNorm (fun z ↦ conjWirtingerDeriv v z 1) 2 volume ≤ (1 - (m : ℝ≥0∞))⁻¹ *
      eLpNorm (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1) 2 volume := by
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (.inl hm₀) (.inl (by simp)), mul_comm]
    exact hv.eLpNorm_conjWirtingerDeriv_le_of_norm_le hc hμ hμm
  calc eLpNorm (fderiv ℝ v) 2 volume
      ≤ eLpNorm (fun z ↦ wirtingerDeriv v z 1) 2 volume +
          eLpNorm (fun z ↦ conjWirtingerDeriv v z 1) 2 volume := by
        rw [funext (fderiv_eq_wirtingerPartsCLM v)]
        exact eLpNorm_wirtingerPartsCLM_le one_le_two hw.aestronglyMeasurable
          hcw.aestronglyMeasurable
    _ ≤ 2 * eLpNorm (fun z ↦ conjWirtingerDeriv v z 1) 2 volume := by
        rw [two_mul]
        gcongr
    _ ≤ 2 * (1 - (m : ℝ≥0∞))⁻¹ *
          eLpNorm (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1) 2 volume := by
        rw [mul_assoc]
        gcongr

section HigherOrder

omit [CompleteSpace F] in
/-- The step of the induction for one partial derivative `∂ₐv`, `‖a‖ = 1`: the order-`k`
estimate applied to `∂ₐv`, with the commutator and the lower-order bound, bounds the derivatives
of `∂ₐv` up to order `k + 1`. -/
private theorem sum_eLpNorm_iteratedFDeriv_fderiv_apply_le {K : Set ℂ} {μ : ℂ → ℂ}
    (hμ : ContDiff ℝ ∞ μ) {k : ℕ} {C₀ C₁ : ℝ≥0}
    (h₀ : ∀ v : ℂ → F, ContDiff ℝ ∞ v → tsupport v ⊆ K →
      ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j v) 2 volume ≤
        C₀ * (∑ j ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ j
            (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1)) 2 volume +
          ∑ j ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ j v) 2 volume))
    {a : ℂ} (ha : ‖a‖ = 1)
    (h₁ : ∀ v : ℂ → F, ContDiff ℝ (k + 1 : ℕ) v → tsupport v ⊆ K → ∀ j ≤ k,
      eLpNorm (iteratedFDeriv ℝ j (fun z ↦ fderiv ℝ μ z a • wirtingerDeriv v z 1)) 2 volume ≤
        C₁ * ∑ i ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ i v) 2 volume)
    {v : ℂ → F} (hv : ContDiff ℝ ∞ v) (hvK : tsupport v ⊆ K) :
    ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j (fun z ↦ fderiv ℝ v z a)) 2 volume ≤
      C₀ * (∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j
            (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1)) 2 volume +
          (k + 1 : ℝ≥0∞) * C₁ *
            ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j v) 2 volume +
          ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j v) 2 volume) := by
  set P : (ℂ → F) → ℂ → F := fun u z ↦ conjWirtingerDeriv u z 1 + μ z • wirtingerDeriv u z 1
  set w : ℂ → F := fun z ↦ fderiv ℝ v z a
  set g : ℂ → F := fun z ↦ fderiv ℝ μ z a • wirtingerDeriv v z 1
  set A := ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j (P v)) 2 volume
  set B := ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j v) 2 volume
  have hw : ContDiff ℝ ∞ w := (hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hPv : ContDiff ℝ ∞ (P v) :=
    (hv.conjWirtingerDeriv_apply (by simp) 1).add (hμ.smul (hv.wirtingerDeriv_apply (by simp) 1))
  have hdPv : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ (P v) z a) :=
    (hPv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  -- The commutator: `P (∂ₐv) = ∂ₐ (P v) - (∂ₐμ) ∂v`.
  have hcomm : P w = (fun z ↦ fderiv ℝ (P v) z a) - g := funext fun z ↦ by
    rw [Pi.sub_apply]
    exact conjWirtingerDeriv_fderiv_apply_add_smul_wirtingerDeriv (hv.of_le (by simp)).contDiffAt
      (hμ.differentiable (by simp) z) a 1
  have hg : ContDiff ℝ ∞ g := by
    rw [show g = (fun z ↦ fderiv ℝ (P v) z a) - P w by rw [hcomm, sub_sub_cancel]]
    exact hdPv.sub ((hw.conjWirtingerDeriv_apply (by simp) 1).add
      (hμ.smul (hw.wirtingerDeriv_apply (by simp) 1)))
  have hPw : ∀ j ≤ k, eLpNorm (iteratedFDeriv ℝ j (P w)) 2 volume ≤
      eLpNorm (iteratedFDeriv ℝ (j + 1) (P v)) 2 volume + C₁ * B := by
    intro j hj
    rw [hcomm, iteratedFDeriv_sub (hdPv.of_le (by simp)) (hg.of_le (by simp))]
    refine (eLpNorm_sub_le one_le_two).trans ?_
    gcongr
    · simpa [ha] using (hPv.of_le (by simp)).eLpNorm_iteratedFDeriv_fderiv_apply_le volume a 2
    · exact h₁ v (hv.of_le (by simp)) hvK j hj
  have hwv : ∀ j, eLpNorm (iteratedFDeriv ℝ j w) 2 volume ≤
      eLpNorm (iteratedFDeriv ℝ (j + 1) v) 2 volume := fun j ↦ by
    simpa [ha] using (hv.of_le (by simp)).eLpNorm_iteratedFDeriv_fderiv_apply_le volume a 2
  refine (h₀ w hw ((tsupport_fderiv_apply_subset ℝ a).trans hvK)).trans ?_
  gcongr (C₀ : ℝ≥0∞) * ?_
  calc _ ≤ ∑ j ∈ Finset.range (k + 1),
          (eLpNorm (iteratedFDeriv ℝ (j + 1) (P v)) 2 volume + C₁ * B) +
        ∑ j ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ (j + 1) v) 2 volume := by
        gcongr with j hj
        · exact hPw j (Finset.mem_range_succ_iff.1 hj)
        · exact hwv j
    _ ≤ A + (k + 1 : ℝ≥0∞) * C₁ * B + B := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← mul_assoc]
        push_cast
        gcongr
        · exact le_of_le_of_eq le_self_add
            (Finset.sum_range_succ' (fun j ↦ eLpNorm (iteratedFDeriv ℝ j (P v)) 2 volume)
              (k + 1)).symm
        · exact le_of_le_of_eq le_self_add
            (Finset.sum_range_succ' (fun j ↦ eLpNorm (iteratedFDeriv ℝ j v) 2 volume) (k + 1)).symm

/-- The estimate at every order for a coefficient `μ` smooth on the whole plane. -/
private theorem exists_sum_eLpNorm_iteratedFDeriv_le_of_contDiff {K : Set ℂ} (hK : IsCompact K)
    {μ : ℂ → ℂ} (hμ : ContDiff ℝ ∞ μ) {m : ℝ≥0} (hm : m < 1) (hμK : ∀ z ∈ K, ‖μ z‖ ≤ m)
    (k : ℕ) :
    ∃ C : ℝ≥0, ∀ v : ℂ → F, ContDiff ℝ ∞ v → tsupport v ⊆ K →
      ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j v) 2 volume ≤
        C * (∑ j ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ j
            (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1)) 2 volume +
          ∑ j ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ j v) 2 volume) := by
  induction k with
  | zero =>
    have hm₀ : (1 - (m : ℝ≥0∞))⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.2 (tsub_pos_of_lt (by exact_mod_cast hm)).ne'
    refine ⟨(1 + 2 * (1 - (m : ℝ≥0∞))⁻¹).toNNReal, fun v hv hvK ↦ ?_⟩
    rw [ENNReal.coe_toNNReal (by finiteness)]
    have hμv : AEStronglyMeasurable μ (volume.restrict (tsupport v)) :=
      hμ.continuous.aestronglyMeasurable
    have h := (hv.of_le (by simp)).eLpNorm_fderiv_le_of_norm_le
      (hK.of_isClosed_subset (isClosed_tsupport v) hvK) hμv hm fun z hz ↦ hμK z (hvK hz)
    simp only [zero_add, Finset.sum_range_succ, Finset.sum_range_zero]
    have hPv : ContDiff ℝ ∞ (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1) :=
      (hv.conjWirtingerDeriv_apply (by simp) 1).add (hμ.smul (hv.wirtingerDeriv_apply (by simp) 1))
    rw [eLpNorm_congr_norm_ae ((hv.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
        ((hv.continuous_fderiv (by simp)).aestronglyMeasurable)
        (.of_forall fun _ ↦ norm_iteratedFDeriv_one v),
      eLpNorm_congr_norm_ae ((hPv.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
        hPv.continuous.aestronglyMeasurable (.of_forall fun _ ↦ norm_iteratedFDeriv_zero)]
    set A := eLpNorm (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1) 2 volume
    set B := eLpNorm (iteratedFDeriv ℝ 0 v) 2 volume
    calc B + eLpNorm (fderiv ℝ v) 2 volume ≤ (A + B) + 2 * (1 - (m : ℝ≥0∞))⁻¹ * (A + B) := by
          gcongr
          · exact le_add_self
          · exact h.trans (by gcongr; exact le_self_add)
      _ = _ := by ring
  | succ k ih =>
    obtain ⟨C₀, hC₀⟩ := ih
    have hμk : ContDiffOn ℝ (k + 1 : ℕ) μ Set.univ :=
      (contDiff_infty.1 hμ (k + 1)).contDiffOn
    obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_iteratedFDeriv_fderiv_smul_wirtingerDeriv_le (F := F)
      volume one_le_two hK isOpen_univ (Set.subset_univ K) hμk 1
    obtain ⟨C₂, hC₂⟩ := exists_eLpNorm_iteratedFDeriv_fderiv_smul_wirtingerDeriv_le (F := F)
      volume one_le_two hK isOpen_univ (Set.subset_univ K) hμk I
    refine ⟨1 + C₀ * (2 + (k + 1) * C₁) + C₀ * (2 + (k + 1) * C₂), fun v hv hvK ↦ ?_⟩
    set A := ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j
      (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1)) 2 volume
    set B := ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j v) 2 volume
    have h₁ := sum_eLpNorm_iteratedFDeriv_fderiv_apply_le hμ hC₀ (by simp) hC₁ hv hvK
    have h₂ := sum_eLpNorm_iteratedFDeriv_fderiv_apply_le hμ hC₀ (by simp) hC₂ hv hvK
    have hB : eLpNorm (iteratedFDeriv ℝ 0 v) 2 volume ≤ B :=
      Finset.single_le_sum (f := fun j ↦ eLpNorm (iteratedFDeriv ℝ j v) 2 volume)
        (fun _ _ ↦ bot_le) (by simp)
    calc ∑ j ∈ Finset.range (k + 1 + 2), eLpNorm (iteratedFDeriv ℝ j v) 2 volume
        = ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ (j + 1) v) 2 volume +
            eLpNorm (iteratedFDeriv ℝ 0 v) 2 volume := Finset.sum_range_succ' _ _
      _ ≤ ∑ j ∈ Finset.range (k + 2),
            (eLpNorm (iteratedFDeriv ℝ j (fun z ↦ fderiv ℝ v z 1)) 2 volume +
              eLpNorm (iteratedFDeriv ℝ j (fun z ↦ fderiv ℝ v z I)) 2 volume) + B := by
          gcongr with j
          exact (hv.of_le (by simp)).eLpNorm_iteratedFDeriv_succ_le_add_fderiv_apply_one_I
            volume one_le_two
      _ ≤ C₀ * (A + (k + 1 : ℝ≥0∞) * C₁ * B + B) + C₀ * (A + (k + 1 : ℝ≥0∞) * C₂ * B + B) + B := by
          rw [Finset.sum_add_distrib]
          gcongr
      _ ≤ C₀ * ((A + B) + (k + 1 : ℝ≥0∞) * C₁ * (A + B) + (A + B)) +
            C₀ * ((A + B) + (k + 1 : ℝ≥0∞) * C₂ * (A + B) + (A + B)) + (A + B) := by
          gcongr <;> first | exact le_self_add | exact le_add_self
      _ = _ := by push_cast; ring

/-- **The `W^{k+1,2}` estimate for `∂̄ + μ ∂` in the plane.** Let `K ⊆ ℂ` be compact, `μ` smooth
on an open set `U ⊇ K` with `‖μ‖ ≤ m < 1` on `K`, and `k : ℕ`. There is a constant `C` such that
every smooth `v : ℂ → F` with `tsupport v ⊆ K` satisfies
`∑_{j ≤ k + 1} ‖Dʲv‖₂ ≤ C (∑_{j ≤ k} ‖Dʲ(∂̄v + μ ∂v)‖₂ + ∑_{j ≤ k} ‖Dʲv‖₂)`. -/
theorem exists_sum_eLpNorm_iteratedFDeriv_le_of_norm_le {K U : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {μ : ℂ → ℂ} (hμ : ContDiffOn ℝ ∞ μ U) {m : ℝ≥0} (hm : m < 1)
    (hμK : ∀ z ∈ K, ‖μ z‖ ≤ m) (k : ℕ) :
    ∃ C : ℝ≥0, ∀ v : ℂ → F, ContDiff ℝ ∞ v → tsupport v ⊆ K →
      ∑ j ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ j v) 2 volume ≤
        C * (∑ j ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ j
            (fun z ↦ conjWirtingerDeriv v z 1 + μ z • wirtingerDeriv v z 1)) 2 volume +
          ∑ j ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ j v) 2 volume) := by
  -- Replace `μ` by `ρ = χ μ`, smooth on the plane and equal to `μ` on `K`.
  obtain ⟨χ, hχ, -, hχ1, -, hχU⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one hU hKU
  set ρ : ℂ → ℂ := fun z ↦ χ z • μ z
  have hρK (z : ℂ) (hz : z ∈ K) : ρ z = μ z := by simp [ρ, (hχ1 z hz).self_of_nhds]
  obtain ⟨C, hC⟩ := exists_sum_eLpNorm_iteratedFDeriv_le_of_contDiff (F := F) (μ := ρ) hK
    (hμ.contDiff_smul_of_tsupport_subset hU hχ.contDiffOn hχU) hm
    (fun z hz ↦ by rw [hρK z hz]; exact hμK z hz) k
  refine ⟨C, fun v hv hvK ↦ ?_⟩
  -- Since `∂v` vanishes off the support of `v`, `∂̄v + ρ ∂v = ∂̄v + μ ∂v`.
  rw [← conjWirtingerDeriv_add_smul_wirtingerDeriv_congr (fun z hz ↦ hρK z (hvK hz)) 1]
  exact hC v hv hvK

end HigherOrder

end TauCeti

end
