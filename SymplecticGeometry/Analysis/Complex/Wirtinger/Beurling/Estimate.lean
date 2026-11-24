/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Beurling.Cauchy
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.Analysis.Normed.Module.RCLike.Basic

/-!
# The `L²` estimate for `∂̄ + μ ∂` in the plane

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
* `MeasureTheory.one_sub_mul_eLpNorm_le_eLpNorm_add_smul`: the absorption step, for any measure
  and exponent.
* `ContinuousLinearMap.norm_complexLinearPart_le` and
  `ContinuousLinearMap.norm_complexAntilinearPart_le`: both parts of a real-linear operator have
  norm at most its norm. Their proofs follow the bound in Tau Ceti's
  `ContinuousLinearMap.continuous_complexAntilinearPart`.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B (the Beurling transform on `L²`).
-/

public section

open MeasureTheory Complex Filter Topology ContinuousLinearMap
open scoped ENNReal NNReal SchwartzMap Convolution ContDiff

/-- The complex-linear part of a real-linear operator has norm at most that of the operator. -/
theorem ContinuousLinearMap.norm_complexLinearPart_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (Ψ : E →L[ℝ] F) :
    ‖Ψ.complexLinearPart‖ ≤ ‖Ψ‖ := by
  refine opNorm_le_bound _ (norm_nonneg Ψ) fun v ↦ ?_
  have h := Ψ.le_opNorm_of_le (x := Complex.I • v) (c := ‖v‖) (by simp [norm_smul])
  rw [complexLinearPart_apply, sub_eq_add_neg]
  exact TauCeti.norm_two_inv_smul_add_le (𝕜 := ℝ) (Ψ.le_opNorm v) (by simpa [norm_smul] using h)

/-- The complex-antilinear part of a real-linear operator has norm at most that of the
operator. -/
theorem ContinuousLinearMap.norm_complexAntilinearPart_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (Ψ : E →L[ℝ] F) :
    ‖Ψ.complexAntilinearPart‖ ≤ ‖Ψ‖ := by
  refine opNorm_le_bound _ (norm_nonneg Ψ) fun v ↦ ?_
  have h := Ψ.le_opNorm_of_le (x := Complex.I • v) (c := ‖v‖) (by simp [norm_smul])
  rw [complexAntilinearPart_apply]
  exact TauCeti.norm_two_inv_smul_add_le (𝕜 := ℝ) (Ψ.le_opNorm v) (by simpa [norm_smul] using h)

/-- Pointwise form of `ContinuousLinearMap.norm_complexLinearPart_le`. -/
theorem ContinuousLinearMap.norm_complexLinearPart_apply_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexLinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ :=
  (Ψ.complexLinearPart.le_opNorm v).trans (by gcongr; exact Ψ.norm_complexLinearPart_le)

/-- Pointwise form of `ContinuousLinearMap.norm_complexAntilinearPart_le`. -/
theorem ContinuousLinearMap.norm_complexAntilinearPart_apply_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Ψ : E →L[ℝ] F) (v : E) : ‖Ψ.complexAntilinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ :=
  (Ψ.complexAntilinearPart.le_opNorm v).trans (by gcongr; exact Ψ.norm_complexAntilinearPart_le)

/-- The value of the complex-antilinear part at a fixed vector depends continuously on the
operator. -/
theorem ContinuousLinearMap.continuous_complexAntilinearPart_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (v : E) :
    Continuous fun Ψ : E →L[ℝ] F ↦ Ψ.complexAntilinearPart v := by
  simp only [complexAntilinearPart_apply]
  fun_prop

namespace MeasureTheory

/-- **Absorbing a small multiple.** If `‖μ‖ ≤ m` almost everywhere and `‖g‖_p ≤ ‖f‖_p < ∞`,
then `(1 - m) ‖f‖_p ≤ ‖f + μ g‖_p`. -/
theorem one_sub_mul_eLpNorm_le_eLpNorm_add_smul {α E : Type*} [MeasurableSpace α]
    {ν : Measure α} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g : α → E} {μ : α → ℂ} {m : ℝ≥0} (hg : AEStronglyMeasurable g ν)
    (hμ : AEStronglyMeasurable μ ν)
    (hμm : ∀ᵐ x ∂ν, ‖μ x‖ ≤ m) (hgf : eLpNorm g p ν ≤ eLpNorm f p ν)
    (hf_top : eLpNorm f p ν ≠ ⊤) :
    (1 - (m : ℝ≥0∞)) * eLpNorm f p ν ≤ eLpNorm (fun x ↦ f x + μ x • g x) p ν := by
  have h₁ : eLpNorm f p ν ≤
      eLpNorm (fun x ↦ f x + μ x • g x) p ν + eLpNorm (fun x ↦ μ x • g x) p ν := by
    have h := eLpNorm_sub_le (f := fun x ↦ f x + μ x • g x) (g := fun x ↦ μ x • g x) (μ := ν) hp
    rwa [show ((fun x ↦ f x + μ x • g x) - fun x ↦ μ x • g x) = f from
      funext fun x ↦ add_sub_cancel_right _ _] at h
  have h₂ : eLpNorm (fun x ↦ μ x • g x) p ν ≤ m * eLpNorm f p ν := by
    have hμg : AEStronglyMeasurable (fun x ↦ μ x • g x) ν := hμ.smul hg
    refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (g := g) (c := m) hμg ?_ p).trans ?_
    · filter_upwards [hμm] with x hx
      rw [nnNorm_smul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hx) zero_le
    · rw [ENNReal.smul_def, smul_eq_mul]
      gcongr
  rw [ENNReal.sub_mul fun _ _ ↦ hf_top, one_mul, tsub_le_iff_right]
  exact h₁.trans (by gcongr)

/-- **Passing an `Lᵖ` norm inequality to the limit.** If `a' n → a` and `b' n → b` in `Lᵖ` and
`‖a' n‖_p ≤ ‖b' n‖_p` for every `n`, then `‖a‖_p ≤ ‖b‖_p`. -/
theorem eLpNorm_le_eLpNorm_of_tendsto {α E : Type*} [MeasurableSpace α] {ν : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} (hp : 1 ≤ p) {a b : α → E} {a' b' : ℕ → α → E}
    (hle : ∀ n, eLpNorm (a' n) p ν ≤ eLpNorm (b' n) p ν)
    (hta : Tendsto (fun n ↦ eLpNorm (a' n - a) p ν) atTop (𝓝 0))
    (htb : Tendsto (fun n ↦ eLpNorm (b' n - b) p ν) atTop (𝓝 0)) :
    eLpNorm a p ν ≤ eLpNorm b p ν := by
  refine ge_of_tendsto' (by simpa using (hta.add htb).add tendsto_const_nhds) fun n ↦ ?_
  calc eLpNorm a p ν = eLpNorm ((a - a' n) + a' n) p ν := by rw [sub_add_cancel]
    _ ≤ eLpNorm (a - a' n) p ν + eLpNorm (a' n) p ν := eLpNorm_add_le hp
    _ ≤ eLpNorm (a' n - a) p ν + eLpNorm ((b' n - b) + b) p ν := by
        rw [eLpNorm_sub_comm, sub_add_cancel]
        gcongr
        exact hle n
    _ ≤ eLpNorm (a' n - a) p ν + eLpNorm (b' n - b) p ν + eLpNorm b p ν := by
        rw [add_assoc]
        gcongr
        exact eLpNorm_add_le hp

end MeasureTheory

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
  have hm₂ := SchwartzMap.memLp (SchwartzMap.wirtingerDerivCLM F u) 2 volume
  rw [funext (SchwartzMap.wirtingerDerivCLM_apply u)] at hm₂
  rw [funext (SchwartzMap.conjWirtingerDerivCLM_apply u)] at hm₁
  exact one_sub_mul_eLpNorm_le_eLpNorm_add_smul one_le_two hm₂.aestronglyMeasurable hμ hμm
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
  -- Mollify `v` by normalized bumps of radius `1 / (n + 1)`.
  let φ : ℕ → ContDiffBump (0 : ℂ) := fun n ↦
    ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1), by positivity,
      one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩
  have hφ : Tendsto (fun n ↦ (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w : ℕ → ℂ → F := fun n ↦ v ⋆[(lsmul ℝ ℝ).flip, volume] (φ n).normed volume
  have hw (n : ℕ) : ContDiff ℝ ∞ (w n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_right _ hvl (φ n).contDiff_normed
  have hwc (n : ℕ) : HasCompactSupport (w n) := hv.convolution _ (φ n).hasCompactSupport_normed
  have hdw (n : ℕ) : fderiv ℝ (w n) = (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] D := by
    ext1 z
    rw [h.fderiv_convolution_right hvl hDl _ (φ n).contDiff_normed (φ n).hasCompactSupport_normed
      z fun _ _ ↦ trivial, convolution_flip]
  have hconv := tendsto_eLpNorm_normed_convolution_sub (by norm_num) hφ hD
  have hdc (n : ℕ) : Continuous (fderiv ℝ (w n)) := (hw n).continuous_fderiv (by simp)
  have hP : Continuous fun A : ℂ →L[ℝ] F ↦ A.complexLinearPart 1 :=
    continuous_complexLinearPart.clm_apply continuous_const
  have hQ := continuous_complexAntilinearPart_apply (E := ℂ) (F := F) 1
  refine eLpNorm_le_eLpNorm_of_tendsto one_le_two
    (a' := fun n z ↦ (fderiv ℝ (w n) z).complexLinearPart 1)
    (b' := fun n z ↦ (fderiv ℝ (w n) z).complexAntilinearPart 1) (fun n ↦ ?_) ?_ ?_
  · have hcoe : ⇑((hwc n).toSchwartzMap (hw n)) = w n :=
      funext (HasCompactSupport.toSchwartzMap_toFun _ _)
    have := eLpNorm_wirtingerDeriv_le_eLpNorm_conjWirtingerDeriv ((hwc n).toSchwartzMap (hw n))
    simpa only [hcoe, wirtingerDeriv_eq_complexLinearPart,
      conjWirtingerDeriv_eq_complexAntilinearPart] using this
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv (fun _ ↦ zero_le)
      fun n ↦ eLpNorm_mono ((hP.comp (hdc n)).aestronglyMeasurable.sub
        (hP.comp_aestronglyMeasurable hD.aestronglyMeasurable)) fun z ↦ ?_
    simp only [Pi.sub_apply, hdw]
    rw [← sub_apply, ← ContinuousLinearMap.complexLinearPart_sub]
    exact (norm_complexLinearPart_apply_le _ 1).trans_eq (by rw [norm_one, mul_one])
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv (fun _ ↦ zero_le)
      fun n ↦ eLpNorm_mono ((hQ.comp (hdc n)).aestronglyMeasurable.sub
        (hQ.comp_aestronglyMeasurable hD.aestronglyMeasurable)) fun z ↦ ?_
    simp only [Pi.sub_apply, hdw]
    rw [← sub_apply, ← ContinuousLinearMap.complexAntilinearPart_sub]
    exact (norm_complexAntilinearPart_apply_le _ 1).trans_eq (by rw [norm_one, mul_one])

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
    hD.of_le ((continuous_complexAntilinearPart_apply 1).comp_aestronglyMeasurable
      hD.aestronglyMeasurable) (.of_forall fun z ↦ by
        simpa using norm_complexAntilinearPart_apply_le (D z) 1)
  exact one_sub_mul_eLpNorm_le_eLpNorm_add_smul one_le_two
    ((continuous_complexLinearPart.clm_apply
      (continuous_const (y := (1 : ℂ)))).comp_aestronglyMeasurable
      hD.aestronglyMeasurable)
    hμ hμm (h.eLpNorm_complexLinearPart_le_eLpNorm_complexAntilinearPart hv hD)
    hQ.eLpNorm_ne_top

end TauCeti

end
