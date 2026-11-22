/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import SymplecticGeometry.Geometry.Manifold.Riemannian.PartialDiffeomorph
import TauCeti.Analysis.InnerProductSpace.Comass
import TauCeti.Geometry.Manifold.Riemannian.Codifferential
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.ModelSpace
import TauCeti.Geometry.Manifold.Riemannian.FormMetric
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# The Hilbert space of `L²` differential forms

Let `M` be a compact manifold with a smooth Riemannian metric and an orientation `o`. The
`L²` inner product of two smooth real `k`-forms is
`⟪α, β⟫_{L²} = ∫_M ⟨α, β⟩ dV`, the integral against the orientation of the pointwise inner
product of the forms times the Riemannian volume form
(`TauCeti.SmoothForm.l2Inner`). It equals the integral of `⟨α, β⟩` against the Riemannian
volume measure (`TauCeti.SmoothForm.l2Inner_eq_integral`), and so it is a positive definite
symmetric bilinear form in every dimension, including dimension zero.

The Hilbert space `SymplecticGeometry.L2Form o k` is the completion of the smooth `k`-forms for
this inner product. The smooth forms embed in it injectively and densely
(`SymplecticGeometry.L2Form.ofSmooth`). A linear map `L` on smooth forms that is bounded in the
`L²` norm therefore extends uniquely to a continuous linear map on `L2Form o k`: this is
Mathlib's `L.extendOfNorm L2Form.ofSmooth` (`LinearMap.extendOfNorm`), whose lemmas take
`L2Form.denseRange_ofSmooth`.

A chart `ψ : M → E` onto an open subset of `E` and a smooth cutoff `χ` supported in its source
turn a smooth form `α` into a function on `E`, `y ↦ χ (ψ⁻¹ y) • (ψ⁻¹)^* α (y)` on `ψ.target` and
`0` elsewhere (`TauCeti.SmoothForm.localize`). It is continuous with compact support, so in `L²`
for the Haar measure `volume` of `E`. Its `L²` norm is at most a constant times that of `α`:
on the compact set `ψ '' tsupport χ` the differential of `ψ.symm` is bounded above and its
Riemannian Jacobian below (`PartialDiffeomorph.exists_mul_norm_le_norm_mfderiv_symm_le`,
`PartialDiffeomorph.exists_le_riemannianJacobian_symm_le`), the comass norm of a form is at most
its Hilbert norm (Tau Ceti's `ContinuousAlternatingMap.norm_le_sqrt_alternatingFormInner_self`),
and the change of variables `PartialDiffeomorph.setLIntegral_riemannianVolume_eq` along
`ψ.symm` compares the integrals. So the localization extends to `L2Form o k`
(`SymplecticGeometry.L2Form.localize`).

## Main definitions and results

* `TauCeti.SmoothForm.l2Inner`: the `L²` inner product of smooth forms, symmetric
  (`l2Inner_comm`), bilinear (`l2Inner_add_left`, `l2Inner_smul_left`, `l2Inner_neg_left`,
  `l2Inner_sub_left`, …), with `l2Inner_self_nonneg` and `l2Inner_self_eq_zero_iff`.
* `SymplecticGeometry.L2Form o k`: the Hilbert space of `L²` `k`-forms, with
  `L2Form.ofSmooth`, `L2Form.inner_ofSmooth`, `L2Form.norm_ofSmooth_sq`,
  `L2Form.ofSmooth_injective`, `L2Form.denseRange_ofSmooth` and `L2Form.induction_on`.
* `TauCeti.SmoothForm.localize ψ χ α`: the localization of a smooth form to a chart, with
  `continuous_localize`, `memLp_localize` and the pointwise bound `norm_localize_apply_le`.
* `SymplecticGeometry.L2Form.localize ψ χ hχ`: its extension to `L2Form o k`, a continuous
  linear map to `Lp (E [⋀^Fin k]→L[ℝ] ℝ) 2 volume`, bounded by
  `L2Form.exists_norm_localizeLp_le`, with `L2Form.localize_ofSmooth`.

## Implementation notes

The construction of `L2Form`, through the type synonym `SymplecticGeometry.PreL2Form` of the
smooth forms carrying the inner product, and the names and proofs of `ofSmooth`,
`inner_ofSmooth`, `norm_ofSmooth_sq`, `denseRange_ofSmooth` and `induction_on`, adapt those of
Tau Ceti's `TauCeti.Manifold.SobolevH1`
(`TauCeti/Geometry/Manifold/Riemannian/Sobolev/H1.lean`, itself after Mathlib's `PreGNS`), with
smooth forms and their `L²` inner product in place of smooth functions and the `H¹` inner
product. Since the `L²` inner
product is definite, the type synonym carries an `InnerProductSpace.Core` rather than a
`PreInnerProductSpace.Core`, so it is a normed space and its map to the completion is
injective.

The definition of `l2Inner` is the integral that Tau Ceti's `Codifferential.lean` writes inline,
with the integrand `alternatingFormInner`. Tau Ceti's `innerZeroForm` would give the same
integrand as a smooth `0`-form, but it needs a splitting `k + l = m` of the dimension, which
nothing here uses.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6.
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer, 1983, Chapter 6.
-/

public section

open Bundle MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {m k : ℕ}

/-- The Riemannian volume measure, and the bounds for a chart on a compact set, need only a
continuous metric. -/
local instance [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

namespace TauCeti.SmoothForm

section Def

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The **`L²` inner product** `∫_M ⟨α, β⟩ dV` of two smooth real `k`-forms on an oriented
Riemannian manifold: the integral, against the orientation `o`, of the pointwise inner product
`⟨α, β⟩` times the Riemannian volume form `dV` of `o`. -/
def l2Inner (o : Manifold.Orientation I M (Fin m)) (α β : SmoothForm I M ℝ k) : ℝ :=
  integralTopForm o fun x ↦
    alternatingFormInner (TangentSpace I x) k (α.val x) (β.val x) • riemannianVolumeForm o x

/-- The `L²` inner product is the integral of `⟨α, β⟩ dV` against the orientation. -/
theorem l2Inner_def (o : Manifold.Orientation I M (Fin m)) (α β : SmoothForm I M ℝ k) :
    l2Inner o α β = integralTopForm o fun x ↦
      alternatingFormInner (TangentSpace I x) k (α.val x) (β.val x) • riemannianVolumeForm o x :=
  (rfl)

/-- The `L²` inner product is symmetric. -/
theorem l2Inner_comm (o : Manifold.Orientation I M (Fin m)) (α β : SmoothForm I M ℝ k) :
    l2Inner o α β = l2Inner o β α := by
  simp only [l2Inner_def, alternatingFormInner_comm (α.val _)]

end Def

variable [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The pointwise inner product of two smooth forms is a continuous function. -/
theorem continuous_alternatingFormInner (α β : SmoothForm I M ℝ k) :
    Continuous fun x ↦ alternatingFormInner (TangentSpace I x) k (α.val x) (β.val x) := by
  -- `contMDiff_alternatingFormInner` asks for `C^(∞ + 1)` charts.
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  exact (α.isSmoothForm.contMDiff_alternatingFormInner β.isSmoothForm).continuous

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The `L²` inner product is homogeneous in its first argument. -/
theorem l2Inner_smul_left (o : Manifold.Orientation I M (Fin m)) (c : ℝ)
    (α β : SmoothForm I M ℝ k) :
    l2Inner o (c • α) β = c * l2Inner o α β :=
  integralTopForm_inner_smul_left o c α β

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The `L²` inner product is homogeneous in its second argument. -/
theorem l2Inner_smul_right (o : Manifold.Orientation I M (Fin m)) (c : ℝ)
    (α β : SmoothForm I M ℝ k) :
    l2Inner o α (c • β) = c * l2Inner o α β := by
  rw [l2Inner_comm, l2Inner_smul_left, l2Inner_comm]

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The `L²` inner product vanishes when its first argument is zero. -/
@[simp]
theorem l2Inner_zero_left (o : Manifold.Orientation I M (Fin m)) (β : SmoothForm I M ℝ k) :
    l2Inner o 0 β = 0 := by
  simpa using l2Inner_smul_left o 0 0 β

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The `L²` inner product vanishes when its second argument is zero. -/
@[simp]
theorem l2Inner_zero_right (o : Manifold.Orientation I M (Fin m)) (α : SmoothForm I M ℝ k) :
    l2Inner o α 0 = 0 := by
  rw [l2Inner_comm, l2Inner_zero_left]

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The `L²` inner product changes sign with its first argument. -/
@[simp]
theorem l2Inner_neg_left (o : Manifold.Orientation I M (Fin m)) (α β : SmoothForm I M ℝ k) :
    l2Inner o (-α) β = -l2Inner o α β := by
  rw [← neg_one_smul ℝ α, l2Inner_smul_left, neg_one_mul]

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The `L²` inner product changes sign with its second argument. -/
@[simp]
theorem l2Inner_neg_right (o : Manifold.Orientation I M (Fin m)) (α β : SmoothForm I M ℝ k) :
    l2Inner o α (-β) = -l2Inner o α β := by
  rw [l2Inner_comm, l2Inner_neg_left, l2Inner_comm]

variable [CompactSpace M]

/-- On a compact manifold, the `L²` inner product of smooth forms is the integral of their
pointwise inner product against the Riemannian volume measure, in every dimension. -/
theorem l2Inner_eq_integral [MeasurableSpace M] [BorelSpace M]
    (o : Manifold.Orientation I M (Fin m)) (α β : SmoothForm I M ℝ k) :
    l2Inner o α β =
      ∫ x, alternatingFormInner (TangentSpace I x) k (α.val x) (β.val x) ∂riemannianVolume I M :=
  integralTopForm_smul_riemannianVolumeForm o (continuous_alternatingFormInner α β)
    (HasCompactSupport.of_compactSpace _)

/-- The `L²` inner product is additive in its first argument. -/
theorem l2Inner_add_left (o : Manifold.Orientation I M (Fin m)) (α β γ : SmoothForm I M ℝ k) :
    l2Inner o (α + β) γ = l2Inner o α γ + l2Inner o β γ := by
  borelize M
  simp only [l2Inner_eq_integral, Submodule.coe_add, Pi.add_apply, LinearMap.map_add₂]
  exact integral_add (continuous_alternatingFormInner α γ).integrable_of_compactSpace
    (continuous_alternatingFormInner β γ).integrable_of_compactSpace

/-- The `L²` inner product is additive in its second argument. -/
theorem l2Inner_add_right (o : Manifold.Orientation I M (Fin m)) (α β γ : SmoothForm I M ℝ k) :
    l2Inner o α (β + γ) = l2Inner o α β + l2Inner o α γ := by
  rw [l2Inner_comm, l2Inner_add_left, l2Inner_comm _ β, l2Inner_comm _ γ]

/-- The `L²` inner product respects subtraction in its first argument. -/
theorem l2Inner_sub_left (o : Manifold.Orientation I M (Fin m)) (α β γ : SmoothForm I M ℝ k) :
    l2Inner o (α - β) γ = l2Inner o α γ - l2Inner o β γ := by
  rw [sub_eq_add_neg, l2Inner_add_left, l2Inner_neg_left, sub_eq_add_neg]

/-- The `L²` inner product respects subtraction in its second argument. -/
theorem l2Inner_sub_right (o : Manifold.Orientation I M (Fin m)) (α β γ : SmoothForm I M ℝ k) :
    l2Inner o α (β - γ) = l2Inner o α β - l2Inner o α γ := by
  rw [l2Inner_comm, l2Inner_sub_left, l2Inner_comm _ β, l2Inner_comm _ γ]

/-- The `L²` inner product of a smooth form with itself is nonnegative. -/
theorem l2Inner_self_nonneg (o : Manifold.Orientation I M (Fin m)) (α : SmoothForm I M ℝ k) :
    0 ≤ l2Inner o α α := by
  borelize M
  rw [l2Inner_eq_integral]
  exact integral_nonneg fun x ↦ alternatingFormInner_self_nonneg _

/-- The `L²` inner product is definite: `∫_M |α|² dV = 0` exactly when `α = 0`, in every
dimension. -/
theorem l2Inner_self_eq_zero_iff (o : Manifold.Orientation I M (Fin m))
    {α : SmoothForm I M ℝ k} : l2Inner o α α = 0 ↔ α = 0 := by
  borelize M
  have hc := continuous_alternatingFormInner α α
  rw [l2Inner_eq_integral, integral_eq_zero_iff_of_nonneg
    (fun x ↦ alternatingFormInner_self_nonneg _) hc.integrable_of_compactSpace,
    hc.ae_eq_iff_eq _ (continuous_zero (X := M) (M := ℝ))]
  refine ⟨fun h ↦ Subtype.ext (funext fun x ↦ alternatingFormInner_self_eq_zero.1
    (congrFun h x)), fun h ↦ ?_⟩
  subst h
  funext x
  exact LinearMap.map_zero₂ _ _

end TauCeti.SmoothForm

/-! ### Localization of a smooth form to a chart -/

namespace TauCeti.SmoothForm

section Localize

omit [FiniteDimensional ℝ E]

variable [IsManifold I ∞ M]

/-- The **localization** of a smooth real `k`-form `α` to a chart `ψ : M → E` with a cutoff
`χ : M → ℝ`: the function on `E` that sends a point `y` of `ψ.target` to
`χ (ψ⁻¹ y) • (ψ⁻¹)^* α (y)`, the pullback of `α` along `ψ.symm` at `y` scaled by `χ (ψ.symm y)`,
and every other point to `0`. -/
def localize (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (χ : M → ℝ) (α : SmoothForm I M ℝ k) :
    E → E [⋀^Fin k]→L[ℝ] ℝ :=
  ψ.target.indicator fun y ↦ χ (ψ.symm y) • TauCeti.mpullback 𝓘(ℝ, E) I ψ.symm α.val y

variable (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (χ : M → ℝ) (α β : SmoothForm I M ℝ k)

/-- On the target of the chart, the localization of `α` evaluated on vectors `v` is `χ (ψ⁻¹ y)`
times `α` at `ψ⁻¹ y` evaluated on the images of `v` under the differential of `ψ.symm`. -/
theorem localize_apply_of_mem {y : E} (hy : y ∈ ψ.target) (v : Fin k → E) :
    α.localize ψ χ y v =
      χ (ψ.symm y) * α.val (ψ.symm y) (fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (v i)) := by
  have h : α.localize ψ χ y = χ (ψ.symm y) • TauCeti.mpullback 𝓘(ℝ, E) I ψ.symm α.val y :=
    Set.indicator_of_mem hy _
  refine (congrArg (fun f : E [⋀^Fin k]→L[ℝ] ℝ ↦ f v) h).trans ?_
  refine (ContinuousAlternatingMap.smul_apply
    (TauCeti.mpullback 𝓘(ℝ, E) I ψ.symm α.val y) _ v).trans ?_
  exact (smul_eq_mul _ _).trans (congrArg _ (TauCeti.mpullback_apply _ _ _ v))

/-- Off the target of the chart, the localization vanishes. -/
theorem localize_apply_of_notMem {y : E} (hy : y ∉ ψ.target) : α.localize ψ χ y = 0 :=
  Set.indicator_of_notMem hy _

/-- The localization vanishes off the image `ψ '' tsupport χ` of the support of the cutoff. -/
theorem localize_apply_eq_zero_of_notMem {y : E} (hy : y ∉ ψ '' tsupport χ) :
    α.localize ψ χ y = 0 := by
  by_cases hyt : y ∈ ψ.target
  · ext v
    rw [localize_apply_of_mem _ _ _ hyt, image_eq_zero_of_notMem_tsupport (f := χ), zero_mul,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    exact fun h ↦ hy ⟨_, h, ψ.right_inv hyt⟩
  · exact localize_apply_of_notMem _ _ _ hyt

/-- The localization is additive in the form. -/
@[simp]
theorem localize_add : (α + β).localize ψ χ = α.localize ψ χ + β.localize ψ χ := by
  ext y v
  by_cases hy : y ∈ ψ.target
  · simp [localize_apply_of_mem _ _ _ hy, mul_add]
  · simp [localize_apply_of_notMem _ _ _ hy]

/-- The localization is homogeneous in the form. -/
@[simp]
theorem localize_smul (c : ℝ) : (c • α).localize ψ χ = c • α.localize ψ χ := by
  ext y v
  by_cases hy : y ∈ ψ.target
  · simp [localize_apply_of_mem _ _ _ hy, mul_left_comm]
  · simp [localize_apply_of_notMem _ _ _ hy]

/-- The localization of a smooth form with a continuous cutoff whose support is compact and lies
in the source of the chart is continuous. -/
theorem continuous_localize (hχc : Continuous χ) (hK : IsCompact (tsupport χ))
    (hχ : tsupport χ ⊆ ψ.source) : Continuous (α.localize ψ χ) := by
  have hKψ : IsCompact (ψ '' tsupport χ) :=
    hK.image_of_continuousOn (ψ.contMDiffOn.continuousOn.mono hχ)
  have hon : ContinuousOn (α.localize ψ χ) ψ.target := by
    refine ((hχc.comp_continuousOn ψ.symm.contMDiffOn.continuousOn).smul
      (α.contDiffOn_mpullback ψ.open_target ψ.symm.contMDiffOn).continuousOn).congr
        fun y hy ↦ ?_
    exact Set.indicator_of_mem hy _
  refine continuous_iff_continuousAt.2 fun y ↦ ?_
  by_cases hy : y ∈ ψ.target
  · exact hon.continuousAt (ψ.open_target.mem_nhds hy)
  · have hyK : y ∉ ψ '' tsupport χ := fun h ↦ hy ((ψ.mapsTo.mono_left hχ).image_subset h)
    refine continuousAt_const.congr (f := fun _ ↦ 0) ?_
    filter_upwards [hKψ.isClosed.isOpen_compl.mem_nhds hyK] with z hz
    exact (localize_apply_eq_zero_of_notMem _ _ _ hz).symm

/-- If the differential of `ψ.symm` at `y` has norm at most `C`, for the Riemannian norm on
the tangent spaces of `M`, the localization at `y` has norm at most
`‖χ (ψ⁻¹ y)‖ * ‖α (ψ⁻¹ y)‖ * C ^ k`. -/
theorem norm_localize_apply_le [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {y : E}
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ v : E, ‖mfderiv 𝓘(ℝ, E) I ψ.symm y v‖ ≤ C * ‖v‖) :
    ‖α.localize ψ χ y‖ ≤ ‖χ (ψ.symm y)‖ * ‖α.val (ψ.symm y)‖ * C ^ k := by
  by_cases hy : y ∈ ψ.target
  · refine (α.localize ψ χ y).opNorm_le_bound (by positivity) fun v ↦ ?_
    rw [localize_apply_of_mem _ _ _ hy, norm_mul]
    calc ‖χ (ψ.symm y)‖ * ‖α.val (ψ.symm y) (fun i ↦ mfderiv 𝓘(ℝ, E) I ψ.symm y (v i))‖
        ≤ ‖χ (ψ.symm y)‖ *
            (‖α.val (ψ.symm y)‖ * ∏ i, ‖mfderiv 𝓘(ℝ, E) I ψ.symm y (v i)‖) := by
          gcongr
          exact (α.val (ψ.symm y)).le_opNorm _
      _ ≤ ‖χ (ψ.symm y)‖ * (‖α.val (ψ.symm y)‖ * ∏ i, (C * ‖v i‖)) := by
          gcongr with i
          exact h (v i)
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          ring
  · rw [localize_apply_of_notMem _ _ _ hy, norm_zero]
    positivity

variable [CompactSpace M] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- On a compact manifold, the localization of a smooth form with a smooth cutoff supported in
the source of the chart is in `Lᵖ` for the Haar measure of `E`, for every `p`. -/
theorem memLp_localize (χ : C^∞⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ ψ.source) (p : ENNReal) :
    MemLp (α.localize ψ χ) p volume := by
  have hK : IsCompact (tsupport χ) := (isClosed_tsupport _).isCompact
  refine (α.continuous_localize ψ χ χ.contMDiff.continuous hK hχ).memLp_of_hasCompactSupport ?_
  exact HasCompactSupport.intro (hK.image_of_continuousOn (ψ.contMDiffOn.continuousOn.mono hχ))
    fun y hy ↦ localize_apply_eq_zero_of_notMem _ _ _ hy

/-- The localization to a chart, as a linear map from the smooth `k`-forms to the `L²` classes
of functions on `E` with values in `E [⋀^Fin k]→L[ℝ] ℝ`. -/
def localizeLp (χ : C^∞⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ ψ.source) :
    SmoothForm I M ℝ k →ₗ[ℝ] Lp (E [⋀^Fin k]→L[ℝ] ℝ) 2 (volume : Measure E) where
  toFun α := (α.memLp_localize ψ χ hχ 2).toLp
  map_add' α β := by
    simp_rw [localize_add]
    exact MemLp.toLp_add _ _
  map_smul' c α := by
    simp_rw [localize_smul]
    exact MemLp.toLp_const_smul _ _

/-- `localizeLp ψ χ hχ α` is the class of the localization of `α`. -/
theorem localizeLp_apply (χ : C^∞⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ ψ.source) :
    localizeLp ψ χ hχ α = (α.memLp_localize ψ χ hχ 2).toLp :=
  (rfl)

end Localize

end TauCeti.SmoothForm

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothForm

variable [IsManifold I ∞ M]

/-- The smooth real `k`-forms, as the space on which the `L²` inner product of the orientation
`o` is defined before completion. -/
@[nolint unusedArguments]
def PreL2Form (_o : Manifold.Orientation I M (Fin m)) (k : ℕ) : Type _ := SmoothForm I M ℝ k

variable (o : Manifold.Orientation I M (Fin m)) (k)

instance : AddCommGroup (PreL2Form o k) := inferInstanceAs (AddCommGroup (SmoothForm I M ℝ k))

instance : Module ℝ (PreL2Form o k) := inferInstanceAs (Module ℝ (SmoothForm I M ℝ k))

variable {o k}

namespace PreL2Form

/-- A smooth form, as an element of `PreL2Form`. -/
def toPreL2Form : SmoothForm I M ℝ k ≃ₗ[ℝ] PreL2Form o k := LinearEquiv.refl ℝ _

/-- An element of `PreL2Form`, as a smooth form. -/
def ofPreL2Form : PreL2Form o k ≃ₗ[ℝ] SmoothForm I M ℝ k := toPreL2Form.symm

@[simp]
theorem toPreL2Form_ofPreL2Form (u : PreL2Form o k) : toPreL2Form (ofPreL2Form u) = u :=
  (rfl)

@[simp]
theorem ofPreL2Form_toPreL2Form (α : SmoothForm I M ℝ k) :
    ofPreL2Form (toPreL2Form α : PreL2Form o k) = α :=
  (rfl)

variable [CompactSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The `L²` inner product on `PreL2Form o k`. -/
abbrev innerCore : InnerProductSpace.Core ℝ (PreL2Form o k) where
  inner u v := l2Inner o (ofPreL2Form u) (ofPreL2Form v)
  conj_inner_symm u v := by simp only [conj_trivial, l2Inner_comm]
  re_inner_nonneg u := l2Inner_self_nonneg o _
  add_left u v w := by simp only [map_add, l2Inner_add_left]
  smul_left u v r := by simp only [map_smul, l2Inner_smul_left, conj_trivial]
  definite u h := ofPreL2Form.injective <| by
    rw [map_zero]
    exact (l2Inner_self_eq_zero_iff o).1 h

instance : NormedAddCommGroup (PreL2Form o k) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := innerCore)

instance : InnerProductSpace ℝ (PreL2Form o k) :=
  InnerProductSpace.ofCore innerCore.toCore

/-- The inner product of two smooth forms in `PreL2Form` is their `L²` inner product. -/
theorem inner_toPreL2Form (α β : SmoothForm I M ℝ k) :
    ⟪(toPreL2Form α : PreL2Form o k), toPreL2Form β⟫_ℝ = l2Inner o α β :=
  (rfl)

end PreL2Form

open PreL2Form

variable [CompactSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The **Hilbert space of `L²` `k`-forms** on a compact oriented Riemannian manifold: the
completion of the smooth real `k`-forms for the inner product `∫_M ⟨α, β⟩ dV`. -/
abbrev L2Form (o : Manifold.Orientation I M (Fin m)) (k : ℕ) :=
  UniformSpace.Completion (PreL2Form o k)

namespace L2Form

/-- The inclusion of the smooth forms into `L2Form o k`. -/
def ofSmooth : SmoothForm I M ℝ k →ₗ[ℝ] L2Form o k :=
  UniformSpace.Completion.toComplL.toLinearMap ∘ₗ toPreL2Form.toLinearMap

/-- A smooth form in `L2Form o k` is the image of its copy in the pre-completion space. -/
theorem ofSmooth_apply (α : SmoothForm I M ℝ k) :
    (ofSmooth α : L2Form o k) = ((toPreL2Form α : PreL2Form o k) : L2Form o k) :=
  (rfl)

/-- The inner product of two smooth forms in `L2Form o k` is their `L²` inner product. -/
@[simp]
theorem inner_ofSmooth (α β : SmoothForm I M ℝ k) :
    ⟪(ofSmooth α : L2Form o k), ofSmooth β⟫_ℝ = l2Inner o α β := by
  rw [ofSmooth_apply, ofSmooth_apply, UniformSpace.Completion.inner_coe, inner_toPreL2Form]

/-- The squared norm of a smooth form in `L2Form o k` is `∫_M |α|² dV`. -/
theorem norm_ofSmooth_sq (α : SmoothForm I M ℝ k) :
    ‖(ofSmooth α : L2Form o k)‖ ^ 2 = l2Inner o α α := by
  rw [← real_inner_self_eq_norm_sq, inner_ofSmooth]

/-- The inclusion of the smooth forms into `L2Form o k` is injective. -/
theorem ofSmooth_injective : Function.Injective (ofSmooth : SmoothForm I M ℝ k → L2Form o k) :=
  UniformSpace.Completion.coe_injective _ |>.comp toPreL2Form.injective

/-- The smooth forms are dense in `L2Form o k`. -/
theorem denseRange_ofSmooth : DenseRange (ofSmooth : SmoothForm I M ℝ k → L2Form o k) :=
  UniformSpace.Completion.denseRange_coe.comp toPreL2Form.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

/-- **Induction principle for `L2Form o k`.** A closed property of `L²` forms that holds for
all smooth forms holds everywhere. -/
@[elab_as_elim]
theorem induction_on {p : L2Form o k → Prop} (u : L2Form o k) (hp : IsClosed {u | p u})
    (h : ∀ α : SmoothForm I M ℝ k, p (ofSmooth α)) : p u :=
  denseRange_ofSmooth.induction_on u hp h


section Localize

variable [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (χ : C^∞⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ ψ.source)

/-- The localization of smooth forms to a chart `ψ` with a cutoff `χ` supported in its source is
bounded for the `L²` norms: `‖localizeLp ψ χ hχ α‖ ≤ C * ‖ofSmooth α‖` for some `C` and every
smooth `k`-form `α`. -/
theorem exists_norm_localizeLp_le (o : Manifold.Orientation I M (Fin m)) :
    ∃ C, ∀ α : SmoothForm I M ℝ k, ‖localizeLp ψ χ hχ α‖ ≤ C * ‖(ofSmooth α : L2Form o k)‖ := by
  borelize M
  have hK : IsCompact (ψ '' tsupport χ) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn (ψ.contMDiffOn.continuousOn.mono hχ)
  have hKt : ψ '' tsupport χ ⊆ ψ.target := (ψ.mapsTo.mono_left hχ).image_subset
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  -- The differential of `ψ.symm` is bounded above, and its Jacobian below, on `ψ '' tsupport χ`.
  obtain ⟨c₁, C₁, -, hC₁⟩ := ψ.exists_mul_norm_le_norm_mfderiv_symm_le hn hK hKt
  let b := Module.finBasis ℝ E
  obtain ⟨c, CJ, hc, hJ⟩ := ψ.exists_le_riemannianJacobian_symm_le hn b hK hKt
  obtain ⟨Cχ, hCχ⟩ :=
    isCompact_univ.exists_bound_of_continuousOn χ.contMDiff.continuous.continuousOn
  set D := max C₁ 0
  set B := (Cχ * D ^ k) ^ 2 / c
  set s := (volume : Measure E).addHaarScalarFactor b.addHaar
  refine ⟨√(s * B), fun α ↦ ?_⟩
  set a : M → ℝ := fun x ↦ alternatingFormInner (TangentSpace I x) k (α.val x) (α.val x)
  set J : E → ℝ := TauCeti.riemannianJacobian (I := I) b ψ.symm
  have hB : 0 ≤ B := by positivity
  -- Pointwise, `|α_ψ|² ≤ J * B * |α|²`.
  have hpt (y) : ‖α.localize ψ χ y‖ ^ 2 ≤ J y * (B * a (ψ.symm y)) := by
    have ha : 0 ≤ a (ψ.symm y) := alternatingFormInner_self_nonneg _
    by_cases hyK : y ∈ ψ '' tsupport χ
    · have hCχ0 : 0 ≤ Cχ := (norm_nonneg _).trans (hCχ (ψ.symm y) (Set.mem_univ _))
      have h1 : ‖α.localize ψ χ y‖ ≤ Cχ * √(a (ψ.symm y)) * D ^ k := by
        refine (α.norm_localize_apply_le ψ χ (le_max_right _ _) fun v ↦
          (hC₁ y hyK v).2.trans (by gcongr; exact le_max_left _ _)).trans ?_
        gcongr
        · exact hCχ _ (Set.mem_univ _)
        · exact ContinuousAlternatingMap.norm_le_sqrt_alternatingFormInner_self _
      calc ‖α.localize ψ χ y‖ ^ 2 ≤ (Cχ * √(a (ψ.symm y)) * D ^ k) ^ 2 := by gcongr
        _ = (Cχ * D ^ k) ^ 2 * a (ψ.symm y) := by rw [mul_pow, mul_pow, Real.sq_sqrt ha]; ring
        _ ≤ J y / c * ((Cχ * D ^ k) ^ 2 * a (ψ.symm y)) :=
          le_mul_of_one_le_left (by positivity) ((one_le_div hc).2 (hJ y hyK).1)
        _ = J y * (B * a (ψ.symm y)) := by simp only [B]; ring
    · rw [localize_apply_eq_zero_of_notMem _ _ _ hyK, norm_zero, sq, zero_mul]
      exact mul_nonneg (TauCeti.riemannianJacobian_nonneg _ _ _) (by positivity)
  -- Integrating, and changing variables along `ψ.symm`, bounds the integral by `B ‖α‖²`.
  have hint : ∫⁻ y, ‖α.localize ψ χ y‖ₑ ^ (2 : ℝ) ∂b.addHaar ≤
      ENNReal.ofReal (B * ‖(ofSmooth α : L2Form o k)‖ ^ 2) := by
    calc ∫⁻ y, ‖α.localize ψ χ y‖ₑ ^ (2 : ℝ) ∂b.addHaar
        ≤ ∫⁻ y, ψ.target.indicator
            (fun y ↦ ENNReal.ofReal (J y) * ENNReal.ofReal (B * a (ψ.symm y))) y ∂b.addHaar := by
          refine lintegral_mono fun y ↦ ?_
          by_cases hy : y ∈ ψ.target
          · rw [Set.indicator_of_mem hy,
              ← ENNReal.ofReal_mul (TauCeti.riemannianJacobian_nonneg _ _ _), ← ofReal_norm,
              ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
            exact ENNReal.ofReal_le_ofReal ((Real.rpow_two _).trans_le (hpt y))
          · rw [localize_apply_of_notMem _ _ _ hy, Set.indicator_of_notMem hy, ← ofReal_norm,
              norm_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos two_pos]
      _ = ∫⁻ x in ψ.source, ENNReal.ofReal (B * a x) ∂riemannianVolume I M := by
          rw [lintegral_indicator ψ.open_target.measurableSet]
          simpa [J] using
            (ψ.symm.setLIntegral_riemannianVolume_eq hn b fun x ↦ ENNReal.ofReal (B * a x)).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (B * a x) ∂riemannianVolume I M := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (B * ‖(ofSmooth α : L2Form o k)‖ ^ 2) := by
          rw [← ofReal_integral_eq_lintegral_ofReal, integral_const_mul, norm_ofSmooth_sq,
            l2Inner_eq_integral]
          · exact ((continuous_alternatingFormInner α α).integrable_of_compactSpace).const_mul B
          · exact Filter.Eventually.of_forall fun x ↦
              mul_nonneg hB (alternatingFormInner_self_nonneg _)
  -- `volume` is `s • b.addHaar`, which gives the bound on the `L²` norm.
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (μ := volume) two_ne_zero
    (α.memLp_localize ψ χ hχ 2).aestronglyMeasurable
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at h2
  have h3 : ∫⁻ y, ‖α.localize ψ χ y‖ₑ ^ (2 : ℝ) ∂volume =
      s * ∫⁻ y, ‖α.localize ψ χ y‖ₑ ^ (2 : ℝ) ∂b.addHaar := by
    conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul volume b.addHaar]
    rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  have hle : eLpNorm (α.localize ψ χ) 2 volume ≤
      ENNReal.ofReal (√(s * B) * ‖(ofSmooth α : L2Form o k)‖) := by
    rw [← ENNReal.rpow_le_rpow_iff (z := 2) two_pos, h2, h3,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) zero_le_two, Real.rpow_two, mul_pow,
      Real.sq_sqrt (by positivity), mul_assoc, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_coe_nnreal]
    gcongr
  rw [localizeLp_apply, Lp.norm_toLp]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

variable {o : Manifold.Orientation I M (Fin m)}

/-- The **localization of `L²` forms to a chart** `ψ` with a smooth cutoff `χ` supported in its
source: the continuous linear map from `L2Form o k` to the `L²` functions on `E` with values in
`E [⋀^Fin k]→L[ℝ] ℝ` that extends `TauCeti.SmoothForm.localize ψ χ` from the smooth forms, which
it may since that map is bounded (`exists_norm_localizeLp_le`). -/
def localize : L2Form o k →L[ℝ] Lp (E [⋀^Fin k]→L[ℝ] ℝ) 2 (volume : Measure E) :=
  (localizeLp ψ χ hχ).extendOfNorm ofSmooth

/-- On a smooth form, `localize` is the class of its localization. -/
@[simp]
theorem localize_ofSmooth_eq_localizeLp (α : SmoothForm I M ℝ k) :
    localize ψ χ hχ (ofSmooth α : L2Form o k) = localizeLp ψ χ hχ α :=
  LinearMap.extendOfNorm_eq denseRange_ofSmooth (exists_norm_localizeLp_le ψ χ hχ o) α

/-- On a smooth form `α`, `localize ψ χ hχ` is almost everywhere the function
`y ↦ χ (ψ⁻¹ y) • (ψ⁻¹)^* α (y)` on `ψ.target`, extended by `0`. -/
theorem localize_ofSmooth (α : SmoothForm I M ℝ k) :
    localize ψ χ hχ (ofSmooth α : L2Form o k) =ᵐ[volume] α.localize ψ χ := by
  rw [localize_ofSmooth_eq_localizeLp, localizeLp_apply]
  exact MemLp.coeFn_toLp _

end Localize

end L2Form

end SymplecticGeometry

end
