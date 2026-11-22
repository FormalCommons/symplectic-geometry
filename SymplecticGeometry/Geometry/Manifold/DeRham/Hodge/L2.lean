/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartialDiffeomorph
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import SymplecticGeometry.Geometry.Manifold.Riemannian.PartialDiffeomorph
import TauCeti.Analysis.InnerProductSpace.Comass
import TauCeti.Geometry.Manifold.Riemannian.Codifferential
import TauCeti.Geometry.Manifold.Riemannian.FormMetric
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
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
`0` elsewhere (`TauCeti.SmoothForm.localize`, defined with its continuity and support in
`SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartialDiffeomorph`). It is continuous
with compact support, so in `L²` for the Haar measure `volume` of `E`. Its `L²` norm is at most
a constant times that of `α`: on the compact set `ψ '' tsupport χ` the differential of `ψ.symm`
is bounded above and its Riemannian Jacobian below
(`PartialDiffeomorph.exists_mul_norm_le_norm_mfderiv_symm_le`,
`PartialDiffeomorph.exists_le_riemannianJacobian_symm_le`), the comass norm of a form is at most
its Hilbert norm (Tau Ceti's `ContinuousAlternatingMap.norm_le_sqrt_alternatingFormInner_self`),
and the change of variables `PartialDiffeomorph.setLIntegral_riemannianVolume_eq` along
`ψ.symm` compares the integrals (`L2Form.exists_lintegral_enorm_localize_sq_le`). So the
localization extends to `L2Form o k` (`SymplecticGeometry.L2Form.localize`).

## Main definitions and results

* `TauCeti.SmoothForm.l2Inner`: the `L²` inner product of smooth forms, symmetric
  (`l2Inner_comm`), bilinear (`l2Inner_add_left`, `l2Inner_smul_left`, `l2Inner_neg_left`,
  `l2Inner_sub_left`, …), with `l2Inner_self_nonneg` and `l2Inner_self_eq_zero_iff`.
* `SymplecticGeometry.L2Form o k`: the Hilbert space of `L²` `k`-forms, with
  `L2Form.ofSmooth`, `L2Form.inner_ofSmooth`, `L2Form.norm_ofSmooth_sq`,
  `L2Form.ofSmooth_injective`, `L2Form.denseRange_ofSmooth` and `L2Form.induction_on`.
* `TauCeti.SmoothForm.memLp_localize`: the localization of a smooth form to a chart is in every
  `Lᵖ`, with the pointwise bounds `norm_localize_apply_le` and
  `exists_norm_localize_apply_sq_le`, and `TauCeti.SmoothForm.localizeLp`, the linear map to
  `L²`.
* `SymplecticGeometry.L2Form.localize ψ χ hχ`: the extension of `localizeLp` to `L2Form o k`, a
  continuous linear map to `Lp (E [⋀^Fin k]→L[ℝ] ℝ) 2 volume`, bounded by
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

/-! ### Localization of a smooth form to a chart, in `L²` -/

namespace TauCeti.SmoothForm

section Localize

variable [IsManifold I ∞ M] (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) {χ : M → ℝ}
  (α : SmoothForm I M ℝ k)

omit [FiniteDimensional ℝ E] in
/-- If the differential of `ψ.symm` at `y` has norm at most `C`, for the Riemannian norm on
the tangent spaces of `M`, the localization at `y` has norm at most
`‖χ (ψ⁻¹ y)‖ * ‖α (ψ⁻¹ y)‖ * C ^ k`. -/
theorem norm_localize_apply_le [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {y : E}
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ v : E, ‖mfderiv 𝓘(ℝ, E) I ψ.symm y v‖ ≤ C * ‖v‖) :
    ‖α.localize ψ χ y‖ ≤ ‖χ (ψ.symm y)‖ * ‖α.val (ψ.symm y)‖ * C ^ k := by
  by_cases hy : y ∈ ψ.target
  · refine (α.localize ψ χ y).opNorm_le_bound (by positivity) fun v ↦ ?_
    rw [localize_apply_of_mem _ _ _ hy, norm_smul]
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

/-- For a continuous cutoff with compact support in the source of the chart, the square of the
norm of the localization of `α` at `y` is at most a constant `B`, independent of `α`, times the
Riemannian Jacobian of `ψ.symm` at `y` for a basis `b` of `E` and the pointwise inner product
`⟨α, α⟩` at `ψ.symm y`. -/
theorem exists_norm_localize_apply_sq_le [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) (hχc : Continuous χ)
    (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source) :
    ∃ B, 0 ≤ B ∧ ∀ (α : SmoothForm I M ℝ k) (y : E), ‖α.localize ψ χ y‖ ^ 2 ≤
      riemannianJacobian (I := I) b ψ.symm y *
        (B * alternatingFormInner (TangentSpace I (ψ.symm y)) k (α.val (ψ.symm y))
          (α.val (ψ.symm y))) := by
  have hKψ : IsCompact (ψ '' tsupport χ) :=
    hK.image_of_continuousOn (ψ.contMDiffOn.continuousOn.mono hχ)
  have hKt : ψ '' tsupport χ ⊆ ψ.target := (ψ.mapsTo.mono_left hχ).image_subset
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  -- The differential of `ψ.symm` is bounded above, and its Jacobian below, on `ψ '' tsupport χ`.
  obtain ⟨c₁, C₁, -, hC₁⟩ := ψ.exists_mul_norm_le_norm_mfderiv_symm_le hn hKψ hKt
  obtain ⟨c, CJ, hc, hJ⟩ := ψ.exists_le_riemannianJacobian_symm_le hn b hKψ hKt
  obtain ⟨Cχ, hCχ⟩ := hχc.bounded_above_of_compact_support hK
  set D := max C₁ 0
  refine ⟨(Cχ * D ^ k) ^ 2 / c, by positivity, fun α y ↦ ?_⟩
  set a := alternatingFormInner (TangentSpace I (ψ.symm y)) k (α.val (ψ.symm y))
    (α.val (ψ.symm y))
  have ha : 0 ≤ a := alternatingFormInner_self_nonneg _
  by_cases hyK : y ∈ ψ '' tsupport χ
  · have hCχ0 : 0 ≤ Cχ := (norm_nonneg _).trans (hCχ (ψ.symm y))
    have h1 : ‖α.localize ψ χ y‖ ≤ Cχ * √a * D ^ k := by
      refine (α.norm_localize_apply_le ψ (le_max_right _ _) fun v ↦
        (hC₁ y hyK v).2.trans (by gcongr; exact le_max_left _ _)).trans ?_
      gcongr
      · exact hCχ _
      · exact ContinuousAlternatingMap.norm_le_sqrt_alternatingFormInner_self _
    calc ‖α.localize ψ χ y‖ ^ 2 ≤ (Cχ * √a * D ^ k) ^ 2 := by gcongr
      _ = (Cχ * D ^ k) ^ 2 * a := by rw [mul_pow, mul_pow, Real.sq_sqrt ha]; ring
      _ ≤ riemannianJacobian (I := I) b ψ.symm y / c * ((Cχ * D ^ k) ^ 2 * a) :=
        le_mul_of_one_le_left (by positivity) ((one_le_div hc).2 (hJ y hyK).1)
      _ = _ := by ring
  · rw [localize_apply_eq_zero_of_notMem _ _ _ hyK, norm_zero, sq, zero_mul]
    exact mul_nonneg (riemannianJacobian_nonneg _ _ _) (by positivity)

omit [FiniteDimensional ℝ E]

variable [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- The localization of a smooth form with a continuous cutoff whose support is compact and lies
in the source of the chart is in `Lᵖ` for the Haar measure of `E`, for every `p`. -/
theorem memLp_localize (hχc : Continuous χ) (hK : IsCompact (tsupport χ))
    (hχ : tsupport χ ⊆ ψ.source) (p : ENNReal) : MemLp (α.localize ψ χ) p volume :=
  (α.continuous_localize ψ hχc hK hχ).memLp_of_hasCompactSupport
    (α.hasCompactSupport_localize ψ hK hχ)

variable [CompactSpace M]

/-- The localization to a chart with a smooth cutoff supported in its source, as a linear map
from the smooth `k`-forms on a compact manifold to the `L²` classes of functions on `E` with
values in `E [⋀^Fin k]→L[ℝ] ℝ`. -/
def localizeLp (χ : C^∞⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ ψ.source) :
    SmoothForm I M ℝ k →ₗ[ℝ] Lp (E [⋀^Fin k]→L[ℝ] ℝ) 2 (volume : Measure E) where
  toFun α :=
    (α.memLp_localize ψ χ.contMDiff.continuous (isClosed_tsupport _).isCompact hχ 2).toLp
  map_add' α β := by
    simp_rw [localize_add]
    exact MemLp.toLp_add _ _
  map_smul' c α := by
    simp_rw [localize_smul]
    exact MemLp.toLp_const_smul _ _

/-- `localizeLp ψ χ hχ α` is the class of the localization of `α`. -/
theorem localizeLp_apply (χ : C^∞⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ ψ.source) :
    localizeLp ψ χ hχ α =
      (α.memLp_localize ψ χ.contMDiff.continuous (isClosed_tsupport _).isCompact hχ 2).toLp :=
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

variable [MeasureSpace E] [BorelSpace E] (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)

/-- The step of `exists_lintegral_enorm_localize_sq_le` for the Haar measure of a basis `b`:
a pointwise bound on the localization of `α` by the Riemannian Jacobian of `ψ.symm` and the
pointwise inner product `⟨α, α⟩` integrates, by the change of variables along `ψ.symm`, to a bound
by the `L²` norm of `α`. -/
private theorem lintegral_enorm_localize_sq_le_addHaar (o : Manifold.Orientation I M (Fin m))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) {χ : M → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (α : SmoothForm I M ℝ k)
    (hpt : ∀ y, ‖α.localize ψ χ y‖ ^ 2 ≤ riemannianJacobian (I := I) b ψ.symm y *
      (B * alternatingFormInner (TangentSpace I (ψ.symm y)) k (α.val (ψ.symm y))
        (α.val (ψ.symm y)))) :
    ∫⁻ y, ‖α.localize ψ χ y‖ₑ ^ (2 : ℝ) ∂b.addHaar ≤
      ENNReal.ofReal (B * ‖(ofSmooth α : L2Form o k)‖ ^ 2) := by
  borelize M
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  set a : M → ℝ := fun x ↦ alternatingFormInner (TangentSpace I x) k (α.val x) (α.val x)
  set J : E → ℝ := riemannianJacobian (I := I) b ψ.symm
  calc ∫⁻ y, ‖α.localize ψ χ y‖ₑ ^ (2 : ℝ) ∂b.addHaar
      ≤ ∫⁻ y, ψ.target.indicator
          (fun y ↦ ENNReal.ofReal (J y) * ENNReal.ofReal (B * a (ψ.symm y))) y ∂b.addHaar := by
        refine lintegral_mono fun y ↦ ?_
        by_cases hy : y ∈ ψ.target
        · rw [Set.indicator_of_mem hy, ← ENNReal.ofReal_mul (riemannianJacobian_nonneg _ _ _),
            ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
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

/-- For a continuous cutoff `χ` with compact support in the source of the chart `ψ` and an
additive Haar measure `μ` on `E`, the integral of `‖α.localize ψ χ‖ ^ 2` against `μ` is at most a
constant `B`, independent of the smooth form `α`, times the square of the `L²` norm of `α`. -/
theorem exists_lintegral_enorm_localize_sq_le (o : Manifold.Orientation I M (Fin m))
    {χ : M → ℝ} (hχc : Continuous χ) (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ B, 0 ≤ B ∧ ∀ α : SmoothForm I M ℝ k,
      ∫⁻ y, ‖α.localize ψ χ y‖ₑ ^ (2 : ℝ) ∂μ ≤
        ENNReal.ofReal (B * ‖(ofSmooth α : L2Form o k)‖ ^ 2) := by
  let b := Module.finBasis ℝ E
  obtain ⟨B, hB, hpt⟩ := exists_norm_localize_apply_sq_le (k := k) ψ b hχc hK hχ
  set s := μ.addHaarScalarFactor b.addHaar
  refine ⟨s * B, by positivity, fun α ↦ ?_⟩
  rw [Measure.isAddLeftInvariant_eq_smul μ b.addHaar, lintegral_smul_measure, ENNReal.smul_def,
    smul_eq_mul, mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
  gcongr
  exact lintegral_enorm_localize_sq_le_addHaar ψ o b hB α (hpt α)

variable [(volume : Measure E).IsAddHaarMeasure] (χ : C^∞⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ ψ.source)

/-- The localization of smooth forms to a chart `ψ` with a cutoff `χ` supported in its source is
bounded for the `L²` norms: `‖localizeLp ψ χ hχ α‖ ≤ C * ‖ofSmooth α‖` for some `C` and every
smooth `k`-form `α`. -/
theorem exists_norm_localizeLp_le (o : Manifold.Orientation I M (Fin m)) :
    ∃ C, ∀ α : SmoothForm I M ℝ k, ‖localizeLp ψ χ hχ α‖ ≤ C * ‖(ofSmooth α : L2Form o k)‖ := by
  obtain ⟨B, hB, hint⟩ := exists_lintegral_enorm_localize_sq_le (k := k) ψ o
    χ.contMDiff.continuous (isClosed_tsupport _).isCompact hχ volume
  refine ⟨√B, fun α ↦ ?_⟩
  rw [localizeLp_apply, Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (eLpNorm_le_of_lintegral_rpow_le
    two_ne_zero ENNReal.ofNat_ne_top
    (α.memLp_localize ψ χ.contMDiff.continuous (isClosed_tsupport _).isCompact hχ
      2).aestronglyMeasurable ?_)
  rw [ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg (by positivity) zero_le_two,
    Real.rpow_two, mul_pow, Real.sq_sqrt hB]
  exact hint α

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
