/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.Chart
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartialDiffeomorph
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.ChangeOfVariables
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
import SymplecticGeometry.Analysis.InnerProductSpace.Comass
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.Riemannian.PartialDiffeomorph
import TauCeti.Analysis.InnerProductSpace.Comass
import TauCeti.Geometry.Manifold.Riemannian.Codifferential
import TauCeti.Geometry.Manifold.Riemannian.FormMetric
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.ContinuousMap
import Mathlib.MeasureTheory.Function.Holder

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
`PartialDiffeomorph.exists_le_riemannianJacobian_symm_le`), which bounds the comass norm of the
localization pointwise (`TauCeti.SmoothForm.norm_localize_apply_le`, from
`TauCeti.SmoothForm.localize_of_mem_eq_smul_compContinuousLinearMap` and Mathlib's
`ContinuousAlternatingMap.norm_compContinuousLinearMap_le`), the comass norm of a form is at most
its Hilbert norm (Tau Ceti's `ContinuousAlternatingMap.norm_le_sqrt_alternatingFormInner_self`),
and the change of variables `PartialDiffeomorph.setLIntegral_riemannianVolume_eq` along
`ψ.symm` compares the integrals (`L2Form.exists_lintegral_enorm_localize_sq_le`). So the
localization extends to `L2Form o k` (`SymplecticGeometry.L2Form.localize`).

In the other direction, extending a smooth flat form `a` supported in a compact `K ⊆ ψ.target`
by zero along `ψ` is bounded in `L²` (`L2Form.exists_norm_ofSmooth_extendByZeroAlong_le`): by
the same change of variables, now with the Jacobian of `ψ.symm` bounded above and the
differential of `ψ` bounded on `ψ.symm '' K`
(`PartialDiffeomorph.exists_norm_mvfderiv_le_mul_norm`), which bounds the comass norm of the
extension in the same way (`TauCeti.RoughForm.norm_extendByZeroAlong_apply_le`), and with the
square of the Hilbert norm of a form at most `n choose k` times the square of its comass norm
(`ContinuousAlternatingMap.alternatingFormInner_self_le`, from Tau Ceti's
`ContinuousAlternatingMap.sqrt_alternatingFormInner_self_le`). This gives the gluing
`L2Form.eq_ofSmooth_of_localize`: for finitely many charts with a subordinate smooth partition of
unity `ρ`, an `L²` form all of whose localizations with the cutoffs `ρ i` are smooth with compact
support is the smooth form glued from them. Every smooth form `β` is the sum of the extensions by
zero of its localizations (`TauCeti.SmoothForm.sum_extendByZeroAlong_localize`); approximating
the `L²` form by such `β`, the localizations converge in `L²`, and the bounded extension by zero
carries this convergence back to `L2Form o k`.

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
  `L2Form.exists_norm_localizeLp_le`, with `L2Form.localize_ofSmooth`, and
  `L2Form.localize_ae_eq_indicator_smul_localize`, which compares the localizations with two
  cutoffs, `χ₂ = 1` on the support of `χ₁`, using that a cutoff read in the chart is continuous
  with compact support (`PartialDiffeomorph.continuous_indicator_comp_symm`,
  `PartialDiffeomorph.hasCompactSupport_indicator_comp_symm`).
* `TauCeti.SmoothForm.l2Inner_eq_integral_formInnerInChart` and
  `SymplecticGeometry.L2Form.inner_ofSmooth_eq_integral_localize`: the `L²` inner product with a
  smooth form supported where the cutoff is `1`, read in the chart as the integral of the inner
  product `PartialDiffeomorph.formInnerInChart` of the localizations, weighted by the density of
  the Riemannian volume; for smooth forms by the change of variables
  `PartialDiffeomorph.setIntegral_riemannianVolume_eq`, and for `L²` forms by density.
* `SymplecticGeometry.L2Form.exists_norm_ofSmooth_extendByZeroAlong_le`: extension by zero along
  a chart, of smooth flat forms supported in a fixed compact subset of its target, is bounded for
  the `L²` norms, from the pointwise bounds
  `TauCeti.RoughForm.norm_extendByZeroAlong_apply_le` and
  `TauCeti.RoughForm.exists_riemannianJacobian_mul_alternatingFormInner_extendByZeroAlong_le`.
* `SymplecticGeometry.L2Form.eq_ofSmooth_of_localize`: an `L²` form whose localizations to a
  finite cover, with a subordinate partition of unity as cutoffs, are smooth with compact support
  is smooth.

## Implementation notes

In `L2Form.inner_ofSmooth_eq_integral_localize`, the pairing of the localization of an `L²` form
with a fixed function is written in the coordinates of a basis of the forms on `E`, so that only
real-valued `L²` functions enter the continuity argument.

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
  · rw [localize_of_mem_eq_smul_compContinuousLinearMap _ _ _ hy, norm_smul, mul_assoc]
    refine mul_le_mul_of_nonneg_left
      ((ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _).trans ?_) (norm_nonneg _)
    rw [Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.opNorm_le_bound _ hC h) _)
      (norm_nonneg _)
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
  have hKψ : IsCompact (ψ '' tsupport χ) := ψ.isCompact_image_of_subset_source hK hχ
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

/-! ### The `L²` inner product of smooth forms read in a chart -/

namespace TauCeti.SmoothForm

section Chart

open Set

variable [IsManifold I ∞ M] [CompactSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- **The `L²` inner product in a chart.** Let `θ` be a cutoff supported in the source of the
chart `ψ` and `β` a smooth form with `θ = 1` on the support of `β`. Then the `L²` inner product of
a smooth form `α` with `β` is the integral over `E`, for the Haar measure `volume`, of the inner
product in the chart of the localizations of `α` and `β`, weighted by the density
`s * riemannianJacobian b ψ.symm` of the Riemannian volume read in the chart, with `s` the
ratio of the Haar measures of `b` and `volume`. -/
theorem l2Inner_eq_integral_formInnerInChart (o : Manifold.Orientation I M (Fin m))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) {θ : M → ℝ}
    (hθ : tsupport θ ⊆ ψ.source) {α β : SmoothForm I M ℝ k}
    (hβ : ∀ x ∈ tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) β.val, θ x = 1) :
    l2Inner o α β = ∫ y, (b.addHaar.addHaarScalarFactor volume : ℝ) *
      riemannianJacobian (I := I) b ψ.symm y *
        ψ.formInnerInChart y (α.localize ψ θ y) (β.localize ψ θ y) := by
  borelize M
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  set s : ℝ := (b.addHaar.addHaarScalarFactor volume : ℝ)
  set g : M → ℝ := fun x ↦ alternatingFormInner (TangentSpace I x) k (α.val x) (β.val x)
  have hβ0 (x : M) (hx : θ x ≠ 1) : β.val x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hβ x h)
  have hgs (x : M) (hx : x ∉ ψ.source) : g x = 0 := by
    have : θ x ≠ 1 := fun h ↦ hx (hθ (subset_tsupport _ (by simp [Function.mem_support, h])))
    simp [g, hβ0 x this]
  have hθg (x : M) : θ x * θ x * g x = g x := by
    by_cases h : θ x = 1
    · simp [h]
    · simp [g, hβ0 x h]
  -- In the chart, the integrand is `g` read through `ψ.symm`.
  have hpt (y : E) (hy : y ∈ ψ.target) :
      ψ.formInnerInChart y (α.localize ψ θ y) (β.localize ψ θ y) = g (ψ.symm y) := by
    have e (γ : SmoothForm I M ℝ k) : γ.localize ψ θ y =
        θ (ψ.symm y) • (TauCeti.mpullback 𝓘(ℝ, E) I ψ.symm γ.val y : E [⋀^Fin k]→L[ℝ] ℝ) :=
      localize_of_mem _ _ _ hy
    have hsm (c : ℝ) (a a' : E [⋀^Fin k]→L[ℝ] ℝ) :
        ψ.formInnerInChart y (c • a) (c • a') = c * c * ψ.formInnerInChart y a a' := by
      simp [mul_assoc]
    rw [e, e]
    refine (hsm _ _ _).trans ?_
    rw [← ψ.alternatingFormInner_eq_formInnerInChart (by simp) _ _ hy]
    -- Restate the goal through `g`, so that both sides read `ψ.symm y` through the same coercion.
    change θ (ψ.symm y) * θ (ψ.symm y) * g (ψ.symm y) = g (ψ.symm y)
    exact hθg _
  calc l2Inner o α β = ∫ x, g x ∂riemannianVolume I M := l2Inner_eq_integral o α β
    _ = ∫ x in ψ.source, g x ∂riemannianVolume I M :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hgs).symm
    _ = ∫ y in ψ.target, riemannianJacobian (I := I) b ψ.symm y • g (ψ.symm y) ∂b.addHaar := by
        simpa using ψ.symm.setIntegral_riemannianVolume_eq hn b g
    _ = ∫ y in ψ.target, s * riemannianJacobian (I := I) b ψ.symm y *
          ψ.formInnerInChart y (α.localize ψ θ y) (β.localize ψ θ y) := by
        rw [Measure.isAddLeftInvariant_eq_smul b.addHaar volume, Measure.restrict_smul,
          integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, ← integral_const_mul]
        refine setIntegral_congr_fun ψ.open_target.measurableSet fun y hy ↦ ?_
        simp only [hpt y hy, smul_eq_mul, s]
        ring
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
        simp [localize_apply_of_notMem _ _ _ hy]

end Chart

end TauCeti.SmoothForm

/-! ### Pointwise bounds for the extension by zero along a chart -/

namespace TauCeti.RoughForm

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] in
/-- If the differential of `ψ` at `x` has norm at most `C`, for the Riemannian norm on the
tangent spaces of `M`, the extension by zero along `ψ` of a flat form `a` has norm at most
`‖a (ψ x)‖ * C ^ k` at `x`. -/
theorem norm_extendByZeroAlong_apply_le {n : WithTop ℕ∞}
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (a : E → E [⋀^Fin k]→L[ℝ] ℝ) {x : M} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ v : TangentSpace I x, @norm E _ (mfderiv I 𝓘(ℝ, E) ψ x v) ≤ C * ‖v‖) :
    ‖extendByZeroAlong ψ a x‖ ≤ ‖a (ψ x)‖ * C ^ k := by
  by_cases hx : x ∈ ψ.source
  · rw [extendByZeroAlong_apply_of_mem _ hx,
      mpullback_apply_eq_compContinuousLinearMap _ (a : RoughForm 𝓘(ℝ, E) E ℝ k)]
    refine (ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.opNorm_le_bound _ hC h) _)
      (norm_nonneg _)
  · rw [extendByZeroAlong_apply_of_notMem _ hx,
      norm_zero (E := TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M ℝ x)]
    positivity

/-- For a compact set `K` in the target of the chart, the Riemannian Jacobian of `ψ.symm` for a
basis `b` of `E`, times the pointwise inner product `⟨γ, γ⟩` at `ψ.symm y` of the extension by
zero `γ` along `ψ` of a flat form `a` supported in `K`, is at most a constant `B`, independent of
`a`, times `‖a y‖ ^ 2`, at every `y` in the target. -/
theorem exists_riemannianJacobian_mul_alternatingFormInner_extendByZeroAlong_le
    [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) {K : Set E} (hK : IsCompact K)
    (hKψ : K ⊆ ψ.target) :
    ∃ B, 0 ≤ B ∧ ∀ a : E → E [⋀^Fin k]→L[ℝ] ℝ, tsupport a ⊆ K → ∀ y ∈ ψ.target,
      riemannianJacobian (I := I) b ψ.symm y *
          alternatingFormInner (TangentSpace I (ψ.symm y)) k
            (extendByZeroAlong ψ a (ψ.symm y)) (extendByZeroAlong ψ a (ψ.symm y)) ≤
        B * ‖a y‖ ^ 2 := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  obtain ⟨Cd, hCd⟩ := ψ.exists_norm_mvfderiv_le_mul_norm hn hK hKψ
  obtain ⟨c₀, CJ, -, hJ⟩ := ψ.exists_le_riemannianJacobian_symm_le hn b hK hKψ
  set D := max Cd 0
  set c : ℝ := ((Module.finrank ℝ E).choose k : ℝ)
  refine ⟨max CJ 0 * (c * D ^ (2 * k)), by positivity, fun a haK y hy ↦ ?_⟩
  have hyy : ψ (ψ.symm y) = y := ψ.right_inv hy
  by_cases hyK : y ∈ K
  · have hnorm := norm_extendByZeroAlong_apply_le ψ a (x := ψ.symm y) (le_max_right Cd 0)
      fun v ↦ (hCd _ ⟨y, hyK, rfl⟩ v).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    rw [hyy] at hnorm
    set γ := extendByZeroAlong ψ a (ψ.symm y)
    have hg : alternatingFormInner (TangentSpace I (ψ.symm y)) k γ γ ≤ c * ‖γ‖ ^ 2 :=
      ContinuousAlternatingMap.alternatingFormInner_self_le γ
    calc riemannianJacobian (I := I) b ψ.symm y *
          alternatingFormInner (TangentSpace I (ψ.symm y)) k γ γ
        ≤ max CJ 0 * (c * (‖a y‖ * D ^ k) ^ 2) :=
          mul_le_mul ((hJ y hyK).2.trans (le_max_left _ _)) (hg.trans (by gcongr))
            (alternatingFormInner_self_nonneg _) (le_max_right _ _)
      _ = max CJ 0 * (c * D ^ (2 * k)) * ‖a y‖ ^ 2 := by ring
  · have ha0 : a y = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hyK (haK h)
    have hγ0 : extendByZeroAlong ψ a (ψ.symm y) = 0 := by
      have hx : ψ.symm y ∈ ψ.source := ψ.map_target hy
      rw [extendByZeroAlong_apply_of_mem _ hx]
      exact mpullback_apply_eq_zero (by rw [hyy]; exact ha0)
    rw [hγ0, map_zero, mul_zero]
    positivity

end TauCeti.RoughForm

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


/-- **Localizing with two cutoffs.** If `χ₂ = 1` on the support of `χ₁`, the localization of an
`L²` form with the cutoff `χ₁` is almost everywhere that with the cutoff `χ₂` multiplied by
`χ₁ ∘ ψ.symm`, extended by `0` outside `ψ.target`. -/
theorem localize_ae_eq_indicator_smul_localize {χ₁ χ₂ : C^∞⟮I, M; ℝ⟯}
    (h₁ : tsupport χ₁ ⊆ ψ.source) (h₂ : tsupport χ₂ ⊆ ψ.source)
    (h : ∀ x ∈ tsupport χ₁, χ₂ x = 1) (u : L2Form o k) :
    localize ψ χ₁ h₁ u =ᵐ[volume]
      fun y ↦ ψ.target.indicator (fun y ↦ χ₁ (ψ.symm y)) y • localize ψ χ₂ h₂ u y := by
  set r : E → ℝ := ψ.target.indicator fun y ↦ χ₁ (ψ.symm y)
  -- `r` is continuous with compact support, so it multiplies `L²` boundedly.
  have hK1 : IsCompact (tsupport χ₁) := (isClosed_tsupport _).isCompact
  have hrm : MemLp r ⊤ volume :=
    (ψ.continuous_indicator_comp_symm χ₁.contMDiff.continuous hK1 h₁).memLp_of_hasCompactSupport
      (ψ.hasCompactSupport_indicator_comp_symm hK1 h₁)
  let B : ℝ →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let T := B.holderL volume ⊤ 2 2 hrm.toLp
  have hT (v : Lp (E [⋀^Fin k]→L[ℝ] ℝ) 2 volume) : T v =ᵐ[volume] fun y ↦ r y • v y := by
    filter_upwards [B.coeFn_holder (r := 2) hrm.toLp v, hrm.coeFn_toLp] with y h1 h2
    rw [ContinuousLinearMap.holderL_apply_apply, h1, h2, ContinuousLinearMap.lsmul_apply]
  suffices hs : localize ψ χ₁ h₁ u = T (localize ψ χ₂ h₂ u) by
    rw [hs]
    exact hT _
  refine induction_on u (isClosed_eq (localize ψ χ₁ h₁).continuous
    (T.continuous.comp (localize ψ χ₂ h₂).continuous)) fun α ↦ Lp.ext ?_
  filter_upwards [localize_ofSmooth ψ χ₁ h₁ α, hT (localize ψ χ₂ h₂ (ofSmooth α)),
    localize_ofSmooth ψ χ₂ h₂ α] with y h1 h2 h3
  rw [h1, h2, h3]
  by_cases hy : y ∈ ψ.target
  · simp only [r, Set.indicator_of_mem hy, SmoothForm.localize_of_mem _ _ _ hy]
    by_cases hx : ψ.symm y ∈ tsupport χ₁
    · -- The scalar multiplications are those of the forms read in the chart, so the identities
      -- are applied by unification rather than rewriting.
      rw [h _ hx]
      exact congrArg _ (one_smul ℝ _).symm
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact (zero_smul ℝ _).trans (zero_smul ℝ _).symm
  · simp [r, SmoothForm.localize_apply_of_notMem _ _ _ hy]

/-- **The `L²` inner product in a chart, for `L²` forms.** Let `χ` be a smooth cutoff supported in
the source of the chart `ψ` and `β` a smooth form with `χ = 1` on the support of `β`. Then the
`L²` inner product of `u` with `β` is the integral over `E` of the inner product in the chart of
the localizations `localize ψ χ hχ u` and `β.localize ψ χ`, weighted by the density of the
Riemannian volume read in the chart, as in
`TauCeti.SmoothForm.l2Inner_eq_integral_formInnerInChart`. -/
theorem inner_ofSmooth_eq_integral_localize [T2Space M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {β : SmoothForm I M ℝ k} (hβ : ∀ x ∈ tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) β.val, χ x = 1)
    (u : L2Form o k) :
    ⟪u, L2Form.ofSmooth β⟫_ℝ = ∫ y, (b.addHaar.addHaarScalarFactor volume : ℝ) *
      riemannianJacobian (I := I) b ψ.symm y *
        ψ.formInnerInChart y (localize ψ χ hχ u y) (β.localize ψ χ y) := by
  set D : E → ℝ := fun y ↦ (b.addHaar.addHaarScalarFactor volume : ℝ) *
    riemannianJacobian (I := I) b ψ.symm y
  have hK : IsCompact (tsupport χ) := (isClosed_tsupport _).isCompact
  have hβl : ContDiff ℝ ∞ (β.localize ψ χ) := β.contDiff_localize ψ χ.contMDiff hK hχ
  have hβc : HasCompactSupport (β.localize ψ χ) := β.hasCompactSupport_localize ψ hK hχ
  have hβt : tsupport (β.localize ψ χ) ⊆ ψ.target :=
    (β.tsupport_localize_subset ψ hK hχ).trans ((ψ.mapsTo.mono_left hχ).image_subset)
  -- In a basis `e` of the forms on `E`, the integrand is a sum of products of a coordinate of the
  -- localization of `u` with a continuous function `G p` with compact support.
  let e := Module.finBasis ℝ (E [⋀^Fin k]→L[ℝ] ℝ)
  let L (p : Fin (Module.finrank ℝ (E [⋀^Fin k]→L[ℝ] ℝ))) :
      (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (e.coord p)
  let G (p : Fin (Module.finrank ℝ (E [⋀^Fin k]→L[ℝ] ℝ))) (y : E) : ℝ :=
    D y * ψ.formInnerInChart y (e p) (β.localize ψ χ y)
  have hGm (p) : MemLp (G p) 2 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_ ?_
    · refine ContinuousOn.continuous_of_tsupport_subset ?_ ψ.open_target
        ((closure_mono (Function.support_subset_iff'.2 fun y hy ↦ by
          simp [G, Function.notMem_support.1 hy])).trans hβt)
      exact ((contDiffOn_const.mul (ψ.contDiffOn_riemannianJacobian_symm b)).mul
        (ψ.contDiffOn_formInnerInChart subset_rfl contDiffOn_const hβl.contDiffOn)).continuousOn
    · exact hβc.mono (Function.support_subset_iff'.2 fun y hy ↦ by
        simp [G, Function.notMem_support.1 hy])
  let B := ContinuousLinearMap.mul ℝ ℝ
  have key (v : L2Form o k) : ∫ y, D y * ψ.formInnerInChart y (localize ψ χ hχ v y)
      (β.localize ψ χ y) =
        ∑ p, B.lpPairing volume 2 2 ((L p).compLp (localize ψ χ hχ v)) (hGm p).toLp := by
    have hint (p) : Integrable (fun y ↦ L p (localize ψ χ hχ v y) * G p y) volume :=
      ((L p).comp_memLp' (Lp.memLp _)).integrable_mul (hGm p)
    simp_rw [ContinuousLinearMap.lpPairing_eq_integral]
    rw [← integral_finsetSum _ fun p _ ↦ (hint p).congr ?_]
    · refine integral_congr_ae ?_
      filter_upwards [ae_all_iff.2 fun p ↦ (L p).coeFn_compLp (localize ψ χ hχ v),
        ae_all_iff.2 fun p ↦ (hGm p).coeFn_toLp] with y h1 h2
      simp only [B, ContinuousLinearMap.mul_apply', h1, h2, G, L,
        LinearMap.coe_toContinuousLinearMap',
        Module.Basis.coord_apply]
      conv_lhs => rw [← e.sum_repr (localize ψ χ hχ v y)]
      simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ ↦ by ring
    · filter_upwards [(L p).coeFn_compLp (localize ψ χ hχ v), (hGm p).coeFn_toLp]
        with y h1 h2
      simp [B, h1, h2]
  rw [key u]
  refine induction_on u (isClosed_eq (continuous_id.inner continuous_const)
    (continuous_finsetSum _ fun p _ ↦ ((B.lpPairing volume 2 2).flip (hGm p).toLp).continuous.comp
      (((L p).compLpL 2 volume).continuous.comp (localize ψ χ hχ).continuous))) fun α ↦ ?_
  rw [← key, inner_ofSmooth, l2Inner_eq_integral_formInnerInChart ψ o b hχ hβ]
  refine integral_congr_ae ?_
  filter_upwards [localize_ofSmooth ψ χ hχ α] with y hy
  rw [hy]

end Localize

/-! ### Extension by zero along a chart, and gluing -/

section ExtendByZero

variable [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] [T2Space M]

/-- The step of `exists_norm_ofSmooth_extendByZeroAlong_le` for the squares of the norms, as an
inequality of integrals: the change of variables along `ψ.symm` turns the integral of `⟨γ, γ⟩` for
the extension by zero `γ` of `a` into an integral over `ψ.target`, where the integrand is bounded by
a multiple of `‖a‖ ^ 2`. -/
private theorem exists_ofReal_norm_ofSmooth_extendByZeroAlong_sq_le
    (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (o : Manifold.Orientation I M (Fin m)) {K : Set E}
    (hK : IsCompact K) (hKψ : K ⊆ ψ.target) :
    ∃ B, 0 ≤ B ∧ ∀ (a : E → E [⋀^Fin k]→L[ℝ] ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ ψ.target), tsupport a ⊆ K →
      ENNReal.ofReal (‖(ofSmooth (SmoothForm.extendByZeroAlong ψ a ha hc hs) : L2Form o k)‖ ^ 2) ≤
        ENNReal.ofReal B * ∫⁻ y, ‖a y‖ₑ ^ (2 : ℝ) ∂volume := by
  borelize M
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let b := Module.finBasis ℝ E
  obtain ⟨B', hB', hB⟩ :=
    RoughForm.exists_riemannianJacobian_mul_alternatingFormInner_extendByZeroAlong_le
      (k := k) b ψ hK hKψ
  set s := b.addHaar.addHaarScalarFactor volume
  refine ⟨s * B', by positivity, fun a ha hc hs haK ↦ ?_⟩
  set γ := SmoothForm.extendByZeroAlong ψ a ha hc hs
  set g : M → ℝ := fun x ↦ alternatingFormInner (TangentSpace I x) k (γ.val x) (γ.val x)
  set J : E → ℝ := riemannianJacobian (I := I) b ψ.symm
  -- The integrand in the chart is bounded by a multiple of `‖a‖ ^ 2`.
  have hpt : ∀ y ∈ ψ.target, J y * g (ψ.symm y) ≤ B' * ‖a y‖ ^ 2 := fun y hy ↦ by
    simpa only [g, γ, SmoothForm.coe_extendByZeroAlong] using hB a haK y hy
  calc ENNReal.ofReal (‖(ofSmooth γ : L2Form o k)‖ ^ 2)
      = ∫⁻ x, ENNReal.ofReal (g x) ∂riemannianVolume I M := by
        rw [norm_ofSmooth_sq, l2Inner_eq_integral, ofReal_integral_eq_lintegral_ofReal]
        · exact (continuous_alternatingFormInner γ γ).integrable_of_compactSpace
        · exact Filter.Eventually.of_forall fun x ↦ alternatingFormInner_self_nonneg _
    _ = ∫⁻ x in ψ.source, ENNReal.ofReal (g x) ∂riemannianVolume I M := by
        refine (setLIntegral_eq_of_support_subset fun x hx ↦ ?_).symm
        by_contra hxs
        apply hx
        simp [g, γ, RoughForm.extendByZeroAlong_apply_of_notMem _ hxs]
    _ = ∫⁻ y in ψ.target, ENNReal.ofReal (J y) * ENNReal.ofReal (g (ψ.symm y)) ∂b.addHaar := by
        simpa [J] using ψ.symm.setLIntegral_riemannianVolume_eq hn b fun x ↦ ENNReal.ofReal (g x)
    _ ≤ ∫⁻ y in ψ.target, ENNReal.ofReal B' * ‖a y‖ₑ ^ (2 : ℝ) ∂b.addHaar := by
        refine setLIntegral_mono' ψ.open_target.measurableSet fun y hy ↦ ?_
        rw [← ENNReal.ofReal_mul (riemannianJacobian_nonneg _ _ _), ← ofReal_norm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two, ← ENNReal.ofReal_mul hB',
          Real.rpow_two]
        exact ENNReal.ofReal_le_ofReal (hpt y hy)
    _ ≤ ∫⁻ y, ENNReal.ofReal B' * ‖a y‖ₑ ^ (2 : ℝ) ∂b.addHaar := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (s * B') * ∫⁻ y, ‖a y‖ₑ ^ (2 : ℝ) ∂volume := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          Measure.isAddLeftInvariant_eq_smul b.addHaar volume, lintegral_smul_measure,
          ENNReal.smul_def, smul_eq_mul, ENNReal.ofReal_mul (q := B') s.coe_nonneg,
          ENNReal.ofReal_coe_nnreal]
        ring

/-- **Extension by zero along a chart is bounded in `L²`.** For a chart `ψ` and a compact set
`K ⊆ ψ.target`, there is `C` such that the extension by zero along `ψ` of every smooth flat form
`a` supported in `K` has `L²` norm at most `C` times the `L²` norm of `a` for the Haar measure
`volume` of `E`. -/
theorem exists_norm_ofSmooth_extendByZeroAlong_le (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    (o : Manifold.Orientation I M (Fin m)) {K : Set E} (hK : IsCompact K) (hKψ : K ⊆ ψ.target) :
    ∃ C, 0 ≤ C ∧ ∀ (a : E → E [⋀^Fin k]→L[ℝ] ℝ) (ha : ContDiff ℝ ∞ a)
      (hc : HasCompactSupport a) (hs : tsupport a ⊆ ψ.target), tsupport a ⊆ K →
      ‖(ofSmooth (SmoothForm.extendByZeroAlong ψ a ha hc hs) : L2Form o k)‖ ≤
        C * (eLpNorm a 2 volume).toReal := by
  obtain ⟨B, hB, h⟩ := exists_ofReal_norm_ofSmooth_extendByZeroAlong_sq_le (k := k) ψ o hK hKψ
  refine ⟨√B, by positivity, fun a ha hc hs haK ↦ ?_⟩
  have hmem : MemLp a 2 volume := ha.continuous.memLp_of_hasCompactSupport hc
  have hX : eLpNorm a 2 volume ^ (2 : ℝ) = ∫⁻ y, ‖a y‖ₑ ^ (2 : ℝ) ∂volume := by
    simpa using eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hmem.aestronglyMeasurable
  have h2 := h a ha hc hs haK
  rw [← hX] at h2
  have h3 := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg zero_le_two hmem.eLpNorm_ne_top))).1 h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, ← ENNReal.toReal_rpow, Real.rpow_two] at h3
  refine (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg) two_ne_zero).1 ?_
  rwa [mul_pow, Real.sq_sqrt hB]

/-- **An `L²` form whose localizations are smooth is smooth.** Let `ψ i` be finitely many charts
and `ρ` a smooth partition of unity subordinate to their sources. If, for every `i`, the
localization of `u` to `ψ i` with the cutoff `ρ i` is almost everywhere a smooth flat form `f i`
with compact support in `(ψ i).target`, then `u` is the smooth form obtained by extending each
`f i` by zero along `ψ i` and summing over `i`. -/
theorem eq_ofSmooth_of_localize {ι : Type*} [Fintype ι]
    (ψ : ι → PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (ρ : SmoothPartitionOfUnity ι I M Set.univ)
    (hρ : ρ.IsSubordinate fun i ↦ (ψ i).source) {u : L2Form o k}
    {f : ι → E → E [⋀^Fin k]→L[ℝ] ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (hfs : ∀ i, tsupport (f i) ⊆ (ψ i).target)
    (hu : ∀ i, localize (ψ i) (ρ i) (hρ i) u =ᵐ[volume] f i) :
    u = ofSmooth (∑ i, SmoothForm.extendByZeroAlong (ψ i) (f i) (hf i) (hfc i) (hfs i)) := by
  have hKρ (i : ι) : IsCompact (tsupport (ρ i)) := (isClosed_tsupport _).isCompact
  have himage (i : ι) : (ψ i) '' tsupport (ρ i) ⊆ (ψ i).target :=
    ((ψ i).mapsTo.mono_left (hρ i)).image_subset
  set K : ι → Set E := fun i ↦ tsupport (f i) ∪ (ψ i) '' tsupport (ρ i)
  have hK (i : ι) : IsCompact (K i) := (hfc i).union
    ((ψ i).isCompact_image_of_subset_source (hKρ i) (hρ i))
  have hKψ (i : ι) : K i ⊆ (ψ i).target := Set.union_subset (hfs i) (himage i)
  choose C hC0 hC using fun i ↦
    exists_norm_ofSmooth_extendByZeroAlong_le (k := k) (ψ i) o (hK i) (hKψ i)
  set L : ι → L2Form o k →L[ℝ] Lp (E [⋀^Fin k]→L[ℝ] ℝ) 2 (volume : Measure E) :=
    fun i ↦ localize (ψ i) (ρ i) (hρ i)
  choose CL hCL0 hCL using fun i ↦ (L i).bound
  set A := 1 + ∑ i, C i * CL i
  have hA : 0 < A := add_pos_of_pos_of_nonneg one_pos
    (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hC0 i) (hCL0 i).le)
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨β, hβ⟩ := denseRange_ofSmooth.exists_dist_lt u (div_pos hε hA)
  rw [dist_eq_norm] at hβ
  set g : ι → E → E [⋀^Fin k]→L[ℝ] ℝ := fun i ↦ β.localize (ψ i) (ρ i)
  have hg (i : ι) : ContDiff ℝ ∞ (g i) := β.contDiff_localize (ψ i) (ρ i).contMDiff (hKρ i) (hρ i)
  have hgc (i : ι) : HasCompactSupport (g i) := β.hasCompactSupport_localize (ψ i) (hKρ i) (hρ i)
  have hsub (i : ι) : tsupport (g i - f i) ⊆ K i := by
    refine closure_minimal (fun y hy ↦ ?_) (hK i).isClosed
    by_contra h
    simp only [K, Set.mem_union, not_or] at h
    exact hy (by simp [g, image_eq_zero_of_notMem_tsupport h.1,
      localize_apply_eq_zero_of_notMem _ _ _ h.2])
  -- The difference of `β` and the glued form is the sum of the extensions of `g i - f i`.
  have hdiff : ofSmooth β - ofSmooth (∑ i, SmoothForm.extendByZeroAlong (ψ i) (f i) (hf i)
      (hfc i) (hfs i)) = ∑ i, (ofSmooth (SmoothForm.extendByZeroAlong (ψ i) (g i - f i)
        ((hg i).sub (hf i)) ((hgc i).sub (hfc i)) ((hsub i).trans (hKψ i))) : L2Form o k) := by
    rw [← map_sub, ← map_sum]
    congr 1
    conv_lhs => rw [← β.sum_extendByZeroAlong_localize ψ ρ hρ hKρ]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ (SmoothForm.extendByZeroAlong_sub _ _ _ _ _ _ _ _ _).symm
  -- Each `g i - f i` is small in `L²`, since `localize` is continuous.
  have hloc (i : ι) : (eLpNorm (g i - f i) 2 volume).toReal ≤ CL i * (ε / A) := by
    have h : (eLpNorm (g i - f i) 2 volume).toReal = ‖L i (ofSmooth β - u)‖ := by
      rw [map_sub, Lp.norm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans
        ((localize_ofSmooth _ _ _ β).sub (hu i)))]
    rw [h]
    refine (hCL i _).trans (mul_le_mul_of_nonneg_left ?_ (hCL0 i).le)
    rw [norm_sub_rev]
    exact hβ.le
  calc ‖u - ofSmooth (∑ i, SmoothForm.extendByZeroAlong (ψ i) (f i) (hf i) (hfc i) (hfs i))‖
      = ‖(u - ofSmooth β) + (ofSmooth β - ofSmooth (∑ i, SmoothForm.extendByZeroAlong (ψ i) (f i)
          (hf i) (hfc i) (hfs i)))‖ := by rw [sub_add_sub_cancel]
    _ ≤ ε / A + ∑ i, C i * (CL i * (ε / A)) := by
        refine (norm_add_le _ _).trans (add_le_add hβ.le ?_)
        rw [hdiff]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        exact (hC i _ _ _ _ (hsub i)).trans (by gcongr; exacts [hC0 i, hloc i])
    _ = 0 + ε := by
        have h : ε / A + ∑ i, C i * (CL i * (ε / A)) = A * (ε / A) := by
          simp only [A, add_mul, one_mul, Finset.sum_mul]
          exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ by ring)
        rw [h, mul_div_cancel₀ _ hA.ne', zero_add]

end ExtendByZero

end L2Form

end SymplecticGeometry

end
