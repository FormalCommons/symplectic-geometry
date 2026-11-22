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
import TauCeti.Geometry.Manifold.Riemannian.Codifferential
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

## Main definitions and results

* `TauCeti.SmoothForm.l2Inner`: the `L²` inner product of smooth forms, symmetric
  (`l2Inner_comm`), bilinear (`l2Inner_add_left`, `l2Inner_smul_left`, `l2Inner_neg_left`,
  `l2Inner_sub_left`, …), with `l2Inner_self_nonneg` and `l2Inner_self_eq_zero_iff`.
* `SymplecticGeometry.L2Form o k`: the Hilbert space of `L²` `k`-forms, with
  `L2Form.ofSmooth`, `L2Form.inner_ofSmooth`, `L2Form.norm_ofSmooth_sq`,
  `L2Form.ofSmooth_injective`, `L2Form.denseRange_ofSmooth` and `L2Form.induction_on`.

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

/-- The Riemannian volume measure needs only a continuous metric. -/
local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

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

end L2Form

end SymplecticGeometry

end
