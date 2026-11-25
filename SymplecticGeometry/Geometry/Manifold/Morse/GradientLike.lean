/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic

/-!
# Gradient-like vector fields

A vector field `X` on a manifold `M` is *gradient-like* for a function `f : M → ℝ`
(`TauCeti.IsGradientLike f X`) when, for some smooth Riemannian metric `g` and some continuous
function `δ > 0`,

`δ x * (g x (X x) (X x) + ‖grad f x‖ ^ 2) ≤ df_x (X x)` for every `x`,

where the gradient and its norm are those of `g`. This is the quantitative condition of
McDuff–Salamon, Definition 7.4.5, and of Cieliebak–Eliashberg, the one with which Weinstein
structures are defined. It makes `f` increase strictly along `X` away from the critical points of
`f`, and makes the zeros of `X` exactly these critical points.

## Main declarations

* `TauCeti.IsGradientLike`: the predicate, with `TauCeti.isGradientLike_def`.
* `TauCeti.IsGradientLike.mvfderiv_apply_pos`: `df(X) > 0` off the critical points of `f`.
* `TauCeti.IsGradientLike.eq_zero_iff`: `X x = 0` exactly when `x` is a critical point of `f`.
* `TauCeti.IsGradientLike.strictMonoOn_comp`, `TauCeti.IsGradientLike.strictMono_comp`: `f`
  increases strictly along an integral curve of `X`, on a convex set of times or on all of `ℝ`,
  that meets no critical point.
* `TauCeti.IsGradientLike.smul`: `a • X` is gradient-like for a continuous positive `a`.
* `TauCeti.IsGradientLike.comp`: `X` is gradient-like for `h ∘ f` when `h` is `C¹` with `h' > 0`.
* `TauCeti.isGradientLike_mgradient`: the gradient of `f` for any smooth metric is gradient-like
  for `f`, with `δ = 1 / 2`.

## Implementation notes

The declarations about gradient-like fields are in the namespace `TauCeti`, since they concern
only Tau Ceti's and Mathlib's notions. The metric is a `Bundle.ContMDiffRiemannianMetric`, and the norm of the gradient
is taken for the `RiemannianBundle` instance that it defines, as in Tau Ceti's
`TauCeti.IsAdaptedPseudoGradient.exists_contMDiffRiemannianMetric_neg_mgradient_eq`; this
instance is introduced in the statements only.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Bundle Set
open scoped ContDiff Manifold

open TauCeti.Manifold

/-- If `0 < b`, `0 ≤ G` and `0 ≤ N`, then `min b b⁻¹ * (b ^ 2 * G + N) ≤ b * (G + N)`. -/
theorem min_inv_mul_sq_mul_add_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {b G N : α} (hb : 0 < b) (hG : 0 ≤ G) (hN : 0 ≤ N) :
    min b b⁻¹ * (b ^ 2 * G + N) ≤ b * (G + N) := by
  have hm₁ : min b b⁻¹ * b ≤ 1 :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hb.le).trans_eq (inv_mul_cancel₀ hb.ne')
  have hm₂ : min b b⁻¹ ≤ b := min_le_left _ _
  calc min b b⁻¹ * (b ^ 2 * G + N) = min b b⁻¹ * b * (b * G) + min b b⁻¹ * N := by ring
    _ ≤ 1 * (b * G) + b * N := by gcongr
    _ = b * (G + N) := by ring

namespace Bundle.ContMDiffRiemannianMetric

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- A smooth Riemannian metric is nonnegative on the diagonal. -/
theorem inner_self_nonneg (g : ContMDiffRiemannianMetric IB n F E) (b : B) (v : E b) :
    0 ≤ g.inner b v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact (g.pos b v hv).le

end Bundle.ContMDiffRiemannianMetric


namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A vector field `X` is **gradient-like** for a function `f` when there are a smooth Riemannian
metric `g` and a continuous positive function `δ` with
`δ x * (g x (X x) (X x) + ‖grad f x‖ ^ 2) ≤ df_x (X x)` at every point `x`, the gradient and its
norm being those of `g`. -/
def IsGradientLike (f : M → ℝ) (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) : Prop :=
  ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
    ∃ δ : M → ℝ, Continuous δ ∧ (∀ x, 0 < δ x) ∧
      letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
      ∀ x, δ x * (g.inner x (X x) (X x) + ‖mgradient 𝓘(ℝ, E) f x‖ ^ 2) ≤
        mvfderiv 𝓘(ℝ, E) f x (X x)

/-- The definition of `TauCeti.IsGradientLike`, unfolded. -/
theorem isGradientLike_def (f : M → ℝ) (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) :
    IsGradientLike f X ↔
      ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
        ∃ δ : M → ℝ, Continuous δ ∧ (∀ x, 0 < δ x) ∧
          letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
          ∀ x, δ x * (g.inner x (X x) (X x) + ‖mgradient 𝓘(ℝ, E) f x‖ ^ 2) ≤
            mvfderiv 𝓘(ℝ, E) f x (X x) :=
  Iff.rfl

variable {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsGradientLike

/-- A gradient-like field increases `f` strictly at every point that is not critical for `f`. -/
theorem mvfderiv_apply_pos (hX : IsGradientLike f X) {x : M} (hx : mvfderiv 𝓘(ℝ, E) f x ≠ 0) :
    0 < mvfderiv 𝓘(ℝ, E) f x (X x) := by
  obtain ⟨g, δ, -, hδ, h⟩ := hX
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  have hgrad : 0 < ‖mgradient 𝓘(ℝ, E) f x‖ :=
    norm_pos_iff.2 (by rwa [ne_eq, mgradient_eq_zero_iff])
  have := g.inner_self_nonneg x (X x)
  exact lt_of_lt_of_le (by have := hδ x; positivity) (h x)

/-- The zeros of a gradient-like field are exactly the critical points of the function. -/
theorem eq_zero_iff (hX : IsGradientLike f X) {x : M} :
    X x = 0 ↔ mvfderiv 𝓘(ℝ, E) f x = 0 := by
  obtain ⟨g, δ, -, hδ, h⟩ := hX
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  have hx := h x
  have hδx := hδ x
  constructor
  · intro h0
    simp only [h0, map_zero, zero_add] at hx
    have : ‖mgradient 𝓘(ℝ, E) f x‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hx hδx
    rw [← mgradient_eq_zero_iff (I := 𝓘(ℝ, E)), ← norm_eq_zero]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (by positivity))
  · intro h0
    rw [h0, zero_apply] at hx
    rw [mgradient_eq_zero_iff.2 h0, norm_zero] at hx
    by_contra hne
    have := g.pos x (X x) hne
    nlinarith

/-- Along an integral curve of a gradient-like field on a convex set `s` of times that meets no
critical point of `f`, the function `f` is strictly increasing on `s`. -/
theorem strictMonoOn_comp (hX : IsGradientLike f X) {γ : ℝ → M} {s : Set ℝ} (hs : Convex ℝ s)
    (hγ : IsMIntegralCurveOn γ X s) (hcrit : ∀ t ∈ s, mvfderiv 𝓘(ℝ, E) f (γ t) ≠ 0) :
    StrictMonoOn (f ∘ γ) s := by
  have hderiv : ∀ t ∈ s,
      HasDerivWithinAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (X (γ t))) s t := fun t ht ↦ by
    have hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (γ t) := by
      by_contra hnd
      exact hcrit t ht (mvfderiv_eq_zero_iff.2 (mfderiv_zero_of_not_mdifferentiableAt hnd))
    exact hasDerivWithinAt_comp_curve hf (hγ t ht)
  refine strictMonoOn_of_deriv_pos hs (fun t ht ↦ (hderiv t ht).continuousWithinAt) fun t ht ↦ ?_
  have ht' := interior_subset ht
  rw [((hderiv t ht').hasDerivAt (mem_interior_iff_mem_nhds.1 ht)).deriv]
  exact hX.mvfderiv_apply_pos (hcrit t ht')

/-- Along an integral curve of a gradient-like field that meets no critical point of `f`, the
function `f` is strictly increasing. -/
theorem strictMono_comp (hX : IsGradientLike f X) {γ : ℝ → M} (hγ : IsMIntegralCurve γ X)
    (hcrit : ∀ t, mvfderiv 𝓘(ℝ, E) f (γ t) ≠ 0) : StrictMono (f ∘ γ) :=
  strictMonoOn_univ.1 <| hX.strictMonoOn_comp convex_univ (hγ.isMIntegralCurveOn univ)
    fun t _ ↦ hcrit t

/-- Multiplying a gradient-like field by a continuous positive function gives a gradient-like
field. -/
theorem smul (hX : IsGradientLike f X) {a : M → ℝ} (ha : Continuous a) (ha₀ : ∀ x, 0 < a x) :
    IsGradientLike f fun x ↦ a x • X x := by
  obtain ⟨g, δ, hδc, hδ, h⟩ := hX
  refine ⟨g, fun x ↦ δ x * min (a x) (a x)⁻¹,
    hδc.mul (ha.min (ha.inv₀ fun x ↦ (ha₀ x).ne')), fun x ↦ ?_, fun x ↦ ?_⟩
  · have := ha₀ x; have := hδ x; positivity
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  have hδx := hδ x
  simp only [map_smul, smul_apply, smul_eq_mul]
  calc δ x * min (a x) (a x)⁻¹ *
        (a x * (a x * g.inner x (X x) (X x)) + ‖mgradient 𝓘(ℝ, E) f x‖ ^ 2)
      = δ x * (min (a x) (a x)⁻¹ *
          (a x ^ 2 * g.inner x (X x) (X x) + ‖mgradient 𝓘(ℝ, E) f x‖ ^ 2)) := by ring
    _ ≤ δ x * (a x * (g.inner x (X x) (X x) + ‖mgradient 𝓘(ℝ, E) f x‖ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (min_inv_mul_sq_mul_add_le (ha₀ x)
        (g.inner_self_nonneg x (X x)) (by positivity)) hδx.le
    _ ≤ a x * mvfderiv 𝓘(ℝ, E) f x (X x) := by
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (h x) (ha₀ x).le

/-- A field that is gradient-like for a differentiable `f` is gradient-like for `h ∘ f`, when `h`
is `C¹` with positive derivative at every value of `f`. -/
theorem comp (hX : IsGradientLike f X) (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {h : ℝ → ℝ}
    (hh : ContDiff ℝ 1 h) (hh' : ∀ x, 0 < deriv h (f x)) : IsGradientLike (h ∘ f) X := by
  obtain ⟨g, δ, hδc, hδ, H⟩ := hX
  have hb : Continuous fun x ↦ deriv h (f x) :=
    (hh.continuous_deriv le_rfl).comp hf.continuous
  refine ⟨g, fun x ↦ δ x * min (deriv h (f x)) (deriv h (f x))⁻¹,
    hδc.mul (hb.min (hb.inv₀ fun x ↦ (hh' x).ne')), fun x ↦ ?_, fun x ↦ ?_⟩
  · have := hh' x; have := hδ x; positivity
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  have hdiff : DifferentiableAt ℝ h (f x) := hh.differentiable one_ne_zero _
  have hgrad := mgradient_comp_deriv (I := 𝓘(ℝ, E)) hdiff (hf x)
  set b := deriv h (f x)
  have hbx : 0 < b := hh' x
  have hD : mvfderiv 𝓘(ℝ, E) (h ∘ f) x (X x) = b * mvfderiv 𝓘(ℝ, E) f x (X x) := by
    rw [← inner_mgradient, hgrad, real_inner_smul_left, inner_mgradient]
  rw [hD, hgrad, norm_smul, Real.norm_of_nonneg hbx.le]
  have hδx := hδ x
  calc δ x * min b b⁻¹ * (g.inner x (X x) (X x) + (b * ‖mgradient 𝓘(ℝ, E) f x‖) ^ 2)
      = δ x * (min b b⁻¹ *
          (b ^ 2 * ‖mgradient 𝓘(ℝ, E) f x‖ ^ 2 + g.inner x (X x) (X x))) := by ring
    _ ≤ δ x * (b * (‖mgradient 𝓘(ℝ, E) f x‖ ^ 2 + g.inner x (X x) (X x))) := by
      exact mul_le_mul_of_nonneg_left (min_inv_mul_sq_mul_add_le hbx (by positivity)
        (g.inner_self_nonneg x (X x))) hδx.le
    _ ≤ b * mvfderiv 𝓘(ℝ, E) f x (X x) := by
      rw [mul_left_comm, add_comm (_ ^ 2)]
      exact mul_le_mul_of_nonneg_left (H x) hbx.le

end IsGradientLike

/-- The gradient of any function for a smooth Riemannian metric `g` is gradient-like for it, with
`δ = 1 / 2`. -/
theorem isGradientLike_mgradient
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (f : M → ℝ) :
    IsGradientLike f
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
      mgradient 𝓘(ℝ, E) f) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  refine ⟨g, fun _ ↦ 1 / 2, continuous_const, fun _ ↦ by norm_num, fun x ↦ ?_⟩
  rw [← g.norm_sq, mvfderiv_apply_mgradient, real_inner_self_eq_norm_sq]
  exact le_of_eq (by ring)

end TauCeti

end
