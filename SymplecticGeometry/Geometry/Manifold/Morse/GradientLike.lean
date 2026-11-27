/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.RegularValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Topology.LocallyFinite.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.VectorBundle.Riemannian.Basic
import SymplecticGeometry.Algebra.Order.Field.Basic
import SymplecticGeometry.Analysis.Convex.Mul
import SymplecticGeometry.Geometry.Manifold.Riemannian.PullbackPartialDiffeomorph
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Riemannian.Existence
import SymplecticGeometry.Geometry.Manifold.VectorField.Pullback

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
* `TauCeti.IsGradientLike.mvfderiv_apply_pos_of_isRegularValue`: `df(X) > 0` on the level
  `f⁻¹(c)` of a regular value `c`.
* `TauCeti.IsGradientLike.eq_zero_iff`: `X x = 0` exactly when `x` is a critical point of `f`.
* `TauCeti.IsGradientLike.strictMonoOn_comp`, `TauCeti.IsGradientLike.strictMono_comp`: `f`
  increases strictly along an integral curve of `X`, on a convex set of times or on all of `ℝ`,
  that meets no critical point.
* `TauCeti.IsGradientLike.smul`: `a • X` is gradient-like for a continuous positive `a`.
* `TauCeti.IsGradientLike.comp`: `X` is gradient-like for `h ∘ f` when `h` is `C¹` with `h' > 0`.
* `TauCeti.IsGradientLike.mpullback`: the pull-back `VectorField.mpullback Φ X` of a gradient-like
  field along a smooth map `Φ` with invertible differential, such as a diffeomorphism, is
  gradient-like for `f ∘ Φ`.
* `TauCeti.isGradientLike_mgradient`: the gradient of `f` for any smooth metric is gradient-like
  for `f`, with `δ = 1 / 2`.
* `TauCeti.isGradientLike_of_forall_exists_nhds`: on a σ-compact Hausdorff manifold the condition
  is local: a metric and a constant for which the inequality holds near each point suffice.
* `TauCeti.exists_nhds_mul_le_of_mvfderiv_apply_pos`: near a point where `df(X) > 0`, the
  inequality holds for every metric and a small constant, when `f` is `C¹` and `X` continuous.
* `TauCeti.IsGradientLike.exists_nhds_mul_le_of_isLocalDiffeomorphAt`: the local hypothesis of
  `TauCeti.isGradientLike_of_forall_exists_nhds` holds at `Φ y` when, near `y`, a local
  diffeomorphism `Φ` carries a gradient-like field for `f'` to `X` and `f ∘ Φ = f'`.

## Implementation notes

The declarations about gradient-like fields are in the namespace `TauCeti`, since they concern
only Tau Ceti's and Mathlib's notions. The metric is a `Bundle.ContMDiffRiemannianMetric`, and
the norm of the gradient is taken for the `RiemannianBundle` instance that it defines, as in
Tau Ceti's `TauCeti.IsAdaptedPseudoGradient.exists_contMDiffRiemannianMetric_neg_mgradient_eq`; this
instance is introduced in the statements only.

For `IsGradientLike.mpullback`, the metric is Tau Ceti's pull-back
`Bundle.ContMDiffRiemannianMetric.pullback` of the metric of `X`, for which `Φ` is a local
isometry (`Bundle.ContMDiffRiemannianMetric.isLocalRiemannianIsometry_pullback_of_isInvertible`);
the norm of the gradient is then preserved by
`TauCeti.IsLocalRiemannianIsometry.norm_mgradient_comp`, and the constant is `δ ∘ Φ`.

The local metrics are glued by `TauCeti.exists_contMDiffRiemannianMetric_inner_mem_of_local`,
the case without prescribed values of Tau Ceti's
`TauCeti.exists_contMDiffRiemannianMetric_inner_eq_and_inner_mem_of_locallyFinite`, which
`TauCeti.IsAdaptedPseudoGradient.exists_contMDiffRiemannianMetric_inner_eq_euclideanForm` uses. A
locally finite refinement of the given neighbourhoods first yields, by Tau Ceti's
`LocallyFinite.exists_continuous_pos_lt`, a continuous `δ > 0` below the local constants.
The inequality with constant `δ y` at `y` is then convex in the metric: with
`R = df(X) - δ g(X, X)`, the bound `δ ‖grad f‖ ^ 2 ≤ R` amounts, by Cauchy–Schwarz, to
`δ (df v) ^ 2 ≤ R g(v, v)` for every `v`, and this is convex in `g` by
`SymplecticGeometry.convex_setOfPred_le_mul`: for any `C` the pairs `(p, q)` of nonnegative reals
with `C ≤ p q` form a convex set.

For `IsGradientLike.exists_nhds_mul_le_of_isLocalDiffeomorphAt`, the metric near `Φ y` is the
metric of the field on `M'` pulled back along the local inverse `Ψ` of `Φ`, which is smooth and
positive definite on the source of `Ψ` (`PartialDiffeomorph.contMDiffOn_pullback`,
`PartialDiffeomorph.pullback_apply_self_pos`). The fibrewise condition with
a constant `c` is carried along `dΨ` from `M'` to `M`. It is imposed only on a closed
neighbourhood `K` of `Φ y`, and the gluing by
`TauCeti.exists_contMDiffRiemannianMetric_inner_mem_of_local` uses any metric off `K` (Tau Ceti's
`TauCeti.nonempty_contMDiffRiemannianMetric`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

open TauCeti.Manifold SymplecticGeometry

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
  have : 0 ≤ g.inner x (X x) (X x) := g.toRiemannianMetric.inner_self_nonneg x (X x)
  exact lt_of_lt_of_le (by have := hδ x; positivity) (h x)

/-- A gradient-like field increases `f` strictly at every point of the level `f⁻¹(c)` of a
regular value `c` of `f`. -/
theorem mvfderiv_apply_pos_of_isRegularValue (hX : IsGradientLike f X) {c : ℝ}
    (hc : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f c) {x : M} (hx : f x = c) :
    0 < mvfderiv 𝓘(ℝ, E) f x (X x) :=
  hX.mvfderiv_apply_pos (isRegularPoint_iff_mvfderiv_ne_zero.1 (hc.isRegularPoint hx))

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
  have hf : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (γ t) := fun t ht ↦ by
    by_contra hnd
    exact hcrit t ht (mvfderiv_eq_zero_iff.2 (mfderiv_zero_of_not_mdifferentiableAt hnd))
  -- Tau Ceti states the decreasing case; apply it to `-f`.
  have hneg := hγ.strictAntiOn_comp (f := -f) hs (fun t ht ↦ (hf t ht).neg) fun t ht ↦ by
    rw [mvfderiv_neg, neg_apply, neg_lt_zero]
    exact hX.mvfderiv_apply_pos (hcrit t (interior_subset ht))
  exact fun a ha b hb hab ↦ neg_lt_neg_iff.1 (hneg ha hb hab)

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
    _ ≤ δ x * (a x * (g.inner x (X x) (X x) + ‖mgradient 𝓘(ℝ, E) f x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (min_inv_mul_sq_mul_add_le (ha₀ x)
        (g.toRiemannianMetric.inner_self_nonneg x (X x)) (by positivity)) hδx.le
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
    _ ≤ δ x * (b * (‖mgradient 𝓘(ℝ, E) f x‖ ^ 2 + g.inner x (X x) (X x))) :=
      mul_le_mul_of_nonneg_left (min_inv_mul_sq_mul_add_le hbx (by positivity)
        (g.toRiemannianMetric.inner_self_nonneg x (X x))) hδx.le
    _ ≤ b * mvfderiv 𝓘(ℝ, E) f x (X x) := by
      rw [mul_left_comm, add_comm (_ ^ 2)]
      exact mul_le_mul_of_nonneg_left (H x) hbx.le

/-- **Gradient-like fields pull back along local diffeomorphisms.** If `X` is gradient-like for
`f` on `M`, and `Φ : M' → M` is smooth with invertible differential at every point (for instance a
diffeomorphism), then the pulled-back field `VectorField.mpullback Φ X x = (dΦ_x)⁻¹ (X (Φ x))` is
gradient-like for `f ∘ Φ`. -/
theorem mpullback {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℝ, E') ∞ M']
    (hX : IsGradientLike f X) {Φ : M' → M} (hΦ : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ Φ)
    (hΦ' : ∀ x, (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) Φ x).IsInvertible) :
    IsGradientLike (f ∘ Φ) (VectorField.mpullback 𝓘(ℝ, E') 𝓘(ℝ, E) Φ X) := by
  have hX0 := fun y ↦ (hX.eq_zero_iff (x := y)).2
  obtain ⟨g, δ, hδc, hδ, h⟩ := hX
  have hΦ₁ : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E) (∞ + 1) Φ := by simpa using hΦ
  refine ⟨g.pullback Φ hΦ₁ fun x ↦ (hΦ' x).injective, δ ∘ Φ, hδc.comp hΦ.continuous,
    fun x ↦ hδ (Φ x), fun x ↦ ?_⟩
  let : RiemannianBundle (fun x : M' ↦ TangentSpace 𝓘(ℝ, E') x) :=
    ⟨(g.pullback Φ hΦ₁ fun x ↦ (hΦ' x).injective).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  have hiso := g.isLocalRiemannianIsometry_pullback_of_isInvertible hΦ₁ hΦ'
  by_cases hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (Φ x)
  · rw [ContMDiffRiemannianMetric.pullback_inner, hiso.mfderiv_apply_mpullback,
      hiso.norm_mgradient_comp hf, VectorField.mvfderiv_comp_apply_mpullback hf (hΦ' x)]
    exact h (Φ x)
  · -- Where `f` is not differentiable, `X` vanishes, and so does the pulled-back field; and
    -- `df` vanishes along `Φ` too, by the chain rule for the local diffeomorphism `Φ`.
    have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ Φ x :=
      isLocalDiffeomorph_of_mfderiv_eq hΦ (by simp) hΦ' x
    have hf0 := mfderiv_zero_of_not_mdifferentiableAt hf
    have hX0x : X (Φ x) = 0 := hX0 _ (mvfderiv_eq_zero_iff.2 hf0)
    have hD : mvfderiv 𝓘(ℝ, E') (f ∘ Φ) x = 0 := mvfderiv_eq_zero_iff.2 (by
      rw [hloc.mfderiv_comp (by simp), hf0, ContinuousLinearMap.zero_comp])
    simp [VectorField.mpullback_apply, hX0x, hD, mgradient_eq_zero_iff.2 hD]

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

section Local

/-- The inequality of `TauCeti.IsGradientLike` at `y`, with the constant `δ` and with a bilinear
form `s` on `T_y M` in place of the metric, put in a form that is convex in `s`: the bound
`‖grad f y‖ ^ 2 ≤ R` is replaced by `(df_y v) ^ 2 ≤ R * s v v` for all `v`. -/
private def gradientLikeCondition (f : M → ℝ) (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) (δ : ℝ)
    (y : M) : Set (TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) :=
  {s | (∀ v, 0 ≤ s v v) ∧ δ * s (X y) (X y) ≤ mvfderiv 𝓘(ℝ, E) f y (X y) ∧
    ∀ v, δ * mvfderiv 𝓘(ℝ, E) f y v ^ 2 ≤
      (mvfderiv 𝓘(ℝ, E) f y (X y) - δ * s (X y) (X y)) * s v v}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem convex_gradientLikeCondition (δ : ℝ) (y : M) :
    Convex ℝ (gradientLikeCondition f X δ y) := by
  rintro s ⟨hs₀, hs₁, hs₂⟩ t ⟨ht₀, ht₁, ht₂⟩ a b ha hb hab
  simp only [gradientLikeCondition, Set.mem_ofPred_eq, add_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  set D := mvfderiv 𝓘(ℝ, E) f y (X y)
  refine ⟨fun v ↦ by have := hs₀ v; have := ht₀ v; positivity, ?_, fun v ↦ ?_⟩
  · have hD : D = a * D + b * D := by rw [← add_mul, hab, one_mul]
    nlinarith
  -- With `pᵢ = D - δ sᵢ (X, X) ≥ 0` and `qᵢ = sᵢ (v, v) ≥ 0`, this is `convex_setOfPred_le_mul`.
  have hp : D - δ * (a * s (X y) (X y) + b * t (X y) (X y)) =
      a * (D - δ * s (X y) (X y)) + b * (D - δ * t (X y) (X y)) := by
    linear_combination (-D) * hab
  rw [hp]
  have := convex_setOfPred_le_mul (δ * mvfderiv 𝓘(ℝ, E) f y v ^ 2)
    (x := (D - δ * s (X y) (X y), s v v)) ⟨sub_nonneg.2 hs₁, hs₀ v, hs₂ v⟩
    (y := (D - δ * t (X y) (X y), t v v)) ⟨sub_nonneg.2 ht₁, ht₀ v, ht₂ v⟩ ha hb hab
  simpa only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] using this.2.2

/-- For a metric `g`, the condition `gradientLikeCondition` on `g` at `y` is the inequality of
`TauCeti.IsGradientLike` at `y`. -/
private theorem inner_mem_gradientLikeCondition_iff
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {δ : ℝ} (hδ : 0 ≤ δ) (y : M) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
    g.inner y ∈ gradientLikeCondition f X δ y ↔
      δ * (g.inner y (X y) (X y) + ‖mgradient 𝓘(ℝ, E) f y‖ ^ 2) ≤
        mvfderiv 𝓘(ℝ, E) f y (X y) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  set G := mgradient 𝓘(ℝ, E) f y
  have hG : g.inner y G G = ‖G‖ ^ 2 := (g.norm_sq y G).symm
  have hDG : mvfderiv 𝓘(ℝ, E) f y G = ‖G‖ ^ 2 := by
    rw [mvfderiv_apply_mgradient, real_inner_self_eq_norm_sq]
  constructor
  · rintro ⟨-, h₁, h₂⟩
    have h := h₂ G
    rw [hG, hDG] at h
    rcases (sq_nonneg ‖G‖).eq_or_lt with h0 | h0
    · rw [← h0]; linarith
    · have : δ * ‖G‖ ^ 2 ≤ mvfderiv 𝓘(ℝ, E) f y (X y) - δ * g.inner y (X y) (X y) :=
        le_of_mul_le_mul_right (by nlinarith) h0
      linarith
  · intro h
    refine ⟨fun v ↦ g.toRiemannianMetric.inner_self_nonneg y v,
      by nlinarith [sq_nonneg ‖G‖], fun v ↦ ?_⟩
    have hcs : mvfderiv 𝓘(ℝ, E) f y v ^ 2 ≤ ‖G‖ ^ 2 * g.inner y v v := by
      rw [← inner_mgradient, ← g.inner_eq, ← real_inner_self_eq_norm_sq, sq]
      exact real_inner_mul_inner_self_le G v
    have hvv : 0 ≤ g.inner y v v := g.toRiemannianMetric.inner_self_nonneg y v
    have hR : δ * ‖G‖ ^ 2 ≤ mvfderiv 𝓘(ℝ, E) f y (X y) - δ * g.inner y (X y) (X y) := by
      linarith
    calc δ * mvfderiv 𝓘(ℝ, E) f y v ^ 2 ≤ δ * ‖G‖ ^ 2 * g.inner y v v := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hcs hδ
      _ ≤ _ := mul_le_mul_of_nonneg_right hR hvv

/-- If the inequality of `TauCeti.IsGradientLike` holds at `y` for a metric `g` with a constant
`δ'`, then `g` satisfies `gradientLikeCondition` at `y` with any constant `δ ∈ [0, δ']`. -/
private theorem inner_mem_gradientLikeCondition_of_le
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδδ' : δ ≤ δ') {y : M}
    (h : letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
      δ' * (g.inner y (X y) (X y) + ‖mgradient 𝓘(ℝ, E) f y‖ ^ 2) ≤
        mvfderiv 𝓘(ℝ, E) f y (X y)) :
    g.inner y ∈ gradientLikeCondition f X δ y := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  refine (inner_mem_gradientLikeCondition_iff g hδ y).2
    ((mul_le_mul_of_nonneg_right hδδ' ?_).trans h)
  exact add_nonneg (g.toRiemannianMetric.inner_self_nonneg y (X y)) (sq_nonneg _)

/-- **Being gradient-like is a local condition.** On a σ-compact Hausdorff manifold, if each point
has a neighbourhood `U`, a smooth metric `g` and a constant `c > 0` such that
`c * (g y (X y) (X y) + ‖grad f y‖ ^ 2) ≤ df_y (X y)` for every `y ∈ U`, the gradient and its norm
being those of `g`, then `X` is gradient-like for `f`. -/
theorem isGradientLike_of_forall_exists_nhds [T2Space M] [SigmaCompactSpace M]
    (h : ∀ x : M, ∃ U ∈ 𝓝 x,
      ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
      ∃ c : ℝ, 0 < c ∧
        letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
        ∀ y ∈ U, c * (g.inner y (X y) (X y) + ‖mgradient 𝓘(ℝ, E) f y‖ ^ 2) ≤
          mvfderiv 𝓘(ℝ, E) f y (X y)) :
    IsGradientLike f X := by
  choose U hU g c hc hg using h
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  -- A locally finite open refinement `V` of the interiors of the sets `U x`.
  obtain ⟨V, hVo, hVcov, hVlf, hVU⟩ := precise_refinement (fun x ↦ interior (U x))
    (fun _ ↦ isOpen_interior)
    (iUnion_eq_univ_iff.2 fun x ↦ ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩)
  -- A continuous `δ > 0` with `δ ≤ c x` on `V x` for every `x`.
  obtain ⟨δ, hδ₀, hδc⟩ := hVlf.closure.exists_continuous_pos_lt (fun _ ↦ isClosed_closure)
    (ε := fun x _ ↦ c x) (fun _ ↦ continuousOn_const) fun x _ _ ↦ hc x
  have hδ (y : M) : 0 < δ y ∧ ∀ x, y ∈ V x → δ y ≤ c x :=
    ⟨hδ₀ y, fun x hy ↦ (hδc x y (subset_closure hy)).le⟩
  -- Glue the metrics `g x`, under the fibrewise condition with constant `δ`, which is convex.
  obtain ⟨G, hG⟩ := exists_contMDiffRiemannianMetric_inner_mem_of_local
    (IB := 𝓘(ℝ, E)) (n := ⊤) (F := E) (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
    (c := fun y ↦ gradientLikeCondition f X (δ y) y)
    (fun y ↦ convex_gradientLikeCondition (δ y) y) fun y₀ ↦ by
      obtain ⟨x, hx⟩ := mem_iUnion.1 (hVcov ▸ mem_univ y₀)
      refine ⟨V x, (hVo x).mem_nhds hx, (g x).inner, (g x).contMDiff.contMDiffOn,
        fun y hy ↦ ⟨⟨(g x).symm y, (g x).pos y⟩, inner_mem_gradientLikeCondition_of_le (g x)
          (hδ y).1.le ((hδ y).2 x hy) (hg x y (interior_subset (hVU x hy)))⟩⟩
  exact ⟨G, δ, δ.continuous, fun y ↦ (hδ y).1,
    fun y ↦ (inner_mem_gradientLikeCondition_iff G (hδ y).1.le y).1 (hG y)⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The condition `gradientLikeCondition` is carried back along a linear map `L : T_x M → T_y M'`
that sends `X x` to `X' y` and through which `df_x` factors as `df'_y ∘ L`. -/
private theorem pullback_mem_gradientLikeCondition {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M']
    {f' : M' → ℝ} {X' : (y : M') → TangentSpace 𝓘(ℝ, E') y} {δ : ℝ} {x : M} {y : M'}
    (L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E') y)
    {t : TangentSpace 𝓘(ℝ, E') y →L[ℝ] TangentSpace 𝓘(ℝ, E') y →L[ℝ] ℝ}
    (ht : t ∈ gradientLikeCondition f' X' δ y) (hLX : L (X x) = X' y)
    (hdf : ∀ v, mvfderiv 𝓘(ℝ, E) f x v = mvfderiv 𝓘(ℝ, E') f' y (L v)) :
    (ContinuousLinearMap.precomp ℝ L).comp (t.comp L) ∈ gradientLikeCondition f X δ x := by
  obtain ⟨h₀, h₁, h₂⟩ := ht
  refine ⟨fun v ↦ ?_, ?_, fun v ↦ ?_⟩ <;>
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.precomp_apply, hdf, hLX]
  · exact h₀ (L v)
  · exact h₁
  · exact h₂ (L v)

/-- **The local criterion through a local diffeomorphism.** Let `X'` be gradient-like for `f'` on
`M'`, and let `Φ : M' → M` be a smooth local diffeomorphism at `y` such that `f ∘ Φ = f'` near `y`
and `dΦ_{y'} (X' y') = X (Φ y')` for `y'` near `y`. Then `Φ y` has a neighbourhood `U`, with a
smooth metric `g` on `M` and a constant `c > 0`, such that
`c * (g x (X x) (X x) + ‖grad f x‖ ^ 2) ≤ df_x (X x)` for every `x ∈ U`, the gradient and its norm
being those of `g`: this is the local hypothesis of `TauCeti.isGradientLike_of_forall_exists_nhds`
at `Φ y`. -/
theorem IsGradientLike.exists_nhds_mul_le_of_isLocalDiffeomorphAt [T2Space M]
    [SigmaCompactSpace M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M']
    [IsManifold 𝓘(ℝ, E') ∞ M'] {f' : M' → ℝ} {X' : (y : M') → TangentSpace 𝓘(ℝ, E') y}
    (hX' : IsGradientLike f' X') {Φ : M' → M} {y : M'}
    (hΦ : IsLocalDiffeomorphAt 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ Φ y) (hf : f ∘ Φ =ᶠ[𝓝 y] f')
    (hX : ∀ᶠ y' in 𝓝 y, mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) Φ y' (X' y') = X (Φ y')) :
    ∃ U ∈ 𝓝 (Φ y),
      ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
      ∃ c : ℝ, 0 < c ∧
        letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
        ∀ x ∈ U, c * (g.inner x (X x) (X x) + ‖mgradient 𝓘(ℝ, E) f x‖ ^ 2) ≤
          mvfderiv 𝓘(ℝ, E) f x (X x) := by
  obtain ⟨g', δ', hδ'c, hδ', hg'⟩ := hX'
  set Ψ := hΦ.localInverse
  set c := δ' y / 2
  have hc : 0 < c := half_pos (hδ' y)
  have hΨy : Ψ (Φ y) = y := hΦ.localInverse_left_inv hΦ.localInverse_mem_target
  -- The conditions that hold near `y`, read near `Φ y` through the local inverse `Ψ`.
  have hev : ∀ᶠ y' in 𝓝 y, IsLocalDiffeomorphAt 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ Φ y' ∧ c < δ' y' ∧
      f ∘ Φ =ᶠ[𝓝 y'] f' ∧ mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) Φ y' (X' y') = X (Φ y') :=
    hΦ.eventually.and ((hδ'c.continuousAt.eventually (lt_mem_nhds (half_lt_self (hδ' y)))).and
      (hf.eventuallyEq_nhds.and hX))
  obtain ⟨V, hVP, hVo, hyV⟩ := eventually_nhds_iff.1 <| Filter.Eventually.and
    (p := (· ∈ Ψ.source)) (hΦ.localInverse_open_source.mem_nhds hΦ.localInverse_mem_source)
    (hΦ.continuousAt_localInverse.eventually (by rwa [hΨy]) : ∀ᶠ x in 𝓝 (Φ y), _)
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  obtain ⟨K, hK, hKc, hKV⟩ := exists_mem_nhds_isClosed_subset (hVo.mem_nhds hyV)
  obtain ⟨g₀⟩ := nonempty_contMDiffRiemannianMetric (IB := 𝓘(ℝ, E)) (n := ⊤) (F := E)
    (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
  -- On `K`, glue under the fibrewise condition with constant `c`; elsewhere, impose nothing.
  obtain ⟨G, hG⟩ := exists_contMDiffRiemannianMetric_inner_mem_of_local
    (IB := 𝓘(ℝ, E)) (n := ⊤) (F := E) (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
    (c := fun x ↦ {s | x ∈ K → s ∈ gradientLikeCondition f X c x})
    (fun x ↦ by
      by_cases hx : x ∈ K
      · simpa [hx] using convex_gradientLikeCondition c x
      · simpa [hx] using convex_univ) fun x₀ ↦ by
      by_cases hx₀ : x₀ ∈ K
      swap
      · exact ⟨Kᶜ, hKc.isOpen_compl.mem_nhds hx₀, g₀.inner, g₀.contMDiff.contMDiffOn,
          fun b hb ↦ ⟨⟨g₀.symm b, g₀.pos b⟩, fun h ↦ (hb h).elim⟩⟩
      -- Near `K`, the metric `g'` pushed forward along `Φ`, that is pulled back along `Ψ`.
      refine ⟨V, hVo.mem_nhds (hKV hx₀), _, (Ψ.contMDiffOn_pullback g' (by simp)).mono
        fun b hb ↦ (hVP b hb).1, fun b hb ↦ ?_⟩
      obtain ⟨hbs, hloc, hcb, hfb, hXb⟩ := hVP b hb
      have hΦΨ : Φ (Ψ b) = b := hΦ.localInverse_right_inv hbs
      have hinv (w : TangentSpace 𝓘(ℝ, E) b) :
          mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) Φ (Ψ b) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') Ψ b w) = w :=
        hΦ.mfderiv_apply_mfderiv_localInverse_apply (by simp) hbs w
      refine ⟨⟨fun v w ↦ by simp [g'.symm], fun v hv ↦
        Ψ.pullback_apply_self_pos g' (by simp) hbs hv⟩, fun _ ↦ ?_⟩
      refine pullback_mem_gradientLikeCondition _
        (inner_mem_gradientLikeCondition_of_le g' hc.le hcb.le (hg' (Ψ b))) ?_ fun v ↦ ?_
      · exact (hloc.isInvertible_mfderiv (by simp)).injective (by rw [hinv, hXb, hΦΨ])
      · rw [← hfb.mvfderiv_eq, mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply,
          hloc.mfderiv_comp (by simp), ContinuousLinearMap.comp_apply, hinv, hΦΨ]
  exact ⟨K, hK, G, c, hc, fun x hx ↦
    (inner_mem_gradientLikeCondition_iff G hc.le x).1 (hG x hx)⟩

/-- Near a point `x` with `df_x (X x) > 0`, the inequality of `TauCeti.IsGradientLike` holds for
every smooth metric `g` with some constant `c > 0`, when `f` is `C¹` at `x` and `X` is continuous
at `x`. With `TauCeti.isGradientLike_of_forall_exists_nhds`, this leaves only the critical points
of `f` to check. -/
theorem exists_nhds_mul_le_of_mvfderiv_apply_pos
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) {x : M}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 1 f x)
    (hX : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 0 (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)) x)
    (hx : 0 < mvfderiv 𝓘(ℝ, E) f x (X x)) :
    ∃ U ∈ 𝓝 x, ∃ c : ℝ, 0 < c ∧
      letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
      ∀ y ∈ U, c * (g.inner y (X y) (X y) + ‖mgradient 𝓘(ℝ, E) f y‖ ^ 2) ≤
        mvfderiv 𝓘(ℝ, E) f y (X y) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  have : IsManifold 𝓘(ℝ, E) (0 + 1) M := by rw [zero_add]; infer_instance
  have hgrad : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 0
      (fun y ↦ (⟨y, mgradient 𝓘(ℝ, E) f y⟩ : TangentBundle 𝓘(ℝ, E) M)) x :=
    contMDiffAt_mgradient (n := 0) (by rwa [zero_add])
  have hG := hgrad.continuousAt
  have hX' := hX.continuousAt
  have hXX : ContinuousAt (fun y ↦ g.inner y (X y) (X y)) x :=
    g.toContinuousRiemannianMetric.continuousAt_inner (b := id) hX' hX'
  have hGG : ContinuousAt
      (fun y ↦ g.inner y (mgradient 𝓘(ℝ, E) f y) (mgradient 𝓘(ℝ, E) f y)) x :=
    g.toContinuousRiemannianMetric.continuousAt_inner (b := id) hG hG
  have hP : ContinuousAt (fun y ↦ mvfderiv 𝓘(ℝ, E) f y (X y)) x :=
    (ContMDiffAt.comp (g := fun q : TangentBundle 𝓘(ℝ, E) M ↦ mvfderiv 𝓘(ℝ, E) f q.proj q.snd) x
      (ContMDiffAt.contMDiffAt_mvfderiv_apply (p := (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M))
        (m := 0) hf le_rfl) hX).continuousAt
  have hQ : ContinuousAt
      (fun y ↦ g.inner y (X y) (X y) + ‖mgradient 𝓘(ℝ, E) f y‖ ^ 2) x :=
    (hXX.add hGG).congr (Filter.Eventually.of_forall fun y ↦ by
      dsimp only [Pi.add_apply]; rw [g.norm_sq])
  set P₀ := mvfderiv 𝓘(ℝ, E) f x (X x)
  set Q₀ := g.inner x (X x) (X x) + ‖mgradient 𝓘(ℝ, E) f x‖ ^ 2
  have hQ₀ : 0 ≤ Q₀ :=
    add_nonneg (g.toRiemannianMetric.inner_self_nonneg x (X x)) (sq_nonneg _)
  refine ⟨_, Filter.inter_mem (hP.eventually (lt_mem_nhds (half_lt_self hx)))
    (hQ.eventually (gt_mem_nhds (lt_add_one Q₀))), P₀ / (2 * (Q₀ + 1)), by positivity,
    fun y ⟨hPy, hQy⟩ ↦ ?_⟩
  calc P₀ / (2 * (Q₀ + 1)) * (g.inner y (X y) (X y) + ‖mgradient 𝓘(ℝ, E) f y‖ ^ 2)
      ≤ P₀ / (2 * (Q₀ + 1)) * (Q₀ + 1) :=
        mul_le_mul_of_nonneg_left (le_of_lt hQy) (by positivity)
    _ = P₀ / 2 := by field_simp
    _ ≤ mvfderiv 𝓘(ℝ, E) f y (X y) := le_of_lt hPy

end Local

end TauCeti

end
