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
public import TauCeti.Dynamics.Flow.Stable
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Topology.LocallyFinite.Basic
import TauCeti.Analysis.RCLike.SesquilinearForm
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
import TauCeti.Topology.VectorBundle.Riemannian.Comparison
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Topology.OmegaLimit
import SymplecticGeometry.Geometry.Manifold.Riemannian.NormedSpace
import SymplecticGeometry.Algebra.Order.Field.Basic
import SymplecticGeometry.Dynamics.Flow.OmegaLimit
import SymplecticGeometry.Analysis.Convex.Mul
import SymplecticGeometry.Geometry.Manifold.Riemannian.PullbackPartialDiffeomorph
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Riemannian.Existence
import SymplecticGeometry.Geometry.Manifold.VectorField.Pullback
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic

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
* `TauCeti.IsGradientLike.mvfderiv_apply_pos_of_criticalPoints_inter_preimage_eq_empty`:
  `df(X) > 0` at the points of `f⁻¹(s)`, for any set `s` of values such that `f` has no critical
  point in `f⁻¹(s)`.
* `TauCeti.IsGradientLike.mvfderiv_apply_pos_of_isRegularValue`: `df(X) > 0` on the level
  `f⁻¹(c)` of a regular value `c`;
  `TauCeti.IsGradientLike.mvfderiv_apply_pos_of_criticalPoints_inter_preimage_Ico_eq_empty`: the
  same on the level `f⁻¹(a)` when `f` has no critical point in a band `f⁻¹([a, c))` with `a < c`.
* `TauCeti.IsGradientLike.eq_zero_iff`: `X x = 0` exactly when `x` is a critical point of `f`.
  This holds already where the inequality holds at the point itself
  (`TauCeti.eq_zero_iff_mem_criticalPoints_of_mul_le`), and near a point where `X` is
  gradient-like (`TauCeti.IsGradientLikeAt.eq_zero_iff`).
* `TauCeti.IsGradientLike.strictMonoOn_comp`, `TauCeti.IsGradientLike.strictMono_comp`: `f`
  increases strictly along an integral curve of `X`, on a convex set of times or on all of `ℝ`,
  that meets no critical point.
* `TauCeti.IsGradientLike.mvfderiv_apply_nonneg` and `TauCeti.IsGradientLike.monotone_comp`:
  `df(X) ≥ 0` everywhere, so `f` is monotone along every integral curve of `X` along which it is
  differentiable.
* `TauCeti.IsGradientLike.smul`: `a • X` is gradient-like for a continuous positive `a`.
* `TauCeti.IsGradientLike.comp`: `X` is gradient-like for `h ∘ f` when `h` is `C¹` with `h' > 0`.
* `TauCeti.IsGradientLike.mpullback`: the pull-back `VectorField.mpullback Φ X` of a gradient-like
  field along a smooth map `Φ` with invertible differential, such as a diffeomorphism, is
  gradient-like for `f ∘ Φ`.
* `TauCeti.isGradientLike_mgradient`: the gradient of `f` for any smooth metric is gradient-like
  for `f`, with `δ = 1 / 2`.
* `TauCeti.isGradientLike_of_mul_le`: on a finite-dimensional normed space, a constant `c > 0`
  with `c (‖X‖² + ‖df‖²) ≤ df(X)` everywhere suffices, for the metric
  `SymplecticGeometry.riemannianMetricToEuclidean` carried over by `toEuclidean`.
* `TauCeti.IsGradientLikeAt f X x`: `X` is gradient-like for `f` near `x`, that is, the inequality
  holds on a neighbourhood of `x` for some metric and some constant `c > 0`; with
  `TauCeti.isGradientLikeAt_def`.
* `TauCeti.isGradientLike_of_forall_isGradientLikeAt` and
  `TauCeti.IsGradientLike.isGradientLikeAt`: on a σ-compact Hausdorff manifold the condition is
  local, `TauCeti.isGradientLike_iff_forall_isGradientLikeAt`.
* `TauCeti.IsGradientLikeAt.one_sub_smul_add_smul` and
  `TauCeti.IsGradientLike.one_sub_smul_add_smul`: for a fixed field, the condition is convex in
  the function, near a point for differentiable functions, and globally.
* `TauCeti.IsGradientLikeAt.one_sub_smul_add_smul_right` and
  `TauCeti.IsGradientLike.one_sub_smul_add_smul_right`: for a fixed function, the condition is
  convex in the field, near a point and globally. Near a point, one metric and one constant serve
  for the whole segment (`TauCeti.IsGradientLikeAt.exists_forall_one_sub_smul_add_smul_right`).
* `TauCeti.exists_nhds_mul_le_of_mvfderiv_apply_pos`: near a point where `df(X) > 0`, the
  inequality holds for every metric and a small constant, when `f` is `C¹` and `X` continuous.
  Hence `TauCeti.isGradientLikeAt_of_mvfderiv_apply_pos`: on a σ-compact Hausdorff manifold, `X`
  is gradient-like for `f` near such a point.
* `TauCeti.IsGradientLike.isGradientLikeAt_of_isLocalDiffeomorphAt`: `X` is gradient-like for `f`
  near `Φ y` when, near `y`, a local diffeomorphism `Φ` carries a gradient-like field for `f'` to
  `X` and `f ∘ Φ = f'`.
* `TauCeti.IsGradientLike.mem_criticalPoints_of_mapClusterPt_atTop` and
  `TauCeti.IsGradientLike.mem_criticalPoints_of_mapClusterPt_atBot`: for a flow `Φ` whose orbits
  are integral curves of `X`, the cluster points of an orbit at `+∞` and at `-∞` are critical
  points of `f`.
* `TauCeti.IsGradientLike.exists_flow_apply_le_or_mapClusterPt_atBot`: when `f ⁻¹' Icc a b` is
  compact, the backward orbit of a point of `{f ≤ b}` either reaches `{f ≤ a}` or clusters at
  `-∞`, only at critical points in `f ⁻¹' Icc a b`.
* `TauCeti.IsGradientLike.exists_mapClusterPt_atTop_of_isCompact` and
  `TauCeti.IsGradientLike.exists_mem_stableSet_of_isCompact`: a forward orbit from `{a ≤ f}` that
  stays in `{f ≤ b}` clusters at `+∞`, only at critical points in `f ⁻¹' Icc a b`, and lies in
  the stable set of one of them when they are finitely many.

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

For convex combinations of functions, the metric of `f₁` serves for both functions: on a compact
neighbourhood the metric of `f₂` lies between two positive multiples of it, by Tau Ceti's
`Bundle.ContinuousRiemannianMetric.exists_mul_inner_le_inner_and_inner_le_mul_inner`, which costs
only a smaller constant. For one metric and one constant, the fibrewise condition above is convex
in the differential of the function, since the square is convex. For convex combinations of
fields the same comparison of metrics applies, and the fibrewise condition is convex in the field,
since `df` is linear in it and `v ↦ g(v, v)` is convex.

For `IsGradientLike.isGradientLikeAt_of_isLocalDiffeomorphAt`, the metric near `Φ y` is the
metric of the field on `M'` pulled back along the local inverse `Ψ` of `Φ`, which is smooth and
positive definite on the source of `Ψ` (`PartialDiffeomorph.contMDiffOn_pullback`,
`PartialDiffeomorph.pullback_apply_self_pos`). The fibrewise condition with
a constant `c` is carried along `dΨ` from `M'` to `M`. It is imposed only on a closed
neighbourhood `K` of `Φ y`, and the gluing by
`TauCeti.exists_contMDiffRiemannianMetric_inner_mem_of_local` uses any metric off `K` (Tau Ceti's
`TauCeti.nonempty_contMDiffRiemannianMetric`).

The limit points of the flow are treated for any flow `Φ : Flow ℝ M` whose orbits are integral
curves of `X`, such as Tau Ceti's `TauCeti.globalFlow` of a complete field, without any symplectic
structure. Since `f` increases along the orbits, `-f` is a Lyapunov function, so it is constant
along the orbit of a cluster point, by Tau Ceti's `Flow.apply_flow_eq_of_mapClusterPt_of_antitone`
in forward time and the library's `Flow.apply_flow_eq_of_mapClusterPt_atBot_of_antitone` in
backward time; then `df(X) = 0` there, which makes the point critical. This follows the proof of
the library's `TauCeti.mvfderiv_eq_zero_of_mapClusterPt_atBot_globalFlow`
(`Morse/Core/Compression.lean`). The convergence of a forward orbit with finitely many cluster
points is Tau Ceti's `TauCeti.exists_tendsto_atTop_of_setOf_mapClusterPt_subset`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §9.3 (the gradient-like condition (9.9)), and the proof of Lemma 12.9 (convex combinations of
  fields)
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.1.6.
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

/-- If `c * (g (X p) (X p) + ‖grad f p‖ ^ 2) ≤ df_p (X p)` at a point `p`, for a Riemannian metric
`g` and a constant `c > 0`, the gradient and its norm being those of `g`, then `X p = 0` exactly
when `p` is a critical point of `f`. -/
theorem eq_zero_iff_mem_criticalPoints_of_mul_le
    (g : RiemannianMetric (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) {c : ℝ} (hc : 0 < c) {p : M}
    (h : letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g⟩
      c * (g.inner p (X p) (X p) + ‖mgradient 𝓘(ℝ, E) f p‖ ^ 2) ≤ mvfderiv 𝓘(ℝ, E) f p (X p)) :
    X p = 0 ↔ p ∈ criticalPoints 𝓘(ℝ, E) f := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g⟩
  rw [mem_criticalPoints]
  constructor
  · intro h0
    simp only [h0, map_zero, zero_add] at h
    rw [← mgradient_eq_zero_iff (I := 𝓘(ℝ, E)), ← norm_eq_zero]
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 <|
      le_antisymm (nonpos_of_mul_nonpos_right h hc) (sq_nonneg _)
  · intro h0
    rw [h0, zero_apply] at h
    by_contra hne
    have := g.pos p (X p) hne
    nlinarith [sq_nonneg ‖mgradient 𝓘(ℝ, E) f p‖]

namespace IsGradientLike

/-- A gradient-like field increases `f` strictly at every point that is not critical for `f`. -/
theorem mvfderiv_apply_pos (hX : IsGradientLike f X) {x : M}
    (hx : x ∉ criticalPoints 𝓘(ℝ, E) f) : 0 < mvfderiv 𝓘(ℝ, E) f x (X x) := by
  obtain ⟨g, δ, -, hδ, h⟩ := hX
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  have hgrad : 0 < ‖mgradient 𝓘(ℝ, E) f x‖ :=
    norm_pos_iff.2 (by rwa [ne_eq, mgradient_eq_zero_iff, ← mem_criticalPoints])
  have : 0 ≤ g.inner x (X x) (X x) := g.toRiemannianMetric.inner_self_nonneg x (X x)
  exact lt_of_lt_of_le (by have := hδ x; positivity) (h x)

/-- A gradient-like field does not decrease `f`: `df(X) ≥ 0` at every point. -/
theorem mvfderiv_apply_nonneg (hX : IsGradientLike f X) (x : M) :
    0 ≤ mvfderiv 𝓘(ℝ, E) f x (X x) := by
  by_cases hx : x ∈ criticalPoints 𝓘(ℝ, E) f
  · simp [mem_criticalPoints.1 hx]
  · exact (hX.mvfderiv_apply_pos hx).le

/-- A gradient-like field increases `f` strictly at every point of the level `f⁻¹(c)` of a
regular value `c` of `f`. -/
theorem mvfderiv_apply_pos_of_isRegularValue (hX : IsGradientLike f X) {c : ℝ}
    (hc : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f c) {x : M} (hx : f x = c) :
    0 < mvfderiv 𝓘(ℝ, E) f x (X x) :=
  hX.mvfderiv_apply_pos (isRegularPoint_iff_notMem_criticalPoints.1 (hc.isRegularPoint hx))

/-- A gradient-like field increases `f` strictly at every point `x` with `f x ∈ s`, if `f` has
no critical point in `f⁻¹(s)`. -/
theorem mvfderiv_apply_pos_of_criticalPoints_inter_preimage_eq_empty
    (hX : IsGradientLike f X) {s : Set ℝ} (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' s = ∅)
    {x : M} (hx : f x ∈ s) : 0 < mvfderiv 𝓘(ℝ, E) f x (X x) :=
  hX.mvfderiv_apply_pos fun h ↦ eq_empty_iff_forall_notMem.1 hc x ⟨h, hx⟩

/-- A gradient-like field increases `f` strictly at every point of the level `f⁻¹(a)`, if `a < c`
and `f` has no critical point in the band `f⁻¹([a, c))`. -/
theorem mvfderiv_apply_pos_of_criticalPoints_inter_preimage_Ico_eq_empty
    (hX : IsGradientLike f X) {a c : ℝ} (hac : a < c)
    (hc : criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Ico a c = ∅) {x : M} (hx : f x = a) :
    0 < mvfderiv 𝓘(ℝ, E) f x (X x) :=
  hX.mvfderiv_apply_pos_of_criticalPoints_inter_preimage_eq_empty hc ⟨hx.ge, hx.trans_lt hac⟩

/-- The zeros of a gradient-like field are exactly the critical points of the function. -/
theorem eq_zero_iff (hX : IsGradientLike f X) {x : M} :
    X x = 0 ↔ x ∈ criticalPoints 𝓘(ℝ, E) f := by
  obtain ⟨g, δ, -, hδ, h⟩ := hX
  exact eq_zero_iff_mem_criticalPoints_of_mul_le g.toRiemannianMetric (hδ x) (h x)

/-- Along an integral curve of a gradient-like field on a convex set `s` of times that meets no
critical point of `f`, the function `f` is strictly increasing on `s`. -/
theorem strictMonoOn_comp (hX : IsGradientLike f X) {γ : ℝ → M} {s : Set ℝ} (hs : Convex ℝ s)
    (hγ : IsMIntegralCurveOn γ X s) (hcrit : ∀ t ∈ s, γ t ∉ criticalPoints 𝓘(ℝ, E) f) :
    StrictMonoOn (f ∘ γ) s := by
  have hf : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (γ t) := fun t ht ↦ by
    by_contra hnd
    exact hcrit t ht (mem_criticalPoints_iff_mfderiv_eq_zero.2
      (mfderiv_zero_of_not_mdifferentiableAt hnd))
  -- Tau Ceti states the decreasing case; apply it to `-f`.
  have hneg := hγ.strictAntiOn_comp (f := -f) hs (fun t ht ↦ (hf t ht).neg) fun t ht ↦ by
    rw [mvfderiv_neg, neg_apply, neg_lt_zero]
    exact hX.mvfderiv_apply_pos (hcrit t (interior_subset ht))
  exact fun a ha b hb hab ↦ neg_lt_neg_iff.1 (hneg ha hb hab)

/-- Along an integral curve of a gradient-like field that meets no critical point of `f`, the
function `f` is strictly increasing. -/
theorem strictMono_comp (hX : IsGradientLike f X) {γ : ℝ → M} (hγ : IsMIntegralCurve γ X)
    (hcrit : ∀ t, γ t ∉ criticalPoints 𝓘(ℝ, E) f) : StrictMono (f ∘ γ) :=
  strictMonoOn_univ.1 <| hX.strictMonoOn_comp convex_univ (hγ.isMIntegralCurveOn univ)
    fun t _ ↦ hcrit t

/-- Along an integral curve of a gradient-like field, if `f` is differentiable at each point of
the curve, then `f` is monotone along it. -/
theorem monotone_comp (hX : IsGradientLike f X) {γ : ℝ → M} (hγ : IsMIntegralCurve γ X)
    (hf : ∀ t, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (γ t)) : Monotone (f ∘ γ) := by
  -- Tau Ceti states the decreasing case; apply it to `-f`.
  have hneg := hγ.antitone_comp (f := -f) (fun t ↦ (hf t).neg) fun t ↦ by
    rw [mvfderiv_neg, neg_apply, neg_nonpos]
    exact hX.mvfderiv_apply_nonneg (γ t)
  exact fun a b hab ↦ neg_le_neg_iff.1 (hneg hab)

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
    have hX0x : X (Φ x) = 0 := hX0 _ (mem_criticalPoints_iff_mfderiv_eq_zero.2 hf0)
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

/-- **A global criterion on a normed space.** On a finite-dimensional real normed space `E`, a
field `X` is gradient-like for `f` if `c * (‖X x‖ ^ 2 + ‖df_x‖ ^ 2) ≤ df_x (X x)` for a constant
`c > 0` and every `x`, the norms being those of `E` and the operator norm. -/
theorem isGradientLike_of_mul_le {f : E → ℝ} {X : E → E} {c : ℝ} (hc : 0 < c)
    (h : ∀ x, c * (‖X x‖ ^ 2 + ‖fderiv ℝ f x‖ ^ 2) ≤ fderiv ℝ f x (X x)) :
    IsGradientLike f (fun x ↦ X x : (x : E) → TangentSpace 𝓘(ℝ, E) x) := by
  -- The metric is the Euclidean one carried over by `toEuclidean`.
  set e := toEuclidean (E := E)
  set g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E)) :=
    (riemannianMetricToEuclidean E).ofLE le_top
  have hg (x : E) (v w : TangentSpace 𝓘(ℝ, E) x) : g.inner x v w = inner ℝ (e v) (e w) := by
    rw [ContMDiffRiemannianMetric.ofLE_inner]
    exact riemannianMetricToEuclidean_inner x v w
  obtain ⟨L, hL⟩ : ∃ L, ∀ v, ‖e v‖ ≤ L * ‖v‖ :=
    ⟨_, e.toContinuousLinearMap.le_opNorm⟩
  obtain ⟨K, hK0, hK⟩ : ∃ K, 0 ≤ K ∧ ∀ v, ‖v‖ ≤ K * ‖e v‖ :=
    ⟨_, norm_nonneg _, fun v ↦ by simpa using e.symm.toContinuousLinearMap.le_opNorm (e v)⟩
  refine ⟨g, fun _ ↦ c / (L ^ 2 + K ^ 2 + 1), continuous_const, fun _ ↦ by positivity,
    fun x ↦ ?_⟩
  let : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  set G := mgradient 𝓘(ℝ, E) f x
  set D := fderiv ℝ f x
  have hD (v : E) : mvfderiv 𝓘(ℝ, E) f x v = D v := mvfderiv_eq_fderiv_apply f x v
  have hGG : ‖G‖ ^ 2 = ‖e G‖ ^ 2 := by
    rw [g.norm_sq, hg, real_inner_self_eq_norm_sq]
  have hGD : ‖G‖ ^ 2 = D G :=
    ((mvfderiv_apply_mgradient (I := 𝓘(ℝ, E))).trans (real_inner_self_eq_norm_sq _)).symm.trans
      (hD G)
  -- The norm of the gradient is bounded by that of `df`, as `‖G‖² = df(G) ≤ ‖df‖ ‖G‖`.
  have hbound (v : E) (hv : ‖e v‖ ^ 2 = D v) : ‖e v‖ ^ 2 ≤ K ^ 2 * ‖D‖ ^ 2 := by
    have h1 : ‖e v‖ ^ 2 ≤ ‖D‖ * K * ‖e v‖ := by
      rw [hv]
      calc D v ≤ ‖D‖ * ‖v‖ := (le_abs_self _).trans (D.le_opNorm v)
        _ ≤ ‖D‖ * (K * ‖e v‖) := mul_le_mul_of_nonneg_left (hK v) (norm_nonneg _)
        _ = _ := by ring
    have h2 : ‖e v‖ ≤ ‖D‖ * K := by
      rcases (norm_nonneg (e v)).eq_or_lt with h0 | h0
      · rw [← h0]; positivity
      · nlinarith
    have := norm_nonneg (e v)
    nlinarith
  have hG : ‖e G‖ ^ 2 ≤ K ^ 2 * ‖D‖ ^ 2 := hbound G (hGG.symm.trans hGD)
  have hX : g.inner x (X x) (X x) ≤ L ^ 2 * ‖X x‖ ^ 2 := by
    rw [hg x (X x) (X x), real_inner_self_eq_norm_sq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hL _) 2
  rw [hGG, hD]
  calc c / (L ^ 2 + K ^ 2 + 1) * (g.inner x (X x) (X x) + ‖e G‖ ^ 2)
      ≤ c / (L ^ 2 + K ^ 2 + 1) * ((L ^ 2 + K ^ 2 + 1) * (‖X x‖ ^ 2 + ‖D‖ ^ 2)) := by
        gcongr
        nlinarith [sq_nonneg ‖X x‖, sq_nonneg ‖D‖, sq_nonneg L, sq_nonneg K]
    _ = c * (‖X x‖ ^ 2 + ‖D‖ ^ 2) := by field_simp
    _ ≤ D (X x) := h x

section Local

/-- A vector field `X` is **gradient-like for `f` near `x`** when `x` has a neighbourhood `U`, with
a smooth Riemannian metric `g` and a constant `c > 0`, such that
`c * (g y (X y) (X y) + ‖grad f y‖ ^ 2) ≤ df_y (X y)` for every `y ∈ U`, the gradient and its norm
being those of `g`. On a σ-compact Hausdorff manifold, `X` is gradient-like for `f` exactly when
this holds at every point (`TauCeti.isGradientLike_iff_forall_isGradientLikeAt`). -/
def IsGradientLikeAt (f : M → ℝ) (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : M) : Prop :=
  ∃ U ∈ 𝓝 x,
    ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
    ∃ c : ℝ, 0 < c ∧
      letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
      ∀ y ∈ U, c * (g.inner y (X y) (X y) + ‖mgradient 𝓘(ℝ, E) f y‖ ^ 2) ≤
        mvfderiv 𝓘(ℝ, E) f y (X y)

/-- The definition of `TauCeti.IsGradientLikeAt`, unfolded. -/
theorem isGradientLikeAt_def (f : M → ℝ) (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : M) :
    IsGradientLikeAt f X x ↔ ∃ U ∈ 𝓝 x,
      ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
      ∃ c : ℝ, 0 < c ∧
        letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
        ∀ y ∈ U, c * (g.inner y (X y) (X y) + ‖mgradient 𝓘(ℝ, E) f y‖ ^ 2) ≤
          mvfderiv 𝓘(ℝ, E) f y (X y) :=
  Iff.rfl

/-- If `X` is gradient-like for `f` near `x`, then `X x = 0` exactly when `x` is a critical point
of `f`. -/
theorem IsGradientLikeAt.eq_zero_iff {x : M} (h : IsGradientLikeAt f X x) :
    X x = 0 ↔ x ∈ criticalPoints 𝓘(ℝ, E) f := by
  obtain ⟨U, hU, g, c, hc, hg⟩ := (isGradientLikeAt_def f X x).1 h
  exact eq_zero_iff_mem_criticalPoints_of_mul_le g.toRiemannianMetric hc
    (hg x (mem_of_mem_nhds hU))

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

/-- **Being gradient-like is a local condition.** On a σ-compact Hausdorff manifold, if `X` is
gradient-like for `f` near every point, then `X` is gradient-like for `f`. -/
theorem isGradientLike_of_forall_isGradientLikeAt [T2Space M] [SigmaCompactSpace M]
    (h : ∀ x : M, IsGradientLikeAt f X x) : IsGradientLike f X := by
  choose U hU g c hc hg using fun x ↦ (isGradientLikeAt_def f X x).1 (h x)
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
and `dΦ_{y'} (X' y') = X (Φ y')` for `y'` near `y`. Then `X` is gradient-like for `f` near
`Φ y`. -/
theorem IsGradientLike.isGradientLikeAt_of_isLocalDiffeomorphAt [T2Space M]
    [SigmaCompactSpace M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] {M' : Type*} [TopologicalSpace M'] [ChartedSpace E' M']
    [IsManifold 𝓘(ℝ, E') ∞ M'] {f' : M' → ℝ} {X' : (y : M') → TangentSpace 𝓘(ℝ, E') y}
    (hX' : IsGradientLike f' X') {Φ : M' → M} {y : M'}
    (hΦ : IsLocalDiffeomorphAt 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ Φ y) (hf : f ∘ Φ =ᶠ[𝓝 y] f')
    (hX : ∀ᶠ y' in 𝓝 y, mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) Φ y' (X' y') = X (Φ y')) :
    IsGradientLikeAt f X (Φ y) := by
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
  exact (isGradientLikeAt_def f X (Φ y)).2 ⟨K, hK, G, c, hc, fun x hx ↦
    (inner_mem_gradientLikeCondition_iff G hc.le x).1 (hG x hx)⟩

/-- Near a point `x` with `df_x (X x) > 0`, the inequality of `TauCeti.IsGradientLike` holds for
every smooth metric `g` with some constant `c > 0`, when `f` is `C¹` at `x` and `X` is continuous
at `x`. -/
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

/-- On a σ-compact Hausdorff manifold, `X` is gradient-like for `f` near every point `x` with
`df_x (X x) > 0`, when `f` is `C¹` at `x` and `X` is continuous at `x`. With
`TauCeti.isGradientLike_of_forall_isGradientLikeAt`, this leaves only the critical points of `f`
to check. -/
theorem isGradientLikeAt_of_mvfderiv_apply_pos [T2Space M] [SigmaCompactSpace M] {x : M}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 1 f x)
    (hX : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 0 (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, E) M)) x)
    (hx : 0 < mvfderiv 𝓘(ℝ, E) f x (X x)) : IsGradientLikeAt f X x := by
  obtain ⟨g⟩ : Nonempty
      (ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) :=
    nonempty_contMDiffRiemannianMetric
  obtain ⟨U, hU, c, hc, h⟩ := exists_nhds_mul_le_of_mvfderiv_apply_pos g hf hX hx
  exact (isGradientLikeAt_def f X x).2 ⟨U, hU, g, c, hc, h⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The condition `gradientLikeCondition` passes from a form `t` to a form `s` with
`l * s ≤ t ≤ L * s` with `L > 0`, for a constant `δ ≥ 0` with `δ ≤ δ' * l` and `δ * L ≤ δ'`. -/
private theorem mem_gradientLikeCondition_of_mul_le_of_le_mul {δ δ' l L : ℝ} {y : M}
    {s t : TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ}
    (ht : t ∈ gradientLikeCondition f X δ' y) (hL : 0 < L)
    (hst : ∀ v, l * s v v ≤ t v v) (hts : ∀ v, t v v ≤ L * s v v)
    (hδ : 0 ≤ δ) (hδl : δ ≤ δ' * l) (hδL : δ * L ≤ δ') :
    s ∈ gradientLikeCondition f X δ y := by
  obtain ⟨h₀, h₁, h₂⟩ := ht
  set D := mvfderiv 𝓘(ℝ, E) f y (X y)
  have hs₀ (v) : 0 ≤ s v v := nonneg_of_mul_nonneg_right ((h₀ v).trans (hts v)) hL
  have hδ' : 0 ≤ δ' := (mul_nonneg hδ hL.le).trans hδL
  have hXX : δ * s (X y) (X y) ≤ δ' * t (X y) (X y) :=
    calc δ * s (X y) (X y) ≤ δ' * l * s (X y) (X y) :=
          mul_le_mul_of_nonneg_right hδl (hs₀ _)
      _ = δ' * (l * s (X y) (X y)) := mul_assoc _ _ _
      _ ≤ δ' * t (X y) (X y) := mul_le_mul_of_nonneg_left (hst _) hδ'
  refine ⟨hs₀, hXX.trans h₁, fun v ↦ le_of_mul_le_mul_left ?_ hL⟩
  calc L * (δ * mvfderiv 𝓘(ℝ, E) f y v ^ 2) = δ * L * mvfderiv 𝓘(ℝ, E) f y v ^ 2 := by ring
    _ ≤ δ' * mvfderiv 𝓘(ℝ, E) f y v ^ 2 := mul_le_mul_of_nonneg_right hδL (sq_nonneg _)
    _ ≤ (D - δ' * t (X y) (X y)) * t v v := h₂ v
    _ ≤ (D - δ * s (X y) (X y)) * (L * s v v) :=
      mul_le_mul (by linarith) (hts v) (h₀ v) (by linarith)
    _ = L * ((D - δ * s (X y) (X y)) * s v v) := by ring

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The condition `gradientLikeCondition` on a form `s` with a constant `δ ≥ 0` is convex in the
function: it holds for `f` at `y` if it holds for `f₁` and `f₂` and `df_y = a df₁_y + b df₂_y`
with `a, b ≥ 0` and `a + b = 1`. -/
private theorem mem_gradientLikeCondition_of_mvfderiv_eq {f₁ f₂ : M → ℝ} {δ a b : ℝ} {y : M}
    {s : TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ}
    (h₁ : s ∈ gradientLikeCondition f₁ X δ y) (h₂ : s ∈ gradientLikeCondition f₂ X δ y)
    (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hf : mvfderiv 𝓘(ℝ, E) f y = a • mvfderiv 𝓘(ℝ, E) f₁ y + b • mvfderiv 𝓘(ℝ, E) f₂ y) :
    s ∈ gradientLikeCondition f X δ y := by
  obtain ⟨hs₀, h₁₁, h₁₂⟩ := h₁
  obtain ⟨-, h₂₁, h₂₂⟩ := h₂
  set S := s (X y) (X y)
  have hS : δ * S = a * (δ * S) + b * (δ * S) := by linear_combination (-(δ * S)) * hab
  simp only [gradientLikeCondition, mem_ofPred_eq, hf, add_apply, smul_apply, smul_eq_mul]
  refine ⟨hs₀, by nlinarith, fun v ↦ ?_⟩
  set u := mvfderiv 𝓘(ℝ, E) f₁ y v
  set w := mvfderiv 𝓘(ℝ, E) f₂ y v
  -- The square is convex: `(a u + b w) ^ 2 ≤ a u ^ 2 + b w ^ 2`.
  have hsq : (a * u + b * w) ^ 2 ≤ a * u ^ 2 + b * w ^ 2 := by
    have : a * u ^ 2 + b * w ^ 2 - (a * u + b * w) ^ 2 = a * b * (u - w) ^ 2 := by
      linear_combination (-(a * u ^ 2 + b * w ^ 2)) * hab
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (u - w))]
  calc δ * (a * u + b * w) ^ 2 ≤ a * (δ * u ^ 2) + b * (δ * w ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hsq hδ]
    _ ≤ a * ((mvfderiv 𝓘(ℝ, E) f₁ y (X y) - δ * S) * s v v) +
        b * ((mvfderiv 𝓘(ℝ, E) f₂ y (X y) - δ * S) * s v v) :=
      add_le_add (mul_le_mul_of_nonneg_left (h₁₂ v) ha) (mul_le_mul_of_nonneg_left (h₂₂ v) hb)
    _ = _ := by linear_combination (-(δ * S * s v v)) * hab

/-- A gradient-like field is gradient-like near every point: near `x` its metric works with the
constant `δ x / 2`. -/
theorem IsGradientLike.isGradientLikeAt (hX : IsGradientLike f X) (x : M) :
    IsGradientLikeAt f X x := by
  obtain ⟨g, δ, hδc, hδ, h⟩ := hX
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  refine (isGradientLikeAt_def f X x).2 ⟨_,
    hδc.continuousAt.eventually (lt_mem_nhds (half_lt_self (hδ x))), g, δ x / 2,
    half_pos (hδ x), fun y hy ↦ ?_⟩
  refine (mul_le_mul_of_nonneg_right (le_of_lt hy) ?_).trans (h y)
  exact add_nonneg (g.toRiemannianMetric.inner_self_nonneg y (X y)) (sq_nonneg _)

/-- On a σ-compact Hausdorff manifold, `X` is gradient-like for `f` exactly when it is
gradient-like for `f` near every point. -/
theorem isGradientLike_iff_forall_isGradientLikeAt [T2Space M] [SigmaCompactSpace M] :
    IsGradientLike f X ↔ ∀ x, IsGradientLikeAt f X x :=
  ⟨IsGradientLike.isGradientLikeAt, isGradientLike_of_forall_isGradientLikeAt⟩

/-- If `X₁` is gradient-like for `f₁` and `X₂` is gradient-like for `f₂` near `x`, then on some
neighbourhood of `x` one smooth metric satisfies `gradientLikeCondition` for both pairs with one
constant `c > 0`: the metric of `X₂` is compared with that of `X₁` on a compact neighbourhood. -/
private theorem exists_forall_mem_gradientLikeCondition_and {f₁ f₂ : M → ℝ}
    {X₁ X₂ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {x : M}
    (h₁ : IsGradientLikeAt f₁ X₁ x) (h₂ : IsGradientLikeAt f₂ X₂ x) :
    ∃ K ∈ 𝓝 x,
      ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
      ∃ c : ℝ, 0 < c ∧ ∀ y ∈ K,
        g.inner y ∈ gradientLikeCondition f₁ X₁ c y ∧
          g.inner y ∈ gradientLikeCondition f₂ X₂ c y := by
  obtain ⟨U₁, hU₁, g₁, c₁, hc₁, H₁⟩ := (isGradientLikeAt_def f₁ X₁ x).1 h₁
  obtain ⟨U₂, hU₂, g₂, c₂, hc₂, H₂⟩ := (isGradientLikeAt_def f₂ X₂ x).1 h₂
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  -- A compact neighbourhood `K` of `x` inside `U₁ ∩ U₂`.
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds (Filter.inter_mem hU₁ hU₂)
  -- On `K`, the metric `g₂` is comparable to `g₁`, which serves for both pairs.
  obtain ⟨l, hl, L, hL, hg⟩ :=
    g₂.toContinuousRiemannianMetric.exists_mul_inner_le_inner_and_inner_le_mul_inner
      g₁.toContinuousRiemannianMetric hKc
  simp only [ContMDiffRiemannianMetric.toContinuousRiemannianMetric_inner] at hg
  set c := min c₁ (min (c₂ * l) (c₂ / L))
  have hc : 0 < c := lt_min hc₁ (lt_min (mul_pos hc₂ hl) (div_pos hc₂ hL))
  refine ⟨K, hK, g₁, c, hc, fun y hy ↦ ?_⟩
  obtain ⟨hy₁, hy₂⟩ := hKU hy
  exact ⟨inner_mem_gradientLikeCondition_of_le g₁ hc.le (min_le_left _ _) (H₁ y hy₁),
    mem_gradientLikeCondition_of_mul_le_of_le_mul
      (inner_mem_gradientLikeCondition_of_le g₂ hc₂.le le_rfl (H₂ y hy₂)) hL
      (fun v ↦ (hg y hy v).1) (fun v ↦ (hg y hy v).2) hc.le
      ((min_le_right _ _).trans (min_le_left _ _))
      ((le_div_iff₀ hL).1 ((min_le_right _ _).trans (min_le_right _ _)))⟩

/-- **Convex combinations of functions, locally.** If `f₁` and `f₂` are differentiable near `x`
and `X` is gradient-like for each of them near `x`, then `X` is gradient-like near `x` for every
function `(1 - s) • f₁ + s • f₂` with `s ∈ [0, 1]`. -/
theorem IsGradientLikeAt.one_sub_smul_add_smul {f₁ f₂ : M → ℝ} {x : M}
    (h₁ : IsGradientLikeAt f₁ X x) (h₂ : IsGradientLikeAt f₂ X x)
    (hf₁ : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f₁ y)
    (hf₂ : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f₂ y) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IsGradientLikeAt ((1 - s) • f₁ + s • f₂) X x := by
  obtain ⟨K, hK, g, c, hc, H⟩ := exists_forall_mem_gradientLikeCondition_and h₁ h₂
  obtain ⟨hs₀, hs₁⟩ := hs
  refine (isGradientLikeAt_def _ X x).2
    ⟨K ∩ {y | MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f₁ y ∧ MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f₂ y},
      Filter.inter_mem hK (hf₁.and hf₂), g, c, hc, fun y ⟨hy, hd₁, hd₂⟩ ↦ ?_⟩
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  refine (inner_mem_gradientLikeCondition_iff g hc.le y).1 <|
    mem_gradientLikeCondition_of_mvfderiv_eq (H y hy).1 (H y hy).2
      hc.le (sub_nonneg.2 hs₁) hs₀ (sub_add_cancel 1 s) ?_
  rw [mvfderiv_add (hd₁.const_smul _) (hd₂.const_smul _), mvfderiv_const_smul_field,
    mvfderiv_const_smul_field]

/-- **Convex combinations of functions.** On a σ-compact Hausdorff manifold, a field that is
gradient-like for two differentiable functions `f₁` and `f₂` is gradient-like for
`(1 - s) • f₁ + s • f₂` for every `s ∈ [0, 1]`. -/
theorem IsGradientLike.one_sub_smul_add_smul [T2Space M] [SigmaCompactSpace M] {f₁ f₂ : M → ℝ}
    (h₁ : IsGradientLike f₁ X) (h₂ : IsGradientLike f₂ X)
    (hf₁ : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f₁) (hf₂ : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f₂) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : IsGradientLike ((1 - s) • f₁ + s • f₂) X :=
  isGradientLike_of_forall_isGradientLikeAt fun x ↦
    (h₁.isGradientLikeAt x).one_sub_smul_add_smul (h₂.isGradientLikeAt x) (.of_forall hf₁)
      (.of_forall hf₂) hs

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The condition `gradientLikeCondition` on a form `s` with a constant `δ ≥ 0` is convex in the
field: it holds for `a • X + b • X'` at `y` if it holds for `X` and `X'`, with `a, b ≥ 0` and
`a + b = 1`. -/
private theorem mem_gradientLikeCondition_smul_add_smul {X' : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    {δ a b : ℝ} {y : M} {s : TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ}
    (h : s ∈ gradientLikeCondition f X δ y) (h' : s ∈ gradientLikeCondition f X' δ y)
    (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    s ∈ gradientLikeCondition f (fun x ↦ a • X x + b • X' x) δ y := by
  obtain ⟨hs₀, h₁, h₂⟩ := h
  obtain ⟨-, h₁', h₂'⟩ := h'
  set u := X y
  set w := X' y
  set D := mvfderiv 𝓘(ℝ, E) f y
  -- The quadratic form of `s` is convex, since `s` is nonnegative on the diagonal.
  have hQ : s (a • u + b • w) (a • u + b • w) ≤ a * s u u + b * s w w := by
    have := (LinearMap.convexOn_re_apply_self (𝕜 := ℝ) (a := s.toLinearMap₁₂)
      (by simpa using hs₀)).2 (Set.mem_univ u) (Set.mem_univ w) ha hb hab
    simpa using this
  have hR : a * (D u - δ * s u u) + b * (D w - δ * s w w) ≤
      D (a • u + b • w) - δ * s (a • u + b • w) (a • u + b • w) := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hQ hδ]
  refine ⟨hs₀, ?_, fun v ↦ ?_⟩
  · nlinarith [mul_nonneg ha (sub_nonneg.2 h₁), mul_nonneg hb (sub_nonneg.2 h₁')]
  · calc δ * D v ^ 2 = a * (δ * D v ^ 2) + b * (δ * D v ^ 2) := by
          linear_combination (-(δ * D v ^ 2)) * hab
      _ ≤ a * ((D u - δ * s u u) * s v v) + b * ((D w - δ * s w w) * s v v) :=
        add_le_add (mul_le_mul_of_nonneg_left (h₂ v) ha) (mul_le_mul_of_nonneg_left (h₂' v) hb)
      _ = (a * (D u - δ * s u u) + b * (D w - δ * s w w)) * s v v := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hR (hs₀ v)

/-- **Convex combinations of fields, locally, with a common constant.** If `X` and `X'` are
gradient-like for `f` near `x`, then there are a neighbourhood `U` of `x`, a smooth metric `g` and
a constant `c > 0` with which every field `(1 - s) • X + s • X'`, `s ∈ [0, 1]`, satisfies the
inequality of `TauCeti.IsGradientLikeAt` on `U`. -/
theorem IsGradientLikeAt.exists_forall_one_sub_smul_add_smul_right
    {X' : (x : M) → TangentSpace 𝓘(ℝ, E) x} {x : M}
    (h : IsGradientLikeAt f X x) (h' : IsGradientLikeAt f X' x) :
    ∃ U ∈ 𝓝 x,
      ∃ g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
      ∃ c : ℝ, 0 < c ∧
        letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ y ∈ U,
          c * (g.inner y ((1 - s) • X y + s • X' y) ((1 - s) • X y + s • X' y) +
            ‖mgradient 𝓘(ℝ, E) f y‖ ^ 2) ≤ mvfderiv 𝓘(ℝ, E) f y ((1 - s) • X y + s • X' y) := by
  obtain ⟨K, hK, g, c, hc, H⟩ := exists_forall_mem_gradientLikeCondition_and h h'
  refine ⟨K, hK, g, c, hc, fun s ⟨hs₀, hs₁⟩ y hy ↦ ?_⟩
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  exact (inner_mem_gradientLikeCondition_iff (X := fun y ↦ (1 - s) • X y + s • X' y) g hc.le
    y).1 <| mem_gradientLikeCondition_smul_add_smul (H y hy).1 (H y hy).2
      hc.le (sub_nonneg.2 hs₁) hs₀ (sub_add_cancel 1 s)

/-- **Convex combinations of fields, locally.** If `X` and `X'` are gradient-like for `f` near
`x`, then so is every field `(1 - s) • X + s • X'` with `s ∈ [0, 1]`. -/
theorem IsGradientLikeAt.one_sub_smul_add_smul_right {X' : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    {x : M} (h : IsGradientLikeAt f X x) (h' : IsGradientLikeAt f X' x) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : IsGradientLikeAt f (fun y ↦ (1 - s) • X y + s • X' y) x := by
  obtain ⟨U, hU, g, c, hc, H⟩ := h.exists_forall_one_sub_smul_add_smul_right h'
  exact (isGradientLikeAt_def _ _ x).2 ⟨U, hU, g, c, hc, H s hs⟩

/-- **Convex combinations of fields.** On a σ-compact Hausdorff manifold, if `X` and `X'` are
gradient-like for `f`, then so is every field `(1 - s) • X + s • X'` with `s ∈ [0, 1]`. -/
theorem IsGradientLike.one_sub_smul_add_smul_right [T2Space M] [SigmaCompactSpace M]
    {X' : (x : M) → TangentSpace 𝓘(ℝ, E) x} (h : IsGradientLike f X) (h' : IsGradientLike f X')
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : IsGradientLike f (fun y ↦ (1 - s) • X y + s • X' y) :=
  isGradientLike_of_forall_isGradientLikeAt fun x ↦
    (h.isGradientLikeAt x).one_sub_smul_add_smul_right (h'.isGradientLikeAt x) hs

end Local

section Flow

open Filter Topology

variable {Φ : Flow ℝ M}

namespace IsGradientLike

/-- An integral curve of a gradient-like field along which `f` is constant near the time `t₀`
passes at `t₀` through a critical point of `f`. -/
theorem mem_criticalPoints_of_eventuallyEq_const (hX : IsGradientLike f X) {γ : ℝ → M}
    {t₀ c : ℝ} (hγ : IsMIntegralCurveAt γ X t₀) (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (γ t₀))
    (hfγ : f ∘ γ =ᶠ[𝓝 t₀] fun _ ↦ c) : γ t₀ ∈ criticalPoints 𝓘(ℝ, E) f := by
  by_contra h
  have := (hX.mvfderiv_apply_pos h).ne'
  rw [mvfderiv_apply_eq_mfderiv_apply] at this
  exact this (hγ.mfderiv_apply_eq_zero_of_eventuallyEq_const hf hfγ)

/-- A point along whose orbit `f` is constant is a critical point of `f`. -/
theorem mem_criticalPoints_of_forall_flow_apply_eq (hX : IsGradientLike f X) {z : M}
    (hz' : IsMIntegralCurve (fun t ↦ Φ t z) X) (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f z)
    (hz : ∀ t, f (Φ t z) = f z) : z ∈ criticalPoints 𝓘(ℝ, E) f := by
  have h := hX.mem_criticalPoints_of_eventuallyEq_const (hz'.isMIntegralCurveAt 0)
    (c := f z) (by simpa only [Flow.map_zero_apply] using hf) (.of_forall hz)
  rwa [Flow.map_zero_apply] at h

/-- **Forward limit points of a gradient-like flow are critical.** If `Φ` is a flow of a
gradient-like field `X` for a differentiable `f`, every cluster point at `+∞` of an orbit of `Φ`
is a critical point of `f`. -/
theorem mem_criticalPoints_of_mapClusterPt_atTop (hX : IsGradientLike f X)
    (hΦ : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) X) (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    {x z : M} (hz : MapClusterPt z atTop fun t ↦ Φ t x) : z ∈ criticalPoints 𝓘(ℝ, E) f :=
  hX.mem_criticalPoints_of_forall_flow_apply_eq (hΦ z) (hf z) fun t ↦ neg_inj.1 <|
    Flow.apply_flow_eq_of_mapClusterPt_of_antitone (g := -f)
      (fun _ _ h ↦ neg_le_neg (hX.monotone_comp (hΦ x) (fun _ ↦ hf _) h))
      hf.continuous.neg hz t

/-- **Backward limit points of a gradient-like flow are critical.** If `Φ` is a flow of a
gradient-like field `X` for a differentiable `f`, every cluster point at `-∞` of an orbit of `Φ`
is a critical point of `f`. -/
theorem mem_criticalPoints_of_mapClusterPt_atBot (hX : IsGradientLike f X)
    (hΦ : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) X) (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    {x z : M} (hz : MapClusterPt z atBot fun t ↦ Φ t x) : z ∈ criticalPoints 𝓘(ℝ, E) f :=
  hX.mem_criticalPoints_of_forall_flow_apply_eq (hΦ z) (hf z) fun t ↦ neg_inj.1 <|
    Flow.apply_flow_eq_of_mapClusterPt_atBot_of_antitone (g := -f)
      (fun _ _ h ↦ neg_le_neg (hX.monotone_comp (hΦ x) (fun _ ↦ hf _) h))
      hf.continuous.neg hz t

/-- **Backward orbits in a compact region of a gradient-like flow.** Let `Φ` be a flow of a
gradient-like field `X` for a differentiable `f`, and `a, b` reals with `f ⁻¹' Icc a b` compact.
If `f x ≤ b`, then either `f (Φ t x) ≤ a` for some `t ≤ 0`, or the backward orbit of `x` has a
cluster point at `-∞`, and every such cluster point is a critical point of `f` in
`f ⁻¹' Icc a b`. -/
theorem exists_flow_apply_le_or_mapClusterPt_atBot (hX : IsGradientLike f X)
    (hΦ : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) X) (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    {a b : ℝ} (hK : IsCompact (f ⁻¹' Icc a b)) {x : M} (hx : f x ≤ b) :
    (∃ t ≤ 0, f (Φ t x) ≤ a) ∨
      ((∃ z, MapClusterPt z atBot fun t ↦ Φ t x) ∧ ∀ z, MapClusterPt z atBot (fun t ↦ Φ t x) →
        z ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b) := by
  refine or_iff_not_imp_left.2 fun h ↦ ?_
  simp only [not_exists, not_and, not_le] at h
  have hmem : ∀ᶠ t in atBot, Φ t x ∈ f ⁻¹' Icc a b :=
    (eventually_le_atBot 0).mono fun t ht ↦ ⟨(h t ht).le,
      (show f (Φ t x) ≤ f x by
        simpa only [Function.comp_apply, Flow.map_zero_apply] using
          hX.monotone_comp (hΦ x) (fun _ ↦ hf _) ht).trans hx⟩
  obtain ⟨z, -, hz⟩ := hK.exists_mapClusterPt_of_frequently hmem.frequently
  exact ⟨⟨z, hz⟩, fun z hz ↦ ⟨hX.mem_criticalPoints_of_mapClusterPt_atBot hΦ hf hz,
    (isClosed_Icc.preimage hf.continuous).mem_of_mapClusterPt hz hmem⟩⟩

/-- The forward orbit of a point of `{a ≤ f}` that stays in `{f ≤ b}` lies in `f ⁻¹' Icc a b`. -/
theorem mapsTo_flow_Ici_preimage_Icc (hX : IsGradientLike f X) {x : M}
    (hx' : IsMIntegralCurve (fun t ↦ Φ t x) X)
    (hf : ∀ t, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f (Φ t x)) {a b : ℝ} (hx : a ≤ f x)
    (hb : ∀ t, 0 ≤ t → f (Φ t x) ≤ b) :
    MapsTo (fun t ↦ Φ t x) (Ici 0) (f ⁻¹' Icc a b) := fun t (ht : 0 ≤ t) ↦ ⟨by
  exact hx.trans (by
    simpa only [Function.comp_apply, Flow.map_zero_apply] using hX.monotone_comp hx' hf ht),
    hb t ht⟩

/-- **Forward orbits in a compact region of a gradient-like flow.** Let `Φ` be a flow of a
gradient-like field `X` for a differentiable `f`, and `a, b` reals with `f ⁻¹' Icc a b` compact.
If `a ≤ f x` and `f (Φ t x) ≤ b` for all `t ≥ 0`, then the forward orbit of `x` has a cluster
point at `+∞`, and every such cluster point is a critical point of `f` in `f ⁻¹' Icc a b`. -/
theorem exists_mapClusterPt_atTop_of_isCompact (hX : IsGradientLike f X)
    (hΦ : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) X) (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    {a b : ℝ} (hK : IsCompact (f ⁻¹' Icc a b)) {x : M} (hx : a ≤ f x)
    (hb : ∀ t, 0 ≤ t → f (Φ t x) ≤ b) :
    (∃ z, MapClusterPt z atTop fun t ↦ Φ t x) ∧ ∀ z, MapClusterPt z atTop (fun t ↦ Φ t x) →
      z ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b := by
  have hmem : ∀ᶠ t in atTop, Φ t x ∈ f ⁻¹' Icc a b :=
    (eventually_ge_atTop 0).mono fun t ht ↦
      hX.mapsTo_flow_Ici_preimage_Icc (hΦ x) (fun _ ↦ hf _) hx hb ht
  obtain ⟨z, -, hz⟩ := hK.exists_mapClusterPt_of_frequently hmem.frequently
  exact ⟨⟨z, hz⟩, fun z hz ↦ ⟨hX.mem_criticalPoints_of_mapClusterPt_atTop hΦ hf hz,
    (isClosed_Icc.preimage hf.continuous).mem_of_mapClusterPt hz hmem⟩⟩

/-- **Forward orbits in a compact region tend to a critical point.** Let `Φ` be a flow of a
gradient-like field `X` for a differentiable `f` on a Hausdorff manifold, and `a, b` reals such
that `f ⁻¹' Icc a b` is compact and contains finitely many critical points of `f`. If `a ≤ f x`
and `f (Φ t x) ≤ b` for all `t ≥ 0`, then `x` lies in the stable set of one of these critical
points. -/
theorem exists_mem_stableSet_of_isCompact [T2Space M] (hX : IsGradientLike f X)
    (hΦ : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) X) (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    {a b : ℝ} (hK : IsCompact (f ⁻¹' Icc a b))
    (hfin : (criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b).Finite) {x : M} (hx : a ≤ f x)
    (hb : ∀ t, 0 ≤ t → f (Φ t x) ≤ b) :
    ∃ p ∈ criticalPoints 𝓘(ℝ, E) f ∩ f ⁻¹' Icc a b, x ∈ Φ.stableSet p := by
  obtain ⟨p, hp, hlim⟩ := exists_tendsto_atTop_of_setOf_mapClusterPt_subset hK
    (Φ.continuous_eval_const x).continuousOn
    (hX.mapsTo_flow_Ici_preimage_Icc (hΦ x) (fun _ ↦ hf _) hx hb) hfin
    (hX.exists_mapClusterPt_atTop_of_isCompact hΦ hf hK hx hb).2
  exact ⟨p, hp, Flow.mem_stableSet.2 hlim⟩

end IsGradientLike

end Flow

end TauCeti

end
