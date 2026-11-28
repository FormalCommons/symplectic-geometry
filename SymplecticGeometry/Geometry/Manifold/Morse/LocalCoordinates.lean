/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import SymplecticGeometry.Geometry.Manifold.Riemannian.NormedSpace
import TauCeti.Topology.VectorBundle.Riemannian.Comparison
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import SymplecticGeometry.Geometry.Manifold.Riemannian.PullbackPartialDiffeomorph

/-!
# The gradient-like inequality in local coordinates

Let `X` be gradient-like for `f : M → ℝ` near a point `p` (`TauCeti.IsGradientLikeAt`), and let
`e` be a chart of the maximal atlas at `p`. Read in `e`, with `f̃ = f ∘ e.symm` and `X̃` the field
`X` pushed forward by `de`, the gradient-like inequality holds near `e p` with the norm of the model
space `E` in place of the Riemannian metric:
`c * (‖X̃ z‖ ^ 2 + ‖df̃_z‖ ^ 2) ≤ df̃_z (X̃ z)` for some `c > 0` and every `z` in a ball around
`e p`. This is the form in which the local estimates of Cieliebak–Eliashberg's Proposition 9.23,
in a Morse or a birth–death chart, use the gradient-like condition. Conversely, on a σ-compact
Hausdorff manifold, such an inequality on a ball around `e p` makes `X` gradient-like for `f`
near `p`.

## Main results

* `TauCeti.IsGradientLikeAt.exists_mul_le_fderiv_comp_symm`: the inequality in a chart.
* `TauCeti.isGradientLikeAt_of_mul_le_fderiv_comp_symm`: its converse.
* `TauCeti.IsGradientLikeAt.exists_pos_eventually_mul_le`: on a normed space, the case of the
  identity chart, with the norm of the space near the point.
* `Bundle.ContMDiffRiemannianMetric.exists_pos_mul_inner_le_norm_mvfderiv_sq`: on a compact
  subset of the source of a chart `e`, a smooth Riemannian metric and the norm of `E` read through
  `de` bound each other up to constants.
* `OpenPartialHomeomorph.fderiv_comp_symm_apply_of_mem_maximalAtlas`: the differential of
  `f ∘ e.symm` is that of `f` composed with `d(e.symm)`.

## Implementation notes

On a compact subset `K` of the source of `e`, a metric `g` is compared with the forms
`(v, w) ↦ ⟪T (de_y v), T (de_y w)⟫`, where `T = toEuclidean`. These are
the pull-back along `e` of the metric `SymplecticGeometry.riemannianMetricToEuclidean E` that
`toEuclidean` carries to `E`; they are continuous and positive definite on the source of
`e` (`PartialDiffeomorph.contMDiffOn_pullback`, `PartialDiffeomorph.pullback_apply_self_pos`), so
Tau Ceti's `IsCompact.exists_pos_forall_mul_norm_sq_le_bundle` and
`IsCompact.exists_bound_of_continuousOn_bilinear_bundle` bound them above and below by the norm of
`g` on `K`. Both directions use this comparison, the first with the metric of the hypothesis and
the converse with any smooth metric (`TauCeti.nonempty_contMDiffRiemannianMetric`). The
differential of `f̃` is that of `f` composed with `d(e.symm)`, by the chain rule
for local diffeomorphisms, Tau Ceti's `IsLocalDiffeomorphAt.mfderiv_comp`, which needs no
differentiability of `f`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 9.23
-/

public section

open Bundle Set Metric
open scoped ContDiff Manifold Topology
open TauCeti.Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **The differential of a function read in a chart.** For a chart `e` of the maximal atlas and
a point `z` of its target, the differential of `f ∘ e.symm` at `z` is that of `f` at `e.symm z`
composed with the differential of `e.symm`. No differentiability of `f` is needed. -/
theorem _root_.OpenPartialHomeomorph.fderiv_comp_symm_apply_of_mem_maximalAtlas
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {z : E} (hz : z ∈ e.target) (f : M → F)
    (u : E) :
    fderiv ℝ (f ∘ e.symm) z u =
      mvfderiv 𝓘(ℝ, E) f (e.symm z) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z u) := by
  have h := (e.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas he hz).mfderiv_comp
    (I' := 𝓘(ℝ, F)) (by simp) f
  rw [← mvfderiv_eq_fderiv_apply (f ∘ e.symm) z u,
    mvfderiv_apply_eq_mfderiv_apply (f ∘ e.symm) z u, h]
  -- The composite of continuous linear maps, applied to `u`.
  exact (mvfderiv_apply_eq_mfderiv_apply f (e.symm z) _).symm

/-- **A Riemannian metric against a chart on a compact set.** Let `g` be a smooth Riemannian
metric on `M`, `e` a chart of the maximal atlas and `K` a compact subset of its source. Then there
are `a > 0` and `C > 0` with `a * g y v v ≤ ‖de_y v‖ ^ 2 ≤ C * g y v v` for every `y ∈ K` and
every tangent vector `v` at `y`, the norm being that of `E`. -/
theorem _root_.Bundle.ContMDiffRiemannianMetric.exists_pos_mul_inner_le_norm_mvfderiv_sq
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {K : Set M}
    (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ a > 0, ∃ C > 0, ∀ y ∈ K, ∀ v : TangentSpace 𝓘(ℝ, E) y,
      a * g.inner y v v ≤ ‖mvfderiv 𝓘(ℝ, E) e y v‖ ^ 2 ∧
        ‖mvfderiv 𝓘(ℝ, E) e y v‖ ^ 2 ≤ C * g.inner y v v := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  -- The metric that `T = toEuclidean` carries to `E`.
  set T := toEuclidean (E := E)
  set g₀ : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E)) :=
    (SymplecticGeometry.riemannianMetricToEuclidean E).ofLE le_top
  have hg₀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x) : g₀.inner x v w = inner ℝ (T v) (T w) := by
    rw [ContMDiffRiemannianMetric.ofLE_inner]
    exact SymplecticGeometry.riemannianMetricToEuclidean_inner x v w
  obtain ⟨L, hL0, hL⟩ : ∃ L, 0 < L ∧ ∀ v, ‖T v‖ ≤ L * ‖v‖ :=
    ⟨_, zero_lt_one.trans_le (le_max_right _ 1), fun v ↦ (T.toContinuousLinearMap.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ 1) (norm_nonneg v))⟩
  obtain ⟨K', hK'⟩ : ∃ K', ∀ v, ‖v‖ ≤ K' * ‖T v‖ :=
    ⟨_, fun v ↦ by simpa using T.symm.toContinuousLinearMap.le_opNorm (T v)⟩
  -- The pull-back of `g₀` along `e`, compared with `g` on `K`.
  set Ψ := e.toPartialDiffeomorph he
  have hΨs : Ψ.source = e.source :=
    congrArg PartialEquiv.source (e.toPartialDiffeomorph_toPartialEquiv he)
  have hΨ : (Ψ : M → E) = e := e.coe_toPartialDiffeomorph he
  have hφ := Ψ.contMDiffOn_pullback g₀ (by simp)
  obtain ⟨a, ha, hlow⟩ := hK.exists_pos_forall_mul_norm_sq_le_bundle (b := id)
    (hφ.continuousOn.mono fun y hy ↦ hΨs ▸ hKe hy)
    fun y hy v hv ↦ Ψ.pullback_apply_self_pos g₀ (by simp) (hΨs ▸ hKe hy) hv
  obtain ⟨C, hup⟩ := hK.exists_bound_of_continuousOn_bilinear_bundle (b := id)
    (hφ.continuousOn.mono fun y hy ↦ hΨs ▸ hKe hy)
  refine ⟨a / L ^ 2, by positivity, K' ^ 2 * max C 0 + 1, by positivity, fun y hy v ↦ ?_⟩
  set A := mvfderiv 𝓘(ℝ, E) e y
  -- The pulled-back form at `y` is `v ↦ ‖T (A v)‖ ^ 2`.
  have hφy : (ContinuousLinearMap.precomp ℝ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ y)).comp
      ((g₀.inner (Ψ y)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ y)) v v = ‖T (A v)‖ ^ 2 := by
    rw [hΨ]
    simp [hg₀, A]
  have hv : g.inner y v v = ‖v‖ ^ 2 := (g.norm_sq y v).symm
  have hTA : ‖T (A v)‖ ^ 2 ≤ L ^ 2 * ‖A v‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hL _) 2
  have hup' : ‖T (A v)‖ ^ 2 ≤ max C 0 * ‖v‖ ^ 2 := by
    rw [← hφy]
    calc _ ≤ ‖_‖ := Real.le_norm_self _
      _ ≤ _ := ContinuousLinearMap.le_opNorm₂ _ v v
      _ ≤ max C 0 * ‖v‖ ^ 2 := by
        rw [mul_assoc, ← sq]
        exact mul_le_mul_of_nonneg_right ((hup y hy).trans (le_max_left _ _)) (sq_nonneg _)
  have hAT : ‖A v‖ ^ 2 ≤ K' ^ 2 * ‖T (A v)‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hK' _) 2
  rw [hv]
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity), mul_comm (‖A v‖ ^ 2)]
    exact ((hlow y hy v).trans_eq hφy).trans hTA
  · calc ‖A v‖ ^ 2 ≤ K' ^ 2 * (max C 0 * ‖v‖ ^ 2) := hAT.trans (by gcongr)
      _ ≤ (K' ^ 2 * max C 0 + 1) * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]

omit [FiniteDimensional ℝ E] in
/-- The pointwise step of `TauCeti.IsGradientLikeAt.exists_mul_le_fderiv_comp_symm`. Let `A : V → E`
and `B : E → V` be mutually inverse, with `a ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2 ≤ C ‖v‖ ^ 2`, and let
`D = ⟪G, B ·⟫`. If `c (‖x‖ ^ 2 + ‖G‖ ^ 2) ≤ ⟪G, x⟫`, then the same inequality holds for `A x` and
`D`, with the smaller constant `c / (C + 1 / a + 1)`. -/
private theorem mul_le_apply_of_forall_mul_norm_sq_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {A : V →L[ℝ] E} {B : E →L[ℝ] V} {D : E →L[ℝ] ℝ} {G x : V}
    {a C c : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hc : 0 < c) (hAB : ∀ u, A (B u) = u)
    (hBA : ∀ v, B (A v) = v) (hlow : ∀ v, a * ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2)
    (hup : ∀ v, ‖A v‖ ^ 2 ≤ C * ‖v‖ ^ 2) (hD : ∀ u, D u = inner ℝ G (B u))
    (h : c * (‖x‖ ^ 2 + ‖G‖ ^ 2) ≤ inner ℝ G x) :
    c / (C + 1 / a + 1) * (‖A x‖ ^ 2 + ‖D‖ ^ 2) ≤ D (A x) := by
  -- `‖B u‖ ≤ ‖u‖ / √a`, so `‖D‖ ^ 2 ≤ ‖G‖ ^ 2 / a`.
  have hB (u : E) : ‖B u‖ ≤ (Real.sqrt a)⁻¹ * ‖u‖ := by
    have h₀ : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    rw [inv_mul_eq_div, le_div_iff₀ h₀, ← Real.sqrt_sq (norm_nonneg (B u)),
      ← Real.sqrt_mul (sq_nonneg _), mul_comm, ← Real.sqrt_sq (norm_nonneg u)]
    exact Real.sqrt_le_sqrt ((hlow _).trans_eq (by rw [hAB]))
  have h₂ : ‖D‖ ^ 2 ≤ 1 / a * ‖G‖ ^ 2 := by
    have hbd : ‖D‖ ≤ (Real.sqrt a)⁻¹ * ‖G‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
      rw [hD u, Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖G‖ * ‖B u‖ ≤ ‖G‖ * ((Real.sqrt a)⁻¹ * ‖u‖) := by gcongr; exact hB u
        _ = _ := by ring
    calc _ ≤ ((Real.sqrt a)⁻¹ * ‖G‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbd 2
      _ = _ := by rw [mul_pow, inv_pow, Real.sq_sqrt ha.le, one_div]
  rw [hD, hBA]
  calc c / (C + 1 / a + 1) * (‖A x‖ ^ 2 + ‖D‖ ^ 2)
      ≤ c / (C + 1 / a + 1) * ((C + 1 / a + 1) * (‖x‖ ^ 2 + ‖G‖ ^ 2)) := by
        gcongr
        have h₅ : 0 ≤ 1 / a := by positivity
        nlinarith [hup x, mul_nonneg hC (sq_nonneg ‖G‖), mul_nonneg h₅ (sq_nonneg ‖x‖)]
    _ = c * (‖x‖ ^ 2 + ‖G‖ ^ 2) := by field_simp
    _ ≤ _ := h

omit [FiniteDimensional ℝ E] in
/-- The pointwise step of `TauCeti.isGradientLikeAt_of_mul_le_fderiv_comp_symm`, the converse of
`mul_le_apply_of_forall_mul_norm_sq_le`. Let `A : V → E` be a linear map with
`a ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2 ≤ C ‖v‖ ^ 2`, and let `D : E → ℝ` satisfy `D (A v) = ⟪G, v⟫`. If
`c (‖A x‖ ^ 2 + ‖D‖ ^ 2) ≤ D (A x)`, then `c / (C + 1 / a + 1) (‖x‖ ^ 2 + ‖G‖ ^ 2) ≤ ⟪G, x⟫`. -/
private theorem mul_le_inner_of_forall_mul_norm_sq_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {A : V →L[ℝ] E} {D : E →L[ℝ] ℝ} {G x : V} {a C c : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hc : 0 < c) (hlow : ∀ v, a * ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2)
    (hup : ∀ v, ‖A v‖ ^ 2 ≤ C * ‖v‖ ^ 2) (hD : ∀ v, D (A v) = inner ℝ G v)
    (h : c * (‖A x‖ ^ 2 + ‖D‖ ^ 2) ≤ D (A x)) :
    c / (C + 1 / a + 1) * (‖x‖ ^ 2 + ‖G‖ ^ 2) ≤ inner ℝ G x := by
  have h₁ : ‖x‖ ^ 2 ≤ 1 / a * ‖A x‖ ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha, mul_comm]; exact hlow x
  -- `‖G‖ ^ 2 = D (A G) ≤ ‖D‖ ‖A G‖ ≤ √C ‖D‖ ‖G‖`, so `‖G‖ ^ 2 ≤ C ‖D‖ ^ 2`.
  have h₂ : ‖G‖ ^ 2 ≤ C * ‖D‖ ^ 2 := by
    have hAG : ‖A G‖ ≤ Real.sqrt C * ‖G‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (A G)), ← Real.sqrt_sq (norm_nonneg G),
        ← Real.sqrt_mul hC]
      exact Real.sqrt_le_sqrt (hup G)
    have hG : ‖G‖ ^ 2 ≤ ‖D‖ * (Real.sqrt C * ‖G‖) := by
      calc ‖G‖ ^ 2 = D (A G) := by rw [hD, real_inner_self_eq_norm_sq]
        _ ≤ ‖D‖ * ‖A G‖ := (le_abs_self _).trans (D.le_opNorm _)
        _ ≤ _ := by gcongr
    have hG' : ‖G‖ ≤ Real.sqrt C * ‖D‖ := by
      rcases (norm_nonneg G).eq_or_lt with h0 | h0
      · rw [← h0]; positivity
      · nlinarith
    calc _ ≤ (Real.sqrt C * ‖D‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG' 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt hC]
  rw [← hD]
  calc c / (C + 1 / a + 1) * (‖x‖ ^ 2 + ‖G‖ ^ 2)
      ≤ c / (C + 1 / a + 1) * ((C + 1 / a + 1) * (‖A x‖ ^ 2 + ‖D‖ ^ 2)) := by
        gcongr
        have h₅ : 0 ≤ 1 / a := by positivity
        nlinarith [mul_nonneg hC (sq_nonneg ‖A x‖), mul_nonneg h₅ (sq_nonneg ‖D‖)]
    _ = c * (‖A x‖ ^ 2 + ‖D‖ ^ 2) := by field_simp
    _ ≤ _ := h

/-- **The gradient-like inequality in a chart.** Let `X` be gradient-like for `f` near `p`, and
let `e` be a chart of the maximal atlas whose source contains `p`. Write `f̃ = f ∘ e.symm` and
`X̃ z = de_{e.symm z} (X (e.symm z))`. Then there are `r₀ > 0` and `c > 0` such that the ball of
radius `r₀` around `e p` lies in the target of `e`, and
`c * (‖X̃ z‖ ^ 2 + ‖df̃_z‖ ^ 2) ≤ df̃_z (X̃ z)` on it, for the norm of `E` and the operator norm.
The converse is `TauCeti.isGradientLikeAt_of_mul_le_fderiv_comp_symm`. -/
theorem IsGradientLikeAt.exists_mul_le_fderiv_comp_symm {f : M → ℝ}
    {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M} (hX : IsGradientLikeAt f X p)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hp : p ∈ e.source) :
    ∃ r₀ > 0, ∃ c > 0, ball (e p) r₀ ⊆ e.target ∧ ∀ z ∈ ball (e p) r₀,
      c * (‖mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))‖ ^ 2 +
          ‖fderiv ℝ (f ∘ e.symm) z‖ ^ 2) ≤
        fderiv ℝ (f ∘ e.symm) z (mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))) := by
  obtain ⟨U, hU, g, c, hc, H⟩ := (isGradientLikeAt_def f X p).1 hX
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  -- A compact neighbourhood `K` of `p` in the source of `e` on which the hypothesis holds.
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds
    (Filter.inter_mem hU (e.open_source.mem_nhds hp))
  obtain ⟨a, ha, C, hC, hAg⟩ :=
    g.exists_pos_mul_inner_le_norm_mvfderiv_sq he hKc fun y hy ↦ (hKU hy).2
  -- A ball around `e p` that `e.symm` maps into `K`.
  have hKn : e.symm ⁻¹' K ∈ 𝓝 (e p) :=
    (e.continuousAt_symm (e.map_source hp)).preimage_mem_nhds (by rwa [e.left_inv hp])
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.1
    (Filter.inter_mem hKn (e.open_target.mem_nhds (e.map_source hp)))
  refine ⟨r₀, hr₀, c / (C + 1 / a + 1), by positivity, fun z hz ↦ (hball hz).2, fun z hz ↦ ?_⟩
  obtain ⟨hzK, hzt⟩ := hball hz
  set y := e.symm z
  obtain ⟨hyU, hys⟩ := hKU (show y ∈ K from hzK)
  set A := mvfderiv 𝓘(ℝ, E) e y
  set B := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z
  set Ψ := e.toPartialDiffeomorph he
  have hΨs : Ψ.source = e.source :=
    congrArg PartialEquiv.source (e.toPartialDiffeomorph_toPartialEquiv he)
  have hΨt : Ψ.target = e.target :=
    congrArg PartialEquiv.target (e.toPartialDiffeomorph_toPartialEquiv he)
  have hΨ : (Ψ : M → E) = e := e.coe_toPartialDiffeomorph he
  have hΨ' : (Ψ.symm : E → M) = e.symm := e.coe_toPartialDiffeomorph_symm he
  have hAB (u : E) : A (B u) = u := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    have := Ψ.mfderiv_apply_mfderiv_symm_apply (by simp) (hΨt ▸ hzt) u
    rwa [hΨ, hΨ'] at this
  have hBA (v : TangentSpace 𝓘(ℝ, E) y) : B (A v) = v := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    have := Ψ.mfderiv_symm_apply_mfderiv_apply (by simp) (hΨs ▸ hys) v
    rwa [hΨ, hΨ', e.right_inv hzt] at this
  have hH := H y hyU
  rw [← g.norm_sq, ← inner_mgradient] at hH
  exact mul_le_apply_of_forall_mul_norm_sq_le ha hC.le hc hAB hBA
    (fun v ↦ (g.norm_sq y v ▸ (hAg y hzK v).1)) (fun v ↦ (g.norm_sq y v ▸ (hAg y hzK v).2))
    (fun u ↦ (e.fderiv_comp_symm_apply_of_mem_maximalAtlas he hzt f u).trans
      (inner_mgradient _).symm) hH

/-- **The gradient-like inequality in a chart gives the local condition.** On a σ-compact
Hausdorff manifold, let `e` be a chart of the maximal atlas whose source contains `x`, and write
`f̃ = f ∘ e.symm` and `X̃ z = de_{e.symm z} (X (e.symm z))`. If, for some `r > 0` and `c > 0`,
`c * (‖X̃ z‖ ^ 2 + ‖df̃_z‖ ^ 2) ≤ df̃_z (X̃ z)` for every `z` in the ball of radius `r` around
`e x`, for the norm of `E` and the operator norm, then `X` is gradient-like for `f` near `x`.
This is the converse of `TauCeti.IsGradientLikeAt.exists_mul_le_fderiv_comp_symm`. -/
theorem isGradientLikeAt_of_mul_le_fderiv_comp_symm [T2Space M] [SigmaCompactSpace M] {f : M → ℝ}
    {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {x : M} {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (hx : x ∈ e.source) {r c : ℝ} (hr : 0 < r)
    (hc : 0 < c)
    (h : ∀ z ∈ ball (e x) r,
      c * (‖mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))‖ ^ 2 +
          ‖fderiv ℝ (f ∘ e.symm) z‖ ^ 2) ≤
        fderiv ℝ (f ∘ e.symm) z (mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z)))) :
    IsGradientLikeAt f X x := by
  obtain ⟨g⟩ : Nonempty
      (ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)) :=
    nonempty_contMDiffRiemannianMetric
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  -- A compact neighbourhood `K` of `x` in the source of `e` that `e` maps into the ball.
  have hU : e.source ∩ e ⁻¹' ball (e x) r ∈ 𝓝 x :=
    (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball).mem_nhds
      ⟨hx, mem_ball_self hr⟩
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds hU
  obtain ⟨a, ha, C, hC, hAg⟩ :=
    g.exists_pos_mul_inner_le_norm_mvfderiv_sq he hKc fun y hy ↦ (hKU hy).1
  refine (isGradientLikeAt_def f X x).2
    ⟨K, hK, g, c / (C + 1 / a + 1), by positivity, fun y hy ↦ ?_⟩
  obtain ⟨hys, hyb⟩ := hKU hy
  have hzt : e y ∈ e.target := e.map_source hys
  -- The differential of `f̃` at `e y`, composed with that of `e`, is that of `f` at `y`.
  set Ψ := e.toPartialDiffeomorph he
  have hΨs : Ψ.source = e.source :=
    congrArg PartialEquiv.source (e.toPartialDiffeomorph_toPartialEquiv he)
  have hΨ : (Ψ : M → E) = e := e.coe_toPartialDiffeomorph he
  have hΨ' : (Ψ.symm : E → M) = e.symm := e.coe_toPartialDiffeomorph_symm he
  have hD (v : TangentSpace 𝓘(ℝ, E) y) :
      fderiv ℝ (f ∘ e.symm) (e y) (mvfderiv 𝓘(ℝ, E) e y v) =
        inner ℝ (mgradient 𝓘(ℝ, E) f y) v := by
    rw [e.fderiv_comp_symm_apply_of_mem_maximalAtlas he hzt, inner_mgradient]
    have hBA := Ψ.mfderiv_symm_apply_mfderiv_apply (by simp) (hΨs ▸ hys) v
    rw [hΨ, hΨ'] at hBA
    rw [mvfderiv_apply_eq_mfderiv_apply e y v, hBA, e.left_inv hys]
  have hy' := h (e y) hyb
  rw [e.left_inv hys] at hy'
  have key := mul_le_inner_of_forall_mul_norm_sq_le ha hC.le hc
    (fun v ↦ (g.norm_sq y v ▸ (hAg y hy v).1)) (fun v ↦ (g.norm_sq y v ▸ (hAg y hy v).2)) hD hy'
  rw [← g.norm_sq, ← inner_mgradient]
  exact key

/-- **The gradient-like inequality on a normed space.** If `X` is gradient-like for `f` near `x`
on a finite-dimensional real normed space `E`, then `c * (‖X y‖ ^ 2 + ‖df_y‖ ^ 2) ≤ df_y (X y)`
for some `c > 0` and every `y` near `x`, for the norm of `E` and the operator norm. The converse
is `TauCeti.isGradientLikeAt_of_eventually_mul_le`. -/
theorem IsGradientLikeAt.exists_pos_eventually_mul_le {f : E → ℝ} {X : E → E} {x : E}
    (hX : IsGradientLikeAt f (fun x ↦ X x : (x : E) → TangentSpace 𝓘(ℝ, E) x) x) :
    ∃ c > 0, ∀ᶠ y in 𝓝 x, c * (‖X y‖ ^ 2 + ‖fderiv ℝ f y‖ ^ 2) ≤ fderiv ℝ f y (X y) := by
  obtain ⟨r₀, hr₀, c, hc, -, h⟩ := hX.exists_mul_le_fderiv_comp_symm
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) x) (mem_chart_source E x)
  refine ⟨c, hc, Filter.mem_of_superset (Metric.ball_mem_nhds _ hr₀) fun y hy ↦ ?_⟩
  have hA (z v : E) : mvfderiv 𝓘(ℝ, E) (chartAt E x) z v = v := by
    refine (mvfderiv_eq_fderiv_apply (𝕜 := ℝ) _ z v).trans ?_
    rw [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, fderiv_id,
      ContinuousLinearMap.id_apply]
  have h := h y hy
  rw [hA] at h
  simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
    Function.comp_id, id_eq, Set.mem_ofPred_eq] using h

end TauCeti
