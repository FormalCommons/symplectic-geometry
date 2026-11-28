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
import SymplecticGeometry.Geometry.Manifold.Riemannian.PullbackPartialDiffeomorph
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# The gradient-like inequality in local coordinates

Let `X` be gradient-like for `f : M → ℝ` near a point `p` (`TauCeti.IsGradientLikeAt`), and let
`e` be a chart of the maximal atlas at `p`. Read in `e`, with `f̃ = f ∘ e.symm` and `X̃` the field
`X` pushed forward by `de`, the gradient-like inequality holds near `e p` with the norm of the model
space `E` in place of the Riemannian metric:
`c * (‖X̃ z‖ ^ 2 + ‖df̃_z‖ ^ 2) ≤ df̃_z (X̃ z)` for some `c > 0` and every `z` in a ball around
`e p`. This is the form in which the local estimates of Cieliebak–Eliashberg's Proposition 9.23,
in a Morse or a birth–death chart, use the gradient-like condition.

## Main results

* `TauCeti.IsGradientLikeAt.exists_mul_le_fderiv_comp_symm`: the inequality in a chart.
* `TauCeti.IsGradientLikeAt.exists_pos_eventually_mul_le`: on a normed space, the case of the
  identity chart, with the norm of the space near the point.

## Implementation notes

On a compact neighbourhood `K` of `p` in the source of `e`, the metric `g` of the hypothesis is
compared with the forms `(v, w) ↦ ⟪T (de_y v), T (de_y w)⟫`, where `T = toEuclidean`. These are
the pull-back along `e` of the metric `SymplecticGeometry.riemannianMetricToEuclidean E` that
`toEuclidean` carries to `E`; they are continuous and positive definite on the source of
`e` (`PartialDiffeomorph.contMDiffOn_pullback`, `PartialDiffeomorph.pullback_apply_self_pos`), so
Tau Ceti's `IsCompact.exists_pos_forall_mul_norm_sq_le_bundle` and
`IsCompact.exists_bound_of_continuousOn_bilinear_bundle` bound them above and below by the norm of
`g` on `K`. The differential of `f̃` is that of `f` composed with `d(e.symm)`, by the chain rule
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

omit [FiniteDimensional ℝ E] in
/-- The pointwise step of `TauCeti.IsGradientLikeAt.exists_mul_le_fderiv_comp_symm`. Let `A : V → E`
and `B : E → V` be mutually inverse, with `a ‖v‖ ^ 2 ≤ ‖T (A v)‖ ^ 2 ≤ C ‖v‖ ^ 2` and `T` bounded
above and below, and let `D = ⟪G, B ·⟫`. If `c (‖x‖ ^ 2 + ‖G‖ ^ 2) ≤ ⟪G, x⟫`, then the same
inequality holds for `A x` and `D`, with an explicit smaller constant. -/
private theorem mul_le_apply_of_forall_mul_norm_sq_le {V F : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] {A : V →L[ℝ] E}
    {B : E →L[ℝ] V} {T : E →L[ℝ] F} {D : E →L[ℝ] ℝ} {G x : V} {a C L K' c : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hc : 0 < c) (hAB : ∀ u, A (B u) = u) (hBA : ∀ v, B (A v) = v)
    (hL : ∀ u, ‖T u‖ ≤ L * ‖u‖) (hK' : ∀ u, ‖u‖ ≤ K' * ‖T u‖)
    (hlow : ∀ v, a * ‖v‖ ^ 2 ≤ ‖T (A v)‖ ^ 2) (hup : ∀ v, ‖T (A v)‖ ^ 2 ≤ C * ‖v‖ ^ 2)
    (hD : ∀ u, D u = inner ℝ G (B u)) (h : c * (‖x‖ ^ 2 + ‖G‖ ^ 2) ≤ inner ℝ G x) :
    c / (K' ^ 2 * C + L ^ 2 / a + 1) * (‖A x‖ ^ 2 + ‖D‖ ^ 2) ≤ D (A x) := by
  have h₁ : ‖A x‖ ^ 2 ≤ K' ^ 2 * C * ‖x‖ ^ 2 := by
    calc ‖A x‖ ^ 2 ≤ (K' * ‖T (A x)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hK' _) 2
      _ = K' ^ 2 * ‖T (A x)‖ ^ 2 := by ring
      _ ≤ K' ^ 2 * (C * ‖x‖ ^ 2) := by gcongr; exact hup _
      _ = _ := by ring
  -- `‖B u‖ ^ 2 ≤ (L ^ 2 / a) ‖u‖ ^ 2`, so `‖D‖ ^ 2 ≤ (L ^ 2 / a) ‖G‖ ^ 2`.
  have hB (u : E) : ‖B u‖ ^ 2 ≤ L ^ 2 / a * ‖u‖ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha, mul_comm]
    calc a * ‖B u‖ ^ 2 ≤ ‖T (A (B u))‖ ^ 2 := hlow _
      _ ≤ (L * ‖u‖) ^ 2 := by rw [hAB]; exact pow_le_pow_left₀ (norm_nonneg _) (hL u) 2
      _ = _ := by ring
  have h₂ : ‖D‖ ^ 2 ≤ L ^ 2 / a * ‖G‖ ^ 2 := by
    have hbd : ‖D‖ ≤ Real.sqrt (L ^ 2 / a) * ‖G‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
      rw [hD u, Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      have := Real.sqrt_le_sqrt (hB u)
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity),
        Real.sqrt_sq (norm_nonneg _)] at this
      calc ‖G‖ * ‖B u‖ ≤ ‖G‖ * (Real.sqrt (L ^ 2 / a) * ‖u‖) := by gcongr
        _ = _ := by ring
    calc _ ≤ (Real.sqrt (L ^ 2 / a) * ‖G‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbd 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hD, hBA]
  calc c / (K' ^ 2 * C + L ^ 2 / a + 1) * (‖A x‖ ^ 2 + ‖D‖ ^ 2)
      ≤ c / (K' ^ 2 * C + L ^ 2 / a + 1) *
          ((K' ^ 2 * C + L ^ 2 / a + 1) * (‖x‖ ^ 2 + ‖G‖ ^ 2)) := by
        gcongr
        have h₄ : 0 ≤ K' ^ 2 * C := by positivity
        have h₅ : 0 ≤ L ^ 2 / a := by positivity
        nlinarith [mul_nonneg h₄ (sq_nonneg ‖G‖), mul_nonneg h₅ (sq_nonneg ‖x‖)]
    _ = c * (‖x‖ ^ 2 + ‖G‖ ^ 2) := by field_simp
    _ ≤ _ := h

/-- **The gradient-like inequality in a chart.** Let `X` be gradient-like for `f` near `p`, and
let `e` be a chart of the maximal atlas whose source contains `p`. Write `f̃ = f ∘ e.symm` and
`X̃ z = de_{e.symm z} (X (e.symm z))`. Then there are `r₀ > 0` and `c > 0` such that the ball of
radius `r₀` around `e p` lies in the target of `e`, and
`c * (‖X̃ z‖ ^ 2 + ‖df̃_z‖ ^ 2) ≤ df̃_z (X̃ z)` on it, for the norm of `E` and the operator norm. -/
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
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  -- A compact neighbourhood `K` of `p` in the source of `e` on which the hypothesis holds.
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds
    (Filter.inter_mem hU (e.open_source.mem_nhds hp))
  -- The metric that `T = toEuclidean` carries to `E`.
  set T := toEuclidean (E := E)
  set g₀ : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E)) :=
    (SymplecticGeometry.riemannianMetricToEuclidean E).ofLE le_top
  have hg₀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x) : g₀.inner x v w = inner ℝ (T v) (T w) := by
    rw [ContMDiffRiemannianMetric.ofLE_inner]
    exact SymplecticGeometry.riemannianMetricToEuclidean_inner x v w
  obtain ⟨L, hL⟩ : ∃ L, ∀ v, ‖T v‖ ≤ L * ‖v‖ := ⟨_, T.toContinuousLinearMap.le_opNorm⟩
  obtain ⟨K', hK'⟩ : ∃ K', ∀ v, ‖v‖ ≤ K' * ‖T v‖ :=
    ⟨_, fun v ↦ by simpa using T.symm.toContinuousLinearMap.le_opNorm (T v)⟩
  -- The pull-back of `g₀` along `e`, compared with `g` on `K`.
  set Ψ := e.toPartialDiffeomorph he
  have hΨs : Ψ.source = e.source :=
    congrArg PartialEquiv.source (e.toPartialDiffeomorph_toPartialEquiv he)
  have hΨ : (Ψ : M → E) = e := e.coe_toPartialDiffeomorph he
  have hφ := Ψ.contMDiffOn_pullback g₀ (by simp)
  obtain ⟨a, ha, hlow⟩ := hKc.exists_pos_forall_mul_norm_sq_le_bundle (b := id)
    (hφ.continuousOn.mono fun y hy ↦ hΨs ▸ (hKU hy).2)
    fun y hy v hv ↦ Ψ.pullback_apply_self_pos g₀ (by simp) (hΨs ▸ (hKU hy).2) hv
  obtain ⟨C, hup⟩ := hKc.exists_bound_of_continuousOn_bilinear_bundle (b := id)
    (hφ.continuousOn.mono fun y hy ↦ hΨs ▸ (hKU hy).2)
  -- A ball around `e p` that `e.symm` maps into `K`.
  have hKn : e.symm ⁻¹' K ∈ 𝓝 (e p) :=
    (e.continuousAt_symm (e.map_source hp)).preimage_mem_nhds (by rwa [e.left_inv hp])
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.1
    (Filter.inter_mem hKn (e.open_target.mem_nhds (e.map_source hp)))
  refine ⟨r₀, hr₀, c / (K' ^ 2 * max C 0 + L ^ 2 / a + 1), by positivity,
    fun z hz ↦ (hball hz).2, fun z hz ↦ ?_⟩
  obtain ⟨hzK, hzt⟩ := hball hz
  set y := e.symm z
  have hyU := (hKU (show y ∈ K from hzK)).1
  set A := mvfderiv 𝓘(ℝ, E) e y
  set B := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z
  have he₁ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hAB (u : E) : A (B u) = u := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact e.mfderiv_apply_mfderiv_symm_apply_of_mem_maximalAtlas he₁ hzt u
  have hBA (v : TangentSpace 𝓘(ℝ, E) y) : B (A v) = v := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact e.mfderiv_symm_apply_mfderiv_apply_of_mem_maximalAtlas he₁ hzt v
  -- The pulled-back form at `y` is `v ↦ ‖T (A v)‖ ^ 2`.
  have hφy (v : TangentSpace 𝓘(ℝ, E) y) :
      (ContinuousLinearMap.precomp ℝ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ y)).comp
        ((g₀.inner (Ψ y)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ y)) v v = ‖T (A v)‖ ^ 2 := by
    rw [hΨ]
    simp [hg₀, A]
  have hlow' (v : TangentSpace 𝓘(ℝ, E) y) : a * ‖v‖ ^ 2 ≤ ‖T (A v)‖ ^ 2 :=
    (hlow y hzK v).trans_eq (hφy v)
  have hup' (v : TangentSpace 𝓘(ℝ, E) y) : ‖T (A v)‖ ^ 2 ≤ max C 0 * ‖v‖ ^ 2 := by
    rw [← hφy]
    calc _ ≤ ‖_‖ := Real.le_norm_self _
      _ ≤ _ := ContinuousLinearMap.le_opNorm₂ _ v v
      _ ≤ max C 0 * ‖v‖ ^ 2 := by
        rw [mul_assoc, ← sq]
        exact mul_le_mul_of_nonneg_right ((hup y hzK).trans (le_max_left _ _)) (sq_nonneg _)
  -- The differential of `f̃` is that of `f` composed with `B`.
  have hD (u : E) : fderiv ℝ (f ∘ e.symm) z u = mvfderiv 𝓘(ℝ, E) f y (B u) := by
    have h := (e.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas he hzt).mfderiv_comp
      (I' := 𝓘(ℝ)) (by simp) f
    rw [← mvfderiv_eq_fderiv_apply (f ∘ e.symm) z u,
      mvfderiv_apply_eq_mfderiv_apply (f ∘ e.symm) z u, h]
    -- The composite of continuous linear maps, applied to `u`.
    exact (mvfderiv_apply_eq_mfderiv_apply f y (B u)).symm
  have hH := H y hyU
  rw [← g.norm_sq, ← inner_mgradient] at hH
  exact mul_le_apply_of_forall_mul_norm_sq_le (T := T.toContinuousLinearMap) ha (le_max_right C 0)
    hc hAB hBA hL hK' hlow' hup' (fun u ↦ (hD u).trans (inner_mgradient _).symm) hH

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
