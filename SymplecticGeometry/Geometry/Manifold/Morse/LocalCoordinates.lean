/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import SymplecticGeometry.Geometry.Manifold.Riemannian.PartialDiffeomorph

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

## Implementation notes

On a compact subset `K` of the source of `e`, the differential `de_y` is bounded above and below,
from the Riemannian norm of a metric `g` to the norm of `E`
(`PartialDiffeomorph.exists_mul_norm_le_norm_mvfderiv_le`, for `e` as a partial
diffeomorphism). Both directions use this comparison, the first with the metric of the
hypothesis and the converse with any smooth metric (`TauCeti.nonempty_contMDiffRiemannianMetric`).
The differential of `f̃` is that of `f` composed with `d(e.symm)`
(`OpenPartialHomeomorph.fderiv_comp_symm_apply_of_mem_maximalAtlas`), with no differentiability
of `f` needed, and `d(e.symm)` undoes `de`.

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
and `B : E → V` be mutually inverse, with `a ‖v‖ ≤ ‖A v‖ ≤ C ‖v‖`, and let `D = ⟪G, B ·⟫`. If
`c (‖x‖ ^ 2 + ‖G‖ ^ 2) ≤ ⟪G, x⟫`, then the same inequality holds for `A x` and `D`, with the
smaller constant `c / (C ^ 2 + 1 / a ^ 2 + 1)`. -/
private theorem mul_le_apply_of_forall_mul_norm_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {A : V →L[ℝ] E} {B : E →L[ℝ] V} {D : E →L[ℝ] ℝ} {G x : V}
    {a C c : ℝ} (ha : 0 < a) (hc : 0 < c) (hAB : ∀ u, A (B u) = u) (hBA : ∀ v, B (A v) = v)
    (hlow : ∀ v, a * ‖v‖ ≤ ‖A v‖) (hup : ∀ v, ‖A v‖ ≤ C * ‖v‖)
    (hD : ∀ u, D u = inner ℝ G (B u)) (h : c * (‖x‖ ^ 2 + ‖G‖ ^ 2) ≤ inner ℝ G x) :
    c / (C ^ 2 + 1 / a ^ 2 + 1) * (‖A x‖ ^ 2 + ‖D‖ ^ 2) ≤ D (A x) := by
  -- `a ‖B u‖ ≤ ‖A (B u)‖ = ‖u‖`, so `‖D‖ ≤ ‖G‖ / a`.
  have hB (u : E) : ‖B u‖ ≤ a⁻¹ * ‖u‖ := by
    rw [inv_mul_eq_div, le_div_iff₀ ha, mul_comm]
    exact (hlow (B u)).trans_eq (by rw [hAB])
  have h₂ : ‖D‖ ^ 2 ≤ 1 / a ^ 2 * ‖G‖ ^ 2 := by
    have hbd : ‖D‖ ≤ a⁻¹ * ‖G‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
      rw [hD u, Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖G‖ * ‖B u‖ ≤ ‖G‖ * (a⁻¹ * ‖u‖) := by gcongr; exact hB u
        _ = _ := by ring
    calc _ ≤ (a⁻¹ * ‖G‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbd 2
      _ = _ := by rw [mul_pow, inv_pow, one_div]
  have h₁ : ‖A x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hup x) 2
  rw [hD, hBA]
  calc c / (C ^ 2 + 1 / a ^ 2 + 1) * (‖A x‖ ^ 2 + ‖D‖ ^ 2)
      ≤ c / (C ^ 2 + 1 / a ^ 2 + 1) * ((C ^ 2 + 1 / a ^ 2 + 1) * (‖x‖ ^ 2 + ‖G‖ ^ 2)) := by
        gcongr
        have h₅ : 0 ≤ 1 / a ^ 2 := by positivity
        nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg ‖G‖), mul_nonneg h₅ (sq_nonneg ‖x‖),
          sq_nonneg ‖x‖, sq_nonneg ‖G‖]
    _ = c * (‖x‖ ^ 2 + ‖G‖ ^ 2) := by field_simp
    _ ≤ _ := h

omit [FiniteDimensional ℝ E] in
/-- The pointwise step of `TauCeti.isGradientLikeAt_of_mul_le_fderiv_comp_symm`, the converse of
`mul_le_apply_of_forall_mul_norm_le`. Let `A : V → E` be a linear map with
`a ‖v‖ ≤ ‖A v‖ ≤ C ‖v‖`, and let `D : E → ℝ` satisfy `D (A v) = ⟪G, v⟫`. If
`c (‖A x‖ ^ 2 + ‖D‖ ^ 2) ≤ D (A x)`, then
`c / (C ^ 2 + 1 / a ^ 2 + 1) (‖x‖ ^ 2 + ‖G‖ ^ 2) ≤ ⟪G, x⟫`. -/
private theorem mul_le_inner_of_forall_mul_norm_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {A : V →L[ℝ] E} {D : E →L[ℝ] ℝ} {G x : V} {a C c : ℝ} (ha : 0 < a)
    (hc : 0 < c) (hlow : ∀ v, a * ‖v‖ ≤ ‖A v‖) (hup : ∀ v, ‖A v‖ ≤ C * ‖v‖)
    (hD : ∀ v, D (A v) = inner ℝ G v) (h : c * (‖A x‖ ^ 2 + ‖D‖ ^ 2) ≤ D (A x)) :
    c / (C ^ 2 + 1 / a ^ 2 + 1) * (‖x‖ ^ 2 + ‖G‖ ^ 2) ≤ inner ℝ G x := by
  have h₁ : ‖x‖ ^ 2 ≤ 1 / a ^ 2 * ‖A x‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) (hlow x) 2
    rw [mul_pow] at this
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity), mul_comm]
    exact this
  -- `‖G‖ ^ 2 = D (A G) ≤ ‖D‖ ‖A G‖ ≤ C ‖D‖ ‖G‖`, so `‖G‖ ^ 2 ≤ C ^ 2 ‖D‖ ^ 2`.
  have h₂ : ‖G‖ ^ 2 ≤ C ^ 2 * ‖D‖ ^ 2 := by
    have hG : ‖G‖ ^ 2 ≤ ‖D‖ * (C * ‖G‖) := by
      calc ‖G‖ ^ 2 = D (A G) := by rw [hD, real_inner_self_eq_norm_sq]
        _ ≤ ‖D‖ * ‖A G‖ := (le_abs_self _).trans (D.le_opNorm _)
        _ ≤ _ := by gcongr; exact hup G
    rcases (norm_nonneg G).eq_or_lt with h0 | h0
    · rw [← h0, zero_pow two_ne_zero]
      positivity
    · have hG' : ‖G‖ ≤ C * ‖D‖ := by nlinarith
      calc _ ≤ (C * ‖D‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG' 2
        _ = _ := mul_pow _ _ _
  rw [← hD]
  calc c / (C ^ 2 + 1 / a ^ 2 + 1) * (‖x‖ ^ 2 + ‖G‖ ^ 2)
      ≤ c / (C ^ 2 + 1 / a ^ 2 + 1) * ((C ^ 2 + 1 / a ^ 2 + 1) * (‖A x‖ ^ 2 + ‖D‖ ^ 2)) := by
        gcongr
        have h₅ : 0 ≤ 1 / a ^ 2 := by positivity
        nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg ‖A x‖), mul_nonneg h₅ (sq_nonneg ‖D‖),
          sq_nonneg ‖A x‖, sq_nonneg ‖D‖]
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
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  have he₁ := IsManifold.maximalAtlas_subset_of_le (m := 1) (by simp) he
  -- A compact neighbourhood `K` of `p` in the source of `e` on which the hypothesis holds.
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds
    (Filter.inter_mem hU (e.open_source.mem_nhds hp))
  obtain ⟨a, C, ha, hAg⟩ := (e.toPartialDiffeomorph he).exists_mul_norm_le_norm_mvfderiv_le
    (by simp) hKc fun y hy ↦ by simpa using (hKU hy).2
  rw [e.coe_toPartialDiffeomorph he] at hAg
  -- A ball around `e p` that `e.symm` maps into `K`.
  have hKn : e.symm ⁻¹' K ∈ 𝓝 (e p) :=
    (e.continuousAt_symm (e.map_source hp)).preimage_mem_nhds (by rwa [e.left_inv hp])
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.1
    (Filter.inter_mem hKn (e.open_target.mem_nhds (e.map_source hp)))
  refine ⟨r₀, hr₀, c / (C ^ 2 + 1 / a ^ 2 + 1), by positivity, fun z hz ↦ (hball hz).2,
    fun z hz ↦ ?_⟩
  obtain ⟨hzK, hzt⟩ := hball hz
  have hH := H (e.symm z) (hKU (show e.symm z ∈ K from hzK)).1
  rw [← g.norm_sq, ← inner_mgradient] at hH
  refine mul_le_apply_of_forall_mul_norm_le (V := TangentSpace 𝓘(ℝ, E) (e.symm z))
    (A := mvfderiv 𝓘(ℝ, E) e (e.symm z)) (B := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z) ha hc
    (fun u ↦ ?_) (fun v ↦ ?_) (fun v ↦ (hAg _ hzK v).1) (fun v ↦ (hAg _ hzK v).2)
    (fun u ↦ (e.fderiv_comp_symm_apply_of_mem_maximalAtlas (by simp) he hzt f u).trans
      (inner_mgradient _).symm) hH
  · rw [mvfderiv_apply_eq_mfderiv_apply]
    exact e.mfderiv_apply_mfderiv_symm_apply_of_mem_maximalAtlas he₁ hzt u
  · rw [mvfderiv_apply_eq_mfderiv_apply]
    exact e.mfderiv_symm_apply_mfderiv_apply_of_mem_maximalAtlas he₁ hzt v

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
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  have he₁ := IsManifold.maximalAtlas_subset_of_le (m := 1) (by simp) he
  -- A compact neighbourhood `K` of `x` in the source of `e` that `e` maps into the ball.
  have hU : e.source ∩ e ⁻¹' ball (e x) r ∈ 𝓝 x :=
    (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball).mem_nhds
      ⟨hx, mem_ball_self hr⟩
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds hU
  obtain ⟨a, C, ha, hAg⟩ := (e.toPartialDiffeomorph he).exists_mul_norm_le_norm_mvfderiv_le
    (by simp) hKc fun y hy ↦ by simpa using (hKU hy).1
  rw [e.coe_toPartialDiffeomorph he] at hAg
  refine (isGradientLikeAt_def f X x).2
    ⟨K, hK, g, c / (C ^ 2 + 1 / a ^ 2 + 1), by positivity, fun y hy ↦ ?_⟩
  obtain ⟨hys, hyb⟩ := hKU hy
  have hzt : e y ∈ e.target := e.map_source hys
  -- The differential of `f̃` at `e y`, composed with that of `e`, is that of `f` at `y`.
  have hD (v : TangentSpace 𝓘(ℝ, E) y) :
      fderiv ℝ (f ∘ e.symm) (e y) (mvfderiv 𝓘(ℝ, E) e y v) =
        inner ℝ (mgradient 𝓘(ℝ, E) f y) v := by
    rw [e.fderiv_comp_symm_apply_of_mem_maximalAtlas (by simp) he hzt, inner_mgradient,
      mvfderiv_apply_eq_mfderiv_apply e y v,
      e.mfderiv_symm_apply_mfderiv_apply hys (mdifferentiableAt_of_mem_maximalAtlas he₁ hys)
        (mdifferentiableAt_symm_of_mem_maximalAtlas he₁ hzt) v,
      e.left_inv hys]
  have hy' := h (e y) hyb
  rw [e.left_inv hys] at hy'
  rw [← g.norm_sq, ← inner_mgradient]
  exact mul_le_inner_of_forall_mul_norm_le ha hc (fun v ↦ (hAg y hy v).1)
    (fun v ↦ (hAg y hy v).2) hD hy'

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
