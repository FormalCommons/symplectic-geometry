/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.BirthDeath.Basic
public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
import SymplecticGeometry.Analysis.Calculus.MeanValue
import SymplecticGeometry.Geometry.Manifold.Morse.LocalCoordinates
import SymplecticGeometry.Geometry.Manifold.Morse.RadialEstimate

/-!
# Gradient-like and primitive estimates in a birth–death chart

Let `X` be gradient-like near `p` for two functions `f` and `f'` with `f' p = f p`, and read
everything in a chart `e` centred at `p`, with `f̃ = f ∘ e.symm`, `f̃' = f' ∘ e.symm` and `X̃` the
push-forward of `X`. On a ball `B(0, r₀)` there are then constants `c > 0` and `A ≥ 0` with

* `c (‖X̃ z‖² + ‖Df̃(z)‖²) ≤ Df̃(z) (X̃ z)`, and the same for `f̃'`;
* `|f̃'(z) - f̃(z)| ≤ A ‖z‖ ‖Df̃(z)‖`,

provided that `f̃` agrees on the target of `e` with a differentiable function whose derivative
grows at most by a constant factor towards the origin. This holds in a birth–death chart, where
that function is the normal form `TauCeti.BirthDeathChart.normalForm`. These are the hypotheses of
`SymplecticGeometry.exists_contDiff_tsupport_subset_ball_mul_le_fderiv_add_smul_mul_apply`, with
`H = f̃' - f̃`, which cuts `t H` off without losing the gradient-like inequality, as in the proofs
of Proposition 9.23 and Lemma 12.9 of [CieliebakEliashberg2012].

The first two estimates are `TauCeti.IsGradientLikeAt.exists_mul_le_fderiv_comp_symm`. They give
`c ‖X̃‖ ≤ ‖Df̃‖` and `c ‖Df̃'‖ ≤ ‖X̃‖`, hence `‖D(f̃' - f̃)‖ ≤ (1 + 1 / c²) ‖Df̃‖`
(`SymplecticGeometry.norm_sub_le_of_mul_le_apply`), and the mean value inequality along rays
(`SymplecticGeometry.norm_le_mul_norm_mul_norm_fderiv_of_norm_fderiv_le`) gives the third.

## Main results

* `SymplecticGeometry.mul_norm_le_norm_and_mul_norm_le_of_mul_le_apply`: a functional `D` that
  satisfies the gradient-like inequality for a vector `x` has `c ‖x‖ ≤ ‖D‖` and `c ‖D‖ ≤ ‖x‖`.
* `SymplecticGeometry.norm_sub_le_of_mul_le_apply`: two functionals that satisfy the
  gradient-like inequality for the same vector are close relative to the first one.
* `TauCeti.IsGradientLikeAt.exists_abs_sub_le_mul_norm_mul_norm_fderiv_comp_symm`: the three
  estimates in a chart in which `f` has a model with a radially controlled derivative.
* `TauCeti.BirthDeathChart.exists_abs_sub_le_mul_norm_mul_norm_fderiv_comp_symm`: the three
  estimates in a birth–death chart.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 9.23 and Lemma 12.9
-/

public section

open Set Metric Filter
open scoped ContDiff Manifold Topology
open TauCeti.Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If a functional `D` satisfies the gradient-like inequality `c (‖x‖² + ‖D‖²) ≤ D x` for a
vector `x` and some `c > 0`, then `c ‖x‖ ≤ ‖D‖` and `c ‖D‖ ≤ ‖x‖`. -/
theorem mul_norm_le_norm_and_mul_norm_le_of_mul_le_apply {D : E →L[ℝ] ℝ} {x : E} {c : ℝ}
    (hc : 0 < c) (h : c * (‖x‖ ^ 2 + ‖D‖ ^ 2) ≤ D x) : c * ‖x‖ ≤ ‖D‖ ∧ c * ‖D‖ ≤ ‖x‖ := by
  have hD : D x ≤ ‖D‖ * ‖x‖ := (le_abs_self _).trans (D.le_opNorm x)
  constructor
  · rcases (norm_nonneg x).eq_or_lt with hx | hx
    · rw [← hx, mul_zero]; exact norm_nonneg _
    · exact le_of_mul_le_mul_right (by nlinarith [sq_nonneg ‖D‖]) hx
  · rcases (norm_nonneg D).eq_or_lt with hx | hx
    · rw [← hx, mul_zero]; exact norm_nonneg _
    · exact le_of_mul_le_mul_right (by nlinarith [sq_nonneg ‖x‖]) hx

/-- If two functionals `D` and `D'` satisfy the gradient-like inequality
`c (‖x‖² + ‖D‖²) ≤ D x` for the same vector `x` and the same `c > 0`, then
`‖D' - D‖ ≤ (1 + 1 / c²) ‖D‖`. -/
theorem norm_sub_le_of_mul_le_apply {D D' : E →L[ℝ] ℝ} {x : E} {c : ℝ} (hc : 0 < c)
    (h : c * (‖x‖ ^ 2 + ‖D‖ ^ 2) ≤ D x) (h' : c * (‖x‖ ^ 2 + ‖D'‖ ^ 2) ≤ D' x) :
    ‖D' - D‖ ≤ (1 + 1 / c ^ 2) * ‖D‖ := by
  have h₁ := (mul_norm_le_norm_and_mul_norm_le_of_mul_le_apply hc h).1
  have h₂ := (mul_norm_le_norm_and_mul_norm_le_of_mul_le_apply hc h').2
  have h₃ : ‖D'‖ ≤ ‖D‖ / c ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc ‖D' - D‖ ≤ ‖D'‖ + ‖D‖ := norm_sub_le _ _
    _ ≤ ‖D‖ / c ^ 2 + ‖D‖ := by gcongr
    _ = (1 + 1 / c ^ 2) * ‖D‖ := by ring

end SymplecticGeometry

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f f' : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M}

/-- **The gradient-like and primitive estimates in a chart.** Let `X` be gradient-like near `p`
for `f` and for `f'`, with `f' p = f p` and `f'` differentiable near `p`, and let `e` be a chart of
the maximal atlas with `e p = 0`. Write `f̃ = f ∘ e.symm`, `f̃' = f' ∘ e.symm` and
`X̃ z = de_{e.symm z} (X (e.symm z))`. Suppose that `f̃` agrees on the target of `e` with a
differentiable `F : E → ℝ` with `‖DF(s z)‖ ≤ K ‖DF(z)‖` for `s ∈ [0, 1]` and some `K ≥ 0`. Then
there are `r₀ > 0`, `c > 0` and `A ≥ 0` such that the ball `B(0, r₀)` lies in the target of `e`,
`f̃` and `f̃'` are differentiable on it, and for every `z` in it
* `c (‖X̃ z‖² + ‖Df̃(z)‖²) ≤ Df̃(z) (X̃ z)`,
* `c (‖X̃ z‖² + ‖Df̃'(z)‖²) ≤ Df̃'(z) (X̃ z)`,
* `|f̃'(z) - f̃(z)| ≤ A ‖z‖ ‖Df̃(z)‖`. -/
theorem IsGradientLikeAt.exists_abs_sub_le_mul_norm_mul_norm_fderiv_comp_symm
    (hX : IsGradientLikeAt f X p) (hX' : IsGradientLikeAt f' X p)
    (hf' : ∀ᶠ y in 𝓝 p, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f' y) (hff' : f' p = f p)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hp : p ∈ e.source) (hep : e p = 0) {F : E → ℝ} (hF : Differentiable ℝ F)
    (hfF : EqOn (f ∘ e.symm) F e.target) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ z : E, ∀ s ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ F (s • z)‖ ≤ K * ‖fderiv ℝ F z‖) :
    ∃ r₀ > 0, ∃ c > 0, ∃ A ≥ 0, ball 0 r₀ ⊆ e.target ∧
      DifferentiableOn ℝ (f ∘ e.symm) (ball 0 r₀) ∧
      DifferentiableOn ℝ (f' ∘ e.symm) (ball 0 r₀) ∧
      (∀ z ∈ ball (0 : E) r₀,
        c * (‖mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))‖ ^ 2 +
            ‖fderiv ℝ (f ∘ e.symm) z‖ ^ 2) ≤
          fderiv ℝ (f ∘ e.symm) z (mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z)))) ∧
      (∀ z ∈ ball (0 : E) r₀,
        c * (‖mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))‖ ^ 2 +
            ‖fderiv ℝ (f' ∘ e.symm) z‖ ^ 2) ≤
          fderiv ℝ (f' ∘ e.symm) z (mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z)))) ∧
      ∀ z ∈ ball (0 : E) r₀,
        |f' (e.symm z) - f (e.symm z)| ≤ A * ‖z‖ * ‖fderiv ℝ (f ∘ e.symm) z‖ := by
  obtain ⟨r₁, hr₁, c₁, hc₁, hr₁t, h₁⟩ := hX.exists_mul_le_fderiv_comp_symm he hp
  obtain ⟨r₂, hr₂, c₂, hc₂, -, h₂⟩ := hX'.exists_mul_le_fderiv_comp_symm he hp
  rw [hep] at hr₁t h₁ h₂
  -- A ball around `0` that `e.symm` maps to where `f'` is differentiable.
  have hn : e.symm ⁻¹' {y | MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f' y} ∈ 𝓝 (0 : E) := by
    rw [← hep]
    exact (e.continuousAt_symm (e.map_source hp)).preimage_mem_nhds (by rwa [e.left_inv hp])
  obtain ⟨r₃, hr₃, hball⟩ := Metric.mem_nhds_iff.1 hn
  set r₀ := min (min r₁ r₂) r₃
  set c := min c₁ c₂
  have hc : 0 < c := lt_min hc₁ hc₂
  have hs₁ : ball (0 : E) r₀ ⊆ ball 0 r₁ := ball_subset_ball ((min_le_left _ _).trans
    (min_le_left _ _))
  have hs₂ : ball (0 : E) r₀ ⊆ ball 0 r₂ := ball_subset_ball ((min_le_left _ _).trans
    (min_le_right _ _))
  have hs₃ : ball (0 : E) r₀ ⊆ ball 0 r₃ := ball_subset_ball (min_le_right _ _)
  have hst : ball (0 : E) r₀ ⊆ e.target := hs₁.trans hr₁t
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  -- `f̃` is `F` near every point of the target, so it is differentiable there with the same
  -- derivative.
  have hfF' {z : E} (hz : z ∈ e.target) : f ∘ e.symm =ᶠ[𝓝 z] F :=
    eventuallyEq_of_mem (e.open_target.mem_nhds hz) hfF
  have hdf : DifferentiableOn ℝ (f ∘ e.symm) (ball 0 r₀) := fun z hz ↦
    ((hF z).congr_of_eventuallyEq (hfF' (hst hz))).differentiableWithinAt
  have hdf' : DifferentiableOn ℝ (f' ∘ e.symm) (ball 0 r₀) := fun z hz ↦
    (mdifferentiableAt_iff_differentiableAt.1 ((hball (hs₃ hz)).comp z
      (mdifferentiableAt_symm_of_mem_maximalAtlas he1 (hst hz)))).differentiableWithinAt
  have hle₁ : ∀ z ∈ ball (0 : E) r₀,
      c * (‖mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))‖ ^ 2 +
          ‖fderiv ℝ (f ∘ e.symm) z‖ ^ 2) ≤
        fderiv ℝ (f ∘ e.symm) z (mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))) :=
    fun z hz ↦ (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
      (h₁ z (hs₁ hz))
  have hle₂ : ∀ z ∈ ball (0 : E) r₀,
      c * (‖mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))‖ ^ 2 +
          ‖fderiv ℝ (f' ∘ e.symm) z‖ ^ 2) ≤
        fderiv ℝ (f' ∘ e.symm) z (mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))) :=
    fun z hz ↦ (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans
      (h₂ z (hs₂ hz))
  refine ⟨r₀, lt_min (lt_min hr₁ hr₂) hr₃, c, hc, (1 + 1 / c ^ 2) * K, by positivity, hst, hdf,
    hdf', hle₁, hle₂, fun z hz ↦ ?_⟩
  -- The primitive estimate for `H = f̃' - f̃`.
  have hH0 : (f' ∘ e.symm - f ∘ e.symm) 0 = 0 := by
    simp [← hep, e.left_inv hp, hff']
  have hDH : ∀ w ∈ ball (0 : E) r₀, ‖fderiv ℝ (f' ∘ e.symm - f ∘ e.symm) w‖ ≤
      (1 + 1 / c ^ 2) * ‖fderiv ℝ (f ∘ e.symm) w‖ := fun w hw ↦ by
    rw [fderiv_sub ((hdf' w hw).differentiableAt (isOpen_ball.mem_nhds hw))
      ((hdf w hw).differentiableAt (isOpen_ball.mem_nhds hw))]
    exact SymplecticGeometry.norm_sub_le_of_mul_le_apply hc (hle₁ w hw) (hle₂ w hw)
  have hrad : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (f ∘ e.symm) (s • z)‖ ≤ K * ‖fderiv ℝ (f ∘ e.symm) z‖ := fun s hs ↦ by
    have hsz : s • z ∈ ball (0 : E) r₀ :=
      (convex_ball (0 : E) r₀).smul_mem_of_zero_mem (mem_ball_self (pos_of_mem_ball hz)) hz hs
    rw [(hfF' (hst hsz)).fderiv_eq, (hfF' (hst hz)).fderiv_eq]
    exact hK z s hs
  have := SymplecticGeometry.norm_le_mul_norm_mul_norm_fderiv_of_norm_fderiv_le hz hrad
    (hdf'.sub hdf) hH0 hDH
  simpa [Real.norm_eq_abs] using this

/-- **The gradient-like and primitive estimates in a birth–death chart.** Let `X` be gradient-like
near `p` for `f` and for `f'`, with `f' p = f p` and `f'` differentiable near `p`, and let `φ` be a
birth–death chart for `f` at `p`, with chart `e`. Write `f̃ = f ∘ e.symm`, `f̃' = f' ∘ e.symm` and
`X̃ z = de_{e.symm z} (X (e.symm z))`. Then there are `r₀ > 0`, `c > 0` and `A ≥ 0` such that the
ball `B(0, r₀)` lies in the target of `e`, `f̃` and `f̃'` are differentiable on it, and for every
`z` in it
* `c (‖X̃ z‖² + ‖Df̃(z)‖²) ≤ Df̃(z) (X̃ z)`,
* `c (‖X̃ z‖² + ‖Df̃'(z)‖²) ≤ Df̃'(z) (X̃ z)`,
* `|f̃'(z) - f̃(z)| ≤ A ‖z‖ ‖Df̃(z)‖`. -/
theorem BirthDeathChart.exists_abs_sub_le_mul_norm_mul_norm_fderiv_comp_symm
    (φ : BirthDeathChart E f p) (hX : IsGradientLikeAt f X p) (hX' : IsGradientLikeAt f' X p)
    (hf' : ∀ᶠ y in 𝓝 p, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f' y) (hff' : f' p = f p) :
    ∃ r₀ > 0, ∃ c > 0, ∃ A ≥ 0, ball 0 r₀ ⊆ φ.toMorseBottChart.toChart.target ∧
      DifferentiableOn ℝ (f ∘ φ.toMorseBottChart.toChart.symm) (ball 0 r₀) ∧
      DifferentiableOn ℝ (f' ∘ φ.toMorseBottChart.toChart.symm) (ball 0 r₀) ∧
      (∀ z ∈ ball (0 : E) r₀,
        c * (‖mvfderiv 𝓘(ℝ, E) φ.toMorseBottChart.toChart (φ.toMorseBottChart.toChart.symm z)
              (X (φ.toMorseBottChart.toChart.symm z))‖ ^ 2 +
            ‖fderiv ℝ (f ∘ φ.toMorseBottChart.toChart.symm) z‖ ^ 2) ≤
          fderiv ℝ (f ∘ φ.toMorseBottChart.toChart.symm) z
            (mvfderiv 𝓘(ℝ, E) φ.toMorseBottChart.toChart (φ.toMorseBottChart.toChart.symm z)
              (X (φ.toMorseBottChart.toChart.symm z)))) ∧
      (∀ z ∈ ball (0 : E) r₀,
        c * (‖mvfderiv 𝓘(ℝ, E) φ.toMorseBottChart.toChart (φ.toMorseBottChart.toChart.symm z)
              (X (φ.toMorseBottChart.toChart.symm z))‖ ^ 2 +
            ‖fderiv ℝ (f' ∘ φ.toMorseBottChart.toChart.symm) z‖ ^ 2) ≤
          fderiv ℝ (f' ∘ φ.toMorseBottChart.toChart.symm) z
            (mvfderiv 𝓘(ℝ, E) φ.toMorseBottChart.toChart (φ.toMorseBottChart.toChart.symm z)
              (X (φ.toMorseBottChart.toChart.symm z)))) ∧
      ∀ z ∈ ball (0 : E) r₀,
        |f' (φ.toMorseBottChart.toChart.symm z) - f (φ.toMorseBottChart.toChart.symm z)| ≤
          A * ‖z‖ * ‖fderiv ℝ (f ∘ φ.toMorseBottChart.toChart.symm) z‖ := by
  set e := φ.toMorseBottChart.toChart
  obtain ⟨K, hK0, hK⟩ := φ.exists_norm_fderiv_normalForm_smul_le
  refine hX.exists_abs_sub_le_mul_norm_mul_norm_fderiv_comp_symm hX' hf' hff'
    φ.toMorseBottChart.mem_maximalAtlas φ.toMorseBottChart.mem_source
    φ.toMorseBottChart.apply_self (φ.contDiff_normalForm.differentiable (by simp))
    (fun z hz ↦ ?_) hK0 hK
  have := φ.eqOn_normalForm (e.map_target hz)
  rwa [Function.comp_apply, e.right_inv hz] at this

end TauCeti

end
