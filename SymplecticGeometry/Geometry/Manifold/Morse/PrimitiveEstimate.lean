/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.GradientLike
public import SymplecticGeometry.Geometry.Symplectic.Liouville.Chart
public import TauCeti.Geometry.Manifold.Morse.Bott.Chart.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import SymplecticGeometry.Analysis.Normed.Operator.Functional
import SymplecticGeometry.Geometry.Manifold.Morse.ChartEstimates
import SymplecticGeometry.Geometry.Manifold.Morse.LocalCoordinates
import SymplecticGeometry.Geometry.Manifold.Morse.RadialEstimate

/-!
# The gradient-like and primitive estimates in a chart

Let `X` be gradient-like near `p` both for `f` and for `f'`, two functions with `f' p = f p`, and
read everything in a chart `e` at `p`: `f̃ = f ∘ e.symm`, `f̃' = f' ∘ e.symm`, and `X̃` the field
pushed forward by `de`. Near `e p`, both `f̃` and `f̃'` satisfy the gradient-like inequality
`c (‖X̃‖² + ‖Df̃‖²) ≤ Df̃ (X̃)` for the norm of the model space, with one constant `c > 0`
(`TauCeti.IsGradientLikeAt.exists_mul_le_fderiv_comp_symm`). Two such inequalities for the same
vector give `c ‖X̃‖ ≤ ‖Df̃‖` and `c ‖Df̃'‖ ≤ ‖X̃‖`, so the difference `H = f̃' - f̃` has
`‖DH‖ ≤ (1 + 1 / c²) ‖Df̃‖` (`ContinuousLinearMap.norm_sub_le_of_mul_le_apply`).

In a Morse–Bott chart (in particular a Morse chart, through `TauCeti.MorseChart.toMorseBottChart`),
`f̃` is the quadratic normal form, and the radial estimate
`TauCeti.MorseBottChart.norm_le_mul_norm_mul_norm_fderiv_quadratic` then bounds `H` itself:
`|H z| ≤ A ‖z‖ ‖Df̃ (z)‖`. These are the three hypotheses of the logarithmic cut-off
`SymplecticGeometry.exists_contDiff_tsupport_subset_ball_mul_le_fderiv_add_smul_mul_apply`, with
`f̃ + H = f̃'`; it moves the function from `f` to `f'` near `p` while `X` stays gradient-like, as
in the proof of Proposition 9.23 (a), and of Lemma 12.9, of [CieliebakEliashberg2012].

The same radial estimate gives the hypotheses of the cut-off step for two Liouville fields that
are gradient-like for `f` near `p`, in Lemma 12.9 of [CieliebakEliashberg2012]: the Hamiltonian
`H` of their difference, which vanishes at `p`, has `|H (e.symm z)| ≤ A ‖z‖ ‖Df̃ (z)‖` in a
Morse–Bott chart. This is the case `F = φ.quadratic`, `K = 1` of
`TauCeti.IsLiouvilleVectorField.exists_abs_comp_symm_le_mul_norm_mul_norm_fderiv`.

## Main results

* `TauCeti.IsGradientLikeAt.exists_norm_fderiv_sub_comp_symm_le`: the gradient-like inequalities
  for `f̃` and `f̃'` and the bound on `DH`, in any chart of the maximal atlas.
* `TauCeti.MorseBottChart.exists_abs_sub_comp_symm_le`: in a Morse–Bott chart, the gradient-like
  inequalities and the primitive estimate `|H z| ≤ A ‖z‖ ‖Df̃ (z)‖`.
* `TauCeti.MorseBottChart.exists_abs_comp_symm_le_mul_norm_mul_norm_fderiv`: in a Morse–Bott
  chart, for two Liouville fields, the gradient-like inequalities, the Hamiltonian reading of
  their difference, and the estimate on its Hamiltonian.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 9.23 and Lemma 12.9
-/

public section

open Set Metric Filter TopologicalSpace
open scoped ContDiff Manifold Topology
open TauCeti.Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **The gradient-like inequalities for two functions in a chart.** Let `X` be gradient-like
near `p` for `f` and for `f'`, both differentiable near `p`, and let `e` be a chart of the
maximal atlas whose source contains `p`. Write `f̃ = f ∘ e.symm`, `f̃' = f' ∘ e.symm` and
`X̃ z = de_{e.symm z} (X (e.symm z))`. Then there are `r₀ > 0` and `c > 0` such that the ball of
radius `r₀` around `e p` lies in the target of `e`, and at each `z` in it `f̃` and `f̃'` are
differentiable, both satisfy `c (‖X̃ z‖² + ‖Df̃_z‖²) ≤ Df̃_z (X̃ z)`, and
`‖D(f̃' - f̃)_z‖ ≤ (1 + 1 / c²) ‖Df̃_z‖`. -/
theorem IsGradientLikeAt.exists_norm_fderiv_sub_comp_symm_le {f f' : M → ℝ}
    {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M} (hX : IsGradientLikeAt f X p)
    (hX' : IsGradientLikeAt f' X p) (hf : ∀ᶠ y in 𝓝 p, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f y)
    (hf' : ∀ᶠ y in 𝓝 p, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f' y)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hp : p ∈ e.source) :
    ∃ r₀ > 0, ∃ c > 0, ball (e p) r₀ ⊆ e.target ∧ ∀ z ∈ ball (e p) r₀,
      DifferentiableAt ℝ (f ∘ e.symm) z ∧ DifferentiableAt ℝ (f' ∘ e.symm) z ∧
      c * (‖mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))‖ ^ 2 +
          ‖fderiv ℝ (f ∘ e.symm) z‖ ^ 2) ≤
        fderiv ℝ (f ∘ e.symm) z (mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))) ∧
      c * (‖mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))‖ ^ 2 +
          ‖fderiv ℝ (f' ∘ e.symm) z‖ ^ 2) ≤
        fderiv ℝ (f' ∘ e.symm) z (mvfderiv 𝓘(ℝ, E) e (e.symm z) (X (e.symm z))) ∧
      ‖fderiv ℝ (f' ∘ e.symm - f ∘ e.symm) z‖ ≤ (1 + 1 / c ^ 2) * ‖fderiv ℝ (f ∘ e.symm) z‖ := by
  obtain ⟨r₁, hr₁, c₁, hc₁, -, h₁⟩ := hX.exists_mul_le_fderiv_comp_symm he hp
  obtain ⟨r₂, hr₂, c₂, hc₂, -, h₂⟩ := hX'.exists_mul_le_fderiv_comp_symm he hp
  -- The points of the chart where `f` and `f'` are differentiable form a neighbourhood of `e p`.
  have hcont := e.continuousAt_symm (e.map_source hp)
  have hD : e.symm ⁻¹' {y | MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f y ∧
      MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f' y} ∈ 𝓝 (e p) :=
    hcont.preimage_mem_nhds (by rw [e.left_inv hp]; exact hf.and hf')
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (inter_mem (inter_mem
    (ball_mem_nhds _ hr₁) (ball_mem_nhds _ hr₂)) hD)
    (e.open_target.mem_nhds (e.map_source hp)))
  have he₁ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  -- The common constant.
  set c := min c₁ c₂
  have hc : 0 < c := lt_min hc₁ hc₂
  refine ⟨r₀, hr₀, c, hc, fun z hz ↦ (hball hz).2, fun z hz ↦ ?_⟩
  obtain ⟨⟨⟨hz₁, hz₂⟩, hfz, hf'z⟩, hzt⟩ := hball hz
  have hsymm := mdifferentiableAt_symm_of_mem_maximalAtlas he₁ hzt
  have hdf : DifferentiableAt ℝ (f ∘ e.symm) z := (hfz.comp z hsymm).differentiableAt
  have hdf' : DifferentiableAt ℝ (f' ∘ e.symm) z := (hf'z.comp z hsymm).differentiableAt
  -- Shrinking the constant keeps the inequalities, whose right sides are at least the left.
  have hmono {c' : ℝ} (hc' : c ≤ c') {a b : ℝ} (hab : c' * a ≤ b) (ha : 0 ≤ a) : c * a ≤ b :=
    (mul_le_mul_of_nonneg_right hc' ha).trans hab
  have i₁ := hmono (min_le_left _ _) (h₁ z hz₁) (by positivity)
  have i₂ := hmono (min_le_right _ _) (h₂ z hz₂) (by positivity)
  refine ⟨hdf, hdf', i₁, i₂, ?_⟩
  rw [fderiv_sub hdf' hdf]
  exact ContinuousLinearMap.norm_sub_le_of_mul_le_apply hc i₁ i₂

namespace MorseBottChart

/-- **The gradient-like and primitive estimates in a Morse–Bott chart.** Let `X` be gradient-like
near `p` for `f` and for `f'`, with `f'` differentiable near `p` and `f' p = f p`, and let `φ` be
a Morse–Bott chart of `f` at `p`, with chart `e`. Write `f̃ = f ∘ e.symm`, `f̃' = f' ∘ e.symm` and
`X̃ z = de_{e.symm z} (X (e.symm z))`. Then there are `r₀ > 0`, `c > 0` and `A ≥ 0` such that the
ball `B(0, r₀)` lies in the target of `e`, `f̃` and `f̃'` are differentiable on it, and for every
`z` in it
* `c (‖X̃ z‖² + ‖Df̃_z‖²) ≤ Df̃_z (X̃ z)`,
* `c (‖X̃ z‖² + ‖Df̃'_z‖²) ≤ Df̃'_z (X̃ z)`,
* `|f̃' z - f̃ z| ≤ A ‖z‖ ‖Df̃_z‖`.

With `H = f̃' - f̃`, these are the hypotheses of
`SymplecticGeometry.exists_contDiff_tsupport_subset_ball_mul_le_fderiv_add_smul_mul_apply`. -/
theorem exists_abs_sub_comp_symm_le {f f' : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    {p : M} (φ : MorseBottChart E f p) (hX : IsGradientLikeAt f X p)
    (hX' : IsGradientLikeAt f' X p) (hf' : ∀ᶠ y in 𝓝 p, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f' y)
    (hfp : f' p = f p) :
    ∃ r₀ > 0, ∃ c > 0, ∃ A ≥ 0, ball 0 r₀ ⊆ φ.toChart.target ∧
      DifferentiableOn ℝ (f ∘ φ.toChart.symm) (ball 0 r₀) ∧
      DifferentiableOn ℝ (f' ∘ φ.toChart.symm) (ball 0 r₀) ∧ ∀ z ∈ ball (0 : E) r₀,
      c * (‖mvfderiv 𝓘(ℝ, E) φ.toChart (φ.toChart.symm z) (X (φ.toChart.symm z))‖ ^ 2 +
          ‖fderiv ℝ (f ∘ φ.toChart.symm) z‖ ^ 2) ≤
        fderiv ℝ (f ∘ φ.toChart.symm) z
          (mvfderiv 𝓘(ℝ, E) φ.toChart (φ.toChart.symm z) (X (φ.toChart.symm z))) ∧
      c * (‖mvfderiv 𝓘(ℝ, E) φ.toChart (φ.toChart.symm z) (X (φ.toChart.symm z))‖ ^ 2 +
          ‖fderiv ℝ (f' ∘ φ.toChart.symm) z‖ ^ 2) ≤
        fderiv ℝ (f' ∘ φ.toChart.symm) z
          (mvfderiv 𝓘(ℝ, E) φ.toChart (φ.toChart.symm z) (X (φ.toChart.symm z))) ∧
      |(f' ∘ φ.toChart.symm) z - (f ∘ φ.toChart.symm) z| ≤
        A * ‖z‖ * ‖fderiv ℝ (f ∘ φ.toChart.symm) z‖ := by
  set e := φ.toChart
  have hf : ∀ᶠ y in 𝓝 p, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f y :=
    Filter.eventually_of_mem (e.open_source.mem_nhds φ.mem_source) fun y hy ↦
      (φ.contMDiffAt hy).mdifferentiableAt (by simp)
  obtain ⟨r₀, hr₀, c, hc, hsub, h⟩ :=
    hX.exists_norm_fderiv_sub_comp_symm_le hX' hf hf' φ.mem_maximalAtlas φ.mem_source
  rw [φ.apply_self] at hsub h
  -- On the target, `f̃` is the quadratic normal form.
  have hQ {z : E} (hz : z ∈ ball (0 : E) r₀) :
      fderiv ℝ (f ∘ e.symm) z = fderiv ℝ φ.quadratic z := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [e.open_target.mem_nhds (hsub hz)] with w hw
    rw [Function.comp_apply, φ.eqOn_quadratic (e.map_target hw), Function.comp_apply,
      e.right_inv hw]
  have hH : DifferentiableOn ℝ (f' ∘ e.symm - f ∘ e.symm) (ball 0 r₀) := fun z hz ↦
    ((h z hz).2.1.sub (h z hz).1).differentiableWithinAt
  have hH0 : (f' ∘ e.symm - f ∘ e.symm) 0 = 0 := by
    rw [Pi.sub_apply, Function.comp_apply, Function.comp_apply, φ.toChart_symm_zero, hfp,
      sub_self]
  refine ⟨r₀, hr₀, c, hc, 1 + 1 / c ^ 2, by positivity, hsub,
    fun z hz ↦ (h z hz).1.differentiableWithinAt, fun z hz ↦ (h z hz).2.1.differentiableWithinAt,
    fun z hz ↦ ⟨(h z hz).2.2.1, (h z hz).2.2.2.1, ?_⟩⟩
  have := φ.norm_le_mul_norm_mul_norm_fderiv_quadratic hH hH0
    (fun w hw ↦ hQ hw ▸ (h w hw).2.2.2.2) hz
  rwa [← hQ hz, Real.norm_eq_abs, Pi.sub_apply] at this

/-- **Two Liouville fields in a Morse–Bott chart.** Let `σ` be a closed nondegenerate two-form on
`M`, `X` a smooth Liouville field of `σ`, gradient-like for `f` near `p`, and `X'` a smooth
Liouville field, on an open `U ∋ p`, of the restriction of `σ` to `U`. Let `Y` be a field on `M`
equal to `X'` on `U` and gradient-like for `f` near `p`, and let `φ` be a Morse–Bott chart (in
particular a Morse chart, through `TauCeti.MorseChart.toMorseBottChart`) of `f` at `p`, with
chart `e`. Write `f̃ = f ∘ e.symm`, `X̃ z = de (X (e.symm z))`, `Ỹ z = de (Y (e.symm z))` and
`J = SmoothTwoForm.inverseFlatInChart σ e`.

Then there are `r₀ > 0`, `c > 0`, `A ≥ 0`, `B` and `H : M → ℝ`, smooth on `U`, with `H p = 0`,
such that the ball `B(0, r₀)` lies in the chart target, `e.symm` maps it into `U`, and at each
of its points `z`, with `H̃ = H ∘ e.symm`:
* `c (‖X̃ z‖² + ‖Df̃_z‖²) ≤ Df̃_z (X̃ z)` and `c (‖Ỹ z‖² + ‖Df̃_z‖²) ≤ Df̃_z (Ỹ z)`;
* `Ỹ z - X̃ z = J z (DH̃_z)`;
* `‖J z‖ ≤ B`;
* `|H̃ z| ≤ A ‖z‖ ‖Df̃_z‖`. -/
theorem exists_abs_comp_symm_le_mul_norm_mul_norm_fderiv [T2Space M] {f : M → ℝ} {p : M}
    (φ : MorseBottChart E f p) {σ : SmoothTwoForm 𝓘(ℝ, E) M} (hσ : σ.IsClosed)
    (hσn : σ.IsNondegenerate) {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hX : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (T% X))
    (hXσ : IsLiouvilleVectorField σ.val X) (hXf : IsGradientLikeAt f X p) {U : Opens M}
    (hp : p ∈ U) {X' : (x : U) → TangentSpace 𝓘(ℝ, E) x}
    (hX' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (T% X'))
    (hX'σ : IsLiouvilleVectorField
      (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ).val X')
    {Y : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hYX' : ∀ x (hx : x ∈ U), Y x = X' ⟨x, hx⟩)
    (hYf : IsGradientLikeAt f Y p) :
    ∃ r₀ > 0, ∃ c > 0, ∃ A ≥ 0, ∃ B : ℝ, ∃ H : M → ℝ, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ H U ∧
      H p = 0 ∧ ball 0 r₀ ⊆ φ.toChart.target ∧ φ.toChart.symm '' ball 0 r₀ ⊆ U ∧
      ∀ z ∈ ball (0 : E) r₀,
        c * (‖mvfderiv 𝓘(ℝ, E) φ.toChart (φ.toChart.symm z) (X (φ.toChart.symm z))‖ ^ 2 +
            ‖fderiv ℝ (f ∘ φ.toChart.symm) z‖ ^ 2) ≤
          fderiv ℝ (f ∘ φ.toChart.symm) z
            (mvfderiv 𝓘(ℝ, E) φ.toChart (φ.toChart.symm z) (X (φ.toChart.symm z))) ∧
        c * (‖mvfderiv 𝓘(ℝ, E) φ.toChart (φ.toChart.symm z) (Y (φ.toChart.symm z))‖ ^ 2 +
            ‖fderiv ℝ (f ∘ φ.toChart.symm) z‖ ^ 2) ≤
          fderiv ℝ (f ∘ φ.toChart.symm) z
            (mvfderiv 𝓘(ℝ, E) φ.toChart (φ.toChart.symm z) (Y (φ.toChart.symm z))) ∧
        mvfderiv 𝓘(ℝ, E) φ.toChart (φ.toChart.symm z) (Y (φ.toChart.symm z)) -
            mvfderiv 𝓘(ℝ, E) φ.toChart (φ.toChart.symm z) (X (φ.toChart.symm z)) =
          σ.inverseFlatInChart φ.toChart z (fderiv ℝ (H ∘ φ.toChart.symm) z) ∧
        ‖σ.inverseFlatInChart φ.toChart z‖ ≤ B ∧
        |H (φ.toChart.symm z)| ≤ A * ‖z‖ * ‖fderiv ℝ (f ∘ φ.toChart.symm) z‖ := by
  set e := φ.toChart
  refine hXσ.exists_abs_comp_symm_le_mul_norm_mul_norm_fderiv hσ hσn hX hXf hp hX' hX'σ hYX' hYf
    φ.mem_maximalAtlas φ.mem_source φ.apply_self (F := φ.quadratic) (K := 1) (fun z hz ↦ ?_)
    fun z s hs ↦ by simpa using φ.norm_fderiv_quadratic_smul_le hs z
  have := φ.eqOn_quadratic (e.map_target hz)
  rwa [Function.comp_apply, e.right_inv hz] at this

end MorseBottChart

end TauCeti

end
