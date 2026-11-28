/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.Basic
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ChartTransition
public import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.JetNorm
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.FirstOrderSystem
import SymplecticGeometry.Geometry.Manifold.DeRham.Circle
import SymplecticGeometry.LinearAlgebra.Complex.LinearPart
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# The change of frame between rescaled unitary charts

Let `D` be rescaled unitary charts, `k` a power, `x` and `y` two points, and
`τ = D.chartTransition k x y` the transition from the chart centred at `y` to the chart centred at
`x`. At the point `p = (D.chart k y)⁻¹ w`, the frames `D.frame k x p` and `D.frame k y p` of `P`
differ by an element of `Circle`, their division. Its `k`-th power, as a complex number, is the
**change of frame** `D.frameChange k x y w`. It compares the readings of a section `s` of
`PowerBundle P k` in the two charts: for `w` in the source of `τ`,
`D.reading k y s w = D.frameChange k x y w * D.reading k x s (τ w)`
(`SymplecticGeometry.RescaledUnitaryCharts.reading_eq_frameChange_mul`).

On the set `D.chartTransitionDomain k x y` of `ChartTransition.lean`, the points `w` of the ball
`B` of radius `ρ₀ * √k` in the source of `τ` with `τ w ∈ B`, both frames are smooth at
`(D.chart k y)⁻¹ w`, so the change of frame is smooth there
(`SymplecticGeometry.RescaledUnitaryCharts.contDiffOn_frameChange`), by Tau Ceti's
`ContMDiffOn.division`. It has norm one everywhere.

Its logarithmic derivative is the difference of the model forms of the two charts
(`SymplecticGeometry.RescaledUnitaryCharts.fderiv_frameChange_apply`): for a connection form `α`
and `w ∈ D.chartTransitionDomain k x y`,
`d e_w(v) = i (λ₀(w)(v) - λ₀(τ w)(dτ_w v)) e(w)`, with `e = D.frameChange k x y` and
`λ₀ = (stdForm ι).radialPrimitive`, `λ₀(z)(u) = ω₀(z, u) / 2`. Both frames read `k α` as `-λ₀` in
their charts (`SymplecticGeometry.RescaledUnitaryCharts.connectionForm_eq_model`), and the
pull-backs of `α` along them differ by the pull-back of the angular form along their division
(`SymplecticGeometry.IsCircleConnectionForm.mpullback_apply_eq_mpullback_division_add`), whose
`k`-th power `e` has derivative `i k e` times that pull-back (`mvfderiv_coe_circle_apply`).

So the connection read in the charts is covariant
(`SymplecticGeometry.RescaledUnitaryCharts.connectionReading_eq_frameChange_smul_comp`): for `w`
in `D.chartTransitionDomain k x y` and a section `s` whose reading `f_x` in the chart at `x` is
differentiable at `τ w`,
`D.connectionReading k y s w = e(w) • (D.connectionReading k x s (τ w)) ∘ dτ_w`. The product and
chain rules give the derivative of `e · (f_x ∘ τ)` at `w`, and the logarithmic derivative of `e`
turns the model term of the chart at `y` into that of the chart at `x`.

The logarithmic derivative is bilinear in the transition and its derivative. Where the
derivatives of the transition at a point `w` of its domain are bounded, the equation
`de = i θ e` is a first-order system whose jet at `(w, e w)` grows at most linearly in
`‖w‖ + ‖τ w‖`, and `SymplecticGeometry.jetNormAt_le_of_eventually_fderiv_eq` bounds the jets of
`e` at `w` by a polynomial in `‖w‖ + ‖τ w‖`.

## Main definitions

* `SymplecticGeometry.RescaledUnitaryCharts.frameChange`: the change of frame.

## Main results

* `SymplecticGeometry.RescaledUnitaryCharts.norm_frameChange`: `‖D.frameChange k x y w‖ = 1`.
* `SymplecticGeometry.RescaledUnitaryCharts.contDiffOn_frameChange`: the change of frame is smooth
  on `D.chartTransitionDomain k x y`, so smooth and differentiable at each of its points
  (`SymplecticGeometry.RescaledUnitaryCharts.contDiffAt_frameChange`,
  `SymplecticGeometry.RescaledUnitaryCharts.differentiableAt_frameChange`).
* `SymplecticGeometry.RescaledUnitaryCharts.reading_eq_frameChange_mul`: the readings of a section
  in the two charts differ by the change of frame, and so agree near each point of the source of
  the transition (`SymplecticGeometry.RescaledUnitaryCharts.reading_eventuallyEq_frameChange_mul`).
* `SymplecticGeometry.RescaledUnitaryCharts.fderiv_frameChange_apply`: the logarithmic derivative
  of the change of frame.
* `SymplecticGeometry.RescaledUnitaryCharts.connectionReading_eq_frameChange_smul_comp`: the
  connection read in the chart at `y` is the change of frame times the connection read in the
  chart at `x`, composed with the derivative of the transition.
* `SymplecticGeometry.RescaledUnitaryCharts.dbarReading_eq_frameChange_smul_comp`: the same for
  the `∂̄` readings, since the derivative of the transition intertwines `J` read in the two charts
  (`SymplecticGeometry.RescaledUnitaryCharts.isComplexLinear_fderiv_chartTransition` and
  `TauCeti.IsComplexLinear.complexAntilinearPart_comp_right`); so the two sides agree near each
  point `w` of the domain at which the reading in the chart at `x` is differentiable near `τ w`
  (`SymplecticGeometry.RescaledUnitaryCharts.dbarReading_eventuallyEq_frameChange_smul_comp`).
* `SymplecticGeometry.RescaledUnitaryCharts.exists_forall_jetNormAt_frameChange_le`: the `r`-jet
  norm of the change of frame at a point `w` of the domain of the transition `τ` is at most
  `K * (1 + ‖w‖ + ‖τ w‖) ^ r`, for `K` that depends only on `r` and on a bound for the
  derivatives of `τ` at `w`.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002].
-/

public section

open scoped Manifold ContDiff Topology
open TauCeti Metric Bundle MulOpposite

namespace SymplecticGeometry

/-! ### Jet norms of solutions of the model equation -/

section ModelEquation

variable {ι : Type*} [Fintype ι]

/-- A step of `RescaledUnitaryCharts.exists_forall_jetNormAt_frameChange_le`: given `r` and a bound
`Cτ`, there is a constant `c₁ ≥ 0` such that for every point `w₀` and every map `τ` smooth at
`w₀` whose derivatives at `w₀` of orders `1` to `r + 1` have norm at most `Cτ`, the map
`w ↦ ω₀(w, ·) - ω₀(τ w, Dτ_w ·)` is `C^r` at `w₀`, with `r`-jet norm at `w₀` at most
`c₁ * (1 + ‖w₀‖ + ‖τ w₀‖)`. -/
private theorem exists_jetNormAt_stdForm_sub_le (r : ℕ) (Cτ : ℝ) :
    ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ {τ : StdSpace ι → StdSpace ι} {w₀ : StdSpace ι}, ContDiffAt ℝ ∞ τ w₀ →
      (∀ j, 1 ≤ j → j ≤ r + 1 → ‖iteratedFDeriv ℝ j τ w₀‖ ≤ Cτ) →
      ContDiffAt ℝ r (⇑(stdFormCompRightL ι 1) +
        -fun w ↦ stdFormCompRightL ι (fderiv ℝ τ w) (τ w)) w₀ ∧
      jetNormAt ℝ r (⇑(stdFormCompRightL ι 1) +
        -fun w ↦ stdFormCompRightL ι (fderiv ℝ τ w) (τ w)) w₀ ≤
        c₁ * (1 + ‖w₀‖ + ‖τ w₀‖) := by
  -- Instance search does not find the norm on the space of `stdFormCompRightL ι` by itself.
  let _ : NormedAddCommGroup (StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] ℝ) := inferInstance
  -- The bilinear map `(A, u) ↦ ω₀(u, A ·)`.
  set B := stdFormCompRightL ι
  set c₁ : ℝ := ‖B 1‖ + 2 ^ r * ‖B‖ * ((r + 1) * |Cτ|) * (1 + r * |Cτ|)
  refine ⟨c₁, by positivity, fun {τ w₀} hτ hCτ ↦ ?_⟩
  set z := τ w₀
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have hw₀ : 0 ≤ ‖w₀‖ := norm_nonneg w₀
  have hDτ : ContDiffAt ℝ r (fderiv ℝ τ) w₀ := hτ.fderiv_right (by simp)
  have hτr : ContDiffAt ℝ r τ w₀ := hτ.of_le (by simp)
  set g : StdSpace ι → StdSpace ι →L[ℝ] ℝ := fun w ↦ B (fderiv ℝ τ w) (τ w)
  have hg : ContDiffAt ℝ r g w₀ :=
    (B.contDiff.contDiffAt.comp w₀ hDτ).clm_apply hτr
  have hB1 : ContDiffAt ℝ r (⇑(B 1)) w₀ := (B 1).contDiff.contDiffAt
  refine ⟨hB1.add hg.neg, ?_⟩
  have hjτ : jetNormAt ℝ r τ w₀ ≤ (1 + r * |Cτ|) * (1 + ‖z‖) :=
    (jetNormAt_le_mul_one_add_norm_of_norm_iteratedFDeriv_succ_le fun j hj ↦
      hCτ (j + 1) (by omega) (by omega)).trans (by gcongr; exact le_abs_self _)
  have hjDτ : jetNormAt ℝ r (fderiv ℝ τ) w₀ ≤ (r + 1) * |Cτ| :=
    (jetNormAt_fderiv_le_of_norm_iteratedFDeriv_succ_le fun j hj ↦
      hCτ (j + 1) (by omega) (by omega)).trans (by gcongr; exact le_abs_self _)
  refine (jetNormAt_add_le (g := -g) hB1 hg.neg).trans ?_
  rw [jetNormAt_neg]
  have h1 : jetNormAt ℝ r (⇑(B 1)) w₀ ≤ ‖B 1‖ * (1 + ‖w₀‖) := by
    have := jetNormAt_continuousLinearMap_le (B 1) r w₀
    have := (B 1).le_opNorm w₀
    nlinarith
  have h3 : jetNormAt ℝ r g w₀ ≤
      2 ^ r * ‖B‖ * ((r + 1) * |Cτ|) * ((1 + r * |Cτ|) * (1 + ‖z‖)) :=
    (jetNormAt_bilinear_le B hDτ hτr).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hjDτ (by positivity)) hjτ (jetNormAt_nonneg _ _ _)
      (by positivity))
  have : 0 ≤ 2 ^ r * ‖B‖ * ((r + 1) * |Cτ|) * (1 + r * |Cτ|) := by positivity
  calc _ ≤ ‖B 1‖ * (1 + ‖w₀‖) +
        2 ^ r * ‖B‖ * ((r + 1) * |Cτ|) * ((1 + r * |Cτ|) * (1 + ‖z‖)) :=
        add_le_add h1 h3
    _ ≤ _ := by
        simp only [c₁]
        nlinarith [mul_nonneg (norm_nonneg (B 1)) hz, mul_nonneg (norm_nonneg (B 1)) hw₀]

/-- A step of `RescaledUnitaryCharts.exists_forall_jetNormAt_frameChange_le`: given `r` and a bound
`Cτ`, there is a constant `K ≥ 0` such that for every point `w₀`, every `e : StdSpace ι → ℂ` with
`‖e w₀‖ = 1` that is `C^r` at `w₀` and solves `de_w(v) = i θ_w(v) e(w)` near `w₀`, where
`θ_w(v) = (ω₀(w, v) - ω₀(τ w, Dτ_w v)) / 2` for a map `τ` smooth at `w₀` whose derivatives at
`w₀` of orders `1` to `r + 1` have norm at most `Cτ`, has `r`-jet norm at `w₀` at most
`K * (1 + ‖w₀‖ + ‖τ w₀‖) ^ r`. -/
private theorem exists_jetNormAt_le_of_fderiv_eq_stdForm (r : ℕ) (Cτ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {τ : StdSpace ι → StdSpace ι} {e : StdSpace ι → ℂ} {w₀ : StdSpace ι},
      ContDiffAt ℝ ∞ τ w₀ → ContDiffAt ℝ r e w₀ → ‖e w₀‖ = 1 →
      (∀ᶠ w in 𝓝 w₀, ∀ v, fderiv ℝ e w v = Complex.I *
        ((2⁻¹ * (stdForm ι w v - stdForm ι (τ w) (fderiv ℝ τ w v)) : ℝ) : ℂ) * e w) →
      (∀ j, 1 ≤ j → j ≤ r + 1 → ‖iteratedFDeriv ℝ j τ w₀‖ ≤ Cτ) →
      jetNormAt ℝ r e w₀ ≤ K * (1 + ‖w₀‖ + ‖τ w₀‖) ^ r := by
  obtain ⟨c₁, hc₁, hθ₁⟩ := exists_jetNormAt_stdForm_sub_le (ι := ι) r Cτ
  -- The bilinear map `(A, u) ↦ ω₀(u, A ·)`, and the map reading real forms in `ℂ`.
  set B := stdFormCompRightL ι
  set L := ContinuousLinearMap.compL ℝ (StdSpace ι) ℝ ℂ Complex.ofRealCLM
  set c : ℂ := Complex.I * 2⁻¹
  set a : ℝ := 2 ^ r * (‖c‖ * (‖L‖ * c₁)) * 2
  have : 0 ≤ a := by positivity
  refine ⟨1 + r * firstOrderSystemConst r * (1 + a) ^ r, by positivity,
    fun {τ e w₀} hτ he he0 heq hCτ ↦ ?_⟩
  set m := ‖w₀‖ + ‖τ w₀‖
  have hm : 0 ≤ m := by positivity
  set θ : StdSpace ι → StdSpace ι →L[ℝ] ℝ :=
    ⇑(B 1) + -fun w ↦ B (fderiv ℝ τ w) (τ w)
  obtain ⟨hθ, hjθ⟩ : ContDiffAt ℝ r θ w₀ ∧ jetNormAt ℝ r θ w₀ ≤ c₁ * (1 + ‖w₀‖ + ‖τ w₀‖) :=
    hθ₁ hτ hCτ
  rw [add_assoc] at hjθ
  -- The first-order system `de_w = Φ (w, e w)` solved by `e`, with `Φ (w, u) = u • G w`.
  set G : StdSpace ι → StdSpace ι →L[ℝ] ℂ := c • (⇑L ∘ θ)
  have hG : ContDiffAt ℝ r G w₀ := (L.contDiff.contDiffAt.comp _ hθ).const_smul c
  have hjG : jetNormAt ℝ r G w₀ ≤ ‖c‖ * (‖L‖ * (c₁ * (1 + m))) := by
    rw [jetNormAt_smul]
    gcongr
    exact (jetNormAt_comp_left_le L hθ).trans (by gcongr)
  set Φ : StdSpace ι × ℂ → StdSpace ι →L[ℝ] ℂ := fun p ↦ Prod.snd p • (G ∘ Prod.fst) p
  have hfst : ContDiffAt ℝ r (G ∘ Prod.fst) (w₀, e w₀) :=
    hG.comp (w₀, e w₀) contDiffAt_fst
  have hΦ : ContDiffAt ℝ r Φ (w₀, e w₀) := contDiffAt_snd.smul hfst
  have heqΦ : ∀ᶠ w in 𝓝 w₀, fderiv ℝ e w = Φ (w, e w) := by
    filter_upwards [heq] with w hw
    ext v
    rw [hw v]
    simp [Φ, G, θ, L, B, c]
    ring
  have hjΦ : jetNormAt ℝ r Φ (w₀, e w₀) ≤ a * (1 + m) := by
    have h3 : jetNormAt ℝ r (Prod.snd : StdSpace ι × ℂ → ℂ) (w₀, e w₀) ≤ 2 := by
      have := jetNormAt_continuousLinearMap_le (ContinuousLinearMap.snd ℝ (StdSpace ι) ℂ) r
        (w₀, e w₀)
      simp only [ContinuousLinearMap.coe_snd', he0] at this
      linarith [ContinuousLinearMap.norm_snd_le ℝ (StdSpace ι) ℂ]
    refine (jetNormAt_fun_smul_le contDiffAt_snd hfst).trans ?_
    rw [jetNormAt_comp_fst]
    calc _ ≤ 2 ^ r * 2 * (‖c‖ * (‖L‖ * (c₁ * (1 + m)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h3 (by positivity)) hjG (jetNormAt_nonneg _ _ _)
            (by positivity)
      _ = a * (1 + m) := by ring
  -- The bound of `jetNormAt_le_of_eventually_fderiv_eq`.
  refine (jetNormAt_le_of_eventually_fderiv_eq he hΦ heqΦ).trans ?_
  rw [he0, add_assoc]
  have h1m : 1 ≤ 1 + m := by simp [hm]
  have hA : 1 + jetNormAt ℝ r Φ (w₀, e w₀) ≤ (1 + a) * (1 + m) := by nlinarith
  calc 1 + r * firstOrderSystemConst r * (1 + jetNormAt ℝ r Φ (w₀, e w₀)) ^ r
      ≤ (1 + m) ^ r + r * firstOrderSystemConst r * ((1 + a) * (1 + m)) ^ r := by
        gcongr
        · exact one_le_pow₀ h1m
        · exact add_nonneg zero_le_one (jetNormAt_nonneg _ _ _)
    _ = _ := by rw [mul_pow]; ring

end ModelEquation

namespace RescaledUnitaryCharts

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}
  (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀)

/-! ### The change of frame -/

/-- The **change of frame** between the chart centred at `y` and the chart centred at `x`, for the
power `k`: at `w`, the `k`-th power of the element of `Circle` that carries the frame
`D.frame k y` to the frame `D.frame k x` at the point `(D.chart k y)⁻¹ w`, as a complex number. -/
noncomputable def frameChange (k : ℕ) (x y : M) (w : StdSpace ι) : ℂ :=
  ((PrincipalBundle.division Circle (D.frame k y ((D.chart k y).symm w))
    (D.frame k x ((D.chart k y).symm w)) ^ k : Circle) : ℂ)

theorem frameChange_def (k : ℕ) (x y : M) (w : StdSpace ι) :
    D.frameChange k x y w = ((PrincipalBundle.division Circle (D.frame k y ((D.chart k y).symm w))
      (D.frame k x ((D.chart k y).symm w)) ^ k : Circle) : ℂ) :=
  (rfl)

/-- The change of frame has values in the unit circle. -/
@[simp]
theorem norm_frameChange (k : ℕ) (x y : M) (w : StdSpace ι) : ‖D.frameChange k x y w‖ = 1 := by
  rw [frameChange_def, Circle.norm_coe]

/-- The change of frame does not vanish. -/
theorem frameChange_ne_zero (k : ℕ) (x y : M) (w : StdSpace ι) : D.frameChange k x y w ≠ 0 := by
  rw [frameChange_def]
  exact Circle.coe_ne_zero _

variable [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P]

attribute [local instance] finrank_real_complex_fact' in
/-- **The change of frame is smooth.** For `k ≥ k₀`, it is smooth on the set of points of the ball
of radius `ρ₀ * √k` that the transition from the chart centred at `y` to the chart centred at `x`
sends into that ball: it is `C^n` there for every `n : ℕ∞`. -/
theorem contDiffOn_frameChange {n : ℕ∞} {k : ℕ} (hk : k₀ ≤ k) (x y : M) :
    ContDiffOn ℝ n (D.frameChange k x y) (D.chartTransitionDomain k x y) := by
  set W := D.chartTransitionDomain k x y
  have hsymm : ContMDiffOn 𝓘(ℝ, StdSpace ι) I ∞ (D.chart k y).symm W :=
    (D.chart k y).symm.contMDiffOn.mono fun w hw ↦
      (D.mem_chartTransition_source_iff.1 (D.chartTransitionDomain_subset_source k x y hw)).1
  -- Both frames are smooth along `(D.chart k y)⁻¹` on `W`.
  have hy : ContMDiffOn 𝓘(ℝ, StdSpace ι) (I.prod (𝓡 1)) ∞ (fun w ↦
      ManifoldTotalSpace.homeomorph Circle P
        ⟨(D.chart k y).symm w, D.frame k y ((D.chart k y).symm w)⟩) W :=
    (D.contMDiffOn_frame hk y).comp hsymm fun w hw ↦
      Set.mem_image_of_mem _ (D.mem_chartTransitionDomain_iff.1 hw).1
  have hx : ContMDiffOn 𝓘(ℝ, StdSpace ι) (I.prod (𝓡 1)) ∞ (fun w ↦
      ManifoldTotalSpace.homeomorph Circle P
        ⟨(D.chart k y).symm w, D.frame k x ((D.chart k y).symm w)⟩) W :=
    (D.contMDiffOn_frame hk x).comp hsymm fun w hw ↦
      ⟨_, (D.mem_chartTransitionDomain_iff.1 hw).2.2,
        D.chart_symm_chartTransition (D.mem_chartTransitionDomain_iff.1 hw).2.1⟩
  have hg := ((hy.division hx).pow k)
  rw [← contMDiffOn_iff_contDiffOn]
  exact (contMDiff_coe_sphere.comp_contMDiffOn (hg.of_le (by exact_mod_cast le_top))).congr
    fun w _ ↦ (frameChange_def ..).symm

/-- For `k ≥ k₀`, the change of frame is smooth at each point of the open set
`D.chartTransitionDomain k x y`: it is `C^n` there for every `n : ℕ∞`. -/
theorem contDiffAt_frameChange {n : ℕ∞} {k : ℕ} (hk : k₀ ≤ k) {x y : M} {w : StdSpace ι}
    (hw : w ∈ D.chartTransitionDomain k x y) :
    ContDiffAt ℝ n (D.frameChange k x y) w :=
  (D.contDiffOn_frameChange hk x y).contDiffAt ((D.isOpen_chartTransitionDomain k x y).mem_nhds hw)

/-- For `k ≥ k₀`, the change of frame is differentiable at each point of the open set
`D.chartTransitionDomain k x y`. -/
theorem differentiableAt_frameChange {k : ℕ} (hk : k₀ ≤ k) {x y : M} {w : StdSpace ι}
    (hw : w ∈ D.chartTransitionDomain k x y) :
    DifferentiableAt ℝ (D.frameChange k x y) w :=
  (D.contDiffAt_frameChange (n := 1) hk hw).differentiableAt (by simp)

/-- **The readings in two charts differ by the change of frame.** For `w` in the source of the
transition `τ` from the chart centred at `y` to the chart centred at `x`, the reading of a section
`s` of `PowerBundle P k` in the chart at `y` is, at `w`, the change of frame times its reading in
the chart at `x` at `τ w`. -/
theorem reading_eq_frameChange_mul {k : ℕ} {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) (s : Π y, PowerBundle P k y) :
    D.reading k y s w = D.frameChange k x y w * D.reading k x s (D.chartTransition k x y w) := by
  have h := D.apply_chart_symm_eq_mk k x s (D.chartTransition k x y w)
  rw [D.chart_symm_chartTransition hw] at h
  rw [reading_def, h, AssociatedBundle.mkLinearIsometryEquiv_symm_apply_mk,
    PowerModel.toComplex_smul, frameChange_def, Circle.coe_pow, zpow_natCast,
    LinearIsometryEquiv.apply_symm_apply]

/-- Near a point `w` of the source of the transition `τ` from the chart centred at `y` to the
chart centred at `x`, the reading of a section `s` of `PowerBundle P k` in the chart at `y` is the
change of frame times the reading of `s` in the chart at `x` composed with `τ`. -/
theorem reading_eventuallyEq_frameChange_mul {k : ℕ} {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) (s : Π y, PowerBundle P k y) :
    D.reading k y s =ᶠ[nhds w]
      fun w' ↦ D.frameChange k x y w' * D.reading k x s (D.chartTransition k x y w') :=
  Filter.eventually_of_mem ((D.chartTransition k x y).open_source.mem_nhds hw) fun _ hw' ↦
    D.reading_eq_frameChange_mul hw' s

attribute [local instance] finrank_real_complex_fact' in
/-- **The logarithmic derivative of the change of frame.** Let `α` be a connection form, `k ≥ k₀`,
and `τ` the transition from the chart centred at `y` to the chart centred at `x`. At a point `w`
of `D.chartTransitionDomain k x y`, the derivative of the change of frame `e` in the direction
`v` is `i θ e(w)`, where `θ = λ₀(w)(v) - λ₀(τ w)(dτ_w v)` is the difference of the model forms
`λ₀ = (stdForm ι).radialPrimitive`, `λ₀(z)(u) = ω₀(z, u) / 2`, read directly and through `τ`. -/
theorem fderiv_frameChange_apply (hα : IsCircleConnectionForm α) {k : ℕ} (hk : k₀ ≤ k)
    {x y : M} {w : StdSpace ι} (hw : w ∈ D.chartTransitionDomain k x y) (v : StdSpace ι) :
    fderiv ℝ (D.frameChange k x y) w v =
      Complex.I * ((2⁻¹ * (stdForm ι w v - stdForm ι (D.chartTransition k x y w)
        (fderiv ℝ (D.chartTransition k x y) w v)) : ℝ) : ℂ) * D.frameChange k x y w := by
  obtain ⟨hwB, hws, hτB⟩ := D.mem_chartTransitionDomain_iff.1 hw
  have hwt : w ∈ (D.chart k y).target := (D.mem_chartTransition_source_iff.1 hws).1
  set τ := D.chartTransition k x y
  set p := (D.chart k y).symm w
  have hpx : (D.chart k x).symm (τ w) = p := D.chart_symm_chartTransition hws
  set g : M → Circle := fun b ↦ PrincipalBundle.division Circle (D.frame k y b) (D.frame k x b)
  -- Both frames are smooth near `p`, on the images of the balls under the inverse charts.
  have hpy : p ∈ (D.chart k y).symm '' ball 0 (ρ₀ * √k) := ⟨w, hwB, rfl⟩
  have hpx' : p ∈ (D.chart k x).symm '' ball 0 (ρ₀ * √k) := ⟨τ w, hτB, hpx⟩
  have hFy := (D.contMDiffOn_frame hk y).contMDiffAt
    ((D.isOpen_image_symm_ball hk y le_rfl).mem_nhds hpy)
  have hFx := (D.contMDiffOn_frame hk x).contMDiffAt
    ((D.isOpen_image_symm_ball hk x le_rfl).mem_nhds hpx')
  have hg : MDifferentiableAt I (𝓡 1) g p := (hFy.division hFx).mdifferentiableAt (by simp)
  have hsymm : MDifferentiableAt 𝓘(ℝ, StdSpace ι) I (D.chart k y).symm w :=
    (D.chart k y).symm.mdifferentiableAt (by simp) (by simpa using hwt)
  -- The tangent vector `u` at `p` that the chart at `y` sends to `v`; the chart at `x` sends it
  -- to `dτ_w v`.
  set u := mfderiv 𝓘(ℝ, StdSpace ι) I (D.chart k y).symm w v
  have hu : mfderiv 𝓘(ℝ, StdSpace ι) I (D.chart k x).symm (τ w) (fderiv ℝ τ w v) = u :=
    D.mfderiv_chart_symm_chartTransition hws v
  -- The change of section: `σ_x^* α = g^* dθ + σ_y^* α` at `p`.
  have hA := congrArg (· ![u]) (hα.mpullback_apply_eq_mpullback_division_add
    (D.isOpen_image_symm_ball hk y le_rfl) (D.contMDiffOn_frame hk y) hpy
    (hFx.mdifferentiableAt (by simp)))
  simp only [ContinuousAlternatingMap.add_apply] at hA
  -- The model forms in the two charts.
  have hmy := D.connectionForm_eq_model hk y w hwB v
  rw [mpullback_apply_one (v := (v : TangentSpace 𝓘(ℝ, StdSpace ι) w))] at hmy
  have hmx := D.connectionForm_eq_model hk x (τ w) hτB (fderiv ℝ τ w v)
  rw [mpullback_apply_one (v := (fderiv ℝ τ w v : TangentSpace 𝓘(ℝ, StdSpace ι) (τ w))), hu,
    hpx] at hmx
  rw [SymplecticForm.radialPrimitive_apply (v := (v : TangentSpace 𝓘(ℝ, StdSpace ι) w))] at hmy
  rw [SymplecticForm.radialPrimitive_apply
    (v := (fderiv ℝ τ w v : TangentSpace 𝓘(ℝ, StdSpace ι) (τ w)))] at hmx
  -- The derivative of `e = (g ∘ (D.chart k y)⁻¹) ^ k` read in `ℂ`.
  have he : D.frameChange k x y = fun w ↦ (((g ∘ (D.chart k y).symm) ^ k) w : ℂ) :=
    funext fun w ↦ by rw [frameChange_def, Pi.pow_apply, Function.comp_apply]
  have hgs : MDifferentiableAt 𝓘(ℝ, StdSpace ι) (𝓡 1) (g ∘ (D.chart k y).symm) w :=
    hg.comp w hsymm
  have hgk : MDifferentiableAt 𝓘(ℝ, StdSpace ι) (𝓡 1) ((g ∘ (D.chart k y).symm) ^ k) w :=
    ((contMDiff_pow (I := 𝓡 1) (G := Circle) (n := 1) k).mdifferentiableAt one_ne_zero).comp w hgs
  have hd := mvfderiv_coe_circle_apply hgk v
  rw [mpullback_pow_circleAngularForm_apply hgs, mpullback_comp_at hsymm hg,
    ContinuousAlternatingMap.smul_apply] at hd
  rw [mpullback_apply_one (v := (v : TangentSpace 𝓘(ℝ, StdSpace ι) w))] at hd
  rw [← mvfderiv_eq_fderiv_apply (v := (v : TangentSpace 𝓘(ℝ, StdSpace ι) w))]
  rw [he, hd, smul_eq_mul]
  have hkA : (k : ℝ) * mpullback I (𝓡 1) g circleAngularForm p ![u] =
      2⁻¹ * (stdForm ι w v - stdForm ι (τ w) (fderiv ℝ τ w v)) := by
    linear_combination hmx - hmy - (k : ℝ) * hA
  rw [hkA]
  push_cast
  ring

/-- **Covariance of the connection read in the charts.** Let `α` be a connection form, `k ≥ k₀`,
and `τ` the transition from the chart centred at `y` to the chart centred at `x`. At a point `w`
of `D.chartTransitionDomain k x y`, for a section `s` of `PowerBundle P k` whose reading in the
chart at `x` is differentiable at `τ w`, the connection read in the chart at `y` at `w` is the
change of frame `e(w)` times the connection read in the chart at `x` at `τ w`, composed with
`dτ_w`. -/
theorem connectionReading_eq_frameChange_smul_comp (hα : IsCircleConnectionForm α) {k : ℕ}
    (hk : k₀ ≤ k) {x y : M} {w : StdSpace ι} (hw : w ∈ D.chartTransitionDomain k x y)
    {s : Π y, PowerBundle P k y}
    (hs : DifferentiableAt ℝ (D.reading k x s) (D.chartTransition k x y w)) :
    D.connectionReading k y s w = D.frameChange k x y w •
      (D.connectionReading k x s (D.chartTransition k x y w)).comp
        (fderiv ℝ (D.chartTransition k x y) w) := by
  have hws := D.chartTransitionDomain_subset_source k x y hw
  have hτ := D.differentiableAt_chartTransition hws
  have he := D.differentiableAt_frameChange hk hw
  have hfτ : DifferentiableAt ℝ (fun w' ↦ D.reading k x s (D.chartTransition k x y w')) w :=
    hs.comp w hτ
  -- Near `w`, the reading at `y` is `e` times the reading at `x` composed with `τ`.
  have heq := D.reading_eventuallyEq_frameChange_mul hws s
  ext v
  rw [smul_apply, ContinuousLinearMap.comp_apply, connectionReading_apply,
    connectionReading_apply, heq.fderiv_eq,
    fderiv_fun_mul he hfτ, fderiv_fun_comp w hs hτ]
  simp [D.fderiv_frameChange_apply hα hk hw v, D.reading_eq_frameChange_mul hws s]
  ring

/-- **Covariance of the `∂̄` reading.** Let `α` be a connection form, `k ≥ k₀`, and `τ` the
transition from the chart centred at `y` to the chart centred at `x`. At a point `w` of
`D.chartTransitionDomain k x y`, for a section `s` of `PowerBundle P k` whose reading in the chart
at `x` is differentiable at `τ w`, the `∂̄` reading in the chart at `y` at `w` is the change of
frame `e(w)` times the `∂̄` reading in the chart at `x` at `τ w`, composed with `dτ_w`. -/
theorem dbarReading_eq_frameChange_smul_comp (hα : IsCircleConnectionForm α) {k : ℕ}
    (hk : k₀ ≤ k) {x y : M} {w : StdSpace ι} (hw : w ∈ D.chartTransitionDomain k x y)
    {s : Π y, PowerBundle P k y}
    (hs : DifferentiableAt ℝ (D.reading k x s) (D.chartTransition k x y w)) :
    D.dbarReading k y s w = D.frameChange k x y w •
      (D.dbarReading k x s (D.chartTransition k x y w)).comp
        (fderiv ℝ (D.chartTransition k x y) w) := by
  have hT :=
    D.isComplexLinear_fderiv_chartTransition (D.chartTransitionDomain_subset_source k x y hw)
  ext v
  have h := LinearMap.congr_fun (hT.complexAntilinearPart_comp_right
    (J' := (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap)
    (D.connectionReading k x s (D.chartTransition k x y w) : StdSpace ι →ₗ[ℝ] ℂ)) v
  simp only [LinearMap.comp_apply, complexAntilinearPart_apply, ContinuousLinearMap.coe_coe,
    AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul] at h
  rw [dbarReading_apply, D.connectionReading_eq_frameChange_smul_comp hα hk hw hs]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, dbarReading_apply]
  rw [← h]
  simp only [smul_eq_mul, Complex.real_smul]
  ring

/-- Let `α` be a connection form, `k ≥ k₀`, `τ` the transition from the chart centred at `y` to
the chart centred at `x`, and `w` a point of `D.chartTransitionDomain k x y`. For a section `s` of
`PowerBundle P k` whose reading in the chart at `x` is differentiable near `τ w`, the `∂̄` reading
of `s` in the chart at `y` agrees near `w` with the change of frame times the `∂̄` reading in the
chart at `x` composed with `τ`, composed with `dτ`. -/
theorem dbarReading_eventuallyEq_frameChange_smul_comp (hα : IsCircleConnectionForm α) {k : ℕ}
    (hk : k₀ ≤ k) {x y : M} {w : StdSpace ι} (hw : w ∈ D.chartTransitionDomain k x y)
    {s : Π y, PowerBundle P k y}
    (hs : ∀ᶠ u in 𝓝 (D.chartTransition k x y w), DifferentiableAt ℝ (D.reading k x s) u) :
    D.dbarReading k y s =ᶠ[𝓝 w] fun w' ↦ D.frameChange k x y w' •
      (D.dbarReading k x s (D.chartTransition k x y w')).comp
        (fderiv ℝ (D.chartTransition k x y) w') :=
  ((Filter.eventually_mem_set.2 ((D.isOpen_chartTransitionDomain k x y).mem_nhds hw)).and
    ((D.differentiableAt_chartTransition (D.chartTransitionDomain_subset_source k x y hw)
      ).continuousAt.tendsto.eventually hs)).mono fun _ ⟨hw', hs'⟩ ↦
    D.dbarReading_eq_frameChange_smul_comp hα hk hw' hs'

/-! ### Jet norms of the change of frame -/

/-- **Jet norms of the change of frame.** Let `α` be a connection form. For every order `r` and
every bound `Cτ` there is a constant `K ≥ 0` with the following property: for all `k ≥ k₀`, all
points `x` and `y` and every `w` in `D.chartTransitionDomain k x y` at which the derivatives of
orders `1` to `r + 1` of the transition `τ` from the chart centred at `y` to the chart centred at
`x` have norm at most `Cτ`, the `r`-jet norm at `w` of the change of frame between the two charts
is at most `K * (1 + ‖w‖ + ‖τ w‖) ^ r`. -/
theorem exists_forall_jetNormAt_frameChange_le (hα : IsCircleConnectionForm α) (r : ℕ)
    (Cτ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {k : ℕ}, k₀ ≤ k → ∀ {x y : M} {w : StdSpace ι},
      w ∈ D.chartTransitionDomain k x y →
      (∀ j, 1 ≤ j → j ≤ r + 1 → ‖iteratedFDeriv ℝ j (D.chartTransition k x y) w‖ ≤ Cτ) →
      jetNormAt ℝ r (D.frameChange k x y) w ≤
        K * (1 + ‖w‖ + ‖D.chartTransition k x y w‖) ^ r := by
  obtain ⟨K, hK0, hK⟩ := exists_jetNormAt_le_of_fderiv_eq_stdForm (ι := ι) r Cτ
  refine ⟨K, hK0, fun {k} hk x y w hw hCτ ↦ ?_⟩
  have hW := (D.isOpen_chartTransitionDomain k x y).mem_nhds hw
  exact hK (D.contDiffAt_chartTransition (D.chartTransitionDomain_subset_source k x y hw))
    (D.contDiffAt_frameChange hk hw) (D.norm_frameChange k x y w)
    (Filter.eventually_of_mem hW fun w hw v ↦ D.fderiv_frameChange_apply hα hk hw v) hCτ

end RescaledUnitaryCharts

end SymplecticGeometry

end
