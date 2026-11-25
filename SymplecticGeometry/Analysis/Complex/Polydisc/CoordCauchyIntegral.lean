/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import TauCeti.Analysis.Calculus.ContDiff.IsOpen
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# The Cauchy integral in one coordinate

For a function `f : (ι → ℂ) → F` on the coordinate space of a finite type `ι`, an index `i`, a
centre `c : ι → ℂ` and a radius `ρ`, the Cauchy integral of `f` in the `i`-th coordinate is

`coordCauchyIntegral i c ρ f z = (2πi)⁻¹ • ∮ ζ in C(c i, ρ), (ζ - z i)⁻¹ • f (update z i ζ)`:

the one-variable Cauchy integral over the circle `C(c i, ρ)` of the restriction of `f` to the
complex line through `z` in the direction of the `i`-th coordinate, the other coordinates of
`z` held fixed. Applying it in each coordinate in turn, as in the proof of the Cauchy integral
formula on a polydisc, approximates a `C¹` function with small `∂̄` by a holomorphic one.

## Main results

* `SymplecticGeometry.norm_coordCauchyIntegral_le`: if `z i` lies in the disc of radius `ρ / 2`
  about `c i`, then `‖coordCauchyIntegral i c ρ f z‖ ≤ 2 * M` for any bound `M` of `‖f‖` on the
  circle of the `i`-th coordinate through `z`.
* `SymplecticGeometry.contDiffAt_coordCauchyIntegral`: for `f` that is `C¹` near the closed
  sup-norm polydisc `closedBall c ρ`, the coordinate Cauchy integral is `C¹` at every `z` with
  `z i` in the open disc and the other coordinates in the closed discs.
* `SymplecticGeometry.differentiableAt_coordCauchyIntegral_update`: it is complex
  differentiable in the `i`-th coordinate.
* `SymplecticGeometry.fderiv_coordCauchyIntegral_apply`: its derivative in a direction `v` with
  `v i = 0` is the coordinate Cauchy integral of the derivative of `f` in that direction.
* `SymplecticGeometry.conjWirtingerDeriv_coordCauchyIntegral_single`: for `j ≠ i` it commutes
  with the conjugate Wirtinger derivative `∂/∂(conj z_j)`.

## Implementation notes

Differentiation under the integral sign uses Tau Ceti's
`TauCeti.contDiffOn_integral_smul_of_contDiffOn`, for the integrand as a function of `z` and of the
angle, rescaled to the unit interval, and `TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn` for
derivatives along real lines. Holomorphy in the `i`-th coordinate is Mathlib's
`hasFPowerSeriesOn_cauchy_integral`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Chapter II (the Cauchy integral formula on polydiscs).
* [D. Auroux, *Symplectic 4-manifolds as branched coverings of ℂℙ²*][Auroux2000], Proposition 2
  (where the approximation by holomorphic functions on polydiscs is used).
-/

public section

open Complex Function Metric Set MeasureTheory
open scoped Real

namespace SymplecticGeometry

variable {ι : Type*} [DecidableEq ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The **Cauchy integral in the `i`-th coordinate** of `f : (ι → ℂ) → F` over the circle
`C(c i, ρ)`: the one-variable Cauchy integral
`(2πi)⁻¹ • ∮ ζ in C(c i, ρ), (ζ - z i)⁻¹ • f (update z i ζ)` of `f` restricted to the complex
line through `z` along the `i`-th coordinate. -/
noncomputable def coordCauchyIntegral (i : ι) (c : ι → ℂ) (ρ : ℝ) (f : (ι → ℂ) → F)
    (z : ι → ℂ) : F :=
  (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c i, ρ), (ζ - z i)⁻¹ • f (update z i ζ)

theorem coordCauchyIntegral_def (i : ι) (c : ι → ℂ) (ρ : ℝ) (f : (ι → ℂ) → F) (z : ι → ℂ) :
    coordCauchyIntegral i c ρ f z =
      (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c i, ρ), (ζ - z i)⁻¹ • f (update z i ζ) :=
  (rfl)

variable {i : ι} {c : ι → ℂ} {ρ : ℝ} {f : (ι → ℂ) → F} {z : ι → ℂ}

/-- **The coordinate Cauchy integral on the half radius.** If `‖z i - c i‖ ≤ ρ / 2` and
`‖f (update z i ζ)‖ ≤ M` for every `ζ` on the circle `C(c i, ρ)`, then the Cauchy integral of
`f` in the `i`-th coordinate is bounded by `2 * M` at `z`. -/
theorem norm_coordCauchyIntegral_le {M : ℝ} (hz : ‖z i - c i‖ ≤ ρ / 2)
    (hM : ∀ ζ ∈ sphere (c i) ρ, ‖f (update z i ζ)‖ ≤ M) :
    ‖coordCauchyIntegral i c ρ f z‖ ≤ 2 * M := by
  obtain rfl | hρ := (show 0 ≤ ρ by linarith [norm_nonneg (z i - c i)]).eq_or_lt
  · have hM₀ := (norm_nonneg _).trans (hM (c i) (by simp))
    simp only [coordCauchyIntegral_def, circleIntegral.integral_radius_zero, smul_zero,
      norm_zero]
    positivity
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun ζ ↦ (ζ - z i)⁻¹ • f (update z i ζ)) (c := c i) (C := (ρ / 2)⁻¹ * M) hρ.le
    fun ζ hζ ↦ by
      have hd : ρ / 2 ≤ ‖ζ - z i‖ := by
        have h₁ := norm_sub_le_norm_sub_add_norm_sub ζ (z i) (c i)
        rw [mem_sphere_iff_norm.1 hζ] at h₁
        linarith
      rw [norm_smul, norm_inv]
      exact mul_le_mul (inv_anti₀ (by positivity) hd) (hM ζ hζ) (norm_nonneg _)
        (by positivity)
  rw [coordCauchyIntegral_def]
  refine h.trans (le_of_eq ?_)
  field_simp

/-- The coordinate Cauchy integral is complex differentiable in the `i`-th coordinate at every
point of the open disc, as soon as the restriction of `f` to the circle is integrable. -/
theorem differentiableAt_coordCauchyIntegral_update [CompleteSpace F]
    (hf : CircleIntegrable (fun ζ ↦ f (update z i ζ)) (c i) ρ) (hzi : z i ∈ ball (c i) ρ) :
    DifferentiableAt ℂ (fun w ↦ coordCauchyIntegral i c ρ f (update z i w)) (z i) := by
  have hρ : 0 < ρ := pos_of_mem_ball hzi
  have hR : ((ρ.toNNReal : NNReal) : ℝ) = ρ := Real.coe_toNNReal _ hρ.le
  have hfun : (fun w ↦ coordCauchyIntegral i c ρ f (update z i w)) =
      fun w ↦ (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c i, ρ.toNNReal), (ζ - w)⁻¹ • f (update z i ζ) := by
    funext w
    simp only [coordCauchyIntegral_def, update_idem, update_self, hR]
  rw [hfun]
  have hps := hasFPowerSeriesOn_cauchy_integral (R := ρ.toNNReal) (by rwa [hR])
    (Real.toNNReal_pos.2 hρ)
  refine (hps.analyticAt_of_mem ?_).differentiableAt
  rw [Metric.eball_coe, hR]
  exact hzi

section Regularity

/-- The integrand of the coordinate Cauchy integral as a function of the point and the angle,
with the derivative of the parametrization of the circle. -/
private noncomputable def integrand (i : ι) (c : ι → ℂ) (ρ : ℝ) (f : (ι → ℂ) → F)
    (p : (ι → ℂ) × ℝ) : F :=
  (circleMap 0 ρ p.2 * I) • ((circleMap (c i) ρ p.2 - p.1 i)⁻¹ •
    f (update p.1 i (circleMap (c i) ρ p.2)))

private theorem coordCauchyIntegral_eq_integral (g : (ι → ℂ) → F) (x : ι → ℂ) :
    coordCauchyIntegral i c ρ g x =
      (2 * π * I : ℂ)⁻¹ • ∫ θ in 0..2 * π, integrand i c ρ g (x, θ) := by
  simp only [coordCauchyIntegral_def, circleIntegral, deriv_circleMap, integrand]

private theorem continuous_update_circleMap :
    Continuous fun p : (ι → ℂ) × ℝ ↦ update p.1 i (circleMap (c i) ρ p.2) :=
  continuous_fst.update i ((continuous_circleMap _ _).comp continuous_snd)

variable [Fintype ι]

/-- The open set of pairs `(x, θ)` at which the integrand is defined by a `C¹` function. -/
private def goodSet (i : ι) (c : ι → ℂ) (ρ : ℝ) (f : (ι → ℂ) → F) : Set ((ι → ℂ) × ℝ) :=
  {p | circleMap (c i) ρ p.2 - p.1 i ≠ 0} ∩
    {p | ContDiffAt ℝ 1 f (update p.1 i (circleMap (c i) ρ p.2))}

private theorem contDiff_update_circleMap :
    ContDiff ℝ 1 fun p : (ι → ℂ) × ℝ ↦ update p.1 i (circleMap (c i) ρ p.2) := by
  refine contDiff_pi.2 fun k ↦ ?_
  by_cases hk : k = i
  · subst hk
    simp only [update_self]
    exact (contDiff_circleMap (c k) ρ).comp contDiff_snd
  · simp only [update_of_ne hk]
    exact (contDiff_apply ℝ (fun _ : ι ↦ ℂ) k).comp contDiff_fst

private theorem isOpen_goodSet : IsOpen (goodSet i c ρ f) := by
  refine IsOpen.inter (isOpen_ne_fun ?_ continuous_const) ?_
  · exact ((continuous_circleMap _ _).comp continuous_snd).sub
      ((continuous_apply i).comp continuous_fst)
  · exact (TauCeti.isOpen_setOf_contDiffAt (𝕜 := ℝ) (n := 1) (f := f) (by simp)).preimage
      continuous_update_circleMap

private theorem contDiffOn_integrand : ContDiffOn ℝ 1 (integrand i c ρ f) (goodSet i c ρ f) := by
  have h₁ : ContDiff ℝ 1 fun p : (ι → ℂ) × ℝ ↦ circleMap 0 ρ p.2 * I :=
    ((contDiff_circleMap 0 ρ).comp contDiff_snd).mul contDiff_const
  have h₂ : ContDiffOn ℝ 1 (fun p : (ι → ℂ) × ℝ ↦ (circleMap (c i) ρ p.2 - p.1 i)⁻¹)
      (goodSet i c ρ f) :=
    (((contDiff_circleMap (c i) ρ).comp contDiff_snd).sub
      ((contDiff_apply ℝ (fun _ : ι ↦ ℂ) i).comp contDiff_fst :
        ContDiff ℝ 1 fun p : (ι → ℂ) × ℝ ↦ p.1 i)).contDiffOn.inv fun p hp ↦ hp.1
  have h₃ : ContDiffOn ℝ 1 (fun p : (ι → ℂ) × ℝ ↦ f (update p.1 i (circleMap (c i) ρ p.2)))
      (goodSet i c ρ f) := fun p hp ↦
    (hp.2.comp p contDiff_update_circleMap.contDiffAt).contDiffWithinAt
  exact h₁.contDiffOn.smul (h₂.smul h₃)

/-- Moving the `i`-th coordinate of a point of the closed polydisc within the closed disc keeps
it in the closed polydisc. -/
private theorem update_mem_closedBall (hρ : 0 ≤ ρ) (hz : ∀ k ≠ i, ‖z k - c k‖ ≤ ρ) {ζ : ℂ}
    (hζ : ‖ζ - c i‖ ≤ ρ) : update z i ζ ∈ closedBall c ρ := by
  rw [mem_closedBall, dist_pi_le_iff hρ]
  intro k
  by_cases hk : k = i
  · subst hk
    rwa [update_self, dist_eq_norm]
  · rw [update_of_ne hk, dist_eq_norm]
    exact hz k hk

/-- The points at which the coordinate Cauchy integral is `C¹`: for these, every pair `(z, θ)`
lies in `goodSet`. -/
private theorem mem_goodSet (hf : ∀ y ∈ closedBall c ρ, ContDiffAt ℝ 1 f y)
    (hzi : z i ∈ ball (c i) ρ) (hz : ∀ k ≠ i, ‖z k - c k‖ ≤ ρ) (θ : ℝ) :
    (z, θ) ∈ goodSet i c ρ f := by
  have hρ : 0 < ρ := pos_of_mem_ball hzi
  have hcirc : ‖circleMap (c i) ρ θ - c i‖ = ρ := by
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ]
  refine ⟨fun h ↦ ?_, hf _ ?_⟩
  · have h' : circleMap (c i) ρ θ = z i := sub_eq_zero.1 h
    rw [mem_ball, dist_eq_norm, ← h', hcirc] at hzi
    exact lt_irrefl _ hzi
  · exact update_mem_closedBall hρ.le hz hcirc.le

private theorem intervalIntegral_eq_integral_unitInterval_two_pi (h : ℝ → F) :
    ∫ θ in 0..2 * π, h θ = ∫ t : unitInterval, (2 * π) • h (2 * π * t) := by
  rw [integral_smul, ← TauCeti.intervalIntegral_eq_integral_unitInterval
    (fun t ↦ h (2 * π * t)), intervalIntegral.smul_integral_comp_mul_left, mul_zero, mul_one]

/-- **Regularity of the coordinate Cauchy integral.** If `f` is `C¹` at every point of the
closed sup-norm polydisc `closedBall c ρ`, then its Cauchy integral in the `i`-th coordinate is
`C¹` at every `z` with `z i` in the open disc `ball (c i) ρ` and `‖z k - c k‖ ≤ ρ` for `k ≠ i`. -/
theorem contDiffAt_coordCauchyIntegral (hf : ∀ y ∈ closedBall c ρ, ContDiffAt ℝ 1 f y)
    (hzi : z i ∈ ball (c i) ρ) (hz : ∀ k ≠ i, ‖z k - c k‖ ≤ ρ) :
    ContDiffAt ℝ 1 (coordCauchyIntegral i c ρ f) z := by
  let ι' : unitInterval → ℝ := fun t ↦ 2 * π * t
  have hι' : Continuous ι' := continuous_const.mul continuous_subtypeVal
  let U : Set (ι → ℂ) := {x | ∀ t, (x, ι' t) ∈ goodSet i c ρ f}
  have hU : IsOpen U := TauCeti.isOpen_forall_prodMk_mem hι' isOpen_goodSet
  have hI : ContDiffOn ℝ 1
      (fun x ↦ ∫ t : unitInterval, (2 * π) • integrand i c ρ f (x, ι' t)) U :=
    TauCeti.contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure unitInterval))
      (g := fun _ ↦ 2 * π) (F := integrand i c ρ f) (n := 1) (integrable_const _) hι'
      isOpen_goodSet contDiffOn_integrand (U := U) fun x hx t ↦ hx t
  have hzU : z ∈ U := fun t ↦ mem_goodSet hf hzi hz _
  refine ((hI.contDiffAt (hU.mem_nhds hzU)).const_smul (2 * π * I : ℂ)⁻¹).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [coordCauchyIntegral_eq_integral, intervalIntegral_eq_integral_unitInterval_two_pi, ι']

/-- **Derivatives of the coordinate Cauchy integral in the other coordinates.** Under the
hypotheses of `contDiffAt_coordCauchyIntegral`, the derivative of the Cauchy integral of `f` in
the `i`-th coordinate, in a direction `v` with `v i = 0`, is the Cauchy integral in the `i`-th
coordinate of the derivative of `f` in the direction `v`. -/
theorem fderiv_coordCauchyIntegral_apply (hf : ∀ y ∈ closedBall c ρ, ContDiffAt ℝ 1 f y)
    (hzi : z i ∈ ball (c i) ρ) (hz : ∀ k ≠ i, ‖z k - c k‖ ≤ ρ) {v : ι → ℂ} (hv : v i = 0) :
    fderiv ℝ (coordCauchyIntegral i c ρ f) z v =
      coordCauchyIntegral i c ρ (fun y ↦ fderiv ℝ f y v) z := by
  have hline : HasDerivAt (fun t : ℝ ↦ z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h₁ : HasDerivAt (fun t : ℝ ↦ coordCauchyIntegral i c ρ f (z + t • v))
      (fderiv ℝ (coordCauchyIntegral i c ρ f) z v) 0 :=
    ((contDiffAt_coordCauchyIntegral hf hzi hz).differentiableAt one_ne_zero).hasFDerivAt
      |>.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  refine h₁.unique ?_
  -- Differentiate under the integral sign along the real line `t ↦ z + t • v`.
  let G : ℝ × ℝ → F := fun q ↦ integrand i c ρ f (z + q.1 • v, q.2)
  let U : Set (ℝ × ℝ) := {q | (z + q.1 • v, q.2) ∈ goodSet i c ρ f}
  have hmap : Continuous fun q : ℝ × ℝ ↦ (z + q.1 • v, q.2) :=
    (continuous_const.add (continuous_fst.smul continuous_const)).prodMk continuous_snd
  have hU : IsOpen U := isOpen_goodSet.preimage hmap
  have hG : ContDiffOn ℝ 1 G U :=
    contDiffOn_integrand.comp
      ((contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk contDiff_snd).contDiffOn
      fun q hq ↦ hq
  have hU₀ (θ : ℝ) : ((0 : ℝ), θ) ∈ U := by
    simpa [U] using mem_goodSet hf hzi hz θ
  have hsub : {(0 : ℝ)} ×ˢ uIcc 0 (2 * π) ⊆ U := by
    rintro ⟨s, θ⟩ ⟨hs, -⟩
    rw [mem_singleton_iff] at hs
    subst hs
    exact hU₀ θ
  obtain ⟨-, hderiv⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hU hG hsub
  -- The partial derivative of the integrand in `t`.
  have hpart (θ : ℝ) : fderiv ℝ G (0, θ) (1, 0) =
      integrand i c ρ (fun y ↦ fderiv ℝ f y v) (z, θ) := by
    have hq : ((0 : ℝ), θ) ∈ U := hU₀ θ
    have hGd : HasDerivAt (fun s : ℝ ↦ G (s, θ)) (fderiv ℝ G (0, θ) (1, 0)) 0 :=
      ((hG.differentiableOn one_ne_zero _ hq).differentiableAt (hU.mem_nhds hq)).hasFDerivAt
        |>.comp_hasDerivAt_of_eq (0 : ℝ)
          ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) θ) :
            HasDerivAt (fun s : ℝ ↦ (s, θ)) ((1 : ℝ), (0 : ℝ)) 0) rfl
    set ζ := circleMap (c i) ρ θ
    have hfy : DifferentiableAt ℝ f (update z i ζ) :=
      (mem_goodSet hf hzi hz θ).2.differentiableAt one_ne_zero
    have hGeq : (fun s : ℝ ↦ G (s, θ)) =
        fun s ↦ (circleMap 0 ρ θ * I) • ((ζ - z i)⁻¹ • f (update z i ζ + s • v)) := by
      funext s
      have hupd : update (z + s • v) i ζ = update z i ζ + s • v := by
        funext k
        by_cases hk : k = i
        · subst hk
          simp [hv]
        · simp [update_of_ne hk]
      simp only [G, integrand, Pi.add_apply, Pi.smul_apply, hv, smul_zero, add_zero]
      exact congrArg (fun y ↦ (circleMap 0 ρ θ * I) • (ζ - z i)⁻¹ • f y) hupd
    have hfd : HasDerivAt (fun s : ℝ ↦ f (update z i ζ + s • v))
        (fderiv ℝ f (update z i ζ) v) 0 :=
      hfy.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
        (by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (update z i ζ))
        (by simp)
    rw [hGeq] at hGd
    exact hGd.unique ((hfd.const_smul _).const_smul _)
  have h₂ : HasDerivAt (fun t : ℝ ↦ coordCauchyIntegral i c ρ f (z + t • v))
      ((2 * π * I : ℂ)⁻¹ • ∫ θ in 0..2 * π, fderiv ℝ G (0, θ) (1, 0)) 0 := by
    simp only [coordCauchyIntegral_eq_integral]
    exact hderiv.const_smul _
  simpa only [hpart, coordCauchyIntegral_eq_integral] using h₂

omit [Fintype ι] in
/-- Integrability of the integrand of a coordinate Cauchy integral, for a function continuous on
the circle of the `i`-th coordinate through `z`. -/
private theorem circleIntegrable_sub_inv_smul {g : (ι → ℂ) → F} (hzi : z i ∈ ball (c i) ρ)
    (hg : ContinuousOn (fun ζ ↦ g (update z i ζ)) (sphere (c i) ρ)) :
    CircleIntegrable (fun ζ ↦ (ζ - z i)⁻¹ • g (update z i ζ)) (c i) ρ := by
  refine ContinuousOn.circleIntegrable (pos_of_mem_ball hzi).le
    (((continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ ↦ ?_).smul hg)
  intro h
  have h' : ζ = z i := sub_eq_zero.1 h
  rw [mem_sphere] at hζ
  rw [mem_ball, ← h', hζ] at hzi
  exact lt_irrefl _ hzi

/-- **The coordinate Cauchy integral commutes with the other `∂/∂(conj z_j)`.** Under the
hypotheses of `contDiffAt_coordCauchyIntegral`, for `j ≠ i` the conjugate Wirtinger derivative in
the `j`-th coordinate of the Cauchy integral of `f` in the `i`-th coordinate is the Cauchy
integral in the `i`-th coordinate of the conjugate Wirtinger derivative of `f` in the `j`-th
coordinate. -/
theorem conjWirtingerDeriv_coordCauchyIntegral_single
    (hf : ∀ y ∈ closedBall c ρ, ContDiffAt ℝ 1 f y) (hzi : z i ∈ ball (c i) ρ)
    (hz : ∀ k ≠ i, ‖z k - c k‖ ≤ ρ) {j : ι} (hj : j ≠ i) :
    TauCeti.conjWirtingerDeriv (coordCauchyIntegral i c ρ f) z (Pi.single j 1) =
      coordCauchyIntegral i c ρ
        (fun y ↦ TauCeti.conjWirtingerDeriv f y (Pi.single j 1)) z := by
  set e : ι → ℂ := Pi.single j 1
  have he : e i = 0 := Pi.single_eq_of_ne hj.symm _
  have hIe : (I • e) i = 0 := by simp [he]
  -- The derivatives of `f` in the directions `e` and `I • e` are integrable on the circle.
  have hint (w : ι → ℂ) :
      CircleIntegrable (fun ζ ↦ (ζ - z i)⁻¹ • fderiv ℝ f (update z i ζ) w) (c i) ρ := by
    have hfV : ContDiffOn ℝ 1 f {y | ContDiffAt ℝ 1 f y} := fun y hy ↦ hy.contDiffWithinAt
    have hD : ContinuousOn (fun y ↦ fderiv ℝ f y) {y | ContDiffAt ℝ 1 f y} :=
      hfV.continuousOn_fderiv_of_isOpen (TauCeti.isOpen_setOf_contDiffAt (by simp)) le_rfl
    refine circleIntegrable_sub_inv_smul (g := fun y ↦ fderiv ℝ f y w) hzi ?_
    refine (hD.comp (continuous_const.update i continuous_id).continuousOn fun ζ hζ ↦ ?_).clm_apply
      continuousOn_const
    exact hf _ (update_mem_closedBall (pos_of_mem_ball hzi).le hz
      (mem_sphere_iff_norm.1 hζ).le)
  have hfun : (fun ζ ↦ (ζ - z i)⁻¹ • TauCeti.conjWirtingerDeriv f (update z i ζ) e) =
      fun ζ ↦ (2 : ℂ)⁻¹ • ((ζ - z i)⁻¹ • fderiv ℝ f (update z i ζ) e +
        I • ((ζ - z i)⁻¹ • fderiv ℝ f (update z i ζ) (I • e))) := by
    funext ζ
    rw [TauCeti.conjWirtingerDeriv_apply]
    module
  have hB : CircleIntegrable
      (fun ζ ↦ I • ((ζ - z i)⁻¹ • fderiv ℝ f (update z i ζ) (I • e))) (c i) ρ :=
    (hint (I • e)).const_smul
  rw [TauCeti.conjWirtingerDeriv_apply, fderiv_coordCauchyIntegral_apply hf hzi hz he,
    fderiv_coordCauchyIntegral_apply hf hzi hz hIe, coordCauchyIntegral_def,
    coordCauchyIntegral_def, coordCauchyIntegral_def, hfun, circleIntegral.integral_smul,
    circleIntegral.integral_add (hint e) hB,
    circleIntegral.integral_smul]
  module

end Regularity

end SymplecticGeometry

end
