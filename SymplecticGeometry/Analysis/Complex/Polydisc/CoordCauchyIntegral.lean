/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import SymplecticGeometry.Analysis.Calculus.ContDiff.Pi
import SymplecticGeometry.Analysis.Complex.Wirtinger.Pi
import SymplecticGeometry.MeasureTheory.Constructions.UnitInterval
import TauCeti.Analysis.Calculus.ContDiff.IsOpen
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic

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
* `SymplecticGeometry.contDiffAt_coordCauchyIntegral`: if `z i` lies in the open disc and `f` is
  `C¹` at every point `update z i ζ` with `ζ` on the circle, the coordinate Cauchy integral is
  `C¹` at `z`.
* `SymplecticGeometry.differentiableAt_coordCauchyIntegral_update`: it is complex
  differentiable in the `i`-th coordinate, and
  `SymplecticGeometry.conjWirtingerDeriv_coordCauchyIntegral_single_self` says that its
  conjugate Wirtinger derivative in that coordinate vanishes.
* `SymplecticGeometry.fderiv_coordCauchyIntegral_apply`: its derivative in a direction `v` with
  `v i = 0` is the coordinate Cauchy integral of the derivative of `f` in that direction.
* `SymplecticGeometry.conjWirtingerDeriv_coordCauchyIntegral`: it commutes with the conjugate
  Wirtinger derivative in every direction `e` with `e i = 0`, and in particular
  (`SymplecticGeometry.conjWirtingerDeriv_coordCauchyIntegral_single`) with `∂/∂(conj z_j)` for
  `j ≠ i`.

## Implementation notes

Differentiation under the integral sign uses Tau Ceti's
`TauCeti.contDiffOn_integral_smul_of_contDiffOn`, for the integrand as a function of `z` and of the
angle, rescaled to the unit interval, and `TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn` for
derivatives along real lines. Holomorphy in the `i`-th coordinate is Mathlib's
`Complex.hasDerivAt_circleIntegral_sub_inv_smul`.

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

/-- The coordinate Cauchy integral at `z` depends only on the values of `f` at the points
`update z i ζ` with `ζ` on the circle `C(c i, ρ)`. -/
theorem coordCauchyIntegral_congr {g : (ι → ℂ) → F} (hρ : 0 ≤ ρ)
    (h : ∀ ζ ∈ sphere (c i) ρ, f (update z i ζ) = g (update z i ζ)) :
    coordCauchyIntegral i c ρ f z = coordCauchyIntegral i c ρ g z := by
  simp only [coordCauchyIntegral_def]
  exact congrArg _ (circleIntegral.integral_congr hρ fun ζ hζ ↦ by simp only [h ζ hζ])

@[simp]
theorem coordCauchyIntegral_zero (i : ι) (c : ι → ℂ) (ρ : ℝ) :
    coordCauchyIntegral i c ρ (0 : (ι → ℂ) → F) = 0 := by
  funext z
  simp [coordCauchyIntegral_def, circleIntegral]

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
theorem differentiableAt_coordCauchyIntegral_update
    (hf : CircleIntegrable (fun ζ ↦ f (update z i ζ)) (c i) ρ) (hzi : z i ∈ ball (c i) ρ) :
    DifferentiableAt ℂ (fun w ↦ coordCauchyIntegral i c ρ f (update z i w)) (z i) := by
  simp only [coordCauchyIntegral_def, update_idem, update_self]
  exact (hasDerivAt_circleIntegral_sub_inv_smul hf
    ((mem_ball.1 hzi).trans_le (le_abs_self ρ)).ne).differentiableAt.const_smul _

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
    (hp.2.comp p (contDiff_fst.update
      ((contDiff_circleMap (c i) ρ).comp contDiff_snd)).contDiffAt).contDiffWithinAt
  exact h₁.contDiffOn.smul (h₂.smul h₃)


/-- The points at which the coordinate Cauchy integral is `C¹`: for these, every pair `(z, θ)`
lies in `goodSet`. -/
private theorem mem_goodSet (hzi : z i ∈ ball (c i) ρ)
    (hf : ∀ ζ ∈ sphere (c i) ρ, ContDiffAt ℝ 1 f (update z i ζ)) (θ : ℝ) :
    (z, θ) ∈ goodSet i c ρ f := by
  have hρ : 0 < ρ := pos_of_mem_ball hzi
  refine ⟨fun h ↦ ?_, hf _ (circleMap_mem_sphere _ hρ.le θ)⟩
  have hcirc : ‖circleMap (c i) ρ θ - c i‖ = ρ := by
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ]
  have h' : circleMap (c i) ρ θ = z i := sub_eq_zero.1 h
  rw [mem_ball, dist_eq_norm, ← h', hcirc] at hzi
  exact lt_irrefl _ hzi

/-- **Regularity of the coordinate Cauchy integral.** If `z i` lies in the open disc
`ball (c i) ρ` and `f` is `C¹` at every point `update z i ζ` with `ζ` on the circle
`sphere (c i) ρ`, then the Cauchy integral of `f` in the `i`-th coordinate is `C¹` at `z`. -/
theorem contDiffAt_coordCauchyIntegral (hzi : z i ∈ ball (c i) ρ)
    (hf : ∀ ζ ∈ sphere (c i) ρ, ContDiffAt ℝ 1 f (update z i ζ)) :
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
  have hzU : z ∈ U := fun t ↦ mem_goodSet hzi hf _
  refine ((hI.contDiffAt (hU.mem_nhds hzU)).const_smul (2 * π * I : ℂ)⁻¹).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [coordCauchyIntegral_eq_integral, intervalIntegral_eq_integral_unitInterval_smul, ι']

omit [Fintype ι] in
/-- Along a real line `s ↦ z + s • v` with `v i = 0`, the derivative at `s = 0` of the integrand
of the coordinate Cauchy integral of `f` is the integrand for the derivative of `f` in the
direction `v`. -/
private theorem hasDerivAt_integrand_line [Finite ι] {v : ι → ℂ} (hv : v i = 0) {θ : ℝ}
    (hf : DifferentiableAt ℝ f (update z i (circleMap (c i) ρ θ))) :
    HasDerivAt (fun s : ℝ ↦ integrand i c ρ f (z + s • v, θ))
      (integrand i c ρ (fun y ↦ fderiv ℝ f y v) (z, θ)) 0 := by
  have := Fintype.ofFinite ι
  -- Since `v i = 0`, moving along the line does not change the `i`-th coordinate.
  have hG : (fun s : ℝ ↦ integrand i c ρ f (z + s • v, θ)) = fun s ↦
      (circleMap 0 ρ θ * I) • ((circleMap (c i) ρ θ - z i)⁻¹ •
        f (update z i (circleMap (c i) ρ θ) + s • v)) := by
    funext s
    have h := update_add z (s • v) i (circleMap (c i) ρ θ) 0
    rw [add_zero, (update_eq_self_iff (f := s • v) (a := i) (b := 0)).2 (by simp [hv])] at h
    simp only [integrand, Pi.add_apply, Pi.smul_apply, hv, smul_zero, add_zero, h]
  have hline : HasDerivAt (fun s : ℝ ↦ update z i (circleMap (c i) ρ θ) + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add
      (update z i (circleMap (c i) ρ θ))
  have hfd : HasDerivAt (fun s : ℝ ↦ f (update z i (circleMap (c i) ρ θ) + s • v))
      (fderiv ℝ f (update z i (circleMap (c i) ρ θ)) v) 0 :=
    hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  rw [hG]
  exact (hfd.const_smul _).const_smul _

/-- **Derivatives of the coordinate Cauchy integral in the other coordinates.** Under the
hypotheses of `contDiffAt_coordCauchyIntegral`, the derivative of the Cauchy integral of `f` in
the `i`-th coordinate, in a direction `v` with `v i = 0`, is the Cauchy integral in the `i`-th
coordinate of the derivative of `f` in the direction `v`. -/
theorem fderiv_coordCauchyIntegral_apply (hzi : z i ∈ ball (c i) ρ)
    (hf : ∀ ζ ∈ sphere (c i) ρ, ContDiffAt ℝ 1 f (update z i ζ)) {v : ι → ℂ} (hv : v i = 0) :
    fderiv ℝ (coordCauchyIntegral i c ρ f) z v =
      coordCauchyIntegral i c ρ (fun y ↦ fderiv ℝ f y v) z := by
  have hline : HasDerivAt (fun t : ℝ ↦ z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h₁ : HasDerivAt (fun t : ℝ ↦ coordCauchyIntegral i c ρ f (z + t • v))
      (fderiv ℝ (coordCauchyIntegral i c ρ f) z v) 0 :=
    ((contDiffAt_coordCauchyIntegral hzi hf).differentiableAt one_ne_zero).hasFDerivAt
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
    simpa [U] using mem_goodSet hzi hf θ
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
    exact hGd.unique (hasDerivAt_integrand_line hv
      ((mem_goodSet hzi hf θ).2.differentiableAt one_ne_zero))
  have h₂ : HasDerivAt (fun t : ℝ ↦ coordCauchyIntegral i c ρ f (z + t • v))
      ((2 * π * I : ℂ)⁻¹ • ∫ θ in 0..2 * π, fderiv ℝ G (0, θ) (1, 0)) 0 := by
    simp only [coordCauchyIntegral_eq_integral]
    exact hderiv.const_smul _
  simpa only [hpart, coordCauchyIntegral_eq_integral] using h₂

/-- **The coordinate Cauchy integral commutes with `∂̄` in the other directions.** Under the
hypotheses of `contDiffAt_coordCauchyIntegral`, for every direction `e` with `e i = 0`, the
conjugate Wirtinger derivative in the direction `e` of the Cauchy integral of `f` in the `i`-th
coordinate is the Cauchy integral in the `i`-th coordinate of the conjugate Wirtinger derivative
of `f` in the direction `e`. -/
theorem conjWirtingerDeriv_coordCauchyIntegral (hzi : z i ∈ ball (c i) ρ)
    (hf : ∀ ζ ∈ sphere (c i) ρ, ContDiffAt ℝ 1 f (update z i ζ)) {e : ι → ℂ} (he : e i = 0) :
    TauCeti.conjWirtingerDeriv (coordCauchyIntegral i c ρ f) z e =
      coordCauchyIntegral i c ρ (fun y ↦ TauCeti.conjWirtingerDeriv f y e) z := by
  have hIe : (I • e) i = 0 := by simp [he]
  -- The derivatives of `f` in the directions `e` and `I • e` are integrable on the circle.
  have hint (w : ι → ℂ) :
      CircleIntegrable (fun ζ ↦ (ζ - z i)⁻¹ • fderiv ℝ f (update z i ζ) w) (c i) ρ := by
    have hg : ContinuousOn (fun ζ ↦ fderiv ℝ f (update z i ζ) w) (sphere (c i) ρ) :=
      fun ζ hζ ↦ ((((hf ζ hζ).continuousAt_fderiv one_ne_zero).comp
        (continuous_const.update i continuous_id).continuousAt).clm_apply
          continuousAt_const).continuousWithinAt
    simpa only [zpow_neg_one] using (hg.circleIntegrable (pos_of_mem_ball hzi).le).sub_zpow_smul
      (-1) ((mem_ball.1 hzi).trans_le (le_abs_self ρ)).ne
  have hfun : (fun ζ ↦ (ζ - z i)⁻¹ • TauCeti.conjWirtingerDeriv f (update z i ζ) e) =
      fun ζ ↦ (2 : ℂ)⁻¹ • ((ζ - z i)⁻¹ • fderiv ℝ f (update z i ζ) e +
        I • ((ζ - z i)⁻¹ • fderiv ℝ f (update z i ζ) (I • e))) := by
    funext ζ
    rw [TauCeti.conjWirtingerDeriv_apply]
    module
  have hB : CircleIntegrable
      (fun ζ ↦ I • ((ζ - z i)⁻¹ • fderiv ℝ f (update z i ζ) (I • e))) (c i) ρ :=
    (hint (I • e)).const_smul
  rw [TauCeti.conjWirtingerDeriv_apply, fderiv_coordCauchyIntegral_apply hzi hf he,
    fderiv_coordCauchyIntegral_apply hzi hf hIe, coordCauchyIntegral_def,
    coordCauchyIntegral_def, coordCauchyIntegral_def, hfun, circleIntegral.integral_smul,
    circleIntegral.integral_add (hint e) hB,
    circleIntegral.integral_smul]
  module

/-- **The coordinate Cauchy integral commutes with the other `∂/∂(conj z_j)`.** Under the
hypotheses of `contDiffAt_coordCauchyIntegral`, for `j ≠ i` the conjugate Wirtinger derivative in
the `j`-th coordinate of the Cauchy integral of `f` in the `i`-th coordinate is the Cauchy
integral in the `i`-th coordinate of the conjugate Wirtinger derivative of `f` in the `j`-th
coordinate. -/
theorem conjWirtingerDeriv_coordCauchyIntegral_single (hzi : z i ∈ ball (c i) ρ)
    (hf : ∀ ζ ∈ sphere (c i) ρ, ContDiffAt ℝ 1 f (update z i ζ)) {j : ι} (hj : j ≠ i) :
    TauCeti.conjWirtingerDeriv (coordCauchyIntegral i c ρ f) z (Pi.single j 1) =
      coordCauchyIntegral i c ρ
        (fun y ↦ TauCeti.conjWirtingerDeriv f y (Pi.single j 1)) z :=
  conjWirtingerDeriv_coordCauchyIntegral hzi hf (Pi.single_eq_of_ne hj.symm _)

/-- **The coordinate Cauchy integral is holomorphic in its own coordinate.** Under the hypotheses
of `contDiffAt_coordCauchyIntegral`, the conjugate Wirtinger derivative in the `i`-th coordinate
of the Cauchy integral of `f` in the `i`-th coordinate vanishes at `z`. -/
theorem conjWirtingerDeriv_coordCauchyIntegral_single_self (hzi : z i ∈ ball (c i) ρ)
    (hf : ∀ ζ ∈ sphere (c i) ρ, ContDiffAt ℝ 1 f (update z i ζ)) :
    TauCeti.conjWirtingerDeriv (coordCauchyIntegral i c ρ f) z (Pi.single i 1) = 0 := by
  have hcont : ContinuousOn (fun ζ ↦ f (update z i ζ)) (sphere (c i) ρ) := fun ζ hζ ↦
    ((hf ζ hζ).continuousAt.comp
      (continuous_const.update i continuous_id).continuousAt).continuousWithinAt
  have hd := differentiableAt_coordCauchyIntegral_update
    (hcont.circleIntegrable (pos_of_mem_ball hzi).le) hzi
  have hC := (contDiffAt_coordCauchyIntegral hzi hf).differentiableAt one_ne_zero
  rw [← update_eq_self i z] at hC
  have h := TauCeti.conjWirtingerDeriv_comp_update hC 1
  rw [update_eq_self] at h
  rw [← h, hd.conjWirtingerDeriv_eq_zero, zero_apply]

end Regularity

end SymplecticGeometry

end
