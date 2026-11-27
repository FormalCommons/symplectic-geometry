/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Attached
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ComplexFrame
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import Mathlib.Geometry.Manifold.Diffeomorph

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import SymplecticGeometry.Algebra.Order.Ring.Basic
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Radial
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Coordinates
import SymplecticGeometry.Analysis.Calculus.BumpFunction.UnitSlope
import SymplecticGeometry.Analysis.Calculus.FDeriv.Radial
import SymplecticGeometry.Analysis.Normed.Module.Ball.Shell
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# Frames adapted to the attaching sphere of a disc

Let `M` be a complex manifold modelled on `E`, `φ : M → ℝ` smooth and `ι : ℝᵏ → M` a smooth
immersion with totally real tangent images, attached J-orthogonally to `{φ ≤ 0}`
(`SymplecticGeometry.IsJOrthogonallyAttached`). With `dim_ℂ E = k + m`,
`SymplecticGeometry.exists_complexFrame_mfderiv` gives complex-linear isomorphisms
`A x : ℂᵏ × ℂᵐ → T_(ι x) M`, smooth in tangent coordinates, that extend `dι x` along the model
disc. This file corrects them so that, along the boundary sphere, the second factor `ℂᵐ` lies
in the kernel of `dφ`. This is the comparison of first-order data along the sphere in Step 3 of
the proof of Cieliebak–Eliashberg's Theorem 8.5.

Write `x₀ = (modelDisc k m x).1` for the point `x` seen in `ℂᵏ`, and `λ x`, `μ x` for the
complex-linear extensions (`StrongDual.extendRCLike`) of `z ↦ dφ (A x (z, 0))` and
`w ↦ dφ (A x (0, w))`. On the sphere the real part of `λ x x₀` is `dφ (dι x x)`, which is
negative by `IsJOrthogonallyAttached.mvfderiv_mfderiv_self_neg`, so `λ x x₀ ≠ 0` on an open set
`S` containing the sphere. With a smooth function `χ` equal to `1` near the sphere and with
topological support in `S` (Tau Ceti's `IsCompact.exists_contDiff_cutoff_eventuallyEq_one`), the
new frame is `A x ∘ U x`, where `U x (z, w) = (z - μ x w • (χ x • (λ x x₀)⁻¹) • x₀, w)`. The map
`U x` is complex linear and unipotent, so the new frame is still invertible and complex linear;
`U x` fixes `ℂᵏ × 0`, so the new frame still extends `dι x`; and `U x` depends smoothly on `x`.

The coefficients `λ x` and `μ x` depend smoothly on `x` because `x ↦ dφ (ι x) ∘ A x` does
(`SymplecticGeometry.contMDiffAt_mvfderiv_comp_of_inTangentCoordinates`) and
`StrongDual.extendRCLikeL` is a continuous real-linear equivalence; the coefficient
`χ x • (λ x x₀)⁻¹` is smooth by Tau Ceti's `ContDiffOn.contDiff_smul_of_tsupport_subset`. Unlike
a cutoff in `‖x‖`, the function `χ` needs neither an annulus around the sphere nor care at the
origin.

The file also builds the radial factor of a reparametrization `x ↦ τ x • x` of the disc that
makes the radial derivative of `φ ∘ ι` equal to `-2` along the sphere, as in Step 2 of the proof
of Theorem 8.5 and in Corollary 8.1 of Cieliebak–Eliashberg. Let `F` be a real inner product
space of finite dimension and `g : F → ℝ` smooth with `a y = dg y y < 0` on the unit sphere.
Then `SymplecticGeometry.exists_contDiff_fderiv_apply_self_eq_on_sphere` gives
`τ y = 1 + h (‖y‖ - 1) * b y` with `b = -2 / a - 1`, smooth where `a < 0`, and a profile `h`
from `SymplecticGeometry.exists_contDiff_deriv_zero_eq_one_abs_le`: `h 0 = 0` and `h' 0 = 1`
make `dτ x x = b x` on the sphere, and `h` is supported in a thin shell around the sphere where
`a < 0`, with height and slope error small against the bounds of `b` and `db y y` on that shell,
so that `τ` and `τ + dτ y y` stay positive. Away from `0` the norm is smooth because `F` has an
inner product; Tau Ceti's `ContDiffOn.contDiff_smul_of_tsupport_subset` makes `τ` smooth on all
of `F`.

For `g = φ ∘ ι`, with `ι` attached J-orthogonally to `{φ ≤ 0}`, this `τ` gives the
reparametrization itself: `SymplecticGeometry.radialSmulDiffeomorph` makes `σ x = τ x • x` a
smooth diffeomorphism that keeps the open unit ball, and on the sphere `σ x = x` and
`dσ x x = (1 + dτ x x) • x`, so that the radial derivative of `φ ∘ ι ∘ σ` there is
`(1 + dτ x x) * dg x x = -2`. By
`SymplecticGeometry.IsJOrthogonallyAttached.comp_of_mfderiv_apply_self_eq_smul`, the disc
`ι ∘ σ` is again attached J-orthogonally.

## Main results

* `SymplecticGeometry.IsJOrthogonallyAttached.exists_complexFrame_mfderiv_ker`: along a disc
  attached J-orthogonally to `{φ ≤ 0}` there is a frame with the properties of
  `exists_complexFrame_mfderiv` whose second factor lies in the kernel of `dφ` along the sphere.
* `SymplecticGeometry.exists_contDiff_fderiv_apply_self_eq_on_sphere`: a smooth positive radial
  factor `τ`, equal to `1` near `0`, on the unit sphere and far out, with `τ + dτ y y > 0` and a
  prescribed radial derivative `dτ x x = -2 / dg x x - 1` on the sphere.
* `SymplecticGeometry.IsJOrthogonallyAttached.exists_smul_self_diffeomorph_mvfderiv_comp_eq_neg_two`
  gives a radial diffeomorphism `σ x = τ x • x`, keeping the open unit ball, after which
  the radial derivative of `φ` along the attached disc `ι ∘ σ` is `-2` on the sphere.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Corollary 8.1, and Steps 2 and 3 of the proof of Theorem 8.5.
-/

public section

noncomputable section

open Manifold Set Filter Metric
open scoped ContDiff Topology TauCeti.ComplexManifold

namespace SymplecticGeometry

section Frame

open ContinuousLinearMap Module TauCeti TauCeti.SmoothAlmostComplexStructure

variable {k m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

variable [FiniteDimensional ℂ E]

namespace IsJOrthogonallyAttached

/-- **Complex frames adapted to the attaching sphere.** Let `M` be a complex manifold modelled on
`E`, with `dim_ℂ E = k + m`, `φ : M → ℝ` smooth and `ι : ℝᵏ → M` a smooth immersion with totally
real tangent images, attached J-orthogonally to `{φ ≤ 0}`. There are real-linear maps
`A x : ℂᵏ × ℂᵐ → T_(ι x) M`, smooth in tangent coordinates along the model disc
`modelDisc k m`, each invertible and complex linear, such that `A x` composed with the
differential of `modelDisc k m` at `x` is the differential of `ι` at `x`, and such that for `x`
on the unit sphere, `dφ` vanishes on the image `A x (0 × ℂᵐ)` of the second factor. -/
theorem exists_complexFrame_mfderiv_ker {φ : M → ℝ} {ι : EuclideanSpace ℝ (Fin k) → M}
    (hι : IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ∞ ι)
    (hιR : ∀ x, IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι x)).toLinearMap
      (LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x).toLinearMap))
    (hdim : finrank ℂ E = k + m)
    (h : IsJOrthogonallyAttached E φ ι) (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) :
    ∃ A : ∀ x, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ]
        TangentSpace 𝓘(ℝ, E) (ι x),
      (∀ x₀, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
        𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ] E) ∞
        (inTangentCoordinates 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
          𝓘(ℝ, E) (modelDisc k m) ι A x₀) x₀) ∧
      (∀ x, (A x).IsInvertible) ∧
      (∀ x v, A x (Complex.I • v) = ofComplexManifold E M (ι x) (A x v)) ∧
      (∀ x, (A x).comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
          𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelDisc k m) x) =
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x) ∧
      ∀ x, ‖x‖ = 1 → ∀ w, mvfderiv 𝓘(ℝ, E) φ (ι x) (A x (0, w)) = 0 := by
  -- Outline: start from the frame `A` of `exists_complexFrame_mfderiv`; read `dφ` through it as
  -- a smooth family `D` of real forms, and take their complex-linear extensions `lam`, `μ` on the
  -- two factors; on an open set `S` around the sphere `lam x x₀ ≠ 0`, and a cutoff `χ` supported
  -- in `S` gives a smooth coefficient `c`; the frame is `A x ∘ (id - N x)` for the nilpotent,
  -- complex-linear correction `N x (z, w) = (μ x w • c x • x₀, 0)`.
  obtain ⟨A, hAs, hAinv, hAI, hAd⟩ := exists_complexFrame_mfderiv hι hιR hdim
  -- The differential of `φ` read through the frame, a smooth family of maps `ℂᵏ × ℂᵐ → ℝ`.
  let D (x : EuclideanSpace ℝ (Fin k)) :
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ] ℝ :=
    (mvfderiv 𝓘(ℝ, E) φ (ι x)).comp (A x)
  have hD : ContDiff ℝ ∞ D := contMDiff_iff_contDiff.1 fun x₀ ↦
    contMDiffAt_mvfderiv_comp_of_inTangentCoordinates 𝓘(ℝ, E) (hφ _) (hι.contMDiff x₀) (hAs x₀)
      le_rfl
  -- The point `x` seen in `ℂᵏ`.
  let p (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℂ (Fin k) := (modelDisc k m x).1
  have hp : ContDiff ℝ ∞ p := (ContinuousLinearMap.fst ℝ _ _ ∘L modelDisc k m).contDiff
  -- The complex-linear extensions of `dφ ∘ A x` on each factor, smooth in `x` because
  -- `StrongDual.extendRCLikeL` is a continuous real-linear equivalence.
  let lam (x : EuclideanSpace ℝ (Fin k)) : StrongDual ℂ (EuclideanSpace ℂ (Fin k)) :=
    StrongDual.extendRCLikeL ((D x).comp (inl ℝ _ _))
  let μ (x : EuclideanSpace ℝ (Fin k)) : StrongDual ℂ (EuclideanSpace ℂ (Fin m)) :=
    StrongDual.extendRCLikeL ((D x).comp (inr ℝ _ _))
  have hlam : ContDiff ℝ ∞ fun x ↦ (lam x).restrictScalars ℝ :=
    ((restrictScalarsL ℂ _ ℂ ℝ ℝ).comp
      (StrongDual.extendRCLikeL (𝕜 := ℂ) (F := EuclideanSpace ℂ (Fin k))).toContinuousLinearMap
      ).contDiff.comp (hD.clm_comp contDiff_const)
  have hμ : ContDiff ℝ ∞ fun x ↦ (μ x).restrictScalars ℝ :=
    ((restrictScalarsL ℂ _ ℂ ℝ ℝ).comp
      (StrongDual.extendRCLikeL (𝕜 := ℂ) (F := EuclideanSpace ℂ (Fin m))).toContinuousLinearMap
      ).contDiff.comp (hD.clm_comp contDiff_const)
  have hz (x : EuclideanSpace ℝ (Fin k)) (z : EuclideanSpace ℂ (Fin k)) :
      D x (z, 0) = (lam x z).re := by
    rw [show lam x = _ from StrongDual.extendRCLikeL_apply _]
    exact (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) ((D x).comp (inl ℝ _ _)) _).symm
  have hw (x : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℂ (Fin m)) :
      D x (0, w) = (μ x w).re := by
    rw [show μ x = _ from StrongDual.extendRCLikeL_apply _]
    exact (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) ((D x).comp (inr ℝ _ _)) _).symm
  -- The number `λ x x₀`, smooth in `x`, with negative real part on the sphere.
  let a (x : EuclideanSpace ℝ (Fin k)) : ℂ := lam x (p x)
  have ha : ContDiff ℝ ∞ a := hlam.clm_apply hp
  have ha_re (x : EuclideanSpace ℝ (Fin k)) : (a x).re =
      mvfderiv 𝓘(ℝ, E) φ (ι x) (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x x) := by
    rw [← hz, ← hAd x, mfderiv_modelDisc]
    exact congrArg (fun v ↦ mvfderiv 𝓘(ℝ, E) φ (ι x) (A x v))
      (Prod.ext rfl (modelDisc_apply_snd x).symm)
  -- The open set where `λ x x₀` does not vanish contains the sphere.
  let S : Set (EuclideanSpace ℝ (Fin k)) := {x | (a x).re < 0}
  have hS : IsOpen S := isOpen_lt (Complex.continuous_re.comp ha.continuous) continuous_const
  have hsphere : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ⊆ S := fun x hx ↦ by
    have hx : ‖x‖ = 1 := by simpa using hx
    -- Membership in `S` is the inequality that defines it.
    change (a x).re < 0
    rw [ha_re]
    exact h.mvfderiv_mfderiv_self_neg x hx
  -- The coefficient `χ x • (λ x x₀)⁻¹`, smooth since `χ` is supported in `S`.
  obtain ⟨χ, hχs, -, hχ1, -, hχS⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin k)) 1).exists_contDiff_cutoff_eventuallyEq_one
      hS hsphere
  let c (x : EuclideanSpace ℝ (Fin k)) : ℂ := χ x • (a x)⁻¹
  have hc : ContDiff ℝ ∞ c :=
    (ha.contDiffOn.inv fun x hx h0 ↦ by simp [S, h0] at hx).contDiff_smul_of_tsupport_subset hS
      hχs.contDiffOn hχS
  have hc1 (x : EuclideanSpace ℝ (Fin k)) (hx : ‖x‖ = 1) : c x * a x = 1 := by
    have hxS : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 := by simpa using hx
    have hax : a x ≠ 0 := fun h0 ↦ by
      have := hsphere hxS
      simp [S, h0] at this
    simp only [c]
    rw [(hχ1 x hxS).self_of_nhds, one_smul, inv_mul_cancel₀ hax]
  -- The correction `N x (z, w) = (μ x w • c x • x₀, 0)`, nilpotent and complex linear.
  let N (x : EuclideanSpace ℝ (Fin k)) :
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ]
        EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) :=
    (ContinuousLinearMap.inl ℝ _ _).comp
      ((((μ x).smulRight (c x • p x)).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _))
  have hN (x : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℂ (Fin k) ×
      EuclideanSpace ℂ (Fin m)) : N x v = (μ x v.2 • c x • p x, 0) := rfl
  have hNs : ContDiff ℝ ∞ N := contDiff_clm_apply_iff.2 fun v ↦
    ((hμ.clm_apply contDiff_const).smul (hc.smul hp)).prodMk contDiff_const
  have hNN (x : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℂ (Fin k) ×
      EuclideanSpace ℂ (Fin m)) : N x (N x v) = 0 := by
    simp [hN]
  have hNI (x : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℂ (Fin k) ×
      EuclideanSpace ℂ (Fin m)) : N x (Complex.I • v) = Complex.I • N x v := by
    rw [hN, hN, Prod.smul_snd, map_smul, smul_eq_mul, mul_smul, Prod.smul_mk, smul_zero]
  -- The corrected frame `A x ∘ (id - N x)`.
  let U (x : EuclideanSpace ℝ (Fin k)) := ContinuousLinearMap.id ℝ
    (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) - N x
  have hU (x : EuclideanSpace ℝ (Fin k)) : (U x).IsInvertible := by
    refine .of_inverse (g := ContinuousLinearMap.id ℝ _ + N x) ?_ ?_ <;>
      refine ContinuousLinearMap.ext fun v ↦ ?_ <;> simp [U, hNN]
  refine ⟨fun x ↦ (A x).comp (U x), fun x₀ ↦ ?_, fun x ↦ (hAinv x).comp (hU x),
    fun x v ↦ ?_, fun x ↦ ?_, fun x hx w ↦ ?_⟩
  · have hUs : ContDiff ℝ ∞ U := contDiff_const.sub hNs
    exact (hAs x₀).inTangentCoordinates_clm_comp 𝓘(ℝ, E) hUs.contMDiff.contMDiffAt
  · have hUI : U x (Complex.I • v) = Complex.I • U x v := by simp [U, hNI, smul_sub]
    simp only [ContinuousLinearMap.comp_apply, hUI]
    exact hAI x _
  · refine Eq.trans ?_ (hAd x)
    rw [mfderiv_modelDisc]
    refine ContinuousLinearMap.ext fun x' ↦ ?_
    have hUx : U x (modelDisc k m x') = modelDisc k m x' := by
      -- `x'` is a tangent vector, which is a point of `ℝᵏ` only up to unfolding.
      have h2 : (modelDisc k m x').2 = 0 :=
        modelDisc_apply_snd (m := m) (show EuclideanSpace ℝ (Fin k) from x')
      simp [U, hN, h2]
    exact congrArg (A x) hUx
  · have hD0 : mvfderiv 𝓘(ℝ, E) φ (ι x) ((A x).comp (U x) (0, w)) = D x (U x (0, w)) := rfl
    have hsplit : U x (0, w) = (0, w) - (μ x w • c x • p x, 0) := by
      simp [U, hN]
    rw [hD0, hsplit, map_sub, hz x, hw x w, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, mul_assoc (μ x w), hc1 x hx, mul_one, sub_self]

end IsJOrthogonallyAttached

end Frame

section RadialProfile

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **A radial profile with prescribed radial derivative on the unit sphere.** Let `F` be a
finite-dimensional real inner product space and `g : F → ℝ` smooth with negative radial
derivative `dg x x < 0` on the unit sphere. There is a smooth positive `τ : F → ℝ`, equal to `1`
near `0`, on the unit sphere and outside a ball, such that `τ x + dτ x x > 0` everywhere and
`dτ x x = -2 / dg x x - 1` on the unit sphere.

With these properties `x ↦ τ x • x` has radial derivative `τ x + dτ x x > 0`, and on the sphere
`dg x (τ x • x + dτ x x • x) = -2`. -/
theorem exists_contDiff_fderiv_apply_self_eq_on_sphere {g : F → ℝ} (hg : ContDiff ℝ ∞ g)
    (hneg : ∀ x, ‖x‖ = 1 → fderiv ℝ g x x < 0) :
    ∃ τ : F → ℝ, ContDiff ℝ ∞ τ ∧ (∀ x, 0 < τ x) ∧ τ =ᶠ[𝓝 0] 1 ∧ (∀ x, ‖x‖ = 1 → τ x = 1) ∧
      (∃ R, ∀ x, R ≤ ‖x‖ → τ x = 1) ∧ (∀ x, 0 < τ x + fderiv ℝ τ x x) ∧
      ∀ x, ‖x‖ = 1 → fderiv ℝ τ x x = -2 / fderiv ℝ g x x - 1 := by
  -- Outline: `a y = dg y y` is negative on the open set `U`, where `b = -2 / a - 1` is smooth.
  -- A closed shell `K` around the sphere lies in `U`, with `1 + ‖y‖ * b y ≥ m > 0` on it and
  -- `b`, `db y y` bounded by `M`. Then `τ y = 1 + h (‖y‖ - 1) * b y` for a profile `h` of
  -- height and slope error `η` small compared with `m / M`, supported in the shell.
  set a : F → ℝ := fun y ↦ fderiv ℝ g y y
  have ha : ContDiff ℝ ∞ a := (hg.fderiv_right le_rfl).clm_apply contDiff_id
  set b : F → ℝ := fun y ↦ -2 / a y - 1
  set U : Set F := {y | a y < 0}
  have hU : IsOpen U := isOpen_lt ha.continuous continuous_const
  have hU0 : ∀ y ∈ U, y ≠ 0 := by
    rintro y hy rfl
    simp [U, a] at hy
  have hbU : ContDiffOn ℝ ∞ b U := fun y hy ↦
    ((contDiffAt_const.div ha.contDiffAt hy.ne).sub contDiffAt_const).contDiffWithinAt
  set V : Set F := U ∩ (fun y ↦ 1 + ‖y‖ * b y) ⁻¹' Ioi 0
  have hq : ContinuousOn (fun y ↦ 1 + ‖y‖ * b y) U :=
    continuousOn_const.add (continuous_norm.continuousOn.mul hbU.continuousOn)
  have hV : IsOpen V := hq.isOpen_inter_preimage hU isOpen_Ioi
  have hSV : sphere (0 : F) 1 ⊆ V := by
    intro x hx
    rw [mem_sphere_zero_iff_norm] at hx
    have hax := hneg x hx
    have : 0 < -2 / a x := div_pos_of_neg_of_neg (by norm_num) hax
    refine ⟨hax, ?_⟩
    simp only [mem_preimage, mem_Ioi, hx, one_mul, b]
    linarith
  -- A closed shell `K` of width `w` around the sphere lies in `V`.
  obtain ⟨w, hw0, hw1, hKV⟩ := exists_abs_norm_sub_le_subset_of_sphere_subset one_pos hV hSV
  set K : Set F := {y | |‖y‖ - 1| ≤ w}
  have hKc : IsCompact K := isCompact_setOfPred_abs_norm_sub_le 1 w
  -- Bounds on the shell.
  obtain ⟨m, hm0, hm⟩ := hKc.exists_forall_le' (f := fun y ↦ 1 + ‖y‖ * b y)
    (hq.mono (hKV.trans inter_subset_left)) fun y hy ↦ (hKV hy).2
  have hDb : ContinuousOn (fun y ↦ fderiv ℝ b y y) U :=
    (hbU.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_id
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    (f := fun y ↦ |‖y‖ * b y| + |b y| + |fderiv ℝ b y y|)
    (((continuous_norm.continuousOn.mul hbU.continuousOn).abs.add hbU.continuousOn.abs).add
      hDb.abs |>.mono (hKV.trans inter_subset_left))
  set m' := min m 1
  set M' := max M 0
  have hm'0 : 0 < m' := lt_min hm0 one_pos
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set η := m' / (2 * (M' + 1)) with hη_def
  have hη : 0 < η := by positivity
  have hηM : η * M' < m' := by
    rw [hη_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hbound : ∀ y ∈ K, |‖y‖ * b y| + |b y| + |fderiv ℝ b y y| ≤ M' := fun y hy ↦ by
    have := hM y hy
    rw [Real.norm_of_nonneg (by positivity)] at this
    exact this.trans (le_max_left _ _)
  -- The profile and the function `τ`.
  obtain ⟨h, hh, hh0, hhd0, hhw, hhb, hhd⟩ :=
    exists_contDiff_deriv_zero_eq_one_abs_le (w := w / 2) (by positivity) hη
  set ψ : F → ℝ := fun y ↦ h (‖y‖ - 1)
  have hψout : ∀ y, w / 2 < |‖y‖ - 1| → ψ y = 0 := fun y hy ↦ hhw _ hy.le
  have hψU : ContDiffOn ℝ ∞ ψ U := fun y hy ↦
    (hh.contDiffAt.comp y ((contDiffAt_norm ℝ (hU0 y hy)).sub contDiffAt_const)).contDiffWithinAt
  have htsU : tsupport ψ ⊆ U := by
    have hT : IsClosed {y : F | |‖y‖ - 1| ≤ w / 2} := isClosed_le (by fun_prop) continuous_const
    refine (closure_minimal (fun y hy ↦ ?_) hT).trans fun y hy ↦ ?_
    · by_contra hy'
      exact hy (hψout y (not_le.1 hy'))
    · -- Membership in `K` and in the smaller shell are the inequalities that define them.
      have hy' : |‖y‖ - 1| ≤ w / 2 := hy
      exact (hKV (show |‖y‖ - 1| ≤ w from hy'.trans (by linarith))).1
  set τ : F → ℝ := fun y ↦ 1 + h (‖y‖ - 1) * b y
  have hτ : ContDiff ℝ ∞ τ :=
    contDiff_const.add (by simpa only [smul_eq_mul] using
      hbU.contDiff_smul_of_tsupport_subset hU hψU htsU)
  have hτout : ∀ y, w / 2 < |‖y‖ - 1| → τ =ᶠ[𝓝 y] fun _ ↦ 1 := fun y hy ↦ by
    filter_upwards [(isOpen_lt (f := fun _ : F ↦ w / 2) (g := fun z : F ↦ |‖z‖ - 1|)
      continuous_const (by fun_prop)).mem_nhds hy] with z hz
    simp [τ, hhw _ (le_of_lt hz)]
  have hτd : ∀ y ∈ U, fderiv ℝ τ y y =
      deriv h (‖y‖ - 1) * ‖y‖ * b y + h (‖y‖ - 1) * fderiv ℝ b y y := fun y hy ↦ by
    have hy0 := hU0 y hy
    have hβ : DifferentiableAt ℝ (fun r ↦ h (r - 1)) ‖y‖ :=
      (hh.differentiable (by simp) _).comp _ (differentiableAt_id.sub_const 1)
    have hb : DifferentiableAt ℝ b y :=
      (hbU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
    have H : HasFDerivAt τ (ψ y • fderiv ℝ b y + b y • fderiv ℝ ψ y) y :=
      ((((TauCeti.differentiableAt_comp_norm_iff hy0).2 hβ).hasFDerivAt.mul
        hb.hasFDerivAt).const_add 1)
    rw [H.fderiv, add_apply, smul_apply, smul_apply, fderiv_comp_norm_apply_self hy0 hβ,
      deriv_comp_sub_const, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  refine ⟨τ, hτ, fun x ↦ ?_, hτout 0 (by simp; linarith), fun x hx ↦ by simp [τ, hx, hh0],
    ⟨2, fun x hx ↦ by
      have := hhw (‖x‖ - 1) (by rw [abs_of_nonneg (by linarith)]; linarith)
      simp [τ, this]⟩,
    fun x ↦ ?_, fun x hx ↦ ?_⟩
  · -- positivity of `τ`
    by_cases hx : |‖x‖ - 1| ≤ w / 2
    · have hB := hbound x (hx.trans (by linarith))
      have hbx : |b x| ≤ M' := by
        linarith [abs_nonneg (‖x‖ * b x), abs_nonneg (fderiv ℝ b x x)]
      exact one_add_mul_pos_of_abs_le (hhb _) hbx (hηM.trans_le (min_le_right m 1))
    · simp [τ, hhw _ (by linarith : w / 2 ≤ |‖x‖ - 1|)]
  · -- positivity of `τ + dτ (x) x`
    by_cases hx : |‖x‖ - 1| ≤ w / 2
    · have hxK : x ∈ K := hx.trans (by linarith)
      rw [hτd x (hKV hxK).1]
      have := one_add_mul_add_mul_add_mul_pos_of_abs_le (min_le_right m 1)
        ((min_le_left m 1).trans (hm x hxK)) (hhb (‖x‖ - 1)) (hhd (‖x‖ - 1)) (hbound x hxK) hηM
      simp only [τ]
      linarith
    · rw [(hτout x (not_le.1 hx)).fderiv_eq]
      simp [τ, hhw _ (by linarith : w / 2 ≤ |‖x‖ - 1|)]
  · -- the radial derivative on the sphere
    have hxU : x ∈ U := (hSV (mem_sphere_zero_iff_norm.2 hx)).1
    rw [hτd x hxU]
    simp [hx, hh0, hhd0, b, a]

end RadialProfile

section RadialReparametrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {φ : M → ℝ} {ι : F → M}

namespace IsJOrthogonallyAttached

/-- **Radial reparametrization of an attached disc.** Let `F` be a finite-dimensional real inner
product space, `φ : M → ℝ` and `ι : F → M` smooth, and `ι` attached J-orthogonally to
`{φ ≤ 0}`. There are a smooth positive `τ : F → ℝ`, equal to `1` near `0` and on the unit sphere,
and a smooth diffeomorphism `σ` of `F` with `σ x = τ x • x`, mapping the open unit ball onto
itself, such that on the unit sphere the derivative of `φ` along the radial direction of
`ι ∘ σ` is `-2`. The disc `ι ∘ σ` is again attached J-orthogonally to `{φ ≤ 0}`. -/
theorem exists_smul_self_diffeomorph_mvfderiv_comp_eq_neg_two
    (h : IsJOrthogonallyAttached E φ ι) (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (hι : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ ι) :
    ∃ (τ : F → ℝ) (σ : F ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ F), ContDiff ℝ ∞ τ ∧ (∀ x, 0 < τ x) ∧
      τ =ᶠ[𝓝 0] 1 ∧ (∀ x, ‖x‖ = 1 → τ x = 1) ∧ (∀ x, σ x = τ x • x) ∧
      (∀ x, ‖σ x‖ < 1 ↔ ‖x‖ < 1) ∧
      (∀ x, ‖x‖ = 1 →
        mvfderiv 𝓘(ℝ, E) φ (ι x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (ι ∘ σ) x x) = -2) ∧
      IsJOrthogonallyAttached E φ (ι ∘ σ) := by
  -- The radial derivative of `φ ∘ ι` on the sphere is `dφ (dι x x) < 0`.
  have hg : ContDiff ℝ ∞ (φ ∘ ι) := contMDiff_iff_contDiff.1 (hφ.comp hι)
  obtain ⟨τ, hτ, hτpos, hτ0, hτ1, ⟨R, hR⟩, hd, hτd⟩ :=
    exists_contDiff_fderiv_apply_self_eq_on_sphere hg fun _ ↦ h.fderiv_comp_apply_self_neg
  have hτ' : Differentiable ℝ τ := hτ.differentiable (by simp)
  set σ := radialSmulDiffeomorph (by simp) hτ hd hR
  have hσ (x : F) : σ x = τ x • x := radialSmulDiffeomorph_apply _ _ _ _ x
  have hball (x : F) : ‖σ x‖ < 1 ↔ ‖x‖ < 1 := hσ x ▸ norm_smul_self_lt_iff hτ' hd hτ1 x
  -- On the sphere, `σ` fixes `x` and its differential sends `x` to `(τ x + dτ x x) • x`.
  have hσx (x : F) (hx : ‖x‖ = 1) : σ x = x := by rw [hσ, hτ1 x hx, one_smul]
  have hdσ (x : F) (hx : ‖x‖ = 1) : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) σ x x =
      (τ x + fderiv ℝ τ x x) • σ x := by
    rw [mfderiv_radialSmulDiffeomorph_apply, hσx x hx, add_smul]
  have hattached : IsJOrthogonallyAttached E φ (ι ∘ σ) :=
    h.comp_of_mfderiv_apply_self_eq_smul (fun x hx ↦ (hball x).2 hx)
      (fun x hx ↦ by rw [hσx x hx, hx]) fun x hx ↦ ⟨_, hd x, hdσ x hx⟩
  refine ⟨τ, σ, hτ, hτpos, hτ0, hτ1, hσ, hball, fun x hx ↦ ?_, hattached⟩
  have hax := h.fderiv_comp_apply_self_neg hx
  have key : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (ι ∘ σ) x x =
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι (σ x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) σ x x) :=
    mfderiv_comp_apply x (h.mdifferentiableAt (by rw [hσx x hx, hx]))
      (σ.contMDiff.mdifferentiable (by simp) x) x
  -- `hdσ` gives a multiple of `x` with the scalar action of `F`, not of the tangent space.
  have e : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι x ((τ x + fderiv ℝ τ x x) • x : F) =
      (τ x + fderiv ℝ τ x x) • mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι x x :=
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι x).map_smul _ x
  rw [key, hdσ x hx, hσx x hx, e, map_smul, smul_eq_mul, ← h.fderiv_comp_apply_self hx,
    hτ1 x hx, hτd x hx]
  field_simp [hax.ne]
  ring

end IsJOrthogonallyAttached

end RadialReparametrization

end SymplecticGeometry

end
