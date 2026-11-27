/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Attached
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ComplexFrame
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Coordinates
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

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

## Main results

* `SymplecticGeometry.IsJOrthogonallyAttached.exists_complexFrame_mfderiv_ker`: along a disc
  attached J-orthogonally to `{φ ≤ 0}` there is a frame with the properties of
  `exists_complexFrame_mfderiv` whose second factor lies in the kernel of `dφ` along the sphere.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Step 3 of the proof of Theorem 8.5.
-/

public section

noncomputable section

open Manifold Set Filter
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

end SymplecticGeometry

end
