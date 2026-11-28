/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Attached
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ChartLeviForm
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.ComplexFrame
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import SymplecticGeometry.Algebra.Order.Ring.Basic
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Interpolation
import SymplecticGeometry.Geometry.Manifold.Complex.TotallyReal.Basic
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.Radial
import SymplecticGeometry.Geometry.Manifold.Instances.Sphere
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.Comp
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Coordinates
import SymplecticGeometry.Analysis.Calculus.BumpFunction.UnitSlope
import SymplecticGeometry.Analysis.Calculus.FDeriv.Radial
import SymplecticGeometry.Analysis.Normed.Module.Ball.Shell
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.Geometry.Manifold.Morse.Sphere.Restriction

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

Next, the file compares `φ` with the model level `modelLevel k m` read through a partial
diffeomorphism `Φ` with `Φ (modelDisc k m x) = ι x` and `dΦ = A x` there, at a point `x` of the
sphere where the radial derivative of `φ ∘ ι` is `-2` and `dφ` vanishes on `A x (0 × ℂᵐ)`. Both
values are `0`. For the differentials, write a vector of `ℂᵏ × ℂᵐ` as `(u, 0) + i (u', 0) + (0, w)`
with `u`, `u'` real. Through `A x`, `dφ` sends it to `dφ (dι x u) = -2 ⟪x, u⟫`: radially this is
the normalization, and tangentially `dφ ∘ dι x` vanishes because `φ ∘ ι` is `0` on the sphere,
so that `x` is a critical point of its restriction there (Tau Ceti's
`TauCeti.fderiv_apply_eq_mul_inner_of_mem_criticalPoints_comp_coe_sphere`). The other two
terms vanish by J-orthogonality and by the choice of `A x`, and the differential of the model
level at `modelDisc k m x` (`fderiv_modelLevel_apply`) takes the same values. Since `A x` is
`dΦ`, which is onto, the two differentials at `ι x` agree. This is the comparison of 1-jets in
Step 3 of the proof of Theorem 8.5 of Cieliebak–Eliashberg.

Finally, it carries the model level `φ₀ = modelLevel k m` to `M` through a chart `Φ`
along a disc that is holomorphic to order `N ≥ 2` along the core, as in Step 4 of the proof of
Theorem 8.5. Its Levi form has a margin of the form that
`SymplecticGeometry.isManifoldStrictlyPlurisubharmonicAt_comp_modelChart_symm` takes with
`N₀ = 0` (`SymplecticGeometry.exists_pos_mul_max_norm_le_re_leviForm_modelLevel`, on a bounded
set containing the handles), so `φ₀ ∘ Φ⁻¹` is strictly plurisubharmonic on the image of a thin
handle, and so on an open neighbourhood of the image of the unit sphere.

These pieces assemble into the normal form of `φ` near the attaching sphere,
`SymplecticGeometry.IsJOrthogonallyAttached.exists_normalForm`. After the radial
reparametrization `σ`, take the adapted frame along `ι ∘ σ` and a chart `Φ` with that
differential (`SymplecticGeometry.exists_modelChart`). On the sphere, `φ` and
`ψ = modelLevel k m ∘ Φ⁻¹` have the same 1-jet, and both are strictly plurisubharmonic there:
`ψ` by the previous paragraph, `φ` because the sphere lies in `{φ = 0}`. The sphere, embedded by
`ι ∘ σ`, is a compact totally real submanifold (`isSmoothEmbedding_coe_sphere`,
`TauCeti.IsTotallyReal.range_mfderiv_comp`), so the interpolation along it,
`Manifold.IsSmoothEmbedding.exists_isManifoldStrictlyPlurisubharmonicAt_interpolate` (the route of
Proposition 3.26 of Cieliebak–Eliashberg), gives `θ` equal to `ψ` near the sphere and to `φ` away
from it. The disc `ι ∘ σ` stays attached J-orthogonally to `{θ ≤ 0}`: near the sphere `θ` is the
model level read through `Φ` (`SymplecticGeometry.isJOrthogonallyAttached_modelLevel_comp_symm`),
and on the open disc `θ` lies above the smaller of `φ` and `ψ`, both positive there. For `k = 0`
the sphere is empty and `θ = φ`. This is Steps 2–4 of the proof of Theorem 8.5 of
Cieliebak–Eliashberg.

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
* `SymplecticGeometry.IsJOrthogonallyAttached.apply_eq_modelLevel_symm_apply` and
  `SymplecticGeometry.IsJOrthogonallyAttached.mvfderiv_eq_mvfderiv_modelLevel_comp_symm`: on the
  sphere, `φ` and `modelLevel k m ∘ Φ.symm` have the same value and the same differential.
* `exists_isManifoldStrictlyPlurisubharmonicAt_modelLevel_comp_modelChart_symm`:
  `modelLevel k m ∘ Φ.symm` is strictly plurisubharmonic on `Φ` of every thin enough handle.
* `exists_isOpen_isManifoldStrictlyPlurisubharmonicAt_modelLevel_comp_modelChart_symm`:
  the same on an open set of `Φ.target` containing `Φ (ι₀ (sphere 0 1))`.
* `SymplecticGeometry.IsJOrthogonallyAttached.exists_normalForm`: after a radial
  reparametrization of the disc and in a chart along it, `φ` is changed near the attaching
  sphere into a function `θ` that is the model level near the sphere, stays strictly
  plurisubharmonic, has no new critical points, and keeps the disc attached J-orthogonally.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Corollary 8.1, Proposition 3.26, and Steps 2, 3 and 4 of the proof of Theorem 8.5.
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

section ModelJet

open scoped InnerProductSpace

variable {k m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : WithTop ℕ∞}
  {φ : M → ℝ} {ι : EuclideanSpace ℝ (Fin k) → M}

namespace IsJOrthogonallyAttached

/-- **The values of `φ` and of the model level agree on the attaching sphere.** Let `ι` be
attached J-orthogonally to `{φ ≤ 0}` and `Φ` a partial diffeomorphism from `ℂᵏ × ℂᵐ` to `M`
with `Φ (modelDisc k m x) = ι x` for a point `x` of the unit sphere. Then
`φ (ι x) = modelLevel k m (Φ.symm (ι x))`: both are `0`. -/
theorem apply_eq_modelLevel_symm_apply (h : IsJOrthogonallyAttached E φ ι)
    (Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E)
      (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M n)
    {x : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ = 1) (hsrc : modelDisc k m x ∈ Φ.source)
    (hval : Φ (modelDisc k m x) = ι x) :
    φ (ι x) = modelLevel k m (Φ.symm (ι x)) := by
  rw [show Φ.symm (ι x) = modelDisc k m x from hval ▸ Φ.left_inv hsrc, modelLevel_modelDisc, hx,
    h.eq_zero x hx]
  norm_num

/-- **The differentials of `φ` and of the model level agree on the attaching sphere.** Let `ι` be
attached J-orthogonally to `{φ ≤ 0}`, and let `x` be a point of the unit sphere at which the
radial derivative `dφ (dι x x)` is `-2`. Let `A : ℂᵏ × ℂᵐ → T_(ι x) M` be a real-linear map
that commutes with multiplication by `i`, extends `dι x` along the model disc and maps the second
factor `ℂᵐ` into the kernel of `dφ`, and let `Φ` be a partial diffeomorphism from `ℂᵏ × ℂᵐ` to
`M`, defined at `modelDisc k m x`, with `Φ (modelDisc k m x) = ι x` and differential `A` there.
Then `dφ` at `ι x` is the differential of `modelLevel k m ∘ Φ.symm` at `ι x`. -/
theorem mvfderiv_eq_mvfderiv_modelLevel_comp_symm (h : IsJOrthogonallyAttached E φ ι)
    {x : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ = 1)
    (hrad : mvfderiv 𝓘(ℝ, E) φ (ι x) (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x x) = -2)
    {A : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ] TangentSpace 𝓘(ℝ, E) (ι x)}
    (hAI : ∀ v, A (Complex.I • v) = Complex.I • (show E from A v))
    (hAd : A.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
        𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelDisc k m) x) =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x)
    (hA0 : ∀ w, mvfderiv 𝓘(ℝ, E) φ (ι x) (A (0, w)) = 0)
    (hn : n ≠ 0)
    (Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E)
      (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M n)
    (hsrc : modelDisc k m x ∈ Φ.source) (hval : Φ (modelDisc k m x) = ι x)
    (hd : mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) Φ
      (modelDisc k m x) = A) :
    mvfderiv 𝓘(ℝ, E) φ (ι x) = mvfderiv 𝓘(ℝ, E) (modelLevel k m ∘ Φ.symm) (ι x) := by
  set p := modelDisc k m x
  have hsymm : Φ.symm (ι x) = p := hval ▸ Φ.left_inv hsrc
  -- Along `dι x`, `dφ` is the derivative of `g = φ ∘ ι`, which vanishes on the sphere.
  set g : EuclideanSpace ℝ (Fin k) → ℝ := φ ∘ ι
  have hdg (u : EuclideanSpace ℝ (Fin k)) : mvfderiv 𝓘(ℝ, E) φ (ι x)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x u) = fderiv ℝ g x u :=
    (h.fderiv_comp_apply hx u).symm
  -- The restriction of `g` to the sphere is constant, so `dg x u = dg x x * ⟪x, u⟫ = -2 ⟪x, u⟫`.
  have hreal (u : EuclideanSpace ℝ (Fin k)) : fderiv ℝ g x u = -2 * ⟪x, u⟫_ℝ := by
    have hgd : DifferentiableAt ℝ g x :=
      ((h.mdifferentiableAt_apply hx).comp x (h.mdifferentiableAt hx)).differentiableAt
    obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 :=
      Nat.exists_eq_succ_of_ne_zero fun hk ↦ by subst hk; simp [Subsingleton.elim x 0] at hx
    have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (l + 1))) = l + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    have hxs : x ∈ sphere (0 : EuclideanSpace ℝ (Fin (l + 1))) 1 := by simp [hx]
    have hcrit : (⟨x, hxs⟩ : sphere (0 : EuclideanSpace ℝ (Fin (l + 1))) 1) ∈
        TauCeti.criticalPoints (𝓡 l)
          (g ∘ ((↑) : sphere (0 : EuclideanSpace ℝ (Fin (l + 1))) 1 → _)) := by
      have hc : g ∘ ((↑) : sphere (0 : EuclideanSpace ℝ (Fin (l + 1))) 1 → _) = fun _ ↦ 0 :=
        funext fun y ↦ h.eq_zero y (by simp)
      rw [hc, TauCeti.criticalPoints_const]
      trivial
    rw [TauCeti.fderiv_apply_eq_mul_inner_of_mem_criticalPoints_comp_coe_sphere (p := ⟨x, hxs⟩)
      hgd hcrit u, h.fderiv_comp_apply_self hx, hrad]
  -- On every vector, `dφ ∘ A` is the differential of the model level at `p`.
  have hA (v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
      mvfderiv 𝓘(ℝ, E) φ (ι x) (A v) = fderiv ℝ (modelLevel k m) p v := by
    set a := modelDiscProj k m v
    set b := modelDiscProj k m (-(Complex.I • v))
    have hv : v = modelDisc k m a + Complex.I • modelDisc k m b + (0, v.2) := by
      ext j
      · apply Complex.ext <;> simp [a, b, modelDisc_apply]
      · simp
    have hAm (u : EuclideanSpace ℝ (Fin k)) :
        A (modelDisc k m u) = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x u := by
      rw [← hAd, mfderiv_modelDisc]
      exact (ContinuousLinearMap.comp_apply _ _ _).symm
    have h1 : mvfderiv 𝓘(ℝ, E) φ (ι x) (A (modelDisc k m a)) = -2 * ⟪x, a⟫_ℝ :=
      (congrArg _ (hAm a)).trans ((hdg a).trans (hreal a))
    have h2 : mvfderiv 𝓘(ℝ, E) φ (ι x) (A (Complex.I • modelDisc k m b)) = 0 :=
      (congrArg _ ((hAI _).trans (congrArg _ (hAm b)))).trans (h.mvfderiv_I_smul_mfderiv x hx b)
    conv_lhs => rw [hv, map_add A, map_add A, map_add (mvfderiv 𝓘(ℝ, E) φ (ι x)),
      map_add (mvfderiv 𝓘(ℝ, E) φ (ι x)), h1, h2, hA0]
    rw [fderiv_modelLevel_apply]
    simp [p, a, PiLp.inner_apply, mul_comm, Finset.mul_sum]
  -- The same holds for the model level read through `Φ`, since `dΦ⁻¹ (ι x)` undoes `A`.
  have hιt : ι x ∈ Φ.target := hval ▸ Φ.map_source hsrc
  have hB (v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
      mvfderiv 𝓘(ℝ, E) (modelLevel k m ∘ Φ.symm) (ι x) (A v) =
        fderiv ℝ (modelLevel k m) p v := by
    have hv := Φ.mfderiv_symm_apply_mfderiv_apply hn hsrc v
    rw [hd, hval] at hv
    exact (mvfderiv_comp_apply_of_eq (ι x)
      (((contDiff_modelLevel (n := 1)).differentiable one_ne_zero p).mdifferentiableAt)
      (Φ.symm.mdifferentiableAt hn hιt) hsymm (A v)).trans
      ((congrArg _ hv).trans (TauCeti.mvfderiv_eq_fderiv_apply _ _ _))
  -- Every tangent vector at `ι x` is `A v` for `v = dΦ⁻¹ (ι x) w`.
  refine ContinuousLinearMap.ext fun w ↦ ?_
  have hw := Φ.mfderiv_apply_mfderiv_symm_apply hn hιt w
  rw [hsymm, hd] at hw
  exact (congrArg _ hw).symm.trans ((hA _).trans ((hB _).symm.trans (congrArg _ hw)))

end IsJOrthogonallyAttached

end ModelJet

section ModelLevel

open TauCeti

variable {k m : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 2 M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {N : ℕ}

/-- **The model level through the chart along a disc.** Let `Φ` be a smooth partial
diffeomorphism from `ℂᵏ × ℂᵐ` to `M` that is holomorphic to order `N ≥ 2` along the core, as
`SymplecticGeometry.exists_modelChart` gives it. Then there is `γ₀ ∈ (0, 1]` such that, for
`0 < γ < γ₀`, the handle `{p | t p ≤ γ² ∧ s p ≤ (1 + γ)²}` lies in the source of `Φ`, and
`φ₀ ∘ Φ⁻¹` is strictly plurisubharmonic at `Φ p` for every `p` in the handle, where
`φ₀ = modelLevel k m` and `(s, t) = shape p`. -/
theorem exists_isManifoldStrictlyPlurisubharmonicAt_modelLevel_comp_modelChart_symm
    (Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      𝓘(ℝ, E) (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞)
    (hΦ : IsHolomorphicToOrderAlongCore N Φ) (hN : 2 ≤ N) :
    ∃ γ₀ ∈ Ioc (0 : ℝ) 1, ∀ γ ∈ Ioo 0 γ₀,
      {p | (shape p).2 ≤ γ ^ 2 ∧ (shape p).1 ≤ (1 + γ) ^ 2} ⊆ Φ.source ∧
      ∀ p, (shape p).2 ≤ γ ^ 2 → (shape p).1 ≤ (1 + γ) ^ 2 →
        IsManifoldStrictlyPlurisubharmonicAt E (modelLevel k m ∘ Φ.symm) (Φ p) := by
  -- The handles of width at most `1` are bounded, so the model level has a margin on them.
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1
    (isCompact_setOfPred_shape_le (k := k) (m := m) (1 ^ 2) ((1 + 1) ^ 2)).isBounded
  obtain ⟨c, hc, hmargin⟩ := exists_pos_mul_max_norm_le_re_leviForm_modelLevel (k := k) (m := m) R
  obtain ⟨γ₀, hγ₀, h⟩ :=
    isManifoldStrictlyPlurisubharmonicAt_comp_modelChart_symm Φ hΦ hc (N₀ := 0) hN
  refine ⟨γ₀, hγ₀, fun γ hγ ↦ ⟨(h γ hγ).1, fun p ht hs ↦ ?_⟩⟩
  refine (h γ hγ).2 (modelLevel k m) contDiff_modelLevel (fun q ht' hs' ↦ ?_) p ht hs
  have hq := hR q (setOfPred_shape_le_subset_setOfPred_shape_le hγ.1.le
    (hγ.2.le.trans hγ₀.2) ⟨ht', hs'⟩)
  exact ⟨isStrictlyPlurisubharmonicAt_modelLevel q, fun v ↦ by simpa using hmargin q hq v⟩

/-- **An open neighbourhood of the attaching sphere on which the model level is strictly
plurisubharmonic.** For `Φ` as in
`exists_isManifoldStrictlyPlurisubharmonicAt_modelLevel_comp_modelChart_symm`, there is an open
set `V ⊆ Φ.target` of `M` that contains the image under `Φ ∘ ι₀` of the unit sphere, at every
point of which `modelLevel k m ∘ Φ⁻¹` is strictly plurisubharmonic. -/
theorem exists_isOpen_isManifoldStrictlyPlurisubharmonicAt_modelLevel_comp_modelChart_symm
    (Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      𝓘(ℝ, E) (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞)
    (hΦ : IsHolomorphicToOrderAlongCore N Φ) (hN : 2 ≤ N) :
    ∃ V : Set M, IsOpen V ∧ V ⊆ Φ.target ∧ Φ '' (modelDisc k m '' sphere 0 1) ⊆ V ∧
      ∀ x ∈ V, IsManifoldStrictlyPlurisubharmonicAt E (modelLevel k m ∘ Φ.symm) x := by
  obtain ⟨γ₀, hγ₀, h⟩ :=
    exists_isManifoldStrictlyPlurisubharmonicAt_modelLevel_comp_modelChart_symm Φ hΦ hN
  have hγ : γ₀ / 2 ∈ Ioo 0 γ₀ := ⟨half_pos hγ₀.1, half_lt_self hγ₀.1⟩
  obtain ⟨hsub, hpsh⟩ := h _ hγ
  set U := {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) |
    (shape p).2 < (γ₀ / 2) ^ 2 ∧ (shape p).1 < (1 + γ₀ / 2) ^ 2}
  have hU : IsOpen U :=
    (isOpen_lt (contDiff_shape (n := 0)).snd.continuous continuous_const).inter
      (isOpen_lt (contDiff_shape (n := 0)).fst.continuous continuous_const)
  have hUs : U ⊆ Φ.source := fun p hp ↦ hsub ⟨hp.1.le, hp.2.le⟩
  refine ⟨Φ '' U, Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hU hUs,
    ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact Φ.map_source (hUs hp)
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨modelDisc k m x, ⟨?_, ?_⟩, rfl⟩
    · simp [hγ.1]
    · simp only [shape_modelDisc, mem_sphere_zero_iff_norm.1 hx]
      nlinarith [hγ.1]
  · rintro _ ⟨p, hp, rfl⟩
    exact hpsh p hp.1.le hp.2.le

end ModelLevel

section NormalForm

open Module TauCeti TauCeti.SmoothAlmostComplexStructure

variable {k m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {φ : M → ℝ} {N : ℕ}

namespace IsJOrthogonallyAttached

/-- The interpolation step of `exists_normalForm`: for a disc whose radial derivative of `φ` is
`-2` on the sphere, and a chart `Φ` along it with an adapted frame, `φ` is joined to
`modelLevel k m ∘ Φ.symm` near the sphere. -/
private theorem exists_interpolate_modelLevel {ι : EuclideanSpace ℝ (Fin k) → M}
    (hι : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ∞ ι)
    (hιR : ∀ x, IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι x)).toLinearMap
      (LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x).toLinearMap))
    (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (hφs : ∀ x, φ x ≤ 0 → IsManifoldStrictlyPlurisubharmonicAt E φ x)
    (h : IsJOrthogonallyAttached E φ ι)
    (hrad : ∀ x, ‖x‖ = 1 →
      mvfderiv 𝓘(ℝ, E) φ (ι x) (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x x) = -2)
    {A : ∀ x, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ]
      TangentSpace 𝓘(ℝ, E) (ι x)}
    (hAI : ∀ x v, A x (Complex.I • v) = Complex.I • (show E from A x v))
    (hAd : ∀ x, (A x).comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
        𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelDisc k m) x) =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x)
    (hA0 : ∀ x, ‖x‖ = 1 → ∀ w, mvfderiv 𝓘(ℝ, E) φ (ι x) (A x (0, w)) = 0)
    (Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      𝓘(ℝ, E) (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞)
    (hsrc : range (modelDisc k m) ⊆ Φ.source) (hval : ∀ x, Φ (modelDisc k m x) = ι x)
    (hd : ∀ x, mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) Φ
      (modelDisc k m x) = A x)
    (hΦ : IsHolomorphicToOrderAlongCore N Φ) (hN : 2 ≤ N)
    {U : Set M} (hU : IsOpen U) (hιU : ι '' sphere 0 1 ⊆ U) :
    ∃ V W : Set M, IsOpen V ∧ IsOpen W ∧ ι '' sphere 0 1 ⊆ V ∧ V ⊆ W ∧ W ⊆ U ∩ Φ.target ∧
      ∃ θ : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ θ ∧ EqOn θ (modelLevel k m ∘ Φ.symm) V ∧
        (∀ x ∉ W, θ =ᶠ[𝓝 x] φ) ∧
        (∀ x ∈ W, min (φ x) (modelLevel k m (Φ.symm x)) ≤ θ x ∧
          θ x ≤ max (φ x) (modelLevel k m (Φ.symm x))) ∧
        (∀ x ∈ W ∪ {x | θ x ≤ 0}, IsManifoldStrictlyPlurisubharmonicAt E θ x) ∧
        (∀ x ∈ W, mvfderiv 𝓘(ℝ, E) θ x ≠ 0) ∧ IsJOrthogonallyAttached E θ ι := by
  -- For `k = 0` the sphere is empty, and `θ = φ`.
  obtain _ | j := k
  · have hs : sphere (0 : EuclideanSpace ℝ (Fin 0)) 1 = ∅ :=
      eq_empty_of_forall_notMem fun x hx ↦ by simp [Subsingleton.elim x 0] at hx
    refine ⟨∅, ∅, isOpen_empty, isOpen_empty, by simp [hs], subset_rfl, empty_subset _, φ, hφ,
      eqOn_empty _ _, fun _ _ ↦ EventuallyEq.rfl, fun _ hx ↦ hx.elim, ?_, fun _ hx ↦ hx.elim, h⟩
    rintro x (hx | hx)
    exacts [hx.elim, hφs x hx]
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (j + 1))) = j + 1) := ⟨finrank_euclideanSpace_fin⟩
  set ψ := modelLevel (j + 1) m ∘ Φ.symm
  -- The model level through `Φ` is strictly plurisubharmonic on an open `V₁ ⊇ ι '' sphere 0 1`.
  obtain ⟨V₁, hV₁, hV₁t, hsV₁, hψs⟩ :=
    exists_isOpen_isManifoldStrictlyPlurisubharmonicAt_modelLevel_comp_modelChart_symm Φ hΦ hN
  have hsph : Φ '' (modelDisc (j + 1) m '' sphere 0 1) = ι '' sphere 0 1 := by
    rw [image_image]
    exact image_congr fun x _ ↦ hval x
  -- The sphere, embedded by `ι`, as a totally real submanifold.
  set ιs : sphere (0 : EuclideanSpace ℝ (Fin (j + 1))) 1 → M := ι ∘ (↑)
  have hιs : IsSmoothEmbedding (𝓡 j) 𝓘(ℝ, E) ∞ ιs :=
    hι.comp_of_boundaryless isSmoothEmbedding_coe_sphere (by simp)
  have hιsR (y) (_ : y ∈ univ) :
      IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ιs y)).toLinearMap
        (LinearMap.range (mfderiv (𝓡 j) 𝓘(ℝ, E) ιs y).toLinearMap) :=
    (hιR y).range_mfderiv_comp (hι.contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero)
  have hK : ιs '' univ = ι '' sphere 0 1 := by
    rw [image_univ, range_comp, Subtype.range_coe]
  have hψsm : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ V₁ :=
    (contDiff_modelLevel.contMDiff.comp_contMDiffOn Φ.symm.contMDiffOn).mono hV₁t
  -- `φ` is strictly plurisubharmonic on the sphere, which lies in `{φ = 0}`.
  have hφsph (x) (hx : x ∈ ι '' sphere 0 1) : φ x = 0 := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact h.eq_zero y (by simpa using hy)
  -- The 1-jets of `φ` and `ψ` agree on the sphere.
  have hjet : ∀ᶠ y in 𝓝ˢ (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin (j + 1))) 1)),
      φ (ιs y) = ψ (ιs y) ∧ mvfderiv 𝓘(ℝ, E) φ (ιs y) = mvfderiv 𝓘(ℝ, E) ψ (ιs y) := by
    refine Eventually.of_forall fun y ↦ ?_
    have hy : ‖(y : EuclideanSpace ℝ (Fin (j + 1)))‖ = 1 := by simp
    exact ⟨h.apply_eq_modelLevel_symm_apply Φ hy (hsrc (mem_range_self _)) (hval _),
      h.mvfderiv_eq_mvfderiv_modelLevel_comp_symm hy (hrad _ hy) (hAI _) (hAd _) (hA0 _ hy)
        (by simp) Φ (hsrc (mem_range_self _)) (hval _) (hd _)⟩
  obtain ⟨V, W, hV, hW, hKV, hVW, hWUO, θ, hθ, hθψ, hθφ, hθs, hθb, hθc⟩ :=
    hιs.exists_isManifoldStrictlyPlurisubharmonicAt_interpolate isCompact_univ hιsR hV₁
      (by rw [hK, ← hsph]; exact hsV₁) hφ.contMDiffOn hψsm
      (fun x hx ↦ hφs x (hφsph x (by rwa [hK] at hx)).le)
      (fun x hx ↦ hψs x (hsV₁ (by rwa [hsph, ← hK]))) hjet hU (by rwa [hK])
  rw [hK] at hKV
  -- `θ` is the model level near the sphere, so the attachment of the model carries over.
  have hmodel := isJOrthogonallyAttached_modelLevel_comp_symm (by simp) Φ
    (fun _ ⟨x, _, hx⟩ ↦ hx ▸ hsrc (mem_range_self x)) fun x _ v ↦ by rw [hd x]; exact hAI x v
  rw [show Φ ∘ modelDisc (j + 1) m = ι from funext hval] at hmodel
  refine ⟨V, W, hV, hW, hKV, hVW, fun x hx ↦ ⟨(hWUO hx).1, hV₁t (hWUO hx).2⟩, θ,
    fun x ↦ ?_, hθψ, hθφ, fun x _ ↦ hθb x, ?_, hθc ?_, ?_⟩
  · by_cases hx : x ∈ V₁
    · exact hθ.contMDiffAt (hV₁.mem_nhds hx)
    · exact (hφ x).congr_of_eventuallyEq (hθφ x fun hxW ↦ hx (hWUO hxW).2)
  · rintro x (hx | hx)
    · exact hθs x hx
    by_cases hxW : x ∈ W
    · exact hθs x hxW
    exact (hφs x ((hθφ x hxW).eq_of_nhds ▸ hx)).congr_of_eventuallyEq (hθφ x hxW)
  · rintro _ ⟨y, -, rfl⟩ h0
    have := h.mvfderiv_mfderiv_self_neg y (by simp)
    have h0' : mvfderiv 𝓘(ℝ, E) φ (ι y) = 0 := h0
    rw [h0'] at this
    simp at this
  · exact hmodel.congr_of_eventuallyEq
      (fun x hx ↦ eventuallyEq_of_mem (hV.mem_nhds (hKV ⟨x, by simpa using hx, rfl⟩)) hθψ)
      fun x hx ↦ (lt_min (h.pos x hx) (hmodel.pos x hx)).trans_le (hθb _).1

/-- **The normal form of `φ` near the attaching sphere.** Let `M` be a Hausdorff complex manifold
modelled on `E`, with `dim_ℂ E = k + m`, and `φ : M → ℝ` smooth and strictly plurisubharmonic on
`{φ ≤ 0}`. Let `ι : ℝᵏ → M` be a smooth embedding with totally real tangent images, attached
J-orthogonally to `{φ ≤ 0}`, and let `O ⊇ range ι` and `U ⊇ ι '' sphere 0 1` be open and
`2 ≤ N`. Then there are:
* a radial reparametrization `σ x = τ x • x` of the disc, as in
  `exists_smul_self_diffeomorph_mvfderiv_comp_eq_neg_two`, after which the radial derivative of
  `φ` along `ι ∘ σ` is `-2` on the sphere and `ι ∘ σ` is still attached J-orthogonally;
* a frame `A` along `ι ∘ σ` as in `exists_complexFrame_mfderiv_ker`;
* a chart `Φ` along `ι ∘ σ` with differential `A` along the core, holomorphic to order `N`
  along the core and with target in `O`, as `exists_modelChart` gives it;
* open sets `V ⊆ W ⊆ U ∩ Φ.target` with `ι '' sphere 0 1 ⊆ V`, and a smooth `θ : M → ℝ` equal to
  the model level `modelLevel k m ∘ Φ.symm` on `V`, to `φ` near every point outside `W`, lying
  between the two on `W`, strictly plurisubharmonic on `W ∪ {θ ≤ 0}`, without critical points
  in `W`, and such that `ι ∘ σ` is attached J-orthogonally to `{θ ≤ 0}`. -/
theorem exists_normalForm (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    (hφs : ∀ x, φ x ≤ 0 → IsManifoldStrictlyPlurisubharmonicAt E φ x)
    {ι : EuclideanSpace ℝ (Fin k) → M}
    (hι : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ∞ ι)
    (hιR : ∀ x, IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι x)).toLinearMap
      (LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x).toLinearMap))
    (hdim : finrank ℂ E = k + m) (h : IsJOrthogonallyAttached E φ ι)
    {O : Set M} (hO : IsOpen O) (hιO : range ι ⊆ O)
    {U : Set M} (hU : IsOpen U) (hιU : ι '' sphere 0 1 ⊆ U) (hN : 2 ≤ N) :
    ∃ (τ : EuclideanSpace ℝ (Fin k) → ℝ)
      (σ : EuclideanSpace ℝ (Fin k) ≃ₘ^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin k)),
        𝓘(ℝ, EuclideanSpace ℝ (Fin k))⟯ EuclideanSpace ℝ (Fin k)),
      ContDiff ℝ ∞ τ ∧ (∀ x, 0 < τ x) ∧ τ =ᶠ[𝓝 0] 1 ∧ (∀ x, ‖x‖ = 1 → τ x = 1) ∧
      (∀ x, σ x = τ x • x) ∧ (∀ x, ‖σ x‖ < 1 ↔ ‖x‖ < 1) ∧
      (∀ x, ‖x‖ = 1 → mvfderiv 𝓘(ℝ, E) φ ((ι ∘ σ) x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) (ι ∘ σ) x x) = -2) ∧
      IsJOrthogonallyAttached E φ (ι ∘ σ) ∧
      ∃ A : ∀ x, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ]
          TangentSpace 𝓘(ℝ, E) ((ι ∘ σ) x),
        (∀ x₀, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
          𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ] E) ∞
          (inTangentCoordinates 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
            𝓘(ℝ, E) (modelDisc k m) (ι ∘ σ) A x₀) x₀) ∧
        (∀ x, (A x).IsInvertible) ∧
        (∀ x v, A x (Complex.I • v) = ofComplexManifold E M ((ι ∘ σ) x) (A x v)) ∧
        (∀ x, (A x).comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
            𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelDisc k m) x) =
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) (ι ∘ σ) x) ∧
        (∀ x, ‖x‖ = 1 → ∀ w, mvfderiv 𝓘(ℝ, E) φ ((ι ∘ σ) x) (A x (0, w)) = 0) ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
          𝓘(ℝ, E) (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞,
        range (modelDisc k m) ⊆ Φ.source ∧ Φ.target ⊆ O ∧
        (∀ x, Φ (modelDisc k m x) = (ι ∘ σ) x) ∧
        (∀ x, mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) Φ
          (modelDisc k m x) = A x) ∧
        IsHolomorphicToOrderAlongCore N Φ ∧
      ∃ V W : Set M, IsOpen V ∧ IsOpen W ∧ ι '' sphere 0 1 ⊆ V ∧ V ⊆ W ∧
        W ⊆ U ∩ Φ.target ∧
      ∃ θ : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ θ ∧ EqOn θ (modelLevel k m ∘ Φ.symm) V ∧
        (∀ x ∉ W, θ =ᶠ[𝓝 x] φ) ∧
        (∀ x ∈ W, min (φ x) (modelLevel k m (Φ.symm x)) ≤ θ x ∧
          θ x ≤ max (φ x) (modelLevel k m (Φ.symm x))) ∧
        (∀ x ∈ W ∪ {x | θ x ≤ 0}, IsManifoldStrictlyPlurisubharmonicAt E θ x) ∧
        (∀ x ∈ W, mvfderiv 𝓘(ℝ, E) θ x ≠ 0) ∧ IsJOrthogonallyAttached E θ (ι ∘ σ) := by
  -- The radial reparametrization, and the disc `ι' = ι ∘ σ`.
  obtain ⟨τ, σ, hτ, hτpos, hτ0, hτ1, hσ, hball, hrad, h'⟩ :=
    h.exists_smul_self_diffeomorph_mvfderiv_comp_eq_neg_two hφ hι.contMDiff
  have hσs (x : EuclideanSpace ℝ (Fin k)) (hx : ‖x‖ = 1) : σ x = x := by
    rw [hσ, hτ1 x hx, one_smul]
  have hι' : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ∞ (ι ∘ σ) :=
    isSmoothEmbedding_comp_diffeomorph σ hι
  have hιR' (x) : IsTotallyReal ((ofComplexManifold E M).toEndomorphism ((ι ∘ σ) x)).toLinearMap
      (LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) (ι ∘ σ) x).toLinearMap) :=
    (hιR (σ x)).range_mfderiv_comp (hι.contMDiff.mdifferentiableAt (by simp))
      (σ.contMDiff.mdifferentiableAt (by simp))
  replace hrad (x) (hx : ‖x‖ = 1) : mvfderiv 𝓘(ℝ, E) φ ((ι ∘ σ) x)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) (ι ∘ σ) x x) = -2 := by
    rw [Function.comp_apply, hσs x hx]
    exact hrad x hx
  have hsph : (ι ∘ σ) '' sphere 0 1 = ι '' sphere 0 1 :=
    image_congr fun x hx ↦ congrArg ι (hσs x (by simpa using hx))
  -- The adapted frame and the chart along `ι'`.
  obtain ⟨A, hA, hAinv, hAI, hAd, hA0⟩ :=
    h'.exists_complexFrame_mfderiv_ker hι'.isImmersion hιR' hdim hφ
  have hAI' (x) (v) : A x (Complex.I • v) = Complex.I • (show E from A x v) :=
    (hAI x v).trans (ofComplexManifold_apply _ _)
  obtain ⟨Φ, hsrc, htgt, hval, hd, hΦ⟩ :=
    exists_modelChart hι'.contMDiff hι'.isEmbedding.isInducing hA hAinv hAd hAI' hO
      ((range_comp_subset_range _ _).trans hιO) N
  obtain ⟨V, W, hV, hW, hKV, hVW, hWUΦ, θ, hθ⟩ :=
    exists_interpolate_modelLevel hι' hιR' hφ hφs h' hrad hAI' hAd hA0 Φ hsrc hval hd hΦ hN hU
      (hsph ▸ hιU)
  exact ⟨τ, σ, hτ, hτpos, hτ0, hτ1, hσ, hball, hrad, h', A, hA, hAinv, hAI, hAd, hA0, Φ, hsrc,
    htgt, hval, hd, hΦ, V, W, hV, hW, hsph ▸ hKV, hVW, hWUΦ, θ, hθ⟩

end IsJOrthogonallyAttached

end NormalForm

end SymplecticGeometry

end
