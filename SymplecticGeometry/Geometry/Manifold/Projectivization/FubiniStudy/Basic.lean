/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Dolbeault.Potential
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
public import TauCeti.Geometry.Contact.Sphere
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The Fubini–Study forms on `ℂⁿ⁺¹ ∖ 0` and on the sphere

Write `Z = TauCeti.puncturedSpace (Fin (n + 1) → ℂ)` for `ℂⁿ⁺¹ ∖ 0`, `|z|² = ∑ᵢ ‖zᵢ‖²`,
`⟨z, v⟩ = Re ∑ᵢ conj zᵢ vᵢ`, and `ω₀ = stdComplexPiSymplecticForm (Fin (n + 1))`. This file
builds the forms upstairs from which the Fubini–Study form of `ℂPⁿ` descends.

* `SymplecticGeometry.fubiniStudyPrimitive n` is the one-form `α` on `Z` with
  `α_z(v) = ω₀(z, v) / (2 |z|²)` (`fubiniStudyPrimitive_apply`). It is defined as the pull-back
  along the radial projection `z ↦ ẑ / ‖ẑ‖` of Tau Ceti's contact form
  `TauCeti.SymplecticForm.sphereContactForm` of the unit sphere of `StdSpace (Fin (n + 1))`,
  since `ω₀(z / |z|, ·)` kills the radial direction. With the potential
  `fubiniStudyPotential n`, the function `log |z|²` with differential
  `v ↦ 2 ⟨z, v⟩ / |z|²` (`mextDerivₗ_fubiniStudyPotential_apply`), it is `(1/4) J* d log |z|²`
  (`fubiniStudyPrimitive_eq`), where `J*` is `covectorComplexStructure` of the complex structure
  of `Z`.
* `SymplecticGeometry.fubiniStudyLift n` is `ρ = dα`. It is closed (`isClosed_fubiniStudyLift`),
  has the value
  `ρ_z(v, w) = ω₀(v, w) / |z|² - (⟨z, v⟩ ω₀(z, w) - ⟨z, w⟩ ω₀(z, v)) / |z|⁴`
  (`fubiniStudyLift_apply`), and its complexification is `(i/2) ∂∂bar log |z|²`
  (`fubiniStudyLift_eq_del_delBar`), by `Dolbeault/Potential.lean`.
* `SymplecticGeometry.sphereStdForm n` is the restriction `σ` of `ω₀ = stdForm (Fin (n + 1))` to
  the unit sphere of `StdSpace (Fin (n + 1))` (`sphereStdForm_apply`). It is the exterior
  derivative of `sphereContactForm` (`sphereStdForm_eq_mextDeriv`), hence closed
  (`isClosed_sphereStdForm`), and its pull-back along the radial projection is `ρ`
  (`mpullback_radialProjection_sphereStdForm`), by naturality of `d`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Example 4.3.3, p. 168, and Exercises 4.3.4–4.3.5, p. 169.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 3.1.
-/

public section

open Metric TauCeti
open scoped Manifold ContDiff InnerProductSpace

namespace SymplecticGeometry

variable (n : ℕ)

/-- The Fubini–Study primitive `α` on `ℂⁿ⁺¹ ∖ 0`, the one-form `α_z(v) = ω₀(z, v) / (2 |z|²)`
(`fubiniStudyPrimitive_apply`): the pull-back of the contact form `λ|S` of the unit sphere of
`StdSpace (Fin (n + 1))` along the radial projection. -/
noncomputable def fubiniStudyPrimitive :
    SmoothForm 𝓘(ℝ, Fin (n + 1) → ℂ) (puncturedSpace (Fin (n + 1) → ℂ)) ℝ 1 :=
  SmoothForm.mpullback (radialProjection n) (contMDiff_radialProjection n ∞)
    ((stdForm (Fin (n + 1))).sphereContactForm (2 * n + 1))

theorem fubiniStudyPrimitive_def :
    fubiniStudyPrimitive n = SmoothForm.mpullback (radialProjection n)
      (contMDiff_radialProjection n ∞) ((stdForm (Fin (n + 1))).sphereContactForm (2 * n + 1)) :=
  (rfl)

variable {n} in
/-- The Fubini–Study primitive evaluates as `α_z(v) = ω₀(z, v) / (2 |z|²)`. -/
@[simp]
theorem fubiniStudyPrimitive_apply (z : puncturedSpace (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    (fubiniStudyPrimitive n).val z ![v] =
      stdComplexPiSymplecticForm (Fin (n + 1)) z v /
        (2 * ∑ i, ‖(z : Fin (n + 1) → ℂ) i‖ ^ 2) := by
  have hz : 0 < ‖complexToRealEuclidean (Fin (n + 1)) z‖ :=
    norm_pos_iff.2 (by simpa using mem_puncturedSpace.1 z.property)
  have h := stdForm_complexToRealEuclidean (z : Fin (n + 1) → ℂ) v
  beta_reduce at h
  rw [fubiniStudyPrimitive_def, SmoothForm.mpullback_apply_one,
    SymplecticForm.sphereContactForm_apply, mvfderiv_radialProjection, radialProjection_apply,
    ← norm_sq_complexToRealEuclidean]
  -- `ω₀(ẑ, ẑ) = 0` removes the radial part of the derivative of the radial projection.
  simp only [map_sub, map_smul, LinearMap.smul_apply, (stdForm _).isAlt.self_eq_zero,
    smul_eq_mul, mul_zero, sub_zero, h]
  field_simp

/-- The Kähler potential `log |z|²` of the Fubini–Study form, as a smooth `0`-form on
`ℂⁿ⁺¹ ∖ 0` (`fubiniStudyPotential_apply`). -/
noncomputable def fubiniStudyPotential :
    SmoothForm 𝓘(ℝ, Fin (n + 1) → ℂ) (puncturedSpace (Fin (n + 1) → ℂ)) ℝ 0 :=
  SmoothForm.ofFunction ⟨fun z ↦ Real.log (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2), by
    intro z
    have h : ContDiffAt ℝ ∞
        (fun w ↦ Real.log (‖complexToRealEuclidean (Fin (n + 1)) w‖ ^ 2)) (z : Fin (n + 1) → ℂ) :=
      ((contDiff_norm_sq ℝ).comp (complexToRealEuclidean (Fin (n + 1))).contDiff).contDiffAt.log
        (by simpa using mem_puncturedSpace.1 z.property)
    exact h.contMDiffAt.comp z (contMDiff_subtypeVal z)⟩

/-- As a rough form, the potential is the `0`-form of the function `z ↦ log ‖ẑ‖²`. -/
theorem fubiniStudyPotential_def :
    (fubiniStudyPotential n : RoughForm 𝓘(ℝ, Fin (n + 1) → ℂ) _ ℝ 0) =
      RoughForm.ofFunction 𝓘(ℝ, Fin (n + 1) → ℂ)
        fun z : puncturedSpace (Fin (n + 1) → ℂ) ↦
          Real.log (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) :=
  SmoothForm.coe_ofFunction _

variable {n} in
/-- The potential `fubiniStudyPotential n` takes the value `log |z|²` at `z`. -/
@[simp]
theorem fubiniStudyPotential_apply (z : puncturedSpace (Fin (n + 1) → ℂ))
    (v : Fin 0 → TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    (fubiniStudyPotential n).val z v = Real.log (∑ i, ‖(z : Fin (n + 1) → ℂ) i‖ ^ 2) := by
  rw [fubiniStudyPotential_def, RoughForm.ofFunction_apply, norm_sq_complexToRealEuclidean]

variable {n} in
/-- The differential of the potential: `d(log |z|²)_z(v) = 2 ⟨z, v⟩ / |z|²`, with
`⟨z, v⟩ = Re ∑ᵢ conj zᵢ vᵢ`. -/
theorem mextDerivₗ_fubiniStudyPotential_apply (z : puncturedSpace (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    (mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 0 (fubiniStudyPotential n)).val z ![v] =
      2 * (star (z : Fin (n + 1) → ℂ) ⬝ᵥ v).re / ∑ i, ‖(z : Fin (n + 1) → ℂ) i‖ ^ 2 := by
  have hz : complexToRealEuclidean (Fin (n + 1)) z ≠ 0 := by
    simpa using mem_puncturedSpace.1 z.property
  have hd : HasFDerivAt (fun w ↦ Real.log (‖complexToRealEuclidean (Fin (n + 1)) w‖ ^ 2))
      ((‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2)⁻¹ •
        (2 • (innerSL ℝ (complexToRealEuclidean (Fin (n + 1)) z)).comp
          (complexToRealEuclidean (Fin (n + 1)) : (Fin (n + 1) → ℂ) →L[ℝ] _)))
      (z : Fin (n + 1) → ℂ) :=
    ((complexToRealEuclidean (Fin (n + 1))).hasFDerivAt.norm_sq).log (by simpa using hz)
  have hf : (fun y ↦ (fubiniStudyPotential n).val y 0) =
      (fun w ↦ Real.log (‖complexToRealEuclidean (Fin (n + 1)) w‖ ^ 2)) ∘ Subtype.val :=
    funext fun y ↦ by
      rw [fubiniStudyPotential_apply, Function.comp_apply, norm_sq_complexToRealEuclidean]
  rw [mextDerivₗ_zero_apply, hf, mvfderiv_comp_apply_of_differentiableAt hd.differentiableAt
      ((contMDiff_subtypeVal z).mdifferentiableAt one_ne_zero),
    Manifold.mvfderiv_subtype_val_apply, hd.fderiv]
  -- Read `v` as a vector of `Fin (n + 1) → ℂ`, so that the evaluation lemmas of continuous linear
  -- maps apply to it.
  revert v
  intro (w : Fin (n + 1) → ℂ)
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, innerSL_apply_apply, inner_complexToRealEuclidean,
    norm_sq_complexToRealEuclidean, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  field_simp

open TauCeti.ComplexManifold in
/-- The Fubini–Study primitive is `(1/4) J* d log |z|²`, where `J*` is the almost complex
structure `a ↦ -a ∘ J` on one-forms dual to the complex structure `J` of `ℂⁿ⁺¹ ∖ 0`. -/
theorem fubiniStudyPrimitive_eq :
    fubiniStudyPrimitive n = (4 : ℝ)⁻¹ •
      (SmoothAlmostComplexStructure.ofComplexManifold (Fin (n + 1) → ℂ)
        (puncturedSpace (Fin (n + 1) → ℂ))).covectorComplexStructure
        (mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 0 (fubiniStudyPotential n)) := by
  refine Subtype.ext <| funext fun z ↦ ?_
  refine sub_eq_zero.1 <| (ContinuousAlternatingMap.eq_zero_iff_forall_apply_fin_one _).2
    fun v ↦ ?_
  rw [ContinuousAlternatingMap.sub_apply, sub_eq_zero, SmoothForm.smul_toRoughForm, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply,
    SmoothAlmostComplexStructure.covectorComplexStructure_apply_vec,
    mextDerivₗ_fubiniStudyPotential_apply, fubiniStudyPrimitive_apply]
  have hJ := SmoothAlmostComplexStructure.ofComplexManifold_apply (E := Fin (n + 1) → ℂ) z v
  have hI := inner_complexToRealEuclidean_I_smul (z : Fin (n + 1) → ℂ) v
  -- `covectorComplexStructure_apply_vec` leaves `J z v` as an application of `fun x ↦ J x`.
  beta_reduce at hJ hI ⊢
  rw [hJ, ← inner_complexToRealEuclidean]
  -- `simp only` matches `hI` up to the identification of `v` with a vector of `Fin (n + 1) → ℂ`.
  simp only [hI]
  field_simp
  ring

/-- The two-form `ρ = dα` on `ℂⁿ⁺¹ ∖ 0`, the exterior derivative of the Fubini–Study primitive.
It has the value
`ρ_z(v, w) = ω₀(v, w) / |z|² - (⟨z, v⟩ ω₀(z, w) - ⟨z, w⟩ ω₀(z, v)) / |z|⁴`
(`fubiniStudyLift_apply`). -/
noncomputable def fubiniStudyLift :
    SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (puncturedSpace (Fin (n + 1) → ℂ)) :=
  mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 1 (fubiniStudyPrimitive n)

theorem fubiniStudyLift_def :
    fubiniStudyLift n = mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 1 (fubiniStudyPrimitive n) :=
  (rfl)

/-- The two-form `ρ` on `ℂⁿ⁺¹ ∖ 0` is closed. -/
theorem isClosed_fubiniStudyLift : (fubiniStudyLift n).IsClosed :=
  SmoothForm.isClosed_mextDerivₗ _

open TauCeti.ComplexManifold in
/-- The complexification of `ρ` is `(i/2) ∂∂bar log |z|²`, for the Dolbeault operators of the
complex structure of `ℂⁿ⁺¹ ∖ 0`. -/
theorem fubiniStudyLift_eq_del_delBar :
    SmoothForm.mapCoeff Complex.ofRealCLM (fubiniStudyLift n) =
      (Complex.I / 2) • (SmoothAlmostComplexStructure.ofComplexManifold (Fin (n + 1) → ℂ)
        (puncturedSpace (Fin (n + 1) → ℂ))).del
          ((SmoothAlmostComplexStructure.ofComplexManifold (Fin (n + 1) → ℂ)
            (puncturedSpace (Fin (n + 1) → ℂ))).delBar
              (SmoothForm.mapCoeff Complex.ofRealCLM (fubiniStudyPotential n))) := by
  rw [SmoothAlmostComplexStructure.del_delBar_mapCoeff_ofReal_ofComplexManifold,
    fubiniStudyLift_def, fubiniStudyPrimitive_eq, map_smul]

/-- The restriction `σ` of the standard form `ω₀ = stdForm (Fin (n + 1))` to the unit sphere of
`StdSpace (Fin (n + 1))`: the pull-back of the constant form along the inclusion. -/
noncomputable def sphereStdForm :
    SmoothTwoForm (𝓡 (2 * n + 1)) (sphere (0 : StdSpace (Fin (n + 1))) 1) :=
  SmoothForm.mpullback (↑) contMDiff_coe_sphere (stdForm (Fin (n + 1))).constSmooth

theorem sphereStdForm_def : sphereStdForm n =
    SmoothForm.mpullback (↑) contMDiff_coe_sphere (stdForm (Fin (n + 1))).constSmooth :=
  (rfl)

variable {n} in
/-- The form `σ` evaluates tangent vectors of the sphere as `ω₀` on their images in
`StdSpace (Fin (n + 1))`. -/
theorem sphereStdForm_apply (x : sphere (0 : StdSpace (Fin (n + 1))) 1)
    (v w : TangentSpace (𝓡 (2 * n + 1)) x) :
    (sphereStdForm n).eval₂ x v w =
      stdForm (Fin (n + 1))
        (mvfderiv (𝓡 (2 * n + 1))
          ((↑) : sphere (0 : StdSpace (Fin (n + 1))) 1 → StdSpace (Fin (n + 1))) x v)
        (mvfderiv (𝓡 (2 * n + 1))
          ((↑) : sphere (0 : StdSpace (Fin (n + 1))) 1 → StdSpace (Fin (n + 1))) x w) := by
  rw [sphereStdForm_def, SmoothForm.eval₂_mpullback,
    SymplecticForm.eval₂_constSmooth_mfderiv_eq]

/-- The form `σ` is the exterior derivative of Tau Ceti's contact form `λ|S` of the sphere, the
restriction of the radial primitive `λₓ(v) = ω₀(x, v) / 2`. -/
theorem sphereStdForm_eq_mextDeriv :
    sphereStdForm n = mextDerivₗ (𝓡 (2 * n + 1)) 1
      ((stdForm (Fin (n + 1))).sphereContactForm (2 * n + 1)) := by
  refine SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
  rw [sphereStdForm_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply,
    SymplecticForm.mextDeriv_sphereContactForm_apply]

/-- The restriction `σ` of `ω₀` to the sphere is closed. -/
theorem isClosed_sphereStdForm : (sphereStdForm n).IsClosed := by
  rw [sphereStdForm_eq_mextDeriv]
  exact SmoothForm.isClosed_mextDerivₗ _

/-- The pull-back of `σ` along the radial projection `z ↦ ẑ / ‖ẑ‖` is `ρ`. -/
theorem mpullback_radialProjection_sphereStdForm :
    SmoothForm.mpullback (radialProjection n) (contMDiff_radialProjection n ∞) (sphereStdForm n) =
      fubiniStudyLift n := by
  rw [sphereStdForm_eq_mextDeriv, ← SmoothForm.mextDerivₗ_mpullback, fubiniStudyLift_def,
    fubiniStudyPrimitive_def]

variable {n} in
/-- The two-form `ρ = dα` on `ℂⁿ⁺¹ ∖ 0` has the value
`ρ_z(v, w) = ω₀(v, w) / |z|² - (⟨z, v⟩ ω₀(z, w) - ⟨z, w⟩ ω₀(z, v)) / |z|⁴`, with
`⟨z, v⟩ = Re ∑ᵢ conj zᵢ vᵢ`. -/
theorem fubiniStudyLift_apply (z : puncturedSpace (Fin (n + 1) → ℂ))
    (v w : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    (fubiniStudyLift n).eval₂ z v w =
      stdComplexPiSymplecticForm (Fin (n + 1)) v w / ∑ i, ‖(z : Fin (n + 1) → ℂ) i‖ ^ 2 -
        ((star (z : Fin (n + 1) → ℂ) ⬝ᵥ v).re * stdComplexPiSymplecticForm (Fin (n + 1)) z w -
          (star (z : Fin (n + 1) → ℂ) ⬝ᵥ w).re * stdComplexPiSymplecticForm (Fin (n + 1)) z v) /
          (∑ i, ‖(z : Fin (n + 1) → ℂ) i‖ ^ 2) ^ 2 := by
  have hz : 0 < ‖complexToRealEuclidean (Fin (n + 1)) z‖ :=
    norm_pos_iff.2 (by simpa using mem_puncturedSpace.1 z.property)
  rw [← mpullback_radialProjection_sphereStdForm, SmoothForm.eval₂_mpullback, sphereStdForm_apply,
    mvfderiv_radialProjection, mvfderiv_radialProjection, ← norm_sq_complexToRealEuclidean]
  have h₁ := stdForm_complexToRealEuclidean (v : Fin (n + 1) → ℂ) w
  have h₂ := stdForm_complexToRealEuclidean (z : Fin (n + 1) → ℂ) w
  have h₃ := stdForm_complexToRealEuclidean (z : Fin (n + 1) → ℂ) v
  have h₄ := (stdForm (Fin (n + 1))).neg_eq (complexToRealEuclidean _ z)
    (complexToRealEuclidean _ v)
  have h₅ := inner_complexToRealEuclidean _ (z : Fin (n + 1) → ℂ) v
  have h₆ := inner_complexToRealEuclidean _ (z : Fin (n + 1) → ℂ) w
  beta_reduce at h₁ h₂ h₃ h₄
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    (stdForm _).isAlt.self_eq_zero, smul_eq_mul, mul_zero, sub_zero, ← h₄, h₁, h₂, h₃, h₅, h₆]
  field_simp
  ring

end SymplecticGeometry

end
