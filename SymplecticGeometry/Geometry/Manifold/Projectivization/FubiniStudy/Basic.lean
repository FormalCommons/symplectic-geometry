/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import SymplecticGeometry.Geometry.Manifold.Complex.RadialPotential
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Dolbeault.Potential
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
public import TauCeti.Geometry.Contact.Sphere
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Symplectic.Manifold.Descent
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import SymplecticGeometry.Analysis.Complex.Euclidean.Space
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.DegreeOne

/-!
# The Fubini–Study form of `ℂPⁿ`

Write `Z = TauCeti.puncturedSpace (Fin (n + 1) → ℂ)` for `ℂⁿ⁺¹ ∖ 0`, `|z|² = ∑ᵢ ‖zᵢ‖²`,
`⟨z, v⟩ = Re ∑ᵢ conj zᵢ vᵢ`, and `ω₀ = stdComplexPiSymplecticForm (Fin (n + 1))`. This file
builds the forms upstairs, and the Fubini–Study form of `ℂPⁿ` as the descent of one of them.

* `SymplecticGeometry.fubiniStudyPrimitive n` is the one-form `α` on `Z` with
  `α_z(v) = ω₀(z, v) / (2 |z|²)` (`fubiniStudyPrimitive_apply`). It is defined as the pull-back
  along the radial projection `z ↦ ẑ / ‖ẑ‖` of Tau Ceti's contact form
  `TauCeti.SymplecticForm.sphereContactForm` of the unit sphere of `StdSpace (Fin (n + 1))`,
  since `ω₀(z / |z|, ·)` kills the radial direction. With the potential
  `fubiniStudyPotential n`, the radial potential `radialPotential` of `Real.log`, that is the
  function `log |z|²`, with differential
  `v ↦ 2 ⟨z, v⟩ / |z|²` (`mextDerivₗ_fubiniStudyPotential_apply`), it is `(1/4) J* d log |z|²`
  (`fubiniStudyPrimitive_eq`), where `J*` is `covectorComplexStructure` of the complex structure
  of `Z`.
* `SymplecticGeometry.fubiniStudyLift n` is `ρ = dα`. It is closed (`isClosed_fubiniStudyLift`),
  has the value
  `ρ_z(v, w) = ω₀(v, w) / |z|² - (⟨z, v⟩ ω₀(z, w) - ⟨z, w⟩ ω₀(z, v)) / |z|⁴`
  (`fubiniStudyLift_apply`), and its complexification is `(i/2) ∂∂bar log |z|²`
  (`fubiniStudyLift_eq_del_delBar`), by `Dolbeault/Potential.lean`, since `ρ` is the form
  `potentialForm` of `log |z|²` (`fubiniStudyLift_eq_potentialForm`).
* `SymplecticGeometry.sphereStdForm n` is the restriction `σ` of `ω₀ = stdForm (Fin (n + 1))` to
  the unit sphere of `StdSpace (Fin (n + 1))` (`sphereStdForm_apply`). It is the exterior
  derivative of `sphereContactForm` (`sphereStdForm_eq_mextDeriv`), hence closed
  (`isClosed_sphereStdForm`), and its pull-back along the radial projection is `ρ`
  (`mpullback_radialProjection_sphereStdForm`), by naturality of `d`.
* `σ` is basic for the Hopf map `sphereHopf n` (`isBasic_sphereStdForm`): it is invariant under
  the circle action `x ↦ cos t • x + sin t • J₀ x`, whose orbits are the fibres of the Hopf map,
  and at every point its kernel is the kernel of the derivative of the Hopf map
  (`ker_sphereStdForm`), the line `ℝ ∙ J₀ x`. These are the hypotheses of Tau Ceti's
  `TauCeti.SmoothTwoForm.isBasic_of_mpullback_eq_of_ker_mfderiv_le`.
* `SymplecticGeometry.fubiniStudyForm n` is the Fubini–Study form `ω_FS` of `ℂPⁿ`, defined as
  Tau Ceti's descent `TauCeti.SmoothForm.descendedForm` of `σ` along the Hopf map. It pulls back
  to `σ` (`mpullback_sphereHopf_fubiniStudyForm`) and, since the projection
  `Projectivization.mkNonzero ℂ n` is the Hopf map after the radial projection, to `ρ` on `Z`
  (`mpullback_mkNonzero_fubiniStudyForm`, `eval₂_fubiniStudyForm_mfderiv_mkNonzero`). It is
  symplectic (`isSymplectic_fubiniStudyForm`), by
  `TauCeti.SmoothTwoForm.isSymplectic_descendedForm_iff`, and it is the only two-form with either
  pull-back (`existsUnique_mpullback_mkNonzero_eq`,
  `existsUnique_mpullback_sphereHopf_eq`), since both projections are surjective submersions.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Example 4.3.3, p. 168, and Exercises 4.3.4–4.3.5, p. 169.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 3.1.
-/

public section

open Metric TauCeti Projectivization
open scoped Manifold ContDiff InnerProductSpace LinearAlgebra.Projectivization

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
  SmoothForm.ofFunction (radialPotential (Real.contDiffOn_log.mono fun _ hx ↦ ne_of_gt hx))

/-- The potential is the `0`-form of the radial potential `z ↦ log |z|²`. -/
theorem fubiniStudyPotential_def :
    fubiniStudyPotential n =
      SmoothForm.ofFunction (radialPotential (Real.contDiffOn_log.mono fun _ hx ↦ ne_of_gt hx)) :=
  (rfl)

variable {n} in
/-- The potential `fubiniStudyPotential n` takes the value `log |z|²` at `z`. -/
@[simp]
theorem fubiniStudyPotential_apply (z : puncturedSpace (Fin (n + 1) → ℂ))
    (v : Fin 0 → TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    (fubiniStudyPotential n).val z v = Real.log (∑ i, ‖(z : Fin (n + 1) → ℂ) i‖ ^ 2) := by
  rw [fubiniStudyPotential_def, SmoothForm.coe_ofFunction, RoughForm.ofFunction_apply,
    radialPotential_apply]

variable {n} in
/-- The differential of the potential: `d(log |z|²)_z(v) = 2 ⟨z, v⟩ / |z|²`, with
`⟨z, v⟩ = Re ∑ᵢ conj zᵢ vᵢ`. -/
theorem mextDerivₗ_fubiniStudyPotential_apply (z : puncturedSpace (Fin (n + 1) → ℂ))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    (mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 0 (fubiniStudyPotential n)).val z ![v] =
      2 * (star (z : Fin (n + 1) → ℂ) ⬝ᵥ v).re / ∑ i, ‖(z : Fin (n + 1) → ℂ) i‖ ^ 2 := by
  have hd : HasFDerivAt (fun w ↦ Real.log (‖complexToRealEuclidean (Fin (n + 1)) w‖ ^ 2))
      ((‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2)⁻¹ •
        (2 • (innerSL ℝ (complexToRealEuclidean (Fin (n + 1)) z)).comp
          (complexToRealEuclidean (Fin (n + 1)) : (Fin (n + 1) → ℂ) →L[ℝ] _)))
      (z : Fin (n + 1) → ℂ) :=
    ((complexToRealEuclidean (Fin (n + 1))).hasFDerivAt.norm_sq).log
      (norm_sq_complexToRealEuclidean_pos z).ne'
  have hf : (fun y ↦ (fubiniStudyPotential n).val y 0) =
      (fun w ↦ Real.log (‖complexToRealEuclidean (Fin (n + 1)) w‖ ^ 2)) ∘ Subtype.val :=
    funext fun y ↦ by
      rw [fubiniStudyPotential_apply, Function.comp_apply, norm_sq_complexToRealEuclidean]
  rw [mextDerivₗ_zero_apply, hf, Manifold.mvfderiv_comp_subtype_val]
  refine (mvfderiv_eq_fderiv_apply _ (z : Fin (n + 1) → ℂ) v).trans ?_
  rw [hd.fderiv]
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
  refine SmoothBundleForm.ext_fin_one fun z v ↦ ?_
  rw [SmoothForm.smul_toRoughForm, Pi.smul_apply,
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

open TauCeti.ComplexManifold in
/-- The two-form `ρ` on `ℂⁿ⁺¹ ∖ 0` is the form `(1/4) d (J* d log |z|²)` of the potential
`log |z|²`, for the complex structure `J` of `ℂⁿ⁺¹ ∖ 0`. -/
theorem fubiniStudyLift_eq_potentialForm :
    fubiniStudyLift n = (SmoothAlmostComplexStructure.ofComplexManifold (Fin (n + 1) → ℂ)
      (puncturedSpace (Fin (n + 1) → ℂ))).potentialForm (fubiniStudyPotential n) := by
  rw [fubiniStudyLift_def, fubiniStudyPrimitive_eq, map_smul,
    SmoothAlmostComplexStructure.potentialForm_def]

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
    fubiniStudyLift_eq_potentialForm]

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

/-! ### The Fubini–Study form as a descended form -/

/-- The kernel of `σ` at every point of the sphere is the kernel of the derivative of the Hopf
map there: read in `StdSpace (Fin (n + 1))`, both are the line `ℝ ∙ J₀ x`. -/
theorem ker_sphereStdForm (x : sphere (0 : StdSpace (Fin (n + 1))) 1) :
    LinearMap.ker ((sphereStdForm n).bilinFormAt x) =
      (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (sphereHopf n) x).ker := by
  set J := stdComplexStructure (Fin (n + 1))
  set D := mvfderiv (𝓡 (2 * n + 1))
    ((↑) : sphere (0 : StdSpace (Fin (n + 1))) 1 → StdSpace (Fin (n + 1))) x
  ext v
  have h₁ : v ∈ (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (sphereHopf n) x).ker ↔
      D v ∈ ℝ ∙ J (x : StdSpace (Fin (n + 1))) := by
    rw [← ker_mfderiv_sphereHopf n x, Submodule.mem_map]
    refine ⟨fun hv ↦ ⟨v, hv, rfl⟩, fun ⟨u, hu, huv⟩ ↦ ?_⟩
    rwa [← injective_mvfderiv_subtypeVal_sphere (n := 2 * n + 1) x huv]
  -- `v` is in the kernel of `σ_x` exactly when `J₀ (D v)` is orthogonal to the tangent space
  -- `(ℝ ∙ x)ᗮ`, the range of `D`.
  have h₂ : v ∈ LinearMap.ker ((sphereStdForm n).bilinFormAt x) ↔
      J (D v) ∈ (ℝ ∙ (x : StdSpace (Fin (n + 1))))ᗮᗮ := by
    rw [LinearMap.mem_ker, LinearMap.ext_iff, ← range_mvfderiv_subtypeVal (n := 2 * n + 1) x,
      Submodule.mem_orthogonal']
    simp only [LinearMap.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      LinearMap.zero_apply, SmoothForm.bilinFormAt_apply, sphereStdForm_apply,
      stdForm_apply_eq_inner, ContinuousLinearMap.coe_coe, J, D]
  rw [h₁, h₂, Submodule.orthogonal_orthogonal, Submodule.mem_span_singleton,
    Submodule.mem_span_singleton]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨-a, ?_⟩, fun ⟨a, ha⟩ ↦ ⟨-a, ?_⟩⟩
  · rw [neg_smul, ← map_smul, ha, AlmostComplexStructure.apply_apply, neg_neg]
  · rw [← ha, map_smul, AlmostComplexStructure.apply_apply, smul_neg, neg_smul]

/-- The restriction `σ` of `ω₀` to the sphere is basic for the Hopf map: its value only depends on
the images of tangent vectors under the derivative of `sphereHopf n`. It is invariant under the
circle action `x ↦ cos t • x + sin t • J₀ x`, whose orbits are the fibres, and its kernel contains
the vertical vectors by `ker_sphereStdForm`. These are the hypotheses of Tau Ceti's
`TauCeti.SmoothTwoForm.isBasic_of_mpullback_eq_of_ker_mfderiv_le`. -/
theorem isBasic_sphereStdForm :
    RoughForm.IsBasic (V := ℝ) 𝓘(ℝ, Fin n → ℂ) (sphereHopf n) (sphereStdForm n).val := by
  refine SmoothTwoForm.isBasic_of_mpullback_eq_of_ker_mfderiv_le
    (τ := fun t ↦ (stdRotation (Fin (n + 1)) t).unitSphereEquiv)
    ((contMDiff_sphereHopf n 1).mdifferentiable one_ne_zero)
    (fun t ↦ ((stdRotation (Fin (n + 1)) t).contMDiff_unitSphereEquiv (n := 2 * n + 1)
      (k := 2 * n + 1)).mdifferentiable one_ne_zero)
    (fun t ↦ funext fun x ↦ ((sphereHopf_eq_sphereHopf_iff n x _).2
      ⟨t, LinearIsometryEquiv.coe_unitSphereEquiv_apply _ _⟩).symm)
    (fun x y h ↦ .inr <|
      let ⟨t, ht⟩ := (sphereHopf_eq_sphereHopf_iff n x y).1 h
      ⟨t, Subtype.ext <| (LinearIsometryEquiv.coe_unitSphereEquiv_apply _ _).trans ht.symm⟩)
    (fun x ↦ (ker_sphereStdForm n x).ge) fun t ↦ ?_
  rw [← SmoothForm.coe_mpullback _
    ((stdRotation (Fin (n + 1)) t).contMDiff_unitSphereEquiv (n := 2 * n + 1) (k := 2 * n + 1))]
  refine congrArg Subtype.val (SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_)
  rw [SmoothForm.eval₂_mpullback, sphereStdForm_apply, sphereStdForm_apply,
    LinearIsometryEquiv.mvfderiv_coe_sphere_unitSphereEquiv,
    LinearIsometryEquiv.mvfderiv_coe_sphere_unitSphereEquiv, stdForm_stdRotation]

/-- The Fubini–Study form `ω_FS` of `ℂPⁿ = ℙ ℂ (Fin (n + 1) → ℂ)`: the descent of the restriction
`σ` of `ω₀` to the unit sphere along the Hopf map, that is, the unique two-form whose pull-back
along `sphereHopf n` is `σ` (`existsUnique_mpullback_sphereHopf_eq`). Its pull-back to
`ℂⁿ⁺¹ ∖ 0` is `ρ`, whose complexification is `(i/2) ∂∂bar log |z|²`
(`mpullback_mkNonzero_fubiniStudyForm`).

This is McDuff–Salamon's normalization, in which every projective line has area `π`. On `ℂP¹` it
is `π` times Tau Ceti's `OnePoint.fubiniStudyForm`, which has total area `1`. -/
noncomputable def fubiniStudyForm :
    SmoothTwoForm 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)) :=
  SmoothForm.descendedForm (isSubmersion_sphereHopf n) (surjective_sphereHopf n) (sphereStdForm n)
    (isBasic_sphereStdForm n)

theorem fubiniStudyForm_def :
    fubiniStudyForm n = SmoothForm.descendedForm (isSubmersion_sphereHopf n)
      (surjective_sphereHopf n) (sphereStdForm n) (isBasic_sphereStdForm n) :=
  (rfl)

/-- The pull-back of the Fubini–Study form along the Hopf map is the restriction `σ` of `ω₀` to
the sphere. -/
@[simp]
theorem mpullback_sphereHopf_fubiniStudyForm :
    SmoothForm.mpullback (sphereHopf n) (contMDiff_sphereHopf n ∞) (fubiniStudyForm n) =
      sphereStdForm n := by
  rw [fubiniStudyForm_def]
  exact SmoothForm.mpullback_descendedForm

/-- The Fubini–Study form is symplectic: it is closed because `σ` is, and nondegenerate because
the kernel of `σ` is that of the derivative of the Hopf map. -/
theorem isSymplectic_fubiniStudyForm : (fubiniStudyForm n).IsSymplectic := by
  rw [fubiniStudyForm_def]
  exact SmoothTwoForm.isSymplectic_descendedForm_iff.2
    ⟨isClosed_sphereStdForm n, ker_sphereStdForm n⟩

/-- The pull-back of the Fubini–Study form along the projection `ℂⁿ⁺¹ ∖ 0 → ℂPⁿ` is `ρ`. -/
@[simp]
theorem mpullback_mkNonzero_fubiniStudyForm :
    SmoothForm.mpullback (mkNonzero ℂ n) (contMDiff_mkNonzero ℂ n ∞) (fubiniStudyForm n) =
      fubiniStudyLift n := by
  rw [← mpullback_radialProjection_sphereStdForm, ← mpullback_sphereHopf_fubiniStudyForm,
    SmoothForm.mpullback_mpullback]
  simp only [sphereHopf_comp_radialProjection]

variable {n} in
/-- The Fubini–Study form evaluates on the images of two tangent vectors of `ℂⁿ⁺¹ ∖ 0` under the
derivative of the projection as `ρ` on these vectors. -/
theorem eval₂_fubiniStudyForm_mfderiv_mkNonzero (z : puncturedSpace (Fin (n + 1) → ℂ))
    (v w : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) z) :
    (fubiniStudyForm n).eval₂ (mkNonzero ℂ n z)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) z v)
        (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin n → ℂ) (mkNonzero ℂ n) z w) =
      (fubiniStudyLift n).eval₂ z v w := by
  rw [← SmoothForm.eval₂_mpullback _ (contMDiff_mkNonzero ℂ n ∞),
    mpullback_mkNonzero_fubiniStudyForm]

/-- The Fubini–Study form is the only smooth two-form on `ℂPⁿ` whose pull-back along the
projection `ℂⁿ⁺¹ ∖ 0 → ℂPⁿ` is `ρ`. -/
theorem existsUnique_mpullback_mkNonzero_eq :
    ∃! η : SmoothTwoForm 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)),
      SmoothForm.mpullback (mkNonzero ℂ n) (contMDiff_mkNonzero ℂ n ∞) η = fubiniStudyLift n :=
  ⟨fubiniStudyForm n, mpullback_mkNonzero_fubiniStudyForm n, fun _ h ↦
    SmoothForm.mpullback_injective_of_surjective _ (surjective_mkNonzero ℂ n)
      ((isSubmersion_mkNonzero ℂ n).surjective_mfderiv (by simp))
      (h.trans (mpullback_mkNonzero_fubiniStudyForm n).symm)⟩

/-- The Fubini–Study form is the only smooth two-form on `ℂPⁿ` whose pull-back along the Hopf map
is the restriction `σ` of `ω₀` to the unit sphere. -/
theorem existsUnique_mpullback_sphereHopf_eq :
    ∃! η : SmoothTwoForm 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)),
      SmoothForm.mpullback (sphereHopf n) (contMDiff_sphereHopf n ∞) η = sphereStdForm n :=
  ⟨fubiniStudyForm n, mpullback_sphereHopf_fubiniStudyForm n, fun _ h ↦
    SmoothForm.eq_descendedForm_iff.2 h⟩

end SymplecticGeometry

end
