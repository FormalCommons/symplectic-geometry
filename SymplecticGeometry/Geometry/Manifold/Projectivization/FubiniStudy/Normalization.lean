/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.UnitSphere
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Manifold.Projectivization.ProjectiveLine
import SymplecticGeometry.Analysis.Matrix.LDL
import SymplecticGeometry.Geometry.Manifold.Orientation.Sphere
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Kahler
import TauCeti.Geometry.Manifold.Instances.OnePoint.Tangent.Basic
import SymplecticGeometry.Data.Matrix.Mul

/-!
# The Fubini–Study form of `ℂP¹`: affine formula, stereographic coordinates, area of lines

This file compares the Fubini–Study form `ω_FS = fubiniStudyForm 1` of
`ℂP¹ = ℙ ℂ (Fin 2 → ℂ)`, normalized as in McDuff–Salamon, with Tau Ceti's models of the Riemann
sphere. Points of the unit sphere of `ℝ³` are written `x = (x₁, x₂, x₃)`, so that `x₁` is the
coordinate `x 0` in Lean.

* `SymplecticGeometry.eval₂_fubiniStudyForm_affineParam`: in either affine coordinate
  `TauCeti.ProjectiveLine.affineParam i` (`t ↦ [1 : t]` or `t ↦ [t : 1]`), the form reads
  `Im (conj v * w) / (1 + |t|²)²`, that is `dx ∧ dy / (1 + x² + y²)²`. It is computed upstairs,
  on the lift `t ↦ (1, t)` of the coordinate to `ℂ² ∖ 0` (the section
  `Projectivization.affineLift ℂ i` of the Hopf projection, read on `ℂ`), from the value of `ρ`.
* `SymplecticGeometry.mpullback_equivProjectivization_fubiniStudyForm`: along Mathlib's
  identification `OnePoint.equivProjectivization` of `OnePoint ℂ` with `ℂP¹`, the map underlying
  Tau Ceti's biholomorphism `OnePoint.diffeomorphProjectivization`, `ω_FS` pulls back to `π` times
  Tau Ceti's `OnePoint.fubiniStudyForm`, which has total area `1`. Both forms are compared at the
  finite points, which are dense.
* `SymplecticGeometry.sphereToProjectiveLine`: the analytic diffeomorphism from the unit sphere of
  `ℝ³` onto `ℂP¹`, the inverse of Tau Ceti's `OnePoint.diffeomorphSphere v ι` followed by
  `OnePoint.equivProjectivization`, for the north pole `v = homeomorphSphere ∞` and the isometry
  `ι = sphereCoordsIsometry`, `z ↦ (Re z, -Im z, 0)`. That inverse is the inverse of Tau Ceti's
  Pauli model `OnePoint.homeomorphSphere` (`sphereToProjectiveLine_apply`,
  `sphereToProjectiveLine_symm_apply`). It sends `x` to `[x₁ - i x₂ : 1 - x₃]` off the
  north pole (`sphereToProjectiveLine_of_ne_northPole`) and to `[1 + x₃ : x₁ + i x₂]` off the
  south pole (`sphereToProjectiveLine_of_ne_southPole`).
* `SymplecticGeometry.mpullback_sphereToProjectiveLine_fubiniStudyForm`: `ω_FS` pulls back along
  `sphereToProjectiveLine` to a quarter of the area form `vol(x, ·, ·)` of the round sphere, by
  `SymplecticGeometry.mpullback_diffeomorphSphere_symm_fubiniStudyForm`, and
  `sphereToProjectiveLine` preserves the outward-normal orientation of the sphere and the complex
  orientation of `ℂP¹` (`isOrientationPreservingAt_sphereToProjectiveLine`).
* `SymplecticGeometry.integralTopForm_fubiniStudyForm_one`: `ω_FS` integrates to `π` over `ℂP¹`
  with its canonical orientation as a complex manifold, by change of variables along
  `sphereToProjectiveLine` and the area `4π` of the round sphere.
* `SymplecticGeometry.integralTopForm_mpullback_map_fubiniStudyForm`: every line of `ℂPⁿ`, the
  image of `Projectivization.map f hf` for an injective linear `f : ℂ² → ℂⁿ⁺¹`, has area `π`.
  With `F` the matrix of `f` and `P` an upper triangular matrix such that `F P` has orthonormal
  columns (`Matrix.exists_isUpperTriangular_conjTranspose_mul_mul_self_eq_one`), `f ∘ P` pulls
  `ω_FS` back to the form of `ℂP¹` (`mpullback_map_fubiniStudyForm`), and the biholomorphism of
  `ℂP¹` induced by `P` preserves the canonical orientation and hence the integral.

The comparison at the finite points through `TauCeti.SmoothBundleForm.eq_of_forall_mem_dense`
follows the proof of Tau Ceti's
`OnePoint.mpullback_smul_fubiniStudyForm_eq_self_iff_mem_unitaryGroup` (through its step
`mpullback_eq_of_sq_norm_add_sq_norm_eq`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Example 4.3.3, p. 168, and Exercises 4.3.4–4.3.5, p. 169.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapters 15 and 16 (the outward-normal orientation and the volume form of the
  sphere).
-/
public section

open Metric TauCeti Projectivization ComplexConjugate
open scoped Manifold ContDiff LinearAlgebra.Projectivization TauCeti.ComplexManifold
open scoped Matrix ComplexOrder

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The standard orientation of `ℝ³`. -/
local notation "o₃" =>
  Module.Basis.orientation (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 3) ℝ))

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

namespace SymplecticGeometry

/-! ### The affine formula -/

/-- **The Fubini–Study form of `ℂP¹` in an affine coordinate.** Along either affine coordinate
`ProjectiveLine.affineParam i` of `ℂP¹` (`t ↦ [1 : t]` for `i = 0`, `t ↦ [t : 1]` for `i = 1`),
the Fubini–Study form pulls back to `Im (conj v * w) / (1 + |t|²)²` at `t`, that is, to
`dx ∧ dy / (1 + x² + y²)²`. -/
theorem eval₂_fubiniStudyForm_affineParam (i : Fin 2) (t v w : ℂ) :
    (SmoothForm.mpullback (ProjectiveLine.affineParam i)
        (ProjectiveLine.contMDiff_affineParam_real i) (fubiniStudyForm 1)).eval₂ t v w =
      (conj v * w).im / (1 + ‖t‖ ^ 2) ^ 2 := by
  -- The affine coordinate lifts to `ℂ² ∖ 0` along `t ↦ Fin.insertNth i 1 (fun _ ↦ t)`: the lift
  -- `affineLift ℂ i` of the chart after the inclusion `c` of `ℂ` as `Fin 1 → ℂ`.
  let c : ℂ →L[ℝ] Fin 1 → ℂ := ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id ℝ ℂ
  have hc : mkNonzero ℂ 1 ∘ affineLift ℂ i ∘ c = ProjectiveLine.affineParam i := by
    rw [← Function.comp_assoc, mkNonzero_comp_affineLift]
    funext t
    simp [ProjectiveLine.affineParam_eq, affineChart_symm_apply, c]
  have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℂ) (affineLift ℂ i ∘ c) t :=
    ((contMDiff_affineLift ℂ i 1).comp c.contMDiff t).mdifferentiableAt one_ne_zero
  have hd (u : TangentSpace 𝓘(ℝ, ℂ) t) :
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℂ) (affineLift ℂ i ∘ c) t u =
        Fin.insertNth (α := fun _ ↦ ℂ) i 0 (c u) := by
    rw [mfderiv_comp_apply t ((contMDiff_affineLift ℂ i 1 _).mdifferentiableAt one_ne_zero)
      c.mdifferentiableAt, ContinuousLinearMap.mfderiv_eq]
    -- `c u` is read in the tangent space at `c t`, which is the model space `Fin 1 → ℂ`.
    exact mfderiv_affineLift_apply i (c t) (c u)
  -- Read `v` and `w` as tangent vectors at `t`, so that the chain rule applies to them.
  revert v w
  intro (v : TangentSpace 𝓘(ℝ, ℂ) t) (w : TangentSpace 𝓘(ℝ, ℂ) t)
  refine (SmoothForm.eval₂_mpullback _ _ _ _ v w).trans ?_
  rw [← SmoothForm.eval₂_mpullback_mfderiv_of_comp_eventuallyEq (contMDiff_mkNonzero ℂ 1 ∞) _ hmd
      hc.eventuallyEq, mpullback_mkNonzero_fubiniStudyForm, fubiniStudyLift_apply, hd, hd,
    Function.comp_apply, coe_affineLift]
  clear hd hmd hc
  -- Read `v` and `w` as complex numbers again, for the computation.
  revert v w
  intro (v : ℂ) (w : ℂ)
  fin_cases i <;>
    simp [c, Fin.sum_univ_two, stdComplexSymplecticForm_apply, dotProduct, Complex.sq_norm,
      Complex.normSq_apply] <;>
    field_simp <;> ring

/-! ### The comparison with Tau Ceti's Fubini–Study form -/

/-- **The Fubini–Study form of `ℂP¹` is `π` times Tau Ceti's.** Along Mathlib's identification
`OnePoint.equivProjectivization` of the Riemann sphere with `ℂP¹`, `t ↦ [t : 1]` and `∞ ↦ [1 : 0]`
(the map of Tau Ceti's biholomorphism `OnePoint.diffeomorphProjectivization`), the Fubini–Study
form pulls back to `π` times `OnePoint.fubiniStudyForm`, the Fubini–Study form of the Riemann
sphere normalized to total area `1`. -/
theorem mpullback_equivProjectivization_fubiniStudyForm :
    SmoothForm.mpullback (OnePoint.equivProjectivization ℂ)
        ((OnePoint.contMDiff_equivProjectivization_real).of_le le_top)
        (fubiniStudyForm 1) =
      Real.pi • OnePoint.fubiniStudyForm := by
  set P := OnePoint.equivProjectivization ℂ
  -- The forms agree at the finite points, which are dense in the sphere.
  refine SmoothBundleForm.eq_of_forall_mem_dense OnePoint.denseRange_coe ?_
  rintro _ ⟨z, rfl⟩
  refine SmoothBundleForm.apply_eq_of_eval₂_eq fun (v w : ℂ) ↦ ?_
  have hP : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) P z :=
    (OnePoint.contMDiff_equivProjectivization_real z).mdifferentiableAt (by simp)
  have hcomp : ⇑P ∘ ((↑) : ℂ → OnePoint ℂ) = ProjectiveLine.affineParam 1 :=
    funext OnePoint.equivProjectivization_apply_coe_eq_affineParam
  have key := (SmoothForm.eval₂_mpullback _ _ _ _ _ _).symm.trans
    (eval₂_fubiniStudyForm_affineParam 1 z v w)
  -- The derivative of the inclusion `ℂ → OnePoint ℂ` is the identity.
  rw [← hcomp, ((hP.hasMFDerivAt.comp z (OnePoint.hasMFDerivAt_coe z)).mfderiv.trans
    (ContinuousLinearMap.comp_id _))] at key
  refine (SmoothForm.eval₂_mpullback _ _ _ _ _ _).trans ((Eq.trans ?_ key).trans ?_)
  · rfl
  · clear key
    -- Read `v` and `w` as tangent vectors at `z`, so that the evaluation lemmas apply to them.
    revert v w
    intro (v : TangentSpace 𝓘(ℝ, ℂ) (z : OnePoint ℂ)) (w : TangentSpace 𝓘(ℝ, ℂ) (z : OnePoint ℂ))
    have h := OnePoint.eval₂_fubiniStudyForm_coe z v w
    rw [SmoothForm.eval₂_smul, h, OnePoint.fubiniStudyDensity_def, smul_eq_mul]
    field_simp

/-! ### The stereographic map onto `ℂP¹` -/

section Stereographic

open OnePoint (diffeomorphSphere homeomorphSphere sphereCoordsIsometry)
open scoped OnePoint

/-- **Stereographic coordinates on `ℂP¹`.** The analytic diffeomorphism from the unit sphere of
`ℝ³` onto `ℂP¹ = ℙ ℂ (Fin 2 → ℂ)`: stereographic projection from the north pole
`homeomorphSphere ∞`, read through `sphereCoordsIsometry`, followed by the identification of the
Riemann sphere with `ℂP¹`. It sends `x` to `[x₁ - i x₂ : 1 - x₃]` off the north pole
(`sphereToProjectiveLine_of_ne_northPole`) and to `[1 + x₃ : x₁ + i x₂]` off the south pole
(`sphereToProjectiveLine_of_ne_southPole`), where `x = (x₁, x₂, x₃)`. -/
noncomputable def sphereToProjectiveLine :
    sphere (0 : ℝ³) 1 ≃ₘ^ω⟮𝓡 2, 𝓘(ℝ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ) where
  toEquiv := (diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry).symm.toEquiv.trans
    (OnePoint.equivProjectivization ℂ)
  contMDiff_toFun := OnePoint.contMDiff_equivProjectivization_real.comp
    (diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry).symm.contMDiff
  contMDiff_invFun :=
    (diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry).contMDiff.comp
      OnePoint.contMDiff_equivProjectivization_symm_real

theorem coe_sphereToProjectiveLine :
    ⇑sphereToProjectiveLine =
      OnePoint.equivProjectivization ℂ ∘
        (diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry).symm :=
  (rfl)

/-- `sphereToProjectiveLine` is the inverse of the Pauli model `homeomorphSphere` of the Riemann
sphere, followed by its identification with `ℂP¹`. -/
theorem sphereToProjectiveLine_apply (p : sphere (0 : ℝ³) 1) :
    sphereToProjectiveLine p = OnePoint.equivProjectivization ℂ (homeomorphSphere.symm p) := by
  rw [coe_sphereToProjectiveLine, Function.comp_apply,
    OnePoint.diffeomorphSphere_sphereCoordsIsometry_symm_apply]

/-- The inverse of `sphereToProjectiveLine` reads a point of `ℂP¹` on the Riemann sphere and maps
it to the unit sphere of `ℝ³` by the Pauli model `homeomorphSphere`. -/
theorem sphereToProjectiveLine_symm_apply (x : ℙ ℂ (Fin 2 → ℂ)) :
    sphereToProjectiveLine.symm x =
      homeomorphSphere ((OnePoint.equivProjectivization ℂ).symm x) := by
  apply sphereToProjectiveLine.toEquiv.injective
  rw [Diffeomorph.coe_toEquiv, Diffeomorph.apply_symm_apply, sphereToProjectiveLine_apply,
    Homeomorph.symm_apply_apply, Equiv.apply_symm_apply]

/-- On the Pauli model, `sphereToProjectiveLine` is the identification of the Riemann sphere with
`ℂP¹`: it sends `homeomorphSphere x` to `equivProjectivization ℂ x`. -/
@[simp]
theorem sphereToProjectiveLine_homeomorphSphere (x : OnePoint ℂ) :
    sphereToProjectiveLine (homeomorphSphere x) = OnePoint.equivProjectivization ℂ x := by
  rw [sphereToProjectiveLine_apply, Homeomorph.symm_apply_apply]

/-- The inverse of `sphereToProjectiveLine` sends `equivProjectivization ℂ x` to the point
`homeomorphSphere x` of the unit sphere. -/
@[simp]
theorem sphereToProjectiveLine_symm_equivProjectivization (x : OnePoint ℂ) :
    sphereToProjectiveLine.symm (OnePoint.equivProjectivization ℂ x) = homeomorphSphere x := by
  rw [sphereToProjectiveLine_symm_apply, Equiv.symm_apply_apply]

/-- Off the north pole, `sphereToProjectiveLine` sends `x = (x₁, x₂, x₃)` to
`[x₁ - i x₂ : 1 - x₃]`. -/
theorem sphereToProjectiveLine_of_ne_northPole {p : sphere (0 : ℝ³) 1}
    (hp : p ≠ homeomorphSphere ∞) :
    sphereToProjectiveLine p =
      mk ℂ ![((p : ℝ³) 0 : ℂ) - ((p : ℝ³) 1 : ℂ) * Complex.I, ((1 - (p : ℝ³) 2 : ℝ) : ℂ)]
        (fun h ↦ OnePoint.one_sub_ne_zero_of_ne_homeomorphSphere_infty hp
          (Complex.ofReal_eq_zero.1 (congrFun h 1))) := by
  obtain ⟨x, rfl⟩ := homeomorphSphere.surjective p
  induction x using OnePoint.rec with
  | infty => exact absurd rfl hp
  | coe z =>
    have h : (1 + Complex.normSq z : ℂ) ≠ 0 := mod_cast (by linarith [Complex.normSq_nonneg z])
    rw [sphereToProjectiveLine_homeomorphSphere, OnePoint.equivProjectivization_apply_coe,
      mk_eq_mk_iff']
    refine ⟨(1 + Complex.normSq z) / 2, ?_⟩
    ext k
    fin_cases k <;> simp [OnePoint.sphereCoords_coe] <;> field_simp
    · exact Complex.re_add_im z
    · ring

/-- Off the south pole, `sphereToProjectiveLine` sends `x = (x₁, x₂, x₃)` to
`[1 + x₃ : x₁ + i x₂]`. -/
theorem sphereToProjectiveLine_of_ne_southPole {p : sphere (0 : ℝ³) 1}
    (hp : p ≠ -homeomorphSphere ∞) :
    sphereToProjectiveLine p =
      mk ℂ ![((1 + (p : ℝ³) 2 : ℝ) : ℂ), ((p : ℝ³) 0 : ℂ) + ((p : ℝ³) 1 : ℂ) * Complex.I]
        (fun h ↦ OnePoint.one_add_ne_zero_of_ne_neg_homeomorphSphere_infty hp
          (Complex.ofReal_eq_zero.1 (congrFun h 0))) := by
  obtain ⟨x, rfl⟩ := homeomorphSphere.surjective p
  rw [sphereToProjectiveLine_homeomorphSphere]
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.equivProjectivization_apply_infinity, mk_eq_mk_iff']
    refine ⟨2⁻¹, ?_⟩
    ext k
    fin_cases k <;> norm_num
  | coe z =>
    have hz : starRingEnd ℂ z ≠ 0 := by
      rintro h
      rw [map_eq_zero] at h
      subst h
      exact hp OnePoint.homeomorphSphere_zero
    have h : (1 + Complex.normSq z : ℂ) ≠ 0 := mod_cast (by linarith [Complex.normSq_nonneg z])
    rw [OnePoint.equivProjectivization_apply_coe, mk_eq_mk_iff']
    refine ⟨(1 + Complex.normSq z) / (2 * starRingEnd ℂ z), ?_⟩
    ext k
    fin_cases k <;> simp [OnePoint.sphereCoords_coe] <;> field_simp
    · rw [← Complex.mul_conj]
      ring
    · apply Complex.ext <;> simp

/-- **The Fubini–Study form of `ℂP¹` in stereographic coordinates.** Along
`sphereToProjectiveLine`, the Fubini–Study form of `ℂP¹` pulls back to a quarter of the area
form `vol(x, ·, ·)` of the unit sphere of `ℝ³` for its standard orientation. -/
theorem mpullback_sphereToProjectiveLine_fubiniStudyForm :
    SmoothForm.mpullback sphereToProjectiveLine (sphereToProjectiveLine.contMDiff.of_le le_top)
        (fubiniStudyForm 1) =
      (4 : ℝ)⁻¹ • Orientation.sphereVolumeForm o₃ := by
  have h₄ : (4 : ℝ)⁻¹ = Real.pi * (4 * Real.pi)⁻¹ := by
    field_simp
  rw [h₄, ← smul_smul, ← mpullback_diffeomorphSphere_symm_fubiniStudyForm, ← map_smul,
    ← mpullback_equivProjectivization_fubiniStudyForm]
  exact (SmoothForm.mpullback_mpullback _ _ _
    ((OnePoint.contMDiff_equivProjectivization_real).of_le le_top) _).symm

end Stereographic

/-! ### Orientations -/

/-- `sphereToProjectiveLine` preserves orientations: from the outward-normal orientation of the
unit sphere of `ℝ³`, for the standard orientation of `ℝ³`, to the canonical orientation of
`ℂP¹` as a complex manifold. -/
theorem isOrientationPreservingAt_sphereToProjectiveLine (p : sphere (0 : ℝ³) 1) :
    Manifold.Orientation.IsOrientationPreservingAt (Orientation.sphereOrientation o₃)
      (complexCurveOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))) sphereToProjectiveLine p := by
  rw [coe_sphereToProjectiveLine]
  refine (OnePoint.isOrientationPreservingAt_equivProjectivization _).comp ?_
  have h := congrFun
    ((SmoothForm.mpullback_eq_iff _).1 mpullback_diffeomorphSphere_symm_fubiniStudyForm) p
  rw [Orientation.sphereOrientation_eq_ofTopForm, ← OnePoint.ofTopForm_fubiniStudyForm]
  exact Manifold.Orientation.isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
    (by positivity) h

/-! ### The area of a line -/

/-- **The area of `ℂP¹`.** The Fubini–Study form of `ℂP¹ = ℙ ℂ (Fin 2 → ℂ)` integrates to `π`
over `ℂP¹` with its canonical orientation as a complex manifold. -/
theorem integralTopForm_fubiniStudyForm_one :
    integralTopForm (complexCurveOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)))
      (fubiniStudyForm 1).val = Real.pi := by
  have he : Topology.IsOpenEmbedding sphereToProjectiveLine := by
    simpa using sphereToProjectiveLine.toHomeomorph.isOpenEmbedding
  rw [← he.integralTopForm_mpullback_of_isOrientationPreservingAt
      isOrientationPreservingAt_sphereToProjectiveLine (by simp),
    ← SmoothForm.coe_mpullback _ (sphereToProjectiveLine.contMDiff.of_le le_top),
    mpullback_sphereToProjectiveLine_fubiniStudyForm, Submodule.coe_smul, integralTopForm_smul,
    Orientation.integralTopForm_sphereOrientation_sphereVolumeForm]
  ring

/-- **Every complex line in `ℂPⁿ` has area `π`.** For every injective complex-linear map
`f : ℂ² → ℂⁿ⁺¹`, the pull-back of the Fubini–Study form of `ℂPⁿ` along the induced embedding
`ℂP¹ → ℂPⁿ`, `[z] ↦ [f z]`, onto the line `ℙ(range f)`, integrates to `π` over `ℂP¹` with its
canonical orientation as a complex manifold. -/
theorem integralTopForm_mpullback_map_fubiniStudyForm {n : ℕ}
    (f : (Fin 2 → ℂ) →ₗ[ℂ] Fin (n + 1) → ℂ) (hf : Function.Injective f) :
    integralTopForm (complexCurveOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)))
      (SmoothForm.mpullback (map f hf) (contMDiff_map_restrictScalars f hf ∞)
        (fubiniStudyForm n)).val = Real.pi := by
  classical
  -- Write `f ∘ g = A` with `A` of orthonormal columns and `g` invertible: `A = F P` for the
  -- matrix `F` of `f` and an upper triangular `P`, the matrix of `g`.
  set F := LinearMap.toMatrix' f
  have hF : Function.Injective F.mulVec := fun x y h ↦
    hf (by simpa only [F, LinearMap.toMatrix'_mulVec] using h)
  obtain ⟨P, -, hPi, hA⟩ := F.exists_isUpperTriangular_conjTranspose_mul_mul_self_eq_one hF
  replace hPi : Function.Injective (Matrix.toLin' P) := by
    rwa [Matrix.toLin'_apply', Matrix.coe_mulVecLin]
  set Φ := mapDiffeomorph (LinearEquiv.ofInjectiveEndo (Matrix.toLin' P) hPi) ω
  have hAi : Function.Injective (Matrix.toLin' (F * P)) := by
    rw [Matrix.toLin'_apply', Matrix.coe_mulVecLin]
    exact Matrix.mulVec_injective_of_mul_eq_one hA
  have hcomp : map f hf ∘ Φ = map (Matrix.toLin' (F * P)) hAi := by
    funext x
    induction x using ind with
    | h v hv => simp [Φ, map_mk, F, Matrix.toLin'_mul]
  have hΦ : Topology.IsOpenEmbedding Φ := by simpa using Φ.toHomeomorph.isOpenEmbedding
  -- `Φ` is a biholomorphism of `ℂP¹`, so it preserves the canonical orientation.
  rw [← hΦ.integralTopForm_mpullback_of_isOrientationPreservingAt
      (Φ.isOrientationPreservingAt_complexCurveOrientation (by simp) ω) (by simp),
    ← SmoothForm.coe_mpullback _ (by simpa [Φ] using contMDiff_map_restrictScalars _ _ ∞),
    SmoothForm.mpullback_mpullback]
  simp only [hcomp, mpullback_map_fubiniStudyForm (F * P) hA]
  exact integralTopForm_fubiniStudyForm_one

end SymplecticGeometry

end
