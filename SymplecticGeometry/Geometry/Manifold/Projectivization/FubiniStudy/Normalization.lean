/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint
public import SymplecticGeometry.Geometry.Manifold.Orientation.Sphere
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Manifold.Projectivization.ProjectiveLine

/-!
# The Fubini–Study form of `ℂP¹`: affine formula and stereographic coordinates

This file compares the Fubini–Study form `ω_FS = fubiniStudyForm 1` of
`ℂP¹ = ℙ ℂ (Fin 2 → ℂ)`, normalized as in McDuff–Salamon, with Tau Ceti's models of the Riemann
sphere. Points of the unit sphere of `ℝ³` are written `x = (x₁, x₂, x₃)`, so that `x₁` is the
coordinate `x 0` in Lean.

* `SymplecticGeometry.eval₂_fubiniStudyForm_affineParam`: in either affine coordinate
  `TauCeti.ProjectiveLine.affineParam i` (`t ↦ [1 : t]` or `t ↦ [t : 1]`), the form reads
  `Im (conj v * w) / (1 + |t|²)²`, that is `dx ∧ dy / (1 + x² + y²)²`. It is computed upstairs,
  on the lift `t ↦ (1, t)` of the coordinate to `ℂ² ∖ 0`, from the value of `ρ`.
* `SymplecticGeometry.mpullback_equivProjectivization_fubiniStudyForm`: along Mathlib's
  identification `OnePoint.equivProjectivization` of `OnePoint ℂ` with `ℂP¹`, the map underlying
  Tau Ceti's biholomorphism `OnePoint.diffeomorphProjectivization`, `ω_FS` pulls back to `π` times
  Tau Ceti's `OnePoint.fubiniStudyForm`, which has total area `1`. Both forms are compared at the
  finite points, which are dense.
* `SymplecticGeometry.sphereToProjectiveLine`: the analytic diffeomorphism from the unit sphere of
  `ℝ³` onto `ℂP¹`, the inverse of Tau Ceti's `OnePoint.diffeomorphSphere v ι` followed by
  `OnePoint.equivProjectivization`, for the north pole `v = northPole` and the isometry
  `ι = equatorIsometry`, `z ↦ (Re z, -Im z, 0)`. It sends `x` to `[x₁ - i x₂ : 1 - x₃]` off the
  north pole (`sphereToProjectiveLine_of_ne_northPole`) and to `[1 + x₃ : x₁ + i x₂]` off the
  south pole (`sphereToProjectiveLine_of_ne_southPole`).
* `SymplecticGeometry.mpullback_sphereToProjectiveLine_fubiniStudyForm`: `ω_FS` pulls back along
  `sphereToProjectiveLine` to a quarter of the area form `vol(x, ·, ·)` of the round sphere, by
  `SymplecticGeometry.mpullback_diffeomorphSphere_symm_fubiniStudyForm`, and
  `sphereToProjectiveLine` preserves the outward-normal orientation of the sphere and the complex
  orientation of `ℂP¹` (`isOrientationPreservingAt_sphereToProjectiveLine`).

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

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The standard orientation of `ℝ³`. -/
local notation "o₃" =>
  Module.Basis.orientation (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 3) ℝ))

/-- The canonical orientation of `ℂP¹`, as a complex manifold, indexed by `Fin 2`. -/
local notation "oCP1" => Manifold.Orientation.reindex (finCongr (by simp))
  (complexManifoldOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)))

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

namespace SymplecticGeometry

/-! ### The affine formula -/

/-- The lift `t ↦ (1, t)` (for `i = 0`) or `t ↦ (t, 1)` (for `i = 1`) of the affine coordinate
`i` of `ℂP¹` to `ℂ² ∖ 0`. -/
private noncomputable def affineLift (i : Fin 2) (t : ℂ) : puncturedSpace (Fin 2 → ℂ) :=
  ⟨Fin.insertNth i 1 fun _ ↦ t, mem_puncturedSpace.2 (Fin.insertNth_one_ne_zero i _)⟩

private theorem coe_affineLift_apply (i : Fin 2) (t : ℂ) :
    (affineLift i t : Fin 2 → ℂ) = Fin.insertNth i 1 fun _ ↦ t :=
  (rfl)

private theorem coe_affineLift (i : Fin 2) :
    (fun t ↦ (affineLift i t : Fin 2 → ℂ)) =
      fun t ↦ Fin.insertNth i 1 0 + t • Fin.insertNth i 0 fun _ ↦ 1 := by
  funext t
  rw [coe_affineLift_apply]
  fin_cases i <;> ext k <;> fin_cases k <;> simp

private theorem hasFDerivAt_coe_affineLift (i : Fin 2) (t : ℂ) :
    HasFDerivAt (fun t ↦ (affineLift i t : Fin 2 → ℂ))
      ((ContinuousLinearMap.id ℝ ℂ).smulRight (Fin.insertNth i 0 fun _ ↦ (1 : ℂ))) t := by
  rw [coe_affineLift]
  exact ((hasFDerivAt_id t).smul_const _).const_add _

private theorem contMDiff_affineLift (i : Fin 2) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℂ) ∞ (affineLift i) := by
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
  refine ContDiff.contMDiff ?_
  rw [show Subtype.val ∘ affineLift i = fun t ↦ (affineLift i t : Fin 2 → ℂ) from rfl,
    coe_affineLift]
  fun_prop

private theorem mkNonzero_comp_affineLift (i : Fin 2) :
    mkNonzero ℂ 1 ∘ affineLift i = ProjectiveLine.affineParam i := by
  funext t
  simp only [Function.comp_apply, ProjectiveLine.affineParam_eq, mkNonzero_apply,
    coe_affineLift_apply]

/-- **The Fubini–Study form of `ℂP¹` in an affine coordinate.** Along either affine coordinate
`ProjectiveLine.affineParam i` of `ℂP¹` (`t ↦ [1 : t]` for `i = 0`, `t ↦ [t : 1]` for `i = 1`),
the Fubini–Study form pulls back to `Im (conj v * w) / (1 + |t|²)²` at `t`, that is, to
`dx ∧ dy / (1 + x² + y²)²`. -/
theorem eval₂_fubiniStudyForm_affineParam (i : Fin 2) (t v w : ℂ) :
    (SmoothForm.mpullback (ProjectiveLine.affineParam i)
        (ProjectiveLine.contMDiff_affineParam_real i) (fubiniStudyForm 1)).eval₂ t v w =
      (conj v * w).im / (1 + ‖t‖ ^ 2) ^ 2 := by
  have hd (u : TangentSpace 𝓘(ℝ, ℂ) t) :
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℂ) (affineLift i) t u : Fin 2 → ℂ) =
        (show ℂ from u) • Fin.insertNth (α := fun _ ↦ ℂ) i 0 fun _ ↦ 1 := by
    rw [← TauCeti.Manifold.mvfderiv_subtype_val_apply (affineLift i t)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 2 → ℂ) (affineLift i) t u),
      ← mvfderiv_comp_apply _ ((contMDiff_subtypeVal _).mdifferentiableAt one_ne_zero)
        ((contMDiff_affineLift i t).mdifferentiableAt (by simp)), mvfderiv_eq_fderiv_apply]
    exact congrFun (congrArg DFunLike.coe (hasFDerivAt_coe_affineLift i t).fderiv) u
  -- Read `v` and `w` as tangent vectors at `t`, so that the chain rule applies to them.
  revert v w
  intro (v : TangentSpace 𝓘(ℝ, ℂ) t) (w : TangentSpace 𝓘(ℝ, ℂ) t)
  refine (SmoothForm.eval₂_mpullback _ _ _ _ v w).trans ?_
  rw [← mkNonzero_comp_affineLift, mfderiv_comp t
    ((contMDiff_mkNonzero ℂ 1 1 _).mdifferentiableAt one_ne_zero)
    ((contMDiff_affineLift i t).mdifferentiableAt (by simp))]
  simp only [ContinuousLinearMap.comp_apply, Function.comp_apply]
  rw [eval₂_fubiniStudyForm_mfderiv_mkNonzero, fubiniStudyLift_apply, hd, hd,
    coe_affineLift_apply]
  clear hd
  -- Read `v` and `w` as complex numbers again, for the computation.
  revert v w
  intro (v : ℂ) (w : ℂ)
  fin_cases i <;>
    simp [Fin.sum_univ_two, stdComplexSymplecticForm_apply, dotProduct, Complex.sq_norm,
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
  rw [← hcomp, mfderiv_comp z hP ((OnePoint.contMDiff_coe_real z).mdifferentiableAt (by simp))]
    at key
  have hd (u : ℂ) : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) P z ∘L
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : ℂ → OnePoint ℂ) z) u =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) P z u :=
    congrArg (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) P z) (OnePoint.mfderiv_coe_apply z u)
  refine (SmoothForm.eval₂_mpullback _ _ _ _ _ _).trans ((Eq.trans ?_ key).trans ?_)
  · rw [hd, hd, Function.comp_apply]
  · clear key hd
    -- Read `v` and `w` as tangent vectors at `z`, so that the evaluation lemmas apply to them.
    revert v w
    intro (v : TangentSpace 𝓘(ℝ, ℂ) (z : OnePoint ℂ)) (w : TangentSpace 𝓘(ℝ, ℂ) (z : OnePoint ℂ))
    have h := OnePoint.eval₂_fubiniStudyForm_coe z v w
    rw [SmoothForm.eval₂_smul, h, OnePoint.fubiniStudyDensity_def, smul_eq_mul]
    field_simp

/-! ### The stereographic map onto `ℂP¹` -/

/-- **Stereographic coordinates on `ℂP¹`.** The analytic diffeomorphism from the unit sphere of
`ℝ³` onto `ℂP¹ = ℙ ℂ (Fin 2 → ℂ)`: stereographic projection from the north pole, read through
`equatorIsometry`, followed by the identification of the Riemann sphere with `ℂP¹`. It sends `x`
to `[x₁ - i x₂ : 1 - x₃]` off the north pole (`sphereToProjectiveLine_of_ne_northPole`) and to
`[1 + x₃ : x₁ + i x₂]` off the south pole (`sphereToProjectiveLine_of_ne_southPole`), where
`x = (x₁, x₂, x₃)`. -/
noncomputable def sphereToProjectiveLine :
    sphere (0 : ℝ³) 1 ≃ₘ^ω⟮𝓡 2, 𝓘(ℝ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ) where
  toEquiv := (OnePoint.diffeomorphSphere northPole equatorIsometry).symm.toEquiv.trans
    (OnePoint.equivProjectivization ℂ)
  contMDiff_toFun := OnePoint.contMDiff_equivProjectivization_real.comp
    (OnePoint.diffeomorphSphere northPole equatorIsometry).symm.contMDiff
  contMDiff_invFun := (OnePoint.diffeomorphSphere northPole equatorIsometry).contMDiff.comp
    OnePoint.contMDiff_equivProjectivization_symm_real

theorem coe_sphereToProjectiveLine :
    ⇑sphereToProjectiveLine =
      OnePoint.equivProjectivization ℂ ∘
        (OnePoint.diffeomorphSphere northPole equatorIsometry).symm :=
  (rfl)

/-- Off the north pole, `sphereToProjectiveLine` sends `x = (x₁, x₂, x₃)` to
`[x₁ - i x₂ : 1 - x₃]`. -/
theorem sphereToProjectiveLine_of_ne_northPole {p : sphere (0 : ℝ³) 1} (hp : p ≠ northPole) :
    sphereToProjectiveLine p =
      mk ℂ ![((p : ℝ³) 0 : ℂ) - ((p : ℝ³) 1 : ℂ) * Complex.I, ((1 - (p : ℝ³) 2 : ℝ) : ℂ)]
        (fun h ↦ one_sub_ne_zero_of_ne_northPole hp
          (Complex.ofReal_eq_zero.1 (congrFun h 1))) := by
  have h₁ : ((1 - (p : ℝ³) 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast one_sub_ne_zero_of_ne_northPole hp
  push_cast at h₁
  rw [coe_sphereToProjectiveLine, Function.comp_apply,
    OnePoint.diffeomorphSphere_symm_apply_of_ne _ _ hp,
    OnePoint.equivProjectivization_apply_coe,
    equatorIsometry_symm_orthogonalProjectionOnto, inner_northPole, mk_eq_mk_iff']
  refine ⟨((1 - (p : ℝ³) 2 : ℝ) : ℂ)⁻¹, ?_⟩
  ext k
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
    apply Complex.ext <;> simp
  · simp [inv_mul_cancel₀ h₁]

/-- Off the south pole, `sphereToProjectiveLine` sends `x = (x₁, x₂, x₃)` to
`[1 + x₃ : x₁ + i x₂]`. -/
theorem sphereToProjectiveLine_of_ne_southPole {p : sphere (0 : ℝ³) 1} (hp : p ≠ -northPole) :
    sphereToProjectiveLine p =
      mk ℂ ![((1 + (p : ℝ³) 2 : ℝ) : ℂ), ((p : ℝ³) 0 : ℂ) + ((p : ℝ³) 1 : ℂ) * Complex.I]
        (fun h ↦ one_add_ne_zero_of_ne_neg_northPole hp
          (Complex.ofReal_eq_zero.1 (congrFun h 0))) := by
  have h₁ : ((1 + (p : ℝ³) 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast one_add_ne_zero_of_ne_neg_northPole hp
  push_cast at h₁
  by_cases hn : p = northPole
  · subst hn
    rw [coe_sphereToProjectiveLine, Function.comp_apply, OnePoint.diffeomorphSphere_symm_self,
      OnePoint.equivProjectivization_apply_infinity, mk_eq_mk_iff']
    refine ⟨((1 + (northPole : ℝ³) 2 : ℝ) : ℂ)⁻¹, ?_⟩
    ext k
    fin_cases k <;> simp
  · rw [sphereToProjectiveLine_of_ne_northPole hn, mk_eq_mk_iff']
    refine ⟨(((p : ℝ³) 0 : ℂ) - ((p : ℝ³) 1 : ℂ) * Complex.I) / ((1 + (p : ℝ³) 2 : ℝ) : ℂ), ?_⟩
    -- On the unit sphere, `x₁² + x₂² = (1 - x₃) (1 + x₃)`.
    have h : ((p : ℝ³) 0 : ℂ) ^ 2 + ((p : ℝ³) 1 : ℂ) ^ 2 =
        (1 - ((p : ℝ³) 2 : ℂ)) * (1 + ((p : ℝ³) 2 : ℂ)) := by
      have hp : ‖(p : ℝ³)‖ ^ 2 = 1 := by rw [norm_eq_of_mem_sphere p, one_pow]
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at hp
      exact_mod_cast (by linear_combination hp :
        (p : ℝ³) 0 ^ 2 + (p : ℝ³) 1 ^ 2 = (1 - (p : ℝ³) 2) * (1 + (p : ℝ³) 2))
    ext k
    fin_cases k
    · simp [div_mul_cancel₀ _ h₁]
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, smul_eq_mul]
      push_cast
      rw [div_mul_eq_mul_div, div_eq_iff h₁]
      linear_combination h - ((p : ℝ³) 1 : ℂ) ^ 2 * Complex.I_sq

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

/-! ### Orientations -/

/-- `sphereToProjectiveLine` preserves orientations: from the outward-normal orientation of the
unit sphere of `ℝ³`, for the standard orientation of `ℝ³`, to the canonical orientation of
`ℂP¹` as a complex manifold. -/
theorem isOrientationPreservingAt_sphereToProjectiveLine (p : sphere (0 : ℝ³) 1) :
    Manifold.Orientation.IsOrientationPreservingAt (Orientation.sphereOrientation o₃) oCP1
      sphereToProjectiveLine p := by
  rw [coe_sphereToProjectiveLine]
  refine (OnePoint.isOrientationPreservingAt_equivProjectivization _).comp ?_
  have h := congrArg (fun φ : SmoothForm (𝓡 2) (sphere (0 : ℝ³) 1) ℝ 2 ↦ φ.val p)
    mpullback_diffeomorphSphere_symm_fubiniStudyForm
  simp only [SmoothForm.coe_mpullback] at h
  rw [Orientation.sphereOrientation_eq_ofTopForm, ← OnePoint.ofTopForm_fubiniStudyForm]
  exact Manifold.Orientation.isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
    (by positivity) h

end SymplecticGeometry

end
