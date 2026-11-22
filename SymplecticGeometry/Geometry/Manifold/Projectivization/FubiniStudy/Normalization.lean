/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Basic
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Manifold.Projectivization.ProjectiveLine
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
import TauCeti.Geometry.Manifold.Orientation.TopForm
import TauCeti.Geometry.Symplectic.Manifold.Sphere
import TauCeti.LinearAlgebra.Complex.Orientation
import TauCeti.LinearAlgebra.Orientation.Basic
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

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
* `SymplecticGeometry.mpullback_diffeomorphSphere_sphereVolumeForm`: inverse stereographic
  projection `OnePoint.diffeomorphSphere v ι` pulls the area form `vol(x, ·, ·)` of the round
  sphere back to `4π` times `OnePoint.fubiniStudyForm`. Tau Ceti's
  `OnePoint.inner_mfderiv_diffeomorphSphere` says as much for the metrics; the sign of the area
  forms is read off the triple product, computed at the finite points.
* `SymplecticGeometry.mpullback_sphereToProjectiveLine_fubiniStudyForm`: hence `ω_FS` pulls back
  along `sphereToProjectiveLine` to a quarter of the area form of the round sphere, and
  `sphereToProjectiveLine` preserves the outward-normal orientation of the sphere and the complex
  orientation of `ℂP¹` (`isOrientationPreservingAt_sphereToProjectiveLine`).

The comparisons at the finite points through `TauCeti.SmoothBundleForm.eq_of_forall_mem_dense`
follow the proof of Tau Ceti's
`OnePoint.mpullback_smul_fubiniStudyForm_eq_self_iff_mem_unitaryGroup` (through its step
`mpullback_eq_of_sq_norm_add_sq_norm_eq`), and the triple product of inverse stereographic
projection with its derivatives is computed as in Tau Ceti's
`Orientation.integralTopForm_sphereOrientation_sphereVolumeForm` (through its step
`dotProduct_cross_fderiv_stereoParam`), here for the projection from the north pole.

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

/-! ### The north pole and the plane orthogonal to it -/

/-- The north pole `(0, 0, 1)` of the unit sphere of `ℝ³`. -/
noncomputable def northPole : sphere (0 : ℝ³) 1 :=
  ⟨EuclideanSpace.single 2 1, by simp⟩

@[simp]
theorem coe_northPole : (northPole : ℝ³) = EuclideanSpace.single 2 1 :=
  (rfl)

/-- The inner product with the north pole is the third coordinate. -/
theorem inner_northPole (p : ℝ³) : inner ℝ (northPole : ℝ³) p = p 2 := by
  simp [EuclideanSpace.inner_single_left]

private theorem single_zero_mem : (EuclideanSpace.single 0 1 : ℝ³) ∈ (ℝ ∙ (northPole : ℝ³))ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [EuclideanSpace.inner_single_left]

private theorem neg_single_one_mem :
    -(EuclideanSpace.single 1 1 : ℝ³) ∈ (ℝ ∙ (northPole : ℝ³))ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [EuclideanSpace.inner_single_left]

/-- The vectors `e₁` and `-e₂` of the plane orthogonal to the north pole. -/
private noncomputable def equatorBasisVec : Fin 2 → (ℝ ∙ (northPole : ℝ³))ᗮ :=
  ![⟨_, single_zero_mem⟩, ⟨_, neg_single_one_mem⟩]

private theorem orthonormal_equatorBasisVec : Orthonormal ℝ equatorBasisVec := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [equatorBasisVec, EuclideanSpace.inner_single_left]

/-- The orthonormal basis `(e₁, -e₂)` of the plane orthogonal to the north pole. -/
private noncomputable def equatorBasis : OrthonormalBasis (Fin 2) ℝ (ℝ ∙ (northPole : ℝ³))ᗮ :=
  OrthonormalBasis.mk orthonormal_equatorBasisVec <| by
    rw [orthonormal_equatorBasisVec.linearIndependent.span_eq_top_of_card_eq_finrank']
    rw [Submodule.finrank_orthogonal_span_singleton (n := 2) (by simp)]
    simp

/-- The isometry `z ↦ (Re z, -Im z, 0)` from `ℂ` onto the plane orthogonal to the north pole,
built from the orthonormal basis `(e₁, -e₂)`. The conjugation makes inverse stereographic
projection through it orientation-preserving. -/
noncomputable def equatorIsometry : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (northPole : ℝ³))ᗮ :=
  Complex.isometryOfOrthonormal equatorBasis

@[simp]
theorem coe_equatorIsometry_apply (z : ℂ) :
    (equatorIsometry z : ℝ³) = WithLp.toLp 2 ![z.re, -z.im, 0] := by
  rw [equatorIsometry, Complex.isometryOfOrthonormal_apply]
  ext i
  fin_cases i <;> simp [equatorBasis, equatorBasisVec]

/-- The inverse of `equatorIsometry` reads the orthogonal projection of `p` onto the plane
orthogonal to the north pole as `p 0 - i p 1`. -/
theorem equatorIsometry_symm_orthogonalProjectionOnto (p : ℝ³) :
    equatorIsometry.symm ((ℝ ∙ (northPole : ℝ³))ᗮ.orthogonalProjectionOnto p) = ⟨p 0, -p 1⟩ := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext i
  have hn : ‖(northPole : ℝ³)‖ = 1 := by simp
  simp only [Submodule.orthogonalProjectionOnto_orthogonal,
    Submodule.starProjection_unit_singleton ℝ hn, inner_northPole, coe_equatorIsometry_apply]
  fin_cases i <;> simp

/-- Off the north pole, the third coordinate of a point of the unit sphere is not `1`. -/
theorem one_sub_ne_zero_of_ne_northPole {p : sphere (0 : ℝ³) 1} (hp : p ≠ northPole) :
    1 - (p : ℝ³) 2 ≠ 0 := by
  rw [sub_ne_zero, ← inner_northPole]
  intro h
  exact hp (Subtype.ext ((inner_eq_one_iff_of_norm_eq_one (by simp)
    (norm_eq_of_mem_sphere p)).1 h.symm).symm)

/-- Off the south pole, the third coordinate of a point of the unit sphere is not `-1`. -/
theorem one_add_ne_zero_of_ne_neg_northPole {p : sphere (0 : ℝ³) 1} (hp : p ≠ -northPole) :
    1 + (p : ℝ³) 2 ≠ 0 := by
  have h := one_sub_ne_zero_of_ne_northPole (p := -p) fun h ↦ hp (by rw [← h, neg_neg])
  rwa [coe_neg_sphere, PiLp.neg_apply, sub_neg_eq_add] at h

/-! ### Inverse stereographic projection and the area form of the sphere -/

/-- The derivative of inverse stereographic projection from the north pole, read on `ℂ`. -/
private theorem hasFDerivAt_coe_diffeomorphSphere_coe (z : ℂ) :
    HasFDerivAt (fun y : ℂ ↦ (OnePoint.diffeomorphSphere northPole equatorIsometry y : ℝ³))
      ((-((1 + ‖z‖ ^ 2) ^ 2)⁻¹ • (2 • (innerSL ℝ z).comp (ContinuousLinearMap.id ℝ ℂ))).smulRight
          ((2 : ℝ) • (equatorIsometry z : ℝ³) + (‖z‖ ^ 2 - 1) • (northPole : ℝ³)) +
        (1 + ‖z‖ ^ 2)⁻¹ • ((2 : ℝ) • ((ℝ ∙ (northPole : ℝ³))ᗮ.subtypeL.comp
          equatorIsometry.toContinuousLinearEquiv.toContinuousLinearMap) +
          (2 • (innerSL ℝ z).comp (ContinuousLinearMap.id ℝ ℂ)).smulRight (northPole : ℝ³))) z := by
  have hN := (hasFDerivAt_id z).norm_sq
  have h := ((hasDerivAt_inv (by positivity : (1 + ‖z‖ ^ 2) ≠ 0)).comp_hasFDerivAt z
    (hN.const_add 1)).smul ((((ℝ ∙ (northPole : ℝ³))ᗮ.subtypeL.comp
      equatorIsometry.toContinuousLinearEquiv.toContinuousLinearMap).hasFDerivAt.const_smul
        (2 : ℝ)).add ((hN.sub_const 1).smul_const (northPole : ℝ³)))
  refine (h.congr_of_eventuallyEq (.of_forall fun y ↦ ?_)).congr_fderiv ?_
  · simp
  · ext a
    simp [smul_add, add_comm]

/-- **The round sphere is `4π` times the Fubini–Study sphere, as an area form.** Inverse
stereographic projection `OnePoint.diffeomorphSphere northPole equatorIsometry` from the north
pole pulls the outward-normal area form `vol(x, ·, ·)` of the unit sphere of `ℝ³` back to `4π`
times the Fubini–Study form `OnePoint.fubiniStudyForm` of the Riemann sphere. -/
theorem mpullback_diffeomorphSphere_sphereVolumeForm :
    SmoothForm.mpullback (OnePoint.diffeomorphSphere northPole equatorIsometry)
        ((OnePoint.diffeomorphSphere northPole equatorIsometry).contMDiff.of_le le_top)
        (Orientation.sphereVolumeForm o₃) =
      (4 * Real.pi) • OnePoint.fubiniStudyForm := by
  set σ := OnePoint.diffeomorphSphere northPole equatorIsometry
  -- The forms agree at the finite points, which are dense in the sphere.
  refine SmoothBundleForm.eq_of_forall_mem_dense OnePoint.denseRange_coe ?_
  rintro _ ⟨z, rfl⟩
  refine SmoothBundleForm.apply_eq_of_eval₂_eq fun a b ↦ ?_
  have hσ : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 2) σ z := σ.mdifferentiable (by simp) _
  have hcoe : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ³) ((↑) : sphere (0 : ℝ³) 1 → ℝ³) (σ z) :=
    (contMDiff_coe_sphere _).mdifferentiableAt one_ne_zero
  have hd (c : TangentSpace 𝓘(ℝ, ℂ) (z : OnePoint ℂ)) :
      mvfderiv (𝓡 2) ((↑) : sphere (0 : ℝ³) 1 → ℝ³) (σ z) (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) σ z c) =
        fderiv ℝ (fun y : ℂ ↦ (σ y : ℝ³)) z c :=
    (mvfderiv_comp_apply _ hcoe hσ c).symm.trans (OnePoint.mvfderiv_coe_apply (hcoe.comp _ hσ) c)
  rw [SmoothForm.eval₂_mpullback, ← sphereAreaForm_eq_sphereVolumeForm, eval₂_sphereAreaForm,
    hd, hd, (hasFDerivAt_coe_diffeomorphSphere_coe z).fderiv]
  have h₁ := SmoothForm.eval₂_smul (4 * Real.pi) OnePoint.fubiniStudyForm (z : OnePoint ℂ) a b
  have h₂ := OnePoint.eval₂_fubiniStudyForm_coe z a b
  rw [h₁, h₂, OnePoint.fubiniStudyDensity_def, OnePoint.coe_diffeomorphSphere_coe]
  clear h₁ h₂ hd
  -- Read `a` and `b` as complex numbers, and compute the triple product in coordinates.
  revert a b
  intro (a : ℂ) (b : ℂ)
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply,
    Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, coe_equatorIsometry_apply, coe_northPole,
    Complex.inner, WithLp.ofLp_add, WithLp.ofLp_smul]
  have hv : (EuclideanSpace.single 2 1 : ℝ³).ofLp = ![0, 0, 1] := by
    ext i
    fin_cases i <;> simp
  rw [hv]
  simp only [cross_apply, dotProduct, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, smul_eq_mul, Pi.add_apply,
    Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, nsmul_eq_mul, Nat.cast_ofNat]
  field_simp
  ring

/-- Stereographic projection from the north pole, the inverse of
`OnePoint.diffeomorphSphere northPole equatorIsometry`, pulls the Fubini–Study form of the
Riemann sphere back to `(4π)⁻¹` times the area form of the unit sphere of `ℝ³`. -/
theorem mpullback_diffeomorphSphere_symm_fubiniStudyForm :
    SmoothForm.mpullback (OnePoint.diffeomorphSphere northPole equatorIsometry).symm
        ((OnePoint.diffeomorphSphere northPole equatorIsometry).symm.contMDiff.of_le le_top)
        OnePoint.fubiniStudyForm =
      (4 * Real.pi)⁻¹ • Orientation.sphereVolumeForm o₃ := by
  have hid : ⇑(OnePoint.diffeomorphSphere northPole equatorIsometry) ∘
      ⇑(OnePoint.diffeomorphSphere northPole equatorIsometry).symm = id :=
    funext (OnePoint.diffeomorphSphere northPole equatorIsometry).apply_symm_apply
  have h₄ : (4 * Real.pi)⁻¹ • (4 * Real.pi) • OnePoint.fubiniStudyForm =
      OnePoint.fubiniStudyForm := by
    rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  rw [← h₄, map_smul, ← mpullback_diffeomorphSphere_sphereVolumeForm,
    SmoothForm.mpullback_mpullback]
  simp only [hid, SmoothForm.mpullback_id, LinearMap.id_apply]

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

/-- The outward-normal orientation of the unit sphere is the orientation of its volume form
`Orientation.sphereVolumeForm`. -/
theorem _root_.Orientation.sphereOrientation_eq_ofTopForm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (o : Orientation ℝ E (Fin (n + 1))) :
    o.sphereOrientation = Manifold.Orientation.ofTopForm finrank_euclideanSpace_fin
      o.sphereVolumeForm.val (o.sphereVolumeForm.isSmoothForm.of_le zero_le)
      o.sphereVolumeForm_apply_ne_zero := by
  ext u
  set o' := Manifold.Orientation.ofTopForm finrank_euclideanSpace_fin o.sphereVolumeForm.val
    (o.sphereVolumeForm.isSmoothForm.of_le zero_le) o.sphereVolumeForm_apply_ne_zero
  let b := Module.finBasisOfFinrankEq ℝ (TangentSpace (𝓡 n) u)
    (finrank_euclideanSpace_fin (𝕜 := ℝ))
  -- A tangent basis is positive for both orientations exactly when `vol(u, b₁, …, bₙ) > 0`.
  have h : b.orientation = o.sphereOrientation.orientationAt u ↔
      b.orientation = o'.orientationAt u := by
    rw [o.orientation_eq_orientationAt_sphereOrientation_iff,
      Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff,
      Orientation.sphereVolumeForm_apply]
  have hcard (o'' : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) :=
    Nat.card_eq_fintype_card.trans (o''.finrank_tangentSpace_eq u).symm
  rcases b.orientation.eq_or_eq_neg (o.sphereOrientation.orientationAt u)
    (hcard o.sphereOrientation) with hb | hb
  · exact hb.symm.trans (h.1 hb)
  · rcases b.orientation.eq_or_eq_neg (o'.orientationAt u) (hcard o') with hb' | hb'
    · exact absurd (h.2 hb') (hb ▸ (Module.Ray.ne_neg_self _).symm)
    · exact neg_injective (hb.symm.trans hb')

/-- The orientation of the Riemann sphere defined by its Fubini–Study form. -/
private noncomputable def onePointOrientation :
    Manifold.Orientation 𝓘(ℝ, ℂ) (OnePoint ℂ) (Fin 2) :=
  Manifold.Orientation.ofTopForm Complex.finrank_real_complex OnePoint.fubiniStudyForm.val
    (OnePoint.fubiniStudyForm.isSmoothForm.of_le zero_le) OnePoint.fubiniStudyForm_apply_ne_zero

/-- In the preferred chart, the orientation of the Fubini–Study form is that of the basis
`(1, i)`. -/
private theorem orientationAt_onePointOrientation (x : OnePoint ℂ) :
    Manifold.Orientation.orientationAt onePointOrientation x = Complex.orientation := by
  refine ((Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff
    Complex.finrank_real_complex (OnePoint.fubiniStudyForm.isSmoothForm.of_le zero_le)
    OnePoint.fubiniStudyForm_apply_ne_zero (x := x) Complex.basisOneI).2 ?_).symm
  have h := (SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans
    (OnePoint.eval₂_fubiniStudyForm x 1 Complex.I)
  have hb : (⇑Complex.basisOneI : Fin 2 → TangentSpace 𝓘(ℝ, ℂ) x) = ![1, Complex.I] :=
    Complex.coe_basisOneI
  refine lt_of_lt_of_eq ?_ ((congrArg (OnePoint.fubiniStudyForm.val x) hb).trans h).symm
  simpa using OnePoint.fubiniStudyDensity_pos _

/-- The biholomorphism of the Riemann sphere onto `ℂP¹` carries the orientation of the
Fubini–Study form to the complex orientation: its derivative is complex-linear. -/
private theorem isOrientationPreservingAt_equivProjectivization (x : OnePoint ℂ) :
    Manifold.Orientation.IsOrientationPreservingAt onePointOrientation oCP1
      (OnePoint.equivProjectivization ℂ) x := by
  set P₀ := OnePoint.diffeomorphProjectivization ℂ ω
  -- The real derivative is the complex one, the casts between tangent spaces being identities.
  have hpt (v : ℂ) : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) (OnePoint.equivProjectivization ℂ) x v =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) P₀ x v := by
    rw [OnePoint.coe_diffeomorphProjectivization]
    exact DFunLike.congr_fun (((OnePoint.contMDiff_equivProjectivization (𝕜 := ℂ) x
      ).mdifferentiableAt (by simp)).mfderiv_restrictScalars ℝ) v
  let Lc : ℂ ≃L[ℂ] (Fin 1 → ℂ) := P₀.mfderivToContinuousLinearEquiv (by simp) x
  refine (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).2
    ⟨Lc.restrictScalars' ℝ, ?_, ?_⟩
  · ext v
    exact ((congrFun (Lc.coe_restrictScalars' (R := ℝ)) v).trans
      (DFunLike.congr_fun (P₀.mfderivToContinuousLinearEquiv_coe (by simp)) v)).trans
        (hpt v).symm
  · have key : Orientation.map (Fin 2) (Lc.restrictScalars' ℝ).toLinearEquiv Complex.orientation =
        Orientation.reindex ℝ (Fin 1 → ℂ) (finCongr (by simp))
          (complexOrientation (Fin 1 → ℂ)) := by
      rw [← reindex_complexOrientation_complex, Orientation.map_reindex,
        ContinuousLinearEquiv.restrictScalars'_toLinearEquiv, LinearEquiv.map_complexOrientation,
        Orientation.reindex_finCongr_reindex_finCongr]
    rw [Manifold.Orientation.orientationAt_reindex,
      orientationAt_complexManifoldOrientation_eq_complexOrientation]
    exact (congrArg _ (orientationAt_onePointOrientation x)).trans key

/-- `sphereToProjectiveLine` preserves orientations: from the outward-normal orientation of the
unit sphere of `ℝ³`, for the standard orientation of `ℝ³`, to the canonical orientation of
`ℂP¹` as a complex manifold. -/
theorem isOrientationPreservingAt_sphereToProjectiveLine (p : sphere (0 : ℝ³) 1) :
    Manifold.Orientation.IsOrientationPreservingAt (Orientation.sphereOrientation o₃) oCP1
      sphereToProjectiveLine p := by
  rw [coe_sphereToProjectiveLine]
  refine (isOrientationPreservingAt_equivProjectivization _).comp ?_
  have h := congrArg (fun φ : SmoothForm (𝓡 2) (sphere (0 : ℝ³) 1) ℝ 2 ↦ φ.val p)
    mpullback_diffeomorphSphere_symm_fubiniStudyForm
  simp only [SmoothForm.coe_mpullback] at h
  rw [Orientation.sphereOrientation_eq_ofTopForm, onePointOrientation]
  exact Manifold.Orientation.isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
    (by positivity) h

end SymplecticGeometry

end
