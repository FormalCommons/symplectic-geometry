/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving.FromTauCeti
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Manifold.Orientation.TopForm
public import TauCeti.Geometry.Manifold.Projectivization.ProjectiveLine
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
import TauCeti.Geometry.Symplectic.Manifold.Sphere

/-!
# The Riemann sphere as a real surface

Tau Ceti charts the Riemann sphere `OnePoint ℂ` by its affine coordinate, whose inverse is the
inclusion `ℂ → OnePoint ℂ`, and by the inverted coordinate. This file records how the inclusion
reads for the underlying real surface, modelled on `𝓘(ℝ, ℂ)`, and compares the Riemann sphere with
`ℂP¹` and with the round sphere of `ℝ³`:

* `OnePoint.contMDiff_coe_real`: the inclusion is real-analytic;
* `OnePoint.mfderiv_coe_apply`: its derivative is the identity of `ℂ`, the tangent spaces at
  `z` and at `(z : OnePoint ℂ)` being `ℂ`;
* `OnePoint.mvfderiv_coe_apply`: so the derivative at a finite point of a map from the sphere to
  a normed space is the derivative of its restriction to `ℂ`;
* `OnePoint.contMDiff_equivProjectivization_real` and
  `OnePoint.contMDiff_equivProjectivization_symm_real`: Mathlib's identification
  `OnePoint.equivProjectivization` of `OnePoint ℂ` with `ℙ ℂ (Fin 2 → ℂ)` and its inverse are
  real-analytic;
* `OnePoint.equivProjectivization_apply_coe_eq_affineParam`: under that identification, the
  inclusion is Tau Ceti's affine coordinate `t ↦ [t : 1]` of the projective line;
* `OnePoint.hasFDerivAt_coe_diffeomorphSphere_coe`: the derivative of Tau Ceti's inverse
  stereographic projection `OnePoint.diffeomorphSphere v ι`, read on `ℂ`;
* `OnePoint.ofTopForm_fubiniStudyForm`: the orientation of Tau Ceti's `OnePoint.fubiniStudyForm`
  is the canonical orientation of the Riemann sphere as a complex manifold;
* `SymplecticGeometry.projectiveLineOrientation`: the canonical orientation of `ℂP¹` as a complex
  manifold, indexed by `Fin 2`, with `SymplecticGeometry.orientationAt_projectiveLineOrientation`;
* `Diffeomorph.isOrientationPreservingAt_projectiveLineOrientation`: biholomorphisms of `ℂP¹`
  preserve that orientation;
* `OnePoint.isOrientationPreservingAt_equivProjectivization`: the identification with `ℂP¹`
  preserves the canonical orientations;
* `SymplecticGeometry.northPole` and `SymplecticGeometry.equatorIsometry`: the north pole
  `(0, 0, 1)` of the unit sphere of `ℝ³`, and the isometry `z ↦ (Re z, -Im z, 0)` of `ℂ` onto
  the plane orthogonal to it;
* `SymplecticGeometry.mpullback_diffeomorphSphere_sphereVolumeForm`: inverse stereographic
  projection `OnePoint.diffeomorphSphere northPole equatorIsometry` pulls the area form
  `vol(x, ·, ·)` of the round sphere back to `4π` times `OnePoint.fubiniStudyForm`, and
  `SymplecticGeometry.mpullback_diffeomorphSphere_symm_fubiniStudyForm` states the inverse
  relation. Tau Ceti's `OnePoint.inner_mfderiv_diffeomorphSphere` says as much for the metrics;
  the sign of the area forms is read off the triple product, computed at the finite points.

The derivative of the inclusion is computed in charts, as in the proof of Tau Ceti's
`OnePoint.mfderiv_smul_coe_apply`. The comparison of area forms at the finite points through
`TauCeti.SmoothBundleForm.eq_of_forall_mem_dense` follows the proof of Tau Ceti's
`OnePoint.mpullback_smul_fubiniStudyForm_eq_self_iff_mem_unitaryGroup` (through its step
`mpullback_eq_of_sq_norm_add_sq_norm_eq`), and the triple product of inverse stereographic
projection with its derivatives is computed as in Tau Ceti's
`Orientation.integralTopForm_sphereOrientation_sphereVolumeForm` (through its step
`dotProduct_cross_fderiv_stereoParam`), here for the projection from the north pole.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1.5.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapters 15 and 16 (the outward-normal orientation and the volume form of the
  sphere).
-/

public section

open Metric TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization TauCeti.ComplexManifold

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The standard orientation of `ℝ³`. -/
local notation "o₃" =>
  Module.Basis.orientation (OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 3) ℝ))

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

namespace SymplecticGeometry

/-! ### The orientation of `ℂP¹` -/

/-- The canonical orientation of `ℂP¹ = ℙ ℂ (Fin 2 → ℂ)` as a complex manifold, Tau Ceti's
`complexManifoldOrientation`, indexed by `Fin 2` instead of `Fin (2 * finrank ℂ (Fin 1 → ℂ))`. -/
noncomputable def projectiveLineOrientation :
    Manifold.Orientation 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) (Fin 2) :=
  (complexManifoldOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))).reindex (finCongr (by simp))

theorem projectiveLineOrientation_def :
    projectiveLineOrientation =
      (complexManifoldOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))).reindex (finCongr (by simp)) :=
  (rfl)

/-- At every point of `ℂP¹`, `projectiveLineOrientation` is the complex orientation of the model
space `Fin 1 → ℂ`, indexed by `Fin 2`. -/
@[simp]
theorem orientationAt_projectiveLineOrientation (x : ℙ ℂ (Fin 2 → ℂ)) :
    projectiveLineOrientation.orientationAt x =
      Orientation.reindex ℝ (TangentSpace 𝓘(ℝ, Fin 1 → ℂ) x) (finCongr (by simp))
        (complexOrientation (Fin 1 → ℂ)) := by
  rw [projectiveLineOrientation_def, Manifold.Orientation.orientationAt_reindex,
    orientationAt_complexManifoldOrientation_eq_complexOrientation]

/-- A biholomorphism of `ℂP¹` (a `C^n` diffeomorphism for the complex model, `n ≠ 0`) preserves
`projectiveLineOrientation` at every point. -/
theorem _root_.Diffeomorph.isOrientationPreservingAt_projectiveLineOrientation (n : ℕ∞ω)
    [NeZero n] (Φ : ℙ ℂ (Fin 2 → ℂ) ≃ₘ^n⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ))
    (x : ℙ ℂ (Fin 2 → ℂ)) :
    Manifold.Orientation.IsOrientationPreservingAt projectiveLineOrientation
      projectiveLineOrientation Φ x := by
  rw [projectiveLineOrientation_def]
  exact (Φ.isOrientationPreservingAt_complexManifoldOrientation n x).reindex _

end SymplecticGeometry

namespace OnePoint

/-- The inclusion `ℂ → OnePoint ℂ` is real-analytic for the underlying real surfaces. -/
theorem contMDiff_coe_real : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ω ((↑) : ℂ → OnePoint ℂ) := by
  simpa only [modelWithCornersSelf_restrictScalars] using
    (contMDiff_coe (𝕜 := ℂ)).restrictScalars ℝ

/-- The real derivative of the inclusion `ℂ → OnePoint ℂ` at `z` is the identity of `ℂ`: the
inclusion is the inverse of the affine chart, through which the tangent space at `z` is read. -/
theorem mfderiv_coe_apply (z v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : ℂ → OnePoint ℂ) z v = v := by
  rw [((contMDiff_coe_real z).mdifferentiableAt (by simp)).mfderiv]
  simp only [writtenInExtChartAt, chartAt_coe, affineChart_coe, fderivWithin_univ,
    Function.comp_def, mfld_simps]
  rw [fderiv_fun_id, ContinuousLinearMap.id_comp]
  -- The casts `tangentSpaceCastModel` between the tangent spaces and `ℂ` are identities.
  rfl

/-- At a finite point `z`, the derivative of a map `F` from the Riemann sphere to a real normed
space is the derivative of `F` restricted to `ℂ`. -/
theorem mvfderiv_coe_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : OnePoint ℂ → E} {z : ℂ} (hF : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z) (a : ℂ) :
    mvfderiv 𝓘(ℝ, ℂ) F z a = fderiv ℝ (F ∘ (↑)) z a :=
  (congrArg (mvfderiv 𝓘(ℝ, ℂ) F z) (mfderiv_coe_apply z a)).symm.trans
    ((mvfderiv_comp_apply z hF ((contMDiff_coe_real z).mdifferentiableAt (by simp)) a).symm.trans
      (TauCeti.mvfderiv_eq_fderiv_apply _ z a))

/-- Mathlib's identification of `OnePoint ℂ` with `ℙ ℂ (Fin 2 → ℂ)`, `t ↦ [t : 1]` and
`∞ ↦ [1 : 0]`, is real-analytic for the underlying real surfaces. -/
theorem contMDiff_equivProjectivization_real :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) ω (equivProjectivization ℂ) := by
  simpa only [modelWithCornersSelf_restrictScalars] using
    (contMDiff_equivProjectivization (𝕜 := ℂ)).restrictScalars ℝ

/-- The inverse of Mathlib's identification of `OnePoint ℂ` with `ℙ ℂ (Fin 2 → ℂ)` is
real-analytic for the underlying real surfaces. -/
theorem contMDiff_equivProjectivization_symm_real :
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, ℂ) ω (equivProjectivization ℂ).symm := by
  simpa only [modelWithCornersSelf_restrictScalars] using
    (contMDiff_equivProjectivization_symm (𝕜 := ℂ)).restrictScalars ℝ

/-- Mathlib's identification of `OnePoint ℂ` with `ℙ ℂ (Fin 2 → ℂ)` sends a finite point `t` to
`[t : 1]`, the value at `t` of Tau Ceti's affine coordinate at the coordinate `1`. -/
theorem equivProjectivization_apply_coe_eq_affineParam (t : ℂ) :
    equivProjectivization ℂ t = TauCeti.ProjectiveLine.affineParam 1 t := by
  rw [equivProjectivization_apply_coe, TauCeti.ProjectiveLine.affineParam_eq]
  congr 1
  ext k
  fin_cases k <;> simp

/-! ### Inverse stereographic projection -/

/-- The derivative of Tau Ceti's inverse stereographic projection
`OnePoint.diffeomorphSphere v ι` from `v`, read on `ℂ`: the derivative at `z` of
`y ↦ (1 + ‖y‖²)⁻¹ • (2 ι y + (‖y‖² - 1) v)`. -/
theorem hasFDerivAt_coe_diffeomorphSphere_coe {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2 + 1)] (v : sphere (0 : E) 1)
    (ι : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (v : E))ᗮ) (z : ℂ) :
    HasFDerivAt (fun y : ℂ ↦ (diffeomorphSphere v ι y : E))
      ((-((1 + ‖z‖ ^ 2) ^ 2)⁻¹ • (2 • (innerSL ℝ z).comp (ContinuousLinearMap.id ℝ ℂ))).smulRight
          ((2 : ℝ) • (ι z : E) + (‖z‖ ^ 2 - 1) • (v : E)) +
        (1 + ‖z‖ ^ 2)⁻¹ • ((2 : ℝ) • ((ℝ ∙ (v : E))ᗮ.subtypeL.comp
          ι.toContinuousLinearEquiv.toContinuousLinearMap) +
          (2 • (innerSL ℝ z).comp (ContinuousLinearMap.id ℝ ℂ)).smulRight (v : E))) z := by
  have hN := (hasFDerivAt_id z).norm_sq
  have h := ((hasDerivAt_inv (by positivity : (1 + ‖z‖ ^ 2) ≠ 0)).comp_hasFDerivAt z
    (hN.const_add 1)).smul ((((ℝ ∙ (v : E))ᗮ.subtypeL.comp
      ι.toContinuousLinearEquiv.toContinuousLinearMap).hasFDerivAt.const_smul
        (2 : ℝ)).add ((hN.sub_const 1).smul_const (v : E)))
  refine (h.congr_of_eventuallyEq (.of_forall fun y ↦ ?_)).congr_fderiv ?_
  · simp
  · ext a
    simp [smul_add, add_comm]

/-! ### Orientations -/

/-- The orientation of the Riemann sphere defined by its Fubini–Study form is its canonical
orientation as a complex manifold. -/
theorem ofTopForm_fubiniStudyForm :
    Manifold.Orientation.ofTopForm Complex.finrank_real_complex fubiniStudyForm.val
        (fubiniStudyForm.isSmoothForm.of_le zero_le) fubiniStudyForm_apply_ne_zero =
      (complexManifoldOrientation ℂ (OnePoint ℂ)).reindex (finCongr (m := 2) (by simp)) := by
  ext x
  rw [Manifold.Orientation.orientationAt_reindex,
    orientationAt_complexManifoldOrientation_eq_complexOrientation]
  refine ((Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff
    Complex.finrank_real_complex (fubiniStudyForm.isSmoothForm.of_le zero_le)
    fubiniStudyForm_apply_ne_zero (x := x) Complex.basisOneI).2 ?_).symm.trans
      reindex_complexOrientation_complex.symm
  -- In the preferred chart, the Fubini–Study form is positive on the basis `(1, i)`.
  have h := (SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans
    (eval₂_fubiniStudyForm x 1 Complex.I)
  have hb : (⇑Complex.basisOneI : Fin 2 → TangentSpace 𝓘(ℝ, ℂ) x) = ![1, Complex.I] :=
    Complex.coe_basisOneI
  refine lt_of_lt_of_eq ?_ ((congrArg (fubiniStudyForm.val x) hb).trans h).symm
  simpa using fubiniStudyDensity_pos _

/-- Mathlib's identification of the Riemann sphere with `ℂP¹`, the map of Tau Ceti's
biholomorphism `OnePoint.diffeomorphProjectivization`, preserves the canonical orientations of
both as complex manifolds: its derivative is complex-linear. -/
theorem isOrientationPreservingAt_equivProjectivization (x : OnePoint ℂ) :
    Manifold.Orientation.IsOrientationPreservingAt
      ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex (finCongr (m := 2) (by simp)))
      SymplecticGeometry.projectiveLineOrientation (equivProjectivization ℂ) x := by
  set P₀ := diffeomorphProjectivization ℂ ω
  -- The real derivative is the complex one, the casts between tangent spaces being identities.
  have hpt (v : ℂ) : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) (equivProjectivization ℂ) x v =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) P₀ x v := by
    rw [coe_diffeomorphProjectivization]
    exact DFunLike.congr_fun (((contMDiff_equivProjectivization (𝕜 := ℂ) x
      ).mdifferentiableAt (by simp)).mfderiv_restrictScalars ℝ) v
  let Lc : ℂ ≃L[ℂ] (Fin 1 → ℂ) := P₀.mfderivToContinuousLinearEquiv (by simp) x
  refine (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).2
    ⟨Lc.restrictScalars' ℝ, ?_, ?_⟩
  · ext v
    exact ((congrFun (Lc.coe_restrictScalars' (R := ℝ)) v).trans
      (DFunLike.congr_fun (P₀.mfderivToContinuousLinearEquiv_coe (by simp)) v)).trans
        (hpt v).symm
  · -- The tangent spaces are `ℂ` and `Fin 1 → ℂ`, so the statement is read on those.
    have key : Orientation.map (Fin 2) (Lc.restrictScalars' ℝ).toLinearEquiv
        (Orientation.reindex ℝ ℂ (finCongr (m := 2) (by simp)) (complexOrientation ℂ)) =
          Orientation.reindex ℝ (Fin 1 → ℂ) (finCongr (by simp))
            (complexOrientation (Fin 1 → ℂ)) := by
      rw [Orientation.map_reindex, ContinuousLinearEquiv.restrictScalars'_toLinearEquiv,
        LinearEquiv.map_complexOrientation, Orientation.reindex_finCongr_reindex_finCongr]
    rw [Manifold.Orientation.orientationAt_reindex,
      orientationAt_complexManifoldOrientation_eq_complexOrientation,
      SymplecticGeometry.orientationAt_projectiveLineOrientation]
    exact key

end OnePoint

namespace SymplecticGeometry

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

/-! ### Inverse stereographic projection from the north pole and the area form of the sphere -/
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
    hd, hd, (OnePoint.hasFDerivAt_coe_diffeomorphSphere_coe northPole equatorIsometry z).fderiv]
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

end SymplecticGeometry

end
