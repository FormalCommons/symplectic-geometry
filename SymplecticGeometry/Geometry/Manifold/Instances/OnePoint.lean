/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import SymplecticGeometry.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Manifold.Orientation.TopForm
public import TauCeti.Geometry.Manifold.Projectivization.ProjectiveLine
import SymplecticGeometry.Geometry.Manifold.Algebra.Inv
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.LinearAlgebra.Complex.Finrank
import TauCeti.Analysis.InnerProductSpace.Euclidean.CoordinateHyperplane
import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
import TauCeti.Geometry.Manifold.Instances.OnePoint.Tangent.Basic
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# The Riemann sphere as a real surface

Tau Ceti charts the Riemann sphere `OnePoint ℂ` by its affine coordinate, whose inverse is the
inclusion `ℂ → OnePoint ℂ`, and by the inverted coordinate. This file records how the inclusion
reads for the underlying real surface, modelled on `𝓘(ℝ, ℂ)`, and compares the Riemann sphere with
`ℂP¹` and with the round sphere of `ℝ³`:

* `OnePoint.mvfderiv_coe_apply`: the derivative at a finite point of a map from the sphere to a
  normed space is the derivative of its restriction to `ℂ`, since the derivative of the inclusion
  is the identity (Tau Ceti's `OnePoint.hasMFDerivAt_coe`);
* `OnePoint.contMDiff_equivProjectivization_real` and
  `OnePoint.contMDiff_equivProjectivization_symm_real`: Mathlib's identification
  `OnePoint.equivProjectivization` of `OnePoint ℂ` with `ℙ ℂ (Fin 2 → ℂ)` and its inverse are
  real-analytic;
* `OnePoint.equivProjectivization_apply_coe_eq_affineParam`: under that identification, the
  inclusion is Tau Ceti's affine coordinate `t ↦ [t : 1]` of the projective line;
* `OnePoint.equivProjectivization_symm_mk_of_ne_zero` and
  `OnePoint.equivProjectivization_symm_mk_eq_invChart_symm`: the point `[a : b]` is `a / b` when
  `b ≠ 0`, and the inverse of Tau Ceti's inverted chart `OnePoint.invChart` at `b / a` when
  `a ≠ 0`;
* `OnePoint.contMDiff_equivProjectivization_symm_mk`: for `C^n` complex functions `f` and `g` on
  a real manifold without common zero, `y ↦ [f y : g y]` is a `C^n` map to the sphere;
* `OnePoint.ofTopForm_fubiniStudyForm`: the orientation of Tau Ceti's `OnePoint.fubiniStudyForm`
  is the canonical orientation `SymplecticGeometry.complexCurveOrientation ℂ (OnePoint ℂ)` of the
  Riemann sphere as a complex manifold;
* `OnePoint.isOrientationPreservingAt_equivProjectivization`: the identification with `ℂP¹`
  preserves the canonical orientations `SymplecticGeometry.complexCurveOrientation` of both;
* `OnePoint.coe_homeomorphSphere_infty`, `OnePoint.inner_homeomorphSphere_infty` and
  `OnePoint.sphereCoordsIsometry_symm_orthogonalProjectionOnto`: the north pole
  `homeomorphSphere ∞ = (0, 0, 1)` of Tau Ceti's model of the unit sphere of `ℝ³`, and the
  inverse of Tau Ceti's isometry `sphereCoordsIsometry`, `z ↦ (Re z, -Im z, 0)`, on the
  orthogonal projection onto the plane orthogonal to it;
* `SymplecticGeometry.mpullback_diffeomorphSphere_sphereVolumeForm`: inverse stereographic
  projection `OnePoint.diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry` pulls the
  area form `vol(x, ·, ·)` of the round sphere back to `4π` times `OnePoint.fubiniStudyForm`, and
  `SymplecticGeometry.mpullback_diffeomorphSphere_symm_fubiniStudyForm` states the inverse
  relation. This is Tau Ceti's general `OnePoint.mpullback_diffeomorphSphere_sphereVolumeForm`
  for this choice of `v` and `ι`, for which the frame `(v, ι 1, ι i) = (e₃, e₁, -e₂)` has
  volume `-1`. As a map, this diffeomorphism is Tau Ceti's Pauli model
  `OnePoint.homeomorphSphere` (`OnePoint.diffeomorphSphere_sphereCoordsIsometry_apply`).

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

namespace OnePoint

/-- At a finite point `z`, the derivative of a map `F` from the Riemann sphere to a real normed
space is the derivative of `F` restricted to `ℂ`. -/
theorem mvfderiv_coe_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : OnePoint ℂ → E} {z : ℂ} (hF : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z) (a : ℂ) :
    mvfderiv 𝓘(ℝ, ℂ) F z a = fderiv ℝ (F ∘ (↑)) z a := by
  have h := mvfderiv_comp_apply z hF (hasMFDerivAt_coe z).mdifferentiableAt a
  simp only [(hasMFDerivAt_coe z).mfderiv] at h
  exact h.symm.trans (TauCeti.mvfderiv_eq_fderiv_apply _ z a)

/-- Mathlib's identification of `OnePoint ℂ` with `ℙ ℂ (Fin 2 → ℂ)`, `t ↦ [t : 1]` and
`∞ ↦ [1 : 0]`, is real-analytic for the underlying real surfaces. -/
theorem contMDiff_equivProjectivization_real :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) ω (equivProjectivization ℂ) :=
  (contMDiff_equivProjectivization (𝕜 := ℂ)).restrictScalars' ℝ

/-- The inverse of Mathlib's identification of `OnePoint ℂ` with `ℙ ℂ (Fin 2 → ℂ)` is
real-analytic for the underlying real surfaces. -/
theorem contMDiff_equivProjectivization_symm_real :
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, ℂ) ω (equivProjectivization ℂ).symm :=
  (contMDiff_equivProjectivization_symm (𝕜 := ℂ)).restrictScalars' ℝ

/-- Mathlib's identification of `OnePoint ℂ` with `ℙ ℂ (Fin 2 → ℂ)` sends a finite point `t` to
`[t : 1]`, the value at `t` of Tau Ceti's affine coordinate at the coordinate `1`. -/
theorem equivProjectivization_apply_coe_eq_affineParam (t : ℂ) :
    equivProjectivization ℂ t = TauCeti.ProjectiveLine.affineParam 1 t := by
  rw [equivProjectivization_apply_coe, TauCeti.ProjectiveLine.affineParam_eq]
  congr 1
  ext k
  fin_cases k <;> simp

/-- Under Mathlib's identification of `OnePoint K` with `ℙ K (Fin 2 → K)`, the point `[a : b]`
with `b ≠ 0` is the finite point `a / b`. -/
theorem equivProjectivization_symm_mk_of_ne_zero {K : Type*} [Field K] [DecidableEq K]
    {a b : K} (h : ![a, b] ≠ 0) (hb : b ≠ 0) :
    (equivProjectivization K).symm (Projectivization.mk K ![a, b] h) =
      ((a / b : K) : OnePoint K) := by
  simp [hb, div_eq_inv_mul]

/-- Under Mathlib's identification of `OnePoint K` with `ℙ K (Fin 2 → K)`, the point `[a : b]`
with `a ≠ 0` is the value at `b / a` of the inverse of Tau Ceti's inverted chart
`OnePoint.invChart`. -/
theorem equivProjectivization_symm_mk_eq_invChart_symm {K : Type*} [NontriviallyNormedField K]
    [ProperSpace K] [DecidableEq K] {a b : K} (h : ![a, b] ≠ 0) (ha : a ≠ 0) :
    (equivProjectivization K).symm (Projectivization.mk K ![a, b] h) = invChart.symm (b / a) := by
  by_cases hb : b = 0
  · simp [hb]
  · simp [ha, hb, div_eq_inv_mul]

/-- For `C^n` complex functions `f` and `g` on a real manifold, without common zero, the map
`y ↦ [f y : g y]` to the Riemann sphere, read through `OnePoint.equivProjectivization`, is
`C^n`. -/
theorem contMDiff_equivProjectivization_symm_mk {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {n : ℕ∞ω} {f g : M → ℂ} (hf : ContMDiff I 𝓘(ℝ, ℂ) n f)
    (hg : ContMDiff I 𝓘(ℝ, ℂ) n g) (h : ∀ y, ![f y, g y] ≠ 0) :
    ContMDiff I 𝓘(ℝ, ℂ) n
      (fun y ↦ (equivProjectivization ℂ).symm (Projectivization.mk ℂ ![f y, g y] (h y))) := by
  intro x
  by_cases hx : g x = 0
  · -- Near `x`, where `f` does not vanish, the map reads through the inverted chart.
    have hfx : f x ≠ 0 := fun h' ↦ h x (by simp [h', hx])
    refine (contMDiff_invChart_symm_real.contMDiffAt.comp x
      ((hg x).div₀ (hf x) hfx)).congr_of_eventuallyEq ?_
    filter_upwards [(hf x).continuousAt.eventually_ne hfx] with y hy
    exact equivProjectivization_symm_mk_eq_invChart_symm (h y) hy
  · -- Near `x`, where `g` does not vanish, the map reads through the inclusion of `ℂ`.
    refine (contMDiff_coe_real.contMDiffAt.comp x
      ((hf x).div₀ (hg x) hx)).congr_of_eventuallyEq ?_
    filter_upwards [(hg x).continuousAt.eventually_ne hx] with y hy
    exact equivProjectivization_symm_mk_of_ne_zero (h y) hy

/-! ### Orientations -/

/-- The orientation of the Riemann sphere defined by its Fubini–Study form is its canonical
orientation as a complex manifold. -/
theorem ofTopForm_fubiniStudyForm :
    Manifold.Orientation.ofTopForm Complex.finrank_real_complex fubiniStudyForm.val
        (fubiniStudyForm.isSmoothForm.of_le zero_le) fubiniStudyForm_apply_ne_zero =
      SymplecticGeometry.complexCurveOrientation ℂ (OnePoint ℂ) := by
  ext x
  rw [SymplecticGeometry.complexCurveOrientation_def,
    orientationAt_reindex_complexManifoldOrientation_complex]
  refine ((Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff
    Complex.finrank_real_complex (fubiniStudyForm.isSmoothForm.of_le zero_le)
    fubiniStudyForm_apply_ne_zero (x := x) Complex.basisOneI).2 ?_).symm
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
      (SymplecticGeometry.complexCurveOrientation ℂ (OnePoint ℂ))
      (SymplecticGeometry.complexCurveOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)))
      (equivProjectivization ℂ) x := by
  set P₀ := diffeomorphProjectivization ℂ ω
  -- The real derivative is the complex one, the casts between tangent spaces being identities.
  have hpt (v : ℂ) : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) (equivProjectivization ℂ) x v =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → ℂ) P₀ x v := by
    rw [coe_diffeomorphProjectivization]
    exact (contMDiff_equivProjectivization (𝕜 := ℂ) x).mdifferentiableAt (by simp)
      |>.mfderiv_modelWithCornersSelf_restrictScalars_apply ℝ v
  let Lc : ℂ ≃L[ℂ] (Fin 1 → ℂ) := P₀.mfderivToContinuousLinearEquiv (by simp) x
  refine (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).2
    ⟨Lc.restrictScalars' ℝ, ?_, ?_⟩
  · ext v
    exact ((congrFun (Lc.coe_restrictScalars' (R := ℝ)) v).trans
      (DFunLike.congr_fun (P₀.mfderivToContinuousLinearEquiv_coe (by simp)) v)).trans
        (hpt v).symm
  · -- The tangent spaces are `ℂ` and `Fin 1 → ℂ`, so the statement is read on those.
    have key : Orientation.map (Fin 2) (Lc.restrictScalars' ℝ).toLinearEquiv
        (Orientation.reindex ℝ ℂ (finCongr Complex.two_mul_finrank_self) (complexOrientation ℂ)) =
          Orientation.reindex ℝ (Fin 1 → ℂ) (finCongr (by simp))
            (complexOrientation (Fin 1 → ℂ)) := by
      rw [Orientation.map_reindex, ContinuousLinearEquiv.restrictScalars'_toLinearEquiv,
        LinearEquiv.map_complexOrientation, Orientation.reindex_finCongr_reindex_finCongr]
    rw [SymplecticGeometry.orientationAt_complexCurveOrientation,
      SymplecticGeometry.orientationAt_complexCurveOrientation]
    exact key

end OnePoint

namespace OnePoint

/-! ### The north pole and the plane orthogonal to it -/

/-- The north pole `homeomorphSphere ∞` of the unit sphere of `ℝ³` is the third standard basis
vector `(0, 0, 1)`. -/
theorem coe_homeomorphSphere_infty :
    (homeomorphSphere ∞ : ℝ³) = EuclideanSpace.single 2 1 := by
  rw [coe_homeomorphSphere, sphereCoords_infty]
  ext i
  fin_cases i <;> simp

/-- The Pauli model `homeomorphSphere` sends `0` to the south pole, the antipode of the north pole
`homeomorphSphere ∞`. -/
@[simp]
theorem homeomorphSphere_zero : homeomorphSphere (0 : ℂ) = -homeomorphSphere ∞ := by
  rw [← diffeomorphSphere_sphereCoordsIsometry_apply, diffeomorphSphere_zero]

/-- The inner product with the north pole `homeomorphSphere ∞` is the third coordinate. -/
theorem inner_homeomorphSphere_infty (p : ℝ³) :
    inner ℝ (homeomorphSphere ∞ : ℝ³) p = p 2 := by
  rw [coe_homeomorphSphere_infty, EuclideanSpace.inner_single_left]
  simp

/-- The inverse of `sphereCoordsIsometry` reads the orthogonal projection of `p` onto the plane
orthogonal to the north pole as `p 0 - i p 1`. -/
theorem sphereCoordsIsometry_symm_orthogonalProjectionOnto (p : ℝ³) :
    sphereCoordsIsometry.symm ((ℝ ∙ (homeomorphSphere ∞ : ℝ³))ᗮ.orthogonalProjectionOnto p) =
      ⟨p 0, -p 1⟩ := by
  have h := TauCeti.coe_orthogonalProjectionOnto_single_one_apply (2 : Fin 3) p
  rw [← coe_homeomorphSphere_infty] at h
  rw [sphereCoordsIsometry_symm_apply, h]
  simp

/-- Off the north pole, the third coordinate of a point of the unit sphere is not `1`. -/
theorem one_sub_ne_zero_of_ne_homeomorphSphere_infty {p : sphere (0 : ℝ³) 1}
    (hp : p ≠ homeomorphSphere ∞) : 1 - (p : ℝ³) 2 ≠ 0 := by
  rw [sub_ne_zero, ← inner_homeomorphSphere_infty]
  intro h
  exact hp (Subtype.ext ((inner_eq_one_iff_of_norm_eq_one (norm_eq_of_mem_sphere _)
    (norm_eq_of_mem_sphere p)).1 h.symm).symm)

/-- Off the south pole, the third coordinate of a point of the unit sphere is not `-1`. -/
theorem one_add_ne_zero_of_ne_neg_homeomorphSphere_infty {p : sphere (0 : ℝ³) 1}
    (hp : p ≠ -homeomorphSphere ∞) : 1 + (p : ℝ³) 2 ≠ 0 := by
  have h := one_sub_ne_zero_of_ne_homeomorphSphere_infty (p := -p)
    fun h ↦ hp (by rw [← h, neg_neg])
  rwa [coe_neg_sphere, PiLp.neg_apply, sub_neg_eq_add] at h

end OnePoint

namespace SymplecticGeometry

open OnePoint (diffeomorphSphere homeomorphSphere sphereCoordsIsometry fubiniStudyForm)
open scoped OnePoint

/-! ### Inverse stereographic projection from the north pole and the area form of the sphere -/
/-- **The round sphere is `4π` times the Fubini–Study sphere, as an area form.** Inverse
stereographic projection `diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry` from the
north pole pulls the outward-normal area form `vol(x, ·, ·)` of the unit sphere of `ℝ³` back to
`4π` times the Fubini–Study form `OnePoint.fubiniStudyForm` of the Riemann sphere. As a map, this
diffeomorphism is the Pauli model `homeomorphSphere`
(`OnePoint.diffeomorphSphere_sphereCoordsIsometry_apply`). -/
theorem mpullback_diffeomorphSphere_sphereVolumeForm :
    SmoothForm.mpullback (diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry)
        ((diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry).contMDiff.of_le le_top)
        (Orientation.sphereVolumeForm o₃) =
      (4 * Real.pi) • fubiniStudyForm := by
  -- The frame `(v, ι 1, ι i) = (e₃, e₁, -e₂)` of Tau Ceti's general comparison is negative.
  have hvol : Orientation.volumeForm o₃ ![(homeomorphSphere ∞ : ℝ³),
      (sphereCoordsIsometry 1 : ℝ³), (sphereCoordsIsometry Complex.I : ℝ³)] = -1 := by
    rw [Orientation.volumeForm_robust _ (EuclideanSpace.basisFun (Fin 3) ℝ) rfl,
      Module.Basis.det_apply, Matrix.det_fin_three]
    simp [Module.Basis.toMatrix_apply]
  rw [SmoothForm.mpullback_eq_iff,
    OnePoint.mpullback_diffeomorphSphere_sphereVolumeForm _ sphereCoordsIsometry o₃, hvol,
    SetLike.val_smul, mul_neg_one, neg_neg]

/-- Stereographic projection from the north pole, the inverse of
`diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry`, pulls the Fubini–Study form of the
Riemann sphere back to `(4π)⁻¹` times the area form of the unit sphere of `ℝ³`. As a map, this
inverse is `homeomorphSphere.symm`, the inverse of the Pauli model
(`OnePoint.diffeomorphSphere_sphereCoordsIsometry_symm_apply`). -/
theorem mpullback_diffeomorphSphere_symm_fubiniStudyForm :
    SmoothForm.mpullback (diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry).symm
        ((diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry).symm.contMDiff.of_le le_top)
        fubiniStudyForm =
      (4 * Real.pi)⁻¹ • Orientation.sphereVolumeForm o₃ := by
  have hid : ⇑(diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry) ∘
      ⇑(diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry).symm = id :=
    funext (diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry).apply_symm_apply
  have h₄ : (4 * Real.pi)⁻¹ • (4 * Real.pi) • fubiniStudyForm = fubiniStudyForm := by
    rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  rw [← h₄, map_smul, ← mpullback_diffeomorphSphere_sphereVolumeForm,
    SmoothForm.mpullback_mpullback]
  rw [SmoothForm.mpullback_eq_self_of_eq_id _ hid]

end SymplecticGeometry

end
