/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.CoordinateDisc
public import SymplecticGeometry.Topology.Homotopy.CubeToSphere
import TauCeti.Geometry.Sphere.Connected

/-!
# The orientation of the sphere from the collapsed square

Tau Ceti's collapse `TauCeti.cubeToSphere 2 : I^2 → S²`, read on the open square of `ℂ`, is an
open embedding `SymplecticGeometry.openSquareToSphere` (in
`SymplecticGeometry.Topology.Homotopy.CubeToSphere`). This file orients `S²`, charted on
`EuclideanSpace ℝ (Fin 2)` as Mathlib does, so that this open embedding preserves orientation.

The open square is connected, so the open embedding carries the canonical orientation
`TauCeti.complexHomologicalOrientation` of the open square to any given orientation of `S²` or to
its opposite at every point
(`TauCeti.HomologicalOrientation.forall_localOrientationEquiv_eq_or_forall_eq_neg`). Starting from
the outward-normal orientation of Tau Ceti (`Orientation.sphereOrientation`), this gives the
orientation `SymplecticGeometry.cubeToSphereOrientation`. Since `S²` is connected, an orientation
is determined by its local orientation at one point
(`TauCeti.HomologicalOrientation.eq_of_apply_eq`),
so it is the only orientation for which the collapse preserves orientation, even at a single point
of the open square.

The map `z ↦ (1 + i) / 2 + z / 5` sends the ball of radius `2` of `ℂ` into the open square and is
holomorphic, so composing it with the collapse gives a coordinate disc
`SymplecticGeometry.CoordinateDisc.cubeToSphere` of `S²` for this orientation. In the coordinates
of the square its closed disc is the image of the points `y` with
`(y₀ - 1/2)² + (y₁ - 1/2)² ≤ 1/25`, and its open disc that of the points where the inequality is
strict.

## Main definitions

* `SymplecticGeometry.cubeToSphereOrientation`: the orientation of `S²` for which the collapse of
  the square preserves orientation on the open square.
* `SymplecticGeometry.ballToOpenSquare`: the map `z ↦ (1 + i) / 2 + z / 5` of the ball of radius
  `2` into the open square.
* `SymplecticGeometry.CoordinateDisc.cubeToSphere`: the coordinate disc
  `z ↦ cubeToSphere 2 (1/2 + re z / 5, 1/2 + im z / 5)` of `S²`.

## Main results

* `SymplecticGeometry.localOrientationEquiv_openSquareToSphere`: the collapse carries the
  canonical orientation of the open square to `cubeToSphereOrientation`.
* `SymplecticGeometry.eq_cubeToSphereOrientation` and
  `SymplecticGeometry.existsUnique_forall_localOrientationEquiv_openSquareToSphere_eq`: it is the
  only such orientation.
* `SymplecticGeometry.CoordinateDisc.cubeToSphere_apply`: the formula of the coordinate disc.
* `SymplecticGeometry.CoordinateDisc.disc_cubeToSphere`,
  `SymplecticGeometry.CoordinateDisc.openDisc_cubeToSphere`: its closed and open discs in the
  coordinates of the square.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  where the first Chern number of a bundle over a surface is computed from trivializations over a
  disc and over its complement.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (local orientations and orientations).
-/

public section

noncomputable section

open Metric Module Topology TauCeti Complex
open scoped unitInterval

namespace SymplecticGeometry

local instance : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

local instance : ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  connectedSpace_euclideanSphere (by norm_num)

/-! ### The orientation -/

/-- The outward-normal orientation of `S²`, for the standard orientation of `ℝ³`, as a homological
orientation. -/
private def sphereHomologicalOrientation :
    HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (EuclideanSpace ℝ (Fin 2)) 2 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation.toHomologicalOrientation
    (n := 1) finrank_euclideanSpace_fin

open Classical in
/-- **The orientation of `S²` from the collapsed square.** The homological orientation of the unit
sphere `S²` of `ℝ³`, charted on `ℝ²`, for which the collapse of the square
`TauCeti.cubeToSphere 2`, read on the open square of `ℂ`, carries the canonical orientation of the
open square to the orientation of `S²` at every point
(`SymplecticGeometry.localOrientationEquiv_openSquareToSphere`). -/
def cubeToSphereOrientation :
    HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (EuclideanSpace ℝ (Fin 2)) 2 :=
  if ∀ z, isOpenEmbedding_openSquareToSphere.localOrientationEquiv z 2
      (complexHomologicalOrientation openSquare z) =
        sphereHomologicalOrientation (openSquareToSphere z) then
    sphereHomologicalOrientation
  else -sphereHomologicalOrientation

/-- The collapse of the square, read on the open square of `ℂ`, carries the canonical orientation
of the open square to `cubeToSphereOrientation` at every point. -/
theorem localOrientationEquiv_openSquareToSphere (z : openSquare) :
    isOpenEmbedding_openSquareToSphere.localOrientationEquiv z 2
      (complexHomologicalOrientation openSquare z) =
        cubeToSphereOrientation (openSquareToSphere z) := by
  rw [cubeToSphereOrientation]
  split_ifs with h
  · exact h z
  · exact ((sphereHomologicalOrientation.forall_localOrientationEquiv_eq_or_forall_eq_neg
      finrank_euclideanSpace_fin isOpenEmbedding_openSquareToSphere).resolve_left h) z

/-- **Uniqueness of the orientation from the collapsed square.** An orientation of `S²` for which
the collapse of the square carries the canonical orientation of the open square to it at a single
point of the open square is `cubeToSphereOrientation`. -/
theorem eq_cubeToSphereOrientation
    {o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (EuclideanSpace ℝ (Fin 2)) 2} {z : openSquare}
    (h : isOpenEmbedding_openSquareToSphere.localOrientationEquiv z 2
      (complexHomologicalOrientation openSquare z) = o (openSquareToSphere z)) :
    o = cubeToSphereOrientation :=
  HomologicalOrientation.eq_of_apply_eq (h.symm.trans (localOrientationEquiv_openSquareToSphere z))

/-- `cubeToSphereOrientation` is the unique orientation of `S²` for which the collapse of the square
carries the canonical orientation of the open square to it at every point. -/
theorem existsUnique_forall_localOrientationEquiv_openSquareToSphere_eq :
    ∃! o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        (EuclideanSpace ℝ (Fin 2)) 2,
      ∀ z, isOpenEmbedding_openSquareToSphere.localOrientationEquiv z 2
        (complexHomologicalOrientation openSquare z) = o (openSquareToSphere z) :=
  ⟨cubeToSphereOrientation, localOrientationEquiv_openSquareToSphere,
    fun _ h ↦ eq_cubeToSphereOrientation (h ⟨(1 + Complex.I) / 2, by norm_num⟩)⟩

/-! ### A coordinate disc in the open square -/

/-- A point at distance less than `2 / 5` from the centre `(1 + i) / 2` lies in the open square. -/
private theorem add_div_five_mem_openSquare {z : ℂ} (hz : ‖z‖ < 2) :
    ((1 + Complex.I) / 2 + z / 5) ∈ openSquare := by
  have hre := abs_le.1 ((abs_re_le_norm z).trans hz.le)
  have him := abs_le.1 ((abs_im_le_norm z).trans hz.le)
  simp only [mem_openSquare_iff, add_re, add_im, div_re, div_im, one_re, one_im, Complex.I_re,
    Complex.I_im]
  norm_num
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- The map `z ↦ (1 + i) / 2 + z / 5` of the ball of radius `2` of `ℂ` into the open square. -/
def ballToOpenSquare (z : CoordinateDisc.ball) : openSquare :=
  ⟨(1 + Complex.I) / 2 + z / 5, add_div_five_mem_openSquare (CoordinateDisc.mem_ball_iff.1 z.prop)⟩

@[simp]
theorem coe_ballToOpenSquare_apply (z : CoordinateDisc.ball) :
    (ballToOpenSquare z : ℂ) = (1 + Complex.I) / 2 + z / 5 :=
  (rfl)

private theorem subtypeVal_comp_ballToOpenSquare :
    Subtype.val ∘ ballToOpenSquare =
      Diffeomorph.smulAdd 1 (5⁻¹ : ℂ) ((1 + Complex.I) / 2) (by norm_num) ∘ Subtype.val := by
  ext z
  simp [div_eq_inv_mul, add_comm]

theorem isOpenEmbedding_ballToOpenSquare : IsOpenEmbedding ballToOpenSquare :=
  (IsOpenEmbedding.of_comp_iff _ openSquare.isOpenEmbedding').1 <| by
    rw [subtypeVal_comp_ballToOpenSquare]
    exact (Diffeomorph.smulAdd 1 (5⁻¹ : ℂ) ((1 + Complex.I) / 2)
      (by norm_num)).toHomeomorph.isOpenEmbedding.comp CoordinateDisc.ball.isOpenEmbedding'

/-- The map `z ↦ (1 + i) / 2 + z / 5` pulls the canonical orientation of the open square back to
that of the ball. -/
theorem comap_ballToOpenSquare_complexHomologicalOrientation :
    (complexHomologicalOrientation openSquare).comap isOpenEmbedding_ballToOpenSquare =
      complexHomologicalOrientation CoordinateDisc.ball :=
  let T := Diffeomorph.smulAdd 1 (5⁻¹ : ℂ) ((1 + Complex.I) / 2) (by norm_num)
  comap_complexHomologicalOrientation_of_comp_eq _ T.toHomeomorph.isOpenEmbedding
    T.isLocalDiffeomorph subtypeVal_comp_ballToOpenSquare

namespace CoordinateDisc

/-- The coordinate disc `z ↦ cubeToSphere 2 (1/2 + re z / 5, 1/2 + im z / 5)` of `S²`, for the
orientation `cubeToSphereOrientation` from the collapsed square. -/
def cubeToSphere : CoordinateDisc cubeToSphereOrientation where
  toFun z := openSquareToSphere (ballToOpenSquare z)
  isOpenEmbedding' := isOpenEmbedding_openSquareToSphere.comp isOpenEmbedding_ballToOpenSquare
  localOrientationEquiv_apply' z := by
    have h := HomologicalOrientation.localOrientationEquiv_comap_apply
      (complexHomologicalOrientation openSquare) isOpenEmbedding_ballToOpenSquare z
    rw [comap_ballToOpenSquare_complexHomologicalOrientation] at h
    rw [← IsOpenEmbedding.localOrientationEquiv_trans isOpenEmbedding_ballToOpenSquare
      isOpenEmbedding_openSquareToSphere, Equiv.trans_apply, h,
      localOrientationEquiv_openSquareToSphere]

theorem cubeToSphere_apply_eq (z : ball) :
    cubeToSphere z = openSquareToSphere (ballToOpenSquare z) :=
  (rfl)

/-- The coordinate disc `cubeToSphere` sends `z` to the image under the collapse of the point `y`
of the square with coordinates `1/2 + re z / 5` and `1/2 + im z / 5`. -/
theorem cubeToSphere_apply (z : ball) {y : I^(Fin 2)} (h₀ : (y 0 : ℝ) = 1 / 2 + (z : ℂ).re / 5)
    (h₁ : (y 1 : ℝ) = 1 / 2 + (z : ℂ).im / 5) :
    cubeToSphere z = TauCeti.cubeToSphere 2 y := by
  rw [cubeToSphere_apply_eq, openSquareToSphere_def]
  congr 1
  ext i
  fin_cases i
  · simp [h₀]
  · simp [h₁]

/-- The images under `cubeToSphere` of the points of the ball cut out by a condition `p` on the
squared norm are the images under the collapse of the points of the square cut out by the same
condition on `25` times the squared distance to the centre `(1/2, 1/2)`. -/
private theorem image_cubeToSphere_eq {p : ℝ → Prop} (hp : ∀ t, p t → t < 4) :
    cubeToSphere '' {z | p (‖(z : ℂ)‖ ^ 2)} =
      TauCeti.cubeToSphere 2 ''
        {y | p (25 * (((y 0 : ℝ) - 1 / 2) ^ 2 + ((y 1 : ℝ) - 1 / 2) ^ 2))} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨openSquareHomeomorph (ballToOpenSquare z), ?_,
      ((cubeToSphere_apply_eq z).trans (openSquareToSphere_def _)).symm⟩
    simp only [Set.mem_ofPred_eq, coe_openSquareHomeomorph_apply_zero,
      coe_openSquareHomeomorph_apply_one, coe_ballToOpenSquare_apply]
    convert hz using 2
    rw [Set.mem_ofPred_eq, Complex.sq_norm, Complex.normSq_apply]
    simp only [add_re, div_ofNat_re, one_re, Complex.I_re, add_zero, one_div, add_sub_cancel_left,
      add_im, div_ofNat_im, one_im, Complex.I_im, zero_add]
    congr! 1
    ring
  · rintro ⟨y, hy, rfl⟩
    let z : ℂ := ⟨5 * ((y 0 : ℝ) - 1 / 2), 5 * ((y 1 : ℝ) - 1 / 2)⟩
    have hz : ‖z‖ ^ 2 = 25 * (((y 0 : ℝ) - 1 / 2) ^ 2 + ((y 1 : ℝ) - 1 / 2) ^ 2) := by
      rw [Complex.sq_norm, Complex.normSq_mk]
      ring
    have hz2 : ‖z‖ < 2 := by
      have := hp _ hy
      nlinarith [norm_nonneg z]
    refine ⟨⟨z, mem_ball_iff.2 hz2⟩, by simpa [hz] using hy, cubeToSphere_apply _ ?_ ?_⟩ <;>
      simp [z]

/-- The closed disc of `cubeToSphere`, in the coordinates of the square: the image under the
collapse of the points at distance at most `1/5` from the centre `(1/2, 1/2)`. -/
theorem disc_cubeToSphere :
    cubeToSphere.disc =
      TauCeti.cubeToSphere 2 ''
        {y | ((y 0 : ℝ) - 1 / 2) ^ 2 + ((y 1 : ℝ) - 1 / 2) ^ 2 ≤ 1 / 25} := by
  have h := image_cubeToSphere_eq (p := (· ≤ 1)) fun t (ht : t ≤ 1) ↦ by linarith
  simp only [pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at h
  rw [disc_def, h]
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- The open disc of `cubeToSphere`, in the coordinates of the square: the image under the
collapse of the points at distance less than `1/5` from the centre `(1/2, 1/2)`. -/
theorem openDisc_cubeToSphere :
    cubeToSphere.openDisc =
      TauCeti.cubeToSphere 2 ''
        {y | ((y 0 : ℝ) - 1 / 2) ^ 2 + ((y 1 : ℝ) - 1 / 2) ^ 2 < 1 / 25} := by
  have h := image_cubeToSphere_eq (p := (· < 1)) fun t (ht : t < 1) ↦ by linarith
  simp only [pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at h
  rw [openDisc_def, h]
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

end CoordinateDisc

end SymplecticGeometry

end
