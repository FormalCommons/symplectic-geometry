/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Orientation.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Complex.Orientation
public import TauCeti.Geometry.Manifold.Orientation.AddCircle
public import TauCeti.Geometry.Manifold.Orientation.Euclidean
import SymplecticGeometry.Geometry.Manifold.Instances.AddCircle
import SymplecticGeometry.LinearAlgebra.Complex.Orientation

/-!
# Polar coordinates on `AddCircle p × ℝ` and the orientation of `ℂ`

For a positive period `p`, polar coordinates `(θ, r) ↦ r · toCircle θ` map `AddCircle p × ℝ` to
`ℂ`. Their derivative at `(θ, r)` sends a tangent vector `(a, b)` to
`(2π r a / p · i + b) · toCircle θ` (`AddCircle.mfderiv_ofReal_mul_toCircle_apply`, in
`SymplecticGeometry.Geometry.Manifold.Instances.AddCircle`).

Orient `AddCircle p × ℝ` by the product of Tau Ceti's positive orientation
`AddCircle.orientation p` of the circle and the standard orientation
`TauCeti.Manifold.Orientation.real` of `ℝ`; in it the standard frame `((1, 0), (0, 1))` is positive
(`AddCircle.orientationAt_orientation_prod_real`). Orient `ℂ` by `Complex.orientation`, the
orientation of the basis `(1, i)`. At `(θ, r)` the derivative carries the standard frame to
`(2π r / p · i z, z)` with `z = toCircle θ`, whose determinant in the basis `(1, i)` is
`-2π r / p`. So polar coordinates preserve orientation exactly where `r < 0`
(`AddCircle.isOrientationPreservingAt_ofReal_mul_toCircle_iff`) and reverse it exactly where
`r > 0` (`AddCircle.isOrientationReversingAt_ofReal_mul_toCircle_iff`). The reason is the order of
the factors: the angular direction comes first, and `(i z, z)` is a negative basis of `ℂ`. At
`r = 0` the derivative kills the angular direction, so it is not invertible and the map does
neither.

The identification `z ↦ (re z, im z)` of `ℂ` with `ℝ²` carries `Complex.orientation` to the
standard orientation of `ℝ²` (`Complex.orientation_map_orthonormalBasisOneI_repr`), so, as a map
of manifolds, it preserves orientation at every point
(`Complex.isOrientationPreservingAt_orthonormalBasisOneI_repr`), and so does its inverse
(`Complex.isOrientationPreservingAt_orthonormalBasisOneI_repr_symm`).

`AddCircle.orientationAt_orientation_prod_real` adapts the proof of Tau Ceti's
`AddCircle.orientationAt_orientation_prod_orientation`, in
`TauCeti.Geometry.Manifold.Orientation.AddCircle`, from the torus to `AddCircle p × ℝ`.

## Main results

* `AddCircle.orientationAt_orientation_prod_real`: the product orientation of `AddCircle p × ℝ`
  is that of the standard frame.
* `AddCircle.isOrientationPreservingAt_ofReal_mul_toCircle_iff`: polar coordinates preserve
  orientation at `(θ, r)` exactly when `r < 0`.
* `AddCircle.isOrientationReversingAt_ofReal_mul_toCircle_iff`: polar coordinates reverse
  orientation at `(θ, r)` exactly when `0 < r`.
* `AddCircle.isOrientationReversingAt_ofReal_mul_toCircle`: polar coordinates reverse
  orientation at positive radii.
* `AddCircle.isOrientationPreservingAt_ofReal_mul_toCircle`: polar coordinates preserve
  orientation at negative radii.
* `Complex.isOrientationPreservingAt_orthonormalBasisOneI_repr`: the identification
  `z ↦ (re z, im z)` of `ℂ` with `ℝ²` preserves orientation.
* `Complex.isOrientationPreservingAt_orthonormalBasisOneI_repr_symm`: so does its inverse.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 15 (orientations, orientation-preserving maps).
-/

public section

open Function Complex Real TauCeti TauCeti.Manifold.Orientation
open scoped Manifold

namespace AddCircle

variable {p : ℝ} [hp : Fact (0 < p)]

variable (p) in
/-- At every point of `AddCircle p × ℝ`, whose tangent spaces are read as `ℝ × ℝ`, the product of
the positive orientation of the circle and the standard orientation of `ℝ` is the orientation of
the standard frame `((1, 0), (0, 1))`. -/
theorem orientationAt_orientation_prod_real (x : AddCircle p × ℝ) :
    ((AddCircle.orientation p).prod real).orientationAt x =
      (Module.Basis.finTwoProd ℝ).orientation := by
  rw [Manifold.Orientation.orientationAt_prod, orientationAt_orientation, orientationAt_real]
  exact _root_.Orientation.prod_singleton_orientation

/-- At `(θ, r)` with `r ≠ 0`, the derivative of polar coordinates carries the standard frame of
`AddCircle p × ℝ` to a basis of `ℂ`, which is positive exactly when `r < 0`. -/
private theorem exists_basis_mfderiv_ofReal_mul_toCircle (θ : AddCircle p) {r : ℝ} (hr : r ≠ 0) :
    ∃ b : Module.Basis (Fin 2) ℝ ℂ,
      (∀ i, mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ)
        (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) (θ, r)
          (Module.Basis.finTwoProd ℝ i) = b i) ∧
      (b.orientation = Complex.orientation ↔ r < 0) := by
  have h := isLocalDiffeomorphAt_ofReal_mul_toCircle (n := 1) (θ := θ) hr
  -- The image of the standard frame, as a basis of `ℂ` rather than of its tangent space.
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 2) ℝ ℂ,
      b = (Module.Basis.finTwoProd ℝ).map
        (h.mfderivToContinuousLinearEquiv one_ne_zero).toLinearEquiv := ⟨_, rfl⟩
  have hbi (i : Fin 2) : mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ)
      (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) (θ, r)
        (Module.Basis.finTwoProd ℝ i) = b i := by
    rw [hb]
    exact (DFunLike.congr_fun (h.mfderivToContinuousLinearEquiv_coe one_ne_zero) _).symm
  refine ⟨b, hbi, ?_⟩
  set z : ℂ := (toCircle θ : ℂ)
  set c : ℝ := 2 * π / p * r
  have hz : z.re * z.re + z.im * z.im = 1 := by
    rw [← normSq_apply]
    exact Circle.normSq_coe _
  -- Tangent vectors of `ℂ` are complex numbers: compare them in `ℂ`.
  have h0 : b 0 = (c : ℂ) * I * z := by
    rw [← hbi, Module.Basis.finTwoProd_zero]
    refine Eq.trans (α := ℂ) (mfderiv_ofReal_mul_toCircle_apply θ r 1 0) ?_
    simp [z, c]
  have h1 : b 1 = z := by
    rw [← hbi, Module.Basis.finTwoProd_one]
    refine Eq.trans (α := ℂ) (mfderiv_ofReal_mul_toCircle_apply θ r 0 1) ?_
    simp [z]
  rw [Complex.orientation, eq_comm, Module.Basis.orientation_eq_iff_det_pos,
    Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, coe_basisOneI_repr, Matrix.cons_val_zero,
    Matrix.cons_val_one, h0, h1]
  have hdet : (c * I * z).re * z.im - z.re * (c * I * z).im = -c := by
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    linear_combination (-c) * hz
  have hk : 0 < 2 * π / p := div_pos (by positivity) hp.out
  rw [hdet, neg_pos]
  exact ⟨fun h ↦ neg_of_mul_neg_right h hk.le, fun h ↦ mul_neg_of_pos_of_neg hk h⟩

/-- Polar coordinates `(θ, r) ↦ r · toCircle θ`, from `AddCircle p × ℝ` with the product of the
positive orientation of the circle and the standard orientation of `ℝ` to `ℂ` with its standard
orientation, preserve orientation at `(θ, r)` exactly when `r < 0`. -/
theorem isOrientationPreservingAt_ofReal_mul_toCircle_iff (θ : AddCircle p) (r : ℝ) :
    IsOrientationPreservingAt ((AddCircle.orientation p).prod real)
        Manifold.Orientation.complex
        (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) (θ, r) ↔
      r < 0 := by
  rcases eq_or_ne r 0 with rfl | hr
  · refine iff_of_false (fun h ↦ ?_) (lt_irrefl 0)
    exact not_isInvertible_mfderiv_ofReal_mul_toCircle_zero θ h.isInvertible_mfderiv
  obtain ⟨b, hb, hbo⟩ := exists_basis_mfderiv_ofReal_mul_toCircle θ hr
  refine (isOrientationPreservingAt_iff_of_basis _ b hb).trans
    ((iff_true_left (orientationAt_orientation_prod_real p _).symm).trans ?_)
  rw [orientationAt_complex]
  exact hbo

/-- Polar coordinates `(θ, r) ↦ r · toCircle θ`, from `AddCircle p × ℝ` with the product of the
positive orientation of the circle and the standard orientation of `ℝ` to `ℂ` with its standard
orientation, reverse orientation at `(θ, r)` exactly when `0 < r`. -/
theorem isOrientationReversingAt_ofReal_mul_toCircle_iff (θ : AddCircle p) (r : ℝ) :
    IsOrientationReversingAt ((AddCircle.orientation p).prod real)
        Manifold.Orientation.complex
        (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) (θ, r) ↔
      0 < r := by
  rcases eq_or_ne r 0 with rfl | hr
  · refine iff_of_false (fun h ↦ ?_) (lt_irrefl 0)
    exact not_isInvertible_mfderiv_ofReal_mul_toCircle_zero θ h.isInvertible_mfderiv
  obtain ⟨b, hb, hbo⟩ := exists_basis_mfderiv_ofReal_mul_toCircle θ hr
  refine (isOrientationReversingAt_iff_of_basis _ b hb).trans
    ((iff_true_left (orientationAt_orientation_prod_real p _).symm).trans ?_)
  rw [orientationAt_complex]
  exact (Orientation.ne_iff_eq_neg _ _ (by simp)).symm.trans
    ((not_congr hbo).trans (not_lt.trans hr.symm.le_iff_lt))

/-- **Polar coordinates preserve orientation at negative radii.** For a positive period `p`, the
map `(θ, r) ↦ r · toCircle θ` from `AddCircle p × ℝ`, with the product of the positive
orientation of the circle and the standard orientation of `ℝ`, to `ℂ`, with its standard
orientation, preserves orientation at every point with `r < 0`. -/
theorem isOrientationPreservingAt_ofReal_mul_toCircle (θ : AddCircle p) {r : ℝ} (hr : r < 0) :
    IsOrientationPreservingAt ((AddCircle.orientation p).prod real)
      Manifold.Orientation.complex
      (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) (θ, r) :=
  (isOrientationPreservingAt_ofReal_mul_toCircle_iff θ r).2 hr

/-- **Polar coordinates reverse orientation at positive radii.** For a positive period `p`, the
map `(θ, r) ↦ r · toCircle θ` from `AddCircle p × ℝ`, with the product of the positive
orientation of the circle and the standard orientation of `ℝ`, to `ℂ`, with its standard
orientation, reverses orientation at every point with `r > 0`. -/
theorem isOrientationReversingAt_ofReal_mul_toCircle (θ : AddCircle p) {r : ℝ} (hr : 0 < r) :
    IsOrientationReversingAt ((AddCircle.orientation p).prod real)
      Manifold.Orientation.complex
      (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) (θ, r) :=
  (isOrientationReversingAt_ofReal_mul_toCircle_iff θ r).2 hr

end AddCircle

/-- The identification `z ↦ (re z, im z)` of `ℂ` with `ℝ²` (`Complex.orthonormalBasisOneI.repr`)
preserves orientation at every point, from the standard orientation of `ℂ` to the standard
orientation of `ℝ²`. -/
theorem Complex.isOrientationPreservingAt_orthonormalBasisOneI_repr (z : ℂ) :
    IsOrientationPreservingAt
      Manifold.Orientation.complex
      (Manifold.Orientation.euclideanSpace 2) Complex.orthonormalBasisOneI.repr z := by
  refine (isOrientationPreservingAt_iff_of_coe_eq _ _ _ z
    Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
    (Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.mfderiv_eq (x := z)).symm).2 ?_
  rw [orientationAt_complex, orientationAt_euclideanSpace]
  exact Complex.orientation_map_orthonormalBasisOneI_repr

/-- The inverse identification `(x, y) ↦ x + y i` of `ℝ²` with `ℂ`
(`Complex.orthonormalBasisOneI.repr.symm`)
preserves orientation at every point, from the standard orientation of `ℝ²` to the standard
orientation of `ℂ`. -/
theorem Complex.isOrientationPreservingAt_orthonormalBasisOneI_repr_symm
    (z : EuclideanSpace ℝ (Fin 2)) :
    IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace 2)
      Manifold.Orientation.complex Complex.orthonormalBasisOneI.repr.symm z := by
  refine (isOrientationPreservingAt_iff_of_coe_eq _ _ _ z
    Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv
    (Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.mfderiv_eq (x := z)).symm).2 ?_
  rw [orientationAt_complex, orientationAt_euclideanSpace]
  exact Complex.orientation_map_orthonormalBasisOneI_repr_symm
