/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Complex.Orientation
public import TauCeti.Geometry.Manifold.Orientation.AddCircle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import SymplecticGeometry.Geometry.Manifold.Instances.AddCircle
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod

/-!
# Polar coordinates on `AddCircle p × ℝ` and the orientation of `ℂ`

For a positive period `p`, polar coordinates `(θ, r) ↦ r · toCircle θ` map `AddCircle p × ℝ` to
`ℂ`. Their derivative at `(θ, r)` sends a tangent vector `(a, b)` to
`(2π r a / p · i + b) · toCircle θ` (`AddCircle.mfderiv_ofReal_mul_toCircle_apply`).

Orient `AddCircle p × ℝ` by the product of Tau Ceti's positive orientation
`AddCircle.orientation p` of the circle and the standard orientation
`TauCeti.Manifold.Orientation.real` of `ℝ`; in it the standard frame `((1, 0), (0, 1))` is positive
(`AddCircle.orientationAt_orientation_prod_real`). Orient `ℂ` by `Complex.orientation`, the
orientation of the basis `(1, i)`. At `(θ, r)` the derivative carries the standard frame to
`(2π r / p · i z, z)` with `z = toCircle θ`, whose determinant in the basis `(1, i)` is
`-2π r / p`. So, away from `r = 0`, polar coordinates preserve orientation exactly where `r < 0`
(`AddCircle.isOrientationPreservingAt_ofReal_mul_toCircle_iff`): they reverse it where `r > 0`
(`AddCircle.isOrientationReversingAt_ofReal_mul_toCircle`) and preserve it where `r < 0`
(`AddCircle.isOrientationPreservingAt_ofReal_mul_toCircle`). The reason is the order of the
factors: the angular direction comes first, and `(i z, z)` is a negative basis of `ℂ`. At `r = 0`
the derivative is not invertible.

## Main results

* `AddCircle.mfderiv_ofReal_mul_toCircle_apply`: the derivative of polar coordinates.
* `AddCircle.orientationAt_orientation_prod_real`: the product orientation of `AddCircle p × ℝ`
  is that of the standard frame.
* `AddCircle.isOrientationPreservingAt_ofReal_mul_toCircle_iff`: for `r ≠ 0`, polar coordinates
  preserve orientation at `(θ, r)` exactly when `r < 0`.
* `AddCircle.isOrientationReversingAt_ofReal_mul_toCircle`: polar coordinates reverse
  orientation at positive radii.
* `AddCircle.isOrientationPreservingAt_ofReal_mul_toCircle`: polar coordinates preserve
  orientation at negative radii.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 15 (orientations, orientation-preserving maps).
-/

public section

open Function Complex Real TauCeti TauCeti.Manifold.Orientation
open scoped Manifold

namespace AddCircle

variable {p : ℝ} [hp : Fact (0 < p)]

/-- **The derivative of polar coordinates.** At `(θ, r)`, the derivative of
`(θ, r) ↦ r · toCircle θ` sends `(a, b)` to `(2π r a / p · i + b) · toCircle θ`. -/
theorem mfderiv_ofReal_mul_toCircle_apply (θ : AddCircle p) (r a b : ℝ) :
    mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ))
        (θ, r) (a, b) =
      (((2 * π / p * r * a : ℝ) : ℂ) * I + (b : ℂ)) * (toCircle θ : ℂ) := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have hz : (toCircle (u : AddCircle p) : ℂ) = exp ((2 * π / p * u : ℝ) * I) := by
    rw [toCircle_apply_mk, Circle.coe_exp]
  -- The angular slice, lifted to `ℝ`, is `t ↦ r · exp (2π t / p · i)`.
  have hθ : HasDerivAt (fun t : ℝ ↦ (r : ℂ) * exp ((2 * π / p * t : ℝ) * I))
      ((r : ℂ) * (exp ((2 * π / p * u : ℝ) * I) * ((2 * π / p : ℝ) * I))) u := by
    have h := (((hasDerivAt_id u).const_mul (2 * π / p)).ofReal_comp.mul_const I).cexp
    simp only [mul_one, id] at h
    exact h.const_mul (r : ℂ)
  -- The radial slice is `s ↦ s · z`.
  have hr : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * (toCircle (u : AddCircle p) : ℂ))
      (toCircle (u : AddCircle p) : ℂ) r := by
    simpa using (hasDerivAt_id r).ofReal_comp.mul_const (toCircle (u : AddCircle p) : ℂ)
  have hf : MDifferentiableAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ)
      (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) ((u : AddCircle p), r) := by
    refine ((isLocalDiffeomorph_prodMap_coe_id p 1 (u, r)).mdifferentiableAt_comp_iff
      one_ne_zero).1 ?_
    have hκ : (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) ∘
        Prod.map ((↑) : ℝ → AddCircle p) id =
        fun q : ℝ × ℝ ↦ (q.2 : ℂ) * exp ((2 * π / p * q.1 : ℝ) * I) :=
      funext fun q ↦ by simp [toCircle_apply_mk, Circle.coe_exp]
    rw [hκ]
    refine (ContDiff.contMDiff (n := 1) ?_).mdifferentiableAt one_ne_zero
    exact (ofRealCLM.contDiff.comp contDiff_snd).mul
      ((ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)).mul contDiff_const).cexp
  have h1 := hf.mfderiv_curry_left_apply a
  have h2 := hf.mfderiv_curry_right_apply b
  have hadd := map_add (mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ)
    (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) ((u : AddCircle p), r))
    ((a, 0) : ℝ × ℝ) (0, b)
  have hθ' : (fun z : AddCircle p ↦ (r : ℂ) * (toCircle z : ℂ)) ∘ ((↑) : ℝ → AddCircle p) =
      fun t : ℝ ↦ (r : ℂ) * exp ((2 * π / p * t : ℝ) * I) :=
    funext fun t ↦ by simp [toCircle_apply_mk, Circle.coe_exp]
  simp only [Prod.mk_add_mk, add_zero, zero_add] at hadd
  -- The two slices, read in `ℂ`; tangent vectors of `ℝ` and `AddCircle p` are real numbers.
  have e1 : mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (fun z : AddCircle p ↦ (r : ℂ) * (toCircle z : ℂ))
      (u : AddCircle p) a =
        a • ((r : ℂ) * (Complex.exp ((2 * π / p * u : ℝ) * I) * (((2 * π / p : ℝ) : ℂ) * I))) := by
    rw [← mfderiv_comp_coe, hθ', (hasMFDerivAt_iff_hasFDerivAt.2 hθ.hasFDerivAt).mfderiv]
    -- The tangent space of `ℂ` is `ℂ` itself, so the derivative applies as a map into `ℂ`.
    exact ContinuousLinearMap.toSpanSingleton_apply (R₁ := ℝ) (M₁ := ℂ) _ a
  have e2 : mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (fun s : ℝ ↦ (s : ℂ) * (toCircle (u : AddCircle p) : ℂ)) r b =
      b • (toCircle (u : AddCircle p) : ℂ) := by
    rw [(hasMFDerivAt_iff_hasFDerivAt.2 hr.hasFDerivAt).mfderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply (R₁ := ℝ) (M₁ := ℂ) _ b
  refine hadd.trans ((congrArg₂ (fun x y : ℂ ↦ x + y) (h1.trans e1) (h2.trans e2)).trans ?_)
  rw [hz, real_smul, real_smul]
  push_cast
  ring

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
  set z : ℂ := (toCircle θ : ℂ)
  set c : ℝ := 2 * π / p * r
  have hc : c ≠ 0 := mul_ne_zero (div_ne_zero (by positivity) hp.out.ne') hr
  have hz : z.re * z.re + z.im * z.im = 1 := by
    rw [← normSq_apply]
    exact Circle.normSq_coe _
  have hz0 : z ≠ 0 := Circle.coe_ne_zero _
  have hli : LinearIndependent ℝ ![(c : ℂ) * I * z, z] := by
    refine LinearIndependent.pair_iff.2 fun s t hst ↦ ?_
    have h : ((s * c : ℝ) * I + t) * z = 0 := by
      rw [← hst]
      simp only [real_smul]
      push_cast
      ring
    have h' := (mul_eq_zero.1 h).resolve_right hz0
    have ht : t = 0 := by simpa using congrArg Complex.re h'
    have hs : s * c = 0 := by simpa using congrArg Complex.im h'
    exact ⟨(mul_eq_zero.1 hs).resolve_right hc, ht⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp), ?_, ?_⟩
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩ <;>
      simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Module.Basis.finTwoProd_zero,
        Module.Basis.finTwoProd_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    -- Tangent vectors of `ℂ` are complex numbers: compare them in `ℂ`.
    · refine Eq.trans (α := ℂ) (mfderiv_ofReal_mul_toCircle_apply θ r 1 0) ?_
      simp [z, c]
    · refine Eq.trans (α := ℂ) (mfderiv_ofReal_mul_toCircle_apply θ r 0 1) ?_
      simp [z]
  · rw [Complex.orientation, eq_comm, Module.Basis.orientation_eq_iff_det_pos,
      Module.Basis.det_apply, Matrix.det_fin_two]
    simp only [Module.Basis.toMatrix_apply, coe_basisOfLinearIndependentOfCardEqFinrank,
      coe_basisOneI_repr]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hdet : (c * I * z).re * z.im - z.re * (c * I * z).im = -c := by
      simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
      linear_combination (-c) * hz
    have hk : 0 < 2 * π / p := div_pos (by positivity) hp.out
    rw [hdet, neg_pos]
    exact ⟨fun h ↦ neg_of_mul_neg_right h hk.le, fun h ↦ mul_neg_of_pos_of_neg hk h⟩

/-- Away from the radius `0`, polar coordinates `(θ, r) ↦ r · toCircle θ`, from `AddCircle p × ℝ`
with the product of the positive orientation of the circle and the standard orientation of `ℝ`
to `ℂ` with its standard orientation, preserve orientation at `(θ, r)` exactly when `r < 0`. -/
theorem isOrientationPreservingAt_ofReal_mul_toCircle_iff (θ : AddCircle p) {r : ℝ}
    (hr : r ≠ 0) :
    IsOrientationPreservingAt ((AddCircle.orientation p).prod real)
        (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation (by simp))
        (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) (θ, r) ↔
      r < 0 := by
  obtain ⟨b, hb, hbo⟩ := exists_basis_mfderiv_ofReal_mul_toCircle θ hr
  refine (isOrientationPreservingAt_iff_of_basis _ b hb).trans
    ((iff_true_left (orientationAt_orientation_prod_real p _).symm).trans ?_)
  rw [orientationAt_model]
  exact hbo

/-- **Polar coordinates preserve orientation at negative radii.** For a positive period `p`, the
map `(θ, r) ↦ r · toCircle θ` from `AddCircle p × ℝ`, with the product of the positive
orientation of the circle and the standard orientation of `ℝ`, to `ℂ`, with its standard
orientation, preserves orientation at every point with `r < 0`. -/
theorem isOrientationPreservingAt_ofReal_mul_toCircle (θ : AddCircle p) {r : ℝ} (hr : r < 0) :
    IsOrientationPreservingAt ((AddCircle.orientation p).prod real)
      (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation (by simp))
      (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) (θ, r) :=
  (isOrientationPreservingAt_ofReal_mul_toCircle_iff θ hr.ne).2 hr

/-- **Polar coordinates reverse orientation at positive radii.** For a positive period `p`, the
map `(θ, r) ↦ r · toCircle θ` from `AddCircle p × ℝ`, with the product of the positive
orientation of the circle and the standard orientation of `ℝ`, to `ℂ`, with its standard
orientation, reverses orientation at every point with `r > 0`. -/
theorem isOrientationReversingAt_ofReal_mul_toCircle (θ : AddCircle p) {r : ℝ} (hr : 0 < r) :
    IsOrientationReversingAt ((AddCircle.orientation p).prod real)
      (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation (by simp))
      (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) (θ, r) :=
  ((isLocalDiffeomorphAt_ofReal_mul_toCircle (n := 1) hr.ne'
    ).isOrientationPreservingAt_or_isOrientationReversingAt one_ne_zero _ _).resolve_left fun h ↦
      ((isOrientationPreservingAt_ofReal_mul_toCircle_iff θ hr.ne').1 h).not_gt hr

end AddCircle
