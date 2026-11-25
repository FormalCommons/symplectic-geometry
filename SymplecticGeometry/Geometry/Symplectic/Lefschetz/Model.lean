/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.QuadraticLeviForm
public import TauCeti.Geometry.Manifold.Morse.Basic
public import TauCeti.Geometry.Manifold.Morse.Index

/-!
# The local model of a Lefschetz critical point

A Lefschetz fibration looks, near each of its critical points and in suitable complex charts,
like the quadric `z ↦ z₁² + z₂²` on `ℂ²`. This file defines that model and records the facts
about it that the rest of the theory uses.

## Main definitions

* `SymplecticGeometry.LefschetzModel.quadric`: the function `z ↦ z 0 ^ 2 + z 1 ^ 2` on
  `Fin 2 → ℂ`.
* `SymplecticGeometry.LefschetzModel.quadricForm`: the symmetric complex bilinear form
  `(v, w) ↦ v 0 * w 0 + v 1 * w 1`, whose diagonal is `quadric`.

## Main results

* `SymplecticGeometry.LefschetzModel.fderiv_quadric_eq_zero_iff`,
  `SymplecticGeometry.LefschetzModel.fderiv_real_quadric_eq_zero_iff`: the complex, or real,
  derivative of `quadric` vanishes only at `0`.
* `SymplecticGeometry.LefschetzModel.isInvertible_fderiv_fderiv_quadric`: the complex Hessian
  of `quadric` is nondegenerate (at every point, in particular at `0`).
* `SymplecticGeometry.LefschetzModel.manifoldMorseIndex_re_mul_quadric`: for `c ≠ 0`, the
  point `0` is a nondegenerate critical point of `z ↦ Re (c * quadric z)`, of Morse index `2`.

The Morse index is computed with Tau Ceti's
`ContinuousLinearMap.morseIndex_re_apply_self_of_ker_eq_bot`: the real part of a holomorphic
quadratic form whose polarization is injective has Morse index the complex dimension.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4.
* J. Milnor, *Morse Theory*, Princeton University Press, 1963.
-/

public section

open Module TauCeti
open scoped Manifold

namespace SymplecticGeometry.LefschetzModel

/-- The quadric `z ↦ z₁² + z₂²` on `ℂ²`, the local model of a Lefschetz fibration near a
critical point. -/
noncomputable def quadric (z : Fin 2 → ℂ) : ℂ :=
  z 0 ^ 2 + z 1 ^ 2

/-- The defining formula of `quadric`. -/
theorem quadric_def (z : Fin 2 → ℂ) : quadric z = z 0 ^ 2 + z 1 ^ 2 :=
  (rfl)

/-- The complex bilinear form `(v, w) ↦ v 0 * w 0 + v 1 * w 1` on `ℂ²`, whose diagonal is
`quadric`. -/
noncomputable def quadricForm : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) →L[ℂ] ℂ :=
  ∑ j : Fin 2, (ContinuousLinearMap.proj j).smulRight (ContinuousLinearMap.proj j)

/-- The defining formula of `quadricForm`. -/
@[simp]
theorem quadricForm_apply (v w : Fin 2 → ℂ) : quadricForm v w = v 0 * w 0 + v 1 * w 1 := by
  simp [quadricForm]

/-- The bilinear form of the quadric is symmetric. -/
@[simp]
theorem quadricForm_flip : quadricForm.flip = quadricForm := by
  ext v w
  simp [mul_comm]

/-- The quadric is the diagonal of `quadricForm`. -/
theorem quadricForm_apply_self (z : Fin 2 → ℂ) : quadricForm z z = quadric z := by
  simp [quadric_def, sq]

/-- `quadric` as the diagonal of `quadricForm`. -/
theorem quadric_eq_quadricForm_apply_self : quadric = fun z ↦ quadricForm z z :=
  funext fun z ↦ (quadricForm_apply_self z).symm

/-- A nonzero multiple of `quadricForm` is nondegenerate: `c • quadricForm` is injective as a
map into the dual. -/
theorem injective_smul_quadricForm {c : ℂ} (hc : c ≠ 0) :
    Function.Injective (c • quadricForm) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  have h (j : Fin 2) := congr($hv (Pi.single j 1))
  ext j
  fin_cases j
  · simpa [hc] using h 0
  · simpa [hc] using h 1

/-- The quadric is complex differentiable, with derivative `v ↦ 2 (z 0 v 0 + z 1 v 1)`. -/
theorem hasFDerivAt_quadric (z : Fin 2 → ℂ) :
    HasFDerivAt quadric ((2 : ℂ) • quadricForm z) z := by
  rw [quadric_eq_quadricForm_apply_self]
  convert quadricForm.hasFDerivAt_apply_self z using 1
  ext v
  simp [two_mul]

/-- The complex derivative of the quadric at `z` is `2 • quadricForm z`. -/
theorem fderiv_quadric (z : Fin 2 → ℂ) : fderiv ℂ quadric z = (2 : ℂ) • quadricForm z :=
  (hasFDerivAt_quadric z).fderiv

/-- The quadric is a complex polynomial, hence complex smooth. -/
theorem contDiff_quadric {n : WithTop ℕ∞} : ContDiff ℂ n quadric := by
  rw [quadric_eq_quadricForm_apply_self]
  exact quadricForm.contDiff_apply_self

/-- The complex Hessian of the quadric is the constant `2 • quadricForm`. -/
theorem fderiv_fderiv_quadric (z : Fin 2 → ℂ) :
    fderiv ℂ (fderiv ℂ quadric) z = (2 : ℂ) • quadricForm := by
  rw [quadric_eq_quadricForm_apply_self, quadricForm.fderiv_fderiv_apply_self, quadricForm_flip]
  ext v w
  simp [two_mul]

/-- The only critical point of the quadric is the origin. -/
theorem fderiv_quadric_eq_zero_iff {z : Fin 2 → ℂ} : fderiv ℂ quadric z = 0 ↔ z = 0 := by
  rw [fderiv_quadric]
  simpa using (injective_iff_map_eq_zero' _).1 (injective_smul_quadricForm two_ne_zero) z

/-- The only critical point of the quadric, as a map of real vector spaces, is the origin. -/
theorem fderiv_real_quadric_eq_zero_iff {z : Fin 2 → ℂ} : fderiv ℝ quadric z = 0 ↔ z = 0 := by
  rw [(contDiff_quadric (n := 1).differentiable one_ne_zero z).fderiv_restrictScalars ℝ,
    ← fderiv_quadric_eq_zero_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, ContinuousLinearMap.restrictScalars_zero]⟩
  ext v
  exact congr($h v)

/-- The complex Hessian of the quadric is nondegenerate, at every point. -/
theorem isInvertible_fderiv_fderiv_quadric (z : Fin 2 → ℂ) :
    (fderiv ℂ (fderiv ℂ quadric) z).IsInvertible := by
  rw [fderiv_fderiv_quadric]
  exact ContinuousLinearMap.isInvertible_of_injective (injective_smul_quadricForm two_ne_zero)

/-- **The Morse index of the Lefschetz model.** For `c ≠ 0`, the origin is a nondegenerate
critical point of `z ↦ Re (c * (z 0 ^ 2 + z 1 ^ 2))` on `ℂ²`, of Morse index `2`. -/
theorem manifoldMorseIndex_re_mul_quadric {c : ℂ} (hc : c ≠ 0) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, Fin 2 → ℂ) (fun z ↦ (c * quadric z).re) 0 ∧
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℂ) (fun z ↦ (c * quadric z).re) 0 = 2 := by
  set q : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) →L[ℂ] ℂ := c • quadricForm
  have hfun : (fun z ↦ (c * quadric z).re) = fun z ↦ (q z z).re := by
    funext z
    simp only [q, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
      quadricForm_apply_self]
  have hker : LinearMap.ker (q.flip + q).toLinearMap = ⊥ := by
    have hq : q.flip + q = (2 * c) • quadricForm := by
      ext v w
      simp only [q, _root_.add_apply, ContinuousLinearMap.flip_apply,
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, quadricForm_apply]
      ring
    rw [hq, LinearMap.ker_eq_bot]
    exact injective_smul_quadricForm (mul_ne_zero two_ne_zero hc)
  rw [isManifoldNondegenerateCriticalPoint_modelSpace_iff, manifoldMorseIndex_modelSpace, hfun,
    q.morseIndex_re_apply_self_of_ker_eq_bot hker, Module.finrank_fin_fun]
  refine ⟨isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate.2
    ⟨(Complex.reCLM.contDiff.comp (q.contDiff_apply_self.restrict_scalars ℝ)).contDiffAt, ?_, ?_⟩,
    rfl⟩
  · have h := Complex.reCLM.hasFDerivAt.comp (0 : Fin 2 → ℂ)
      ((q.hasFDerivAt_apply_self 0).restrictScalars ℝ)
    simpa [Function.comp_def] using h.fderiv
  · rw [QuadraticMap.nondegenerate_iff_radical_eq_bot,
      q.radical_hessianQuadraticForm_re_apply_self, hker, Submodule.restrictScalars_bot]

end SymplecticGeometry.LefschetzModel

end
