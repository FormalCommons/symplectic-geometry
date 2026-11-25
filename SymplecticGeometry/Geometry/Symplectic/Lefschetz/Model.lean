/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import SymplecticGeometry.Analysis.Complex.HolomorphicQuadratic
public import TauCeti.Geometry.Manifold.Morse.Basic
public import TauCeti.Geometry.Manifold.Morse.Index
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.DSlope
import TauCeti.Analysis.Complex.BranchLogRoot

/-!
# The local model of a Lefschetz critical point

A Lefschetz fibration looks, near each of its critical points and in suitable complex charts,
like the quadric `z ↦ z₁² + z₂²` on `ℂ²`. This file defines that model and records the facts
about it that the rest of the theory uses.

## Main definitions

* `SymplecticGeometry.LefschetzModel.quadric`: the function `z ↦ z 0 ^ 2 + z 1 ^ 2` on
  `Fin 2 → ℂ`.
* `SymplecticGeometry.LefschetzModel.quadricForm`: the symmetric complex bilinear form
  `(v, w) ↦ v 0 * w 0 + v 1 * w 1`, whose diagonal is `quadric`: Mathlib's dot product
  `dotProductBilin`, as a continuous bilinear map.

## Main results

* `SymplecticGeometry.LefschetzModel.fderiv_quadric_eq_zero_iff`,
  `SymplecticGeometry.LefschetzModel.fderiv_real_quadric_eq_zero_iff`: the complex, or real,
  derivative of `quadric` vanishes only at `0`.
* `SymplecticGeometry.LefschetzModel.isInvertible_fderiv_fderiv_quadric`: the complex Hessian
  of `quadric` is nondegenerate (at every point, in particular at `0`).
* `SymplecticGeometry.LefschetzModel.manifoldMorseIndex_re_mul_quadric`: for `c ≠ 0`, the
  point `0` is a nondegenerate critical point of `z ↦ Re (c * quadric z)`, of Morse index `2`.
* `SymplecticGeometry.LefschetzModel.exists_openPartialHomeomorph_apply_add_quadric`: after a
  holomorphic change `h` of the base coordinate with `h' c ≠ 0`, the map `w ↦ h (c + quadric w)`
  is again `h c + quadric`, in new holomorphic coordinates near `0`.

The Morse index is computed with Tau Ceti's
`ContinuousLinearMap.morseIndex_re_apply_self_of_ker_eq_bot`: the real part of a holomorphic
quadratic form whose polarization is injective has Morse index the complex dimension. The
critical point is nondegenerate by
`ContinuousLinearMap.isNondegenerateCriticalPoint_re_apply_self_of_ker_eq_bot`.

The reparametrisation writes `h (c + t) = h c + t * g t` with the slope `g = dslope _ 0`, takes
a holomorphic square root `s` of `g` near `0` from Tau Ceti's
`TauCeti.exists_eventuallyEq_pow_iff_dvd`, and applies the inverse function theorem
(`ContDiffAt.toOpenPartialHomeomorph`) to `w ↦ s (quadric w) • w`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4.
* J. Milnor, *Morse Theory*, Princeton University Press, 1963.
-/

public section

open Filter Module TauCeti Topology
open scoped ContDiff Manifold

namespace SymplecticGeometry.LefschetzModel

/-- The quadric `z ↦ z₁² + z₂²` on `ℂ²`, the local model of a Lefschetz fibration near a
critical point. -/
noncomputable def quadric (z : Fin 2 → ℂ) : ℂ :=
  z 0 ^ 2 + z 1 ^ 2

/-- The defining formula of `quadric`. -/
theorem quadric_def (z : Fin 2 → ℂ) : quadric z = z 0 ^ 2 + z 1 ^ 2 :=
  (rfl)

/-- The complex bilinear form `(v, w) ↦ v 0 * w 0 + v 1 * w 1` on `ℂ²`, whose diagonal is
`quadric`: the dot product, as a continuous bilinear map. -/
noncomputable def quadricForm : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) →L[ℂ] ℂ :=
  (dotProductBilin ℂ ℂ).toContinuousBilinearMap

/-- `quadricForm` is the dot product `dotProductBilin`, made continuous. -/
theorem quadricForm_def : quadricForm = (dotProductBilin ℂ ℂ).toContinuousBilinearMap :=
  (rfl)

/-- `quadricForm` in coordinates. -/
@[simp]
theorem quadricForm_apply (v w : Fin 2 → ℂ) : quadricForm v w = v 0 * w 0 + v 1 * w 1 := by
  simp [quadricForm_def, dotProduct, Fin.sum_univ_two]

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
  intro v w h
  apply (dotProductEquiv ℂ (Fin 2)).injective
  refine LinearMap.ext fun u ↦ ?_
  simpa [hc] using congr($h u)

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

/-- The quadric is complex analytic. -/
theorem analyticAt_quadric (z : Fin 2 → ℂ) : AnalyticAt ℂ quadric z :=
  (contDiff_quadric (n := ω)).contDiffAt.analyticAt

/-- The quadric vanishes at the origin. -/
@[simp]
theorem quadric_zero : quadric 0 = 0 := by
  simp [quadric_def]

/-- The quadric is homogeneous of degree two. -/
theorem quadric_smul (a : ℂ) (z : Fin 2 → ℂ) : quadric (a • z) = a ^ 2 * quadric z := by
  simp only [quadric_def, Pi.smul_apply, smul_eq_mul]
  ring

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
  exact ⟨q.isNondegenerateCriticalPoint_re_apply_self_of_ker_eq_bot hker, rfl⟩

/-- **Reparametrising the quadric.** A holomorphic change `h` of the base coordinate near `c`,
with `h' c ≠ 0`, keeps the exact model: there is a biholomorphic change of coordinates `e` of
`ℂ²` near `0`, fixing `0`, with `h (c + quadric w) = h c + quadric (e w)` on its source.

Here `e` is a partial homeomorphism whose source is a neighbourhood of `0`, complex analytic
on its source, with invertible complex derivative there. Explicitly, `e w = s (quadric w) • w`
for a holomorphic square root `s` of the slope `t ↦ (h (c + t) - h c) / t` of `h` at `c`. -/
theorem exists_openPartialHomeomorph_apply_add_quadric {h : ℂ → ℂ} {c : ℂ}
    (hh : AnalyticAt ℂ h c) (hc : deriv h c ≠ 0) :
    ∃ e : OpenPartialHomeomorph (Fin 2 → ℂ) (Fin 2 → ℂ), 0 ∈ e.source ∧ e 0 = 0 ∧
      AnalyticOnNhd ℂ e e.source ∧ (∀ w ∈ e.source, (fderiv ℂ e w).IsInvertible) ∧
      ∀ w ∈ e.source, h (c + quadric w) = h c + quadric (e w) := by
  -- `h (c + t) = h c + t * g t`, with `g` the slope of `h` at `c`, and `g 0 = h' c ≠ 0`.
  set g := dslope (fun t ↦ h (c + t)) 0
  have hga : AnalyticAt ℂ g 0 :=
    (hh.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)).dslope 0
  have hg0 : g 0 ≠ 0 := by simpa [g, dslope_same, deriv_comp_const_add] using hc
  have hgeq (t : ℂ) : h (c + t) = h c + t * g t := by
    have := sub_smul_dslope (fun t ↦ h (c + t)) 0 t
    simp only [sub_zero, smul_eq_mul, add_zero] at this
    rw [this]
    ring
  -- A holomorphic square root `s` of `g` on an open neighbourhood `W` of `0`.
  obtain ⟨s, hsa, hseq⟩ := (exists_eventuallyEq_pow_iff_dvd hga two_ne_zero).2
    (by rw [analyticOrderAt_eq_zero.2 (Or.inr hg0)]; exact dvd_zero _)
  obtain ⟨W, hW, hWo, h0W⟩ := eventually_nhds_iff.1 (hsa.eventually_analyticAt.and hseq)
  set V := quadric ⁻¹' W
  have hVo : IsOpen V := hWo.preimage (contDiff_quadric (n := 0)).continuous
  have h0V : (0 : Fin 2 → ℂ) ∈ V := by simpa [V] using h0W
  -- The reparametrisation `ψ w = s (quadric w) • w`, with derivative `s 0 • id` at `0`.
  set ψ : (Fin 2 → ℂ) → Fin 2 → ℂ := fun w ↦ s (quadric w) • w
  have hψa : AnalyticOnNhd ℂ ψ V := fun w hw ↦
    ((hW _ hw).1.comp (analyticAt_quadric w)).smul analyticAt_id
  have hs0 : s 0 ≠ 0 := by
    intro h0
    exact hg0 (by rw [(hW 0 h0W).2, h0]; simp)
  set f' := (LinearEquiv.smulOfNeZero ℂ (Fin 2 → ℂ) (s 0) hs0).toContinuousLinearEquiv
  have hd : HasFDerivAt ψ (f' : (Fin 2 → ℂ) →L[ℂ] Fin 2 → ℂ) 0 := by
    have h1 : AnalyticAt ℂ (fun w ↦ s (quadric w)) 0 :=
      (hW _ (by simpa using h0W)).1.comp (analyticAt_quadric 0)
    refine (h1.differentiableAt.hasFDerivAt.smul (hasFDerivAt_id 0)).congr_fderiv ?_
    ext v i
    simp [f']
  -- The inverse function theorem, restricted to where `ψ` is analytic with invertible
  -- derivative.
  have hcd := (hψa 0 h0V).contDiffAt (n := ω)
  set e₀ := hcd.toOpenPartialHomeomorph ψ hd (by simp)
  set O := V ∩ fderiv ℂ ψ ⁻¹' {T | T.IsInvertible}
  have hO : IsOpen O :=
    ((hψa.contDiffOn hVo.uniqueDiffOn (n := 1)).continuousOn_fderiv_of_isOpen hVo
      le_rfl).isOpen_inter_preimage hVo ContinuousLinearMap.isOpen_setOfPred_isInvertible
  refine ⟨e₀.restrOpen O hO, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hcd.mem_toOpenPartialHomeomorph_source hd _, h0V, ⟨f', hd.fderiv.symm⟩⟩
  · simp [e₀, ψ]
  · exact fun w hw ↦ hψa w hw.2.1
  · exact fun w hw ↦ hw.2.2
  · intro w hw
    have hq := (hW _ hw.2.1).2
    simp only [OpenPartialHomeomorph.coe_restrOpen, e₀, ContDiffAt.toOpenPartialHomeomorph_coe,
      ψ, quadric_smul, hgeq, ← hq]
    ring

end SymplecticGeometry.LefschetzModel

end
