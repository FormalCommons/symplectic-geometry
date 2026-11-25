/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import SymplecticGeometry.Analysis.Complex.HolomorphicQuadratic
import SymplecticGeometry.Analysis.Complex.RealFunctional
public import TauCeti.Geometry.Manifold.Morse.Basic
public import TauCeti.Geometry.Manifold.Morse.Index
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.DSlope
import TauCeti.Analysis.Analytic.Inverse
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
* `SymplecticGeometry.LefschetzModel.manifoldMorseIndex_comp_quadric`: the same for `ν ∘ quadric`,
  for any `ν : ℂ → ℝ` that is `C²` at `0` with nonzero derivative there.
* `SymplecticGeometry.LefschetzModel.exists_openPartialHomeomorph_apply_add_quadric`: after a
  holomorphic change `h` of the base coordinate with `h' c ≠ 0`, the map `w ↦ h (c + quadric w)`
  is again `h c + quadric`, in biholomorphic coordinates near `0` whose domain lies in any
  prescribed neighbourhood of `0`.

The Morse index is computed with Tau Ceti's
`ContinuousLinearMap.morseIndex_re_apply_self_of_ker_eq_bot`: the real part of a holomorphic
quadratic form whose polarization is injective has Morse index the complex dimension. The
critical point is nondegenerate by
`ContinuousLinearMap.isNondegenerateCriticalPoint_re_apply_self_of_ker_eq_bot`. For a general
`ν`, Tau Ceti's `TauCeti.hessianQuadraticForm_comp_eq_fderiv_comp` replaces `ν` by its derivative
at `0`, since the quadric is critical there, and that derivative is `t ↦ Re (c * t)` by
`ContinuousLinearMap.exists_apply_eq_re_mul`.

The reparametrisation adapts the proof of Tau Ceti's
`AnalyticAt.exists_openPartialHomeomorph_sub_eq_pow` from one variable to the quadric on `ℂ²`.
It writes `h (c + t) = h c + t * g t` with the slope `g = dslope _ 0`, takes a holomorphic
square root `s` of `g` near `0` from Tau Ceti's `TauCeti.exists_eventuallyEq_pow_iff_dvd`, and
applies Tau Ceti's analytic inverse function theorem `AnalyticAt.exists_openPartialHomeomorph`
to `w ↦ s (quadric w) • w`.

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

/-- **The Morse index of a function of the quadric.** If `ν : ℂ → ℝ` is `C²` at `0` with nonzero
real derivative there, then the origin is a nondegenerate critical point of `ν ∘ quadric` on `ℂ²`,
of Morse index `2`. -/
theorem manifoldMorseIndex_comp_quadric {ν : ℂ → ℝ} (hν : ContDiffAt ℝ 2 ν 0)
    (hd : fderiv ℝ ν 0 ≠ 0) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, Fin 2 → ℂ) (ν ∘ quadric) 0 ∧
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℂ) (ν ∘ quadric) 0 = 2 := by
  -- The derivative of `ν` at `0` is `t ↦ Re (c * t)` with `c ≠ 0`; since the quadric is critical
  -- at `0`, the Hessian of `ν ∘ quadric` there is that of `z ↦ Re (c * quadric z)`.
  obtain ⟨c, hc⟩ := (fderiv ℝ ν 0).exists_apply_eq_re_mul
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hd (ContinuousLinearMap.ext fun t ↦ by simp [hc])
  have hq : ContDiffAt ℝ 2 quadric 0 := (contDiff_quadric.restrict_scalars ℝ).contDiffAt
  have hq0 : fderiv ℝ quadric 0 = 0 := fderiv_real_quadric_eq_zero_iff.2 rfl
  have hν' : ContDiffAt ℝ 2 ν (quadric 0) := by rwa [quadric_zero]
  have hH : hessianQuadraticForm (ν ∘ quadric) 0 =
      hessianQuadraticForm (fun z ↦ (c * quadric z).re) 0 := by
    rw [hessianQuadraticForm_comp_eq_fderiv_comp hν' hq hq0, quadric_zero]
    congr 1
    funext z
    simp [hc]
  obtain ⟨hnd, hidx⟩ := manifoldMorseIndex_re_mul_quadric hc0
  rw [isManifoldNondegenerateCriticalPoint_modelSpace_iff,
    isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate] at hnd ⊢
  rw [manifoldMorseIndex_modelSpace, morseIndex_def] at hidx ⊢
  refine ⟨⟨hν'.comp 0 hq, ?_, hH ▸ hnd.2.2⟩, hH ▸ hidx⟩
  rw [fderiv_comp 0 (hν'.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num)), hq0,
    ContinuousLinearMap.comp_zero]

/-- **Reparametrising the quadric.** A holomorphic change `h` of the base coordinate near `c`,
with `h' c ≠ 0`, keeps the exact model: there is a biholomorphic change of coordinates `e` of
`ℂ²` near `0`, fixing `0`, with `h (c + quadric w) = h c + quadric (e w)` on its source.

Here `e` is a partial homeomorphism whose source is a neighbourhood of `0` contained in the
given neighbourhood `U` of `0`; it is complex analytic on its source, and its inverse is
complex analytic on its target. -/
theorem exists_openPartialHomeomorph_apply_add_quadric {h : ℂ → ℂ} {c : ℂ}
    (hh : AnalyticAt ℂ h c) (hc : deriv h c ≠ 0) {U : Set (Fin 2 → ℂ)} (hU : U ∈ 𝓝 0) :
    ∃ e : OpenPartialHomeomorph (Fin 2 → ℂ) (Fin 2 → ℂ), 0 ∈ e.source ∧ e 0 = 0 ∧
      e.source ⊆ U ∧ AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
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
  -- The analytic inverse function theorem, with source inside `U ∩ V`.
  obtain ⟨e, he, h0e, hesub, hea, hei⟩ :=
    (hψa 0 h0V).exists_openPartialHomeomorph hd.fderiv (inter_mem hU (hVo.mem_nhds h0V))
  refine ⟨e, h0e, by simp [he, ψ], fun w hw ↦ (hesub hw).1, he ▸ hea, hei, fun w hw ↦ ?_⟩
  have hq := (hW _ (hesub hw).2).2
  simp only [he, ψ, quadric_smul, hgeq, ← hq]
  ring

end SymplecticGeometry.LefschetzModel

end
