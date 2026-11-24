/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Beltrami.HigherHolder
public import TauCeti.Analysis.Complex.Beltrami.Chart
public import TauCeti.Analysis.Complex.Beltrami.Linear

/-!
# Planar charts of class `C^{k+1}` for a small `C^{k,α}` Beltrami coefficient

Let `0 < α < 1`, `k : ℕ` and `0 < r`. For a field `J` of almost complex structures on the plane,
tame on `closedBall c r`, whose scalar Beltrami coefficient agrees there with a `C^{k,α}` function
`μ` vanishing off the disc and of small `C^{k,α}` norm, this file gives an open partial
homeomorphism near `c`, of class `C^{k+1}` with invertible derivative, whose derivative carries
`J` to multiplication by `i`.

The chart is the solution `ψ = z + T h` of the Beltrami equation `\bar∂ψ = μ ∂ψ` given by the
contraction in `C^{k,α}` (`TauCeti.exists_ckHolder_conjWirtingerDeriv_eq_mul_wirtingerDeriv`),
restricted by the inverse function theorem to a neighbourhood of `c` inside `ball c r`. Its
derivative is `J`-complex linear on the disc by
`TauCeti.Beltrami.isComplexLinear_iff_conjWirtingerDeriv_eq`. The statement and the steps follow
those of Tau Ceti's `TauCeti.Beltrami.exists_isComplexLinear_chart`, which does the same for a
Hölder coefficient and a chart of class `C¹`.

## Main results

* `TauCeti.Beltrami.exists_isComplexLinear_contDiff_chart`: charts of class `C^{k+1}` in which a
  field of almost complex structures with small `C^{k,α}` coefficient becomes standard.

## References

* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter V.
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B and Appendix E.
-/

public section

open Complex Metric
open scoped NNReal

namespace TauCeti.Beltrami

/-- **Planar charts of class `C^{k+1}` for a small `C^{k,α}` coefficient.** Let `0 < α < 1`,
`k : ℕ` and `0 < r`. There is `δ > 0` such that the following holds. Let `J` be a field of almost
complex structures on the plane, tame on `closedBall c r`, and let `μ` be a `C^{k,α}` function
vanishing off that disc, equal there to the scalar Beltrami coefficient of `J`, with `‖μ‖ < δ`.
Then there is an open partial homeomorphism `e` of `ℂ` whose source contains `c` and lies in
`ball c r`, which is of class `C^{k+1}` on its source with invertible derivative there, and whose
derivative carries `J` to multiplication by `i` at every point of its source. -/
theorem exists_isComplexLinear_contDiff_chart (k : ℕ) {α : ℝ≥0} {r : ℝ} (hα : 0 < α)
    (hα1 : α < 1) (c : ℂ) (hr : 0 < r) :
    ∃ δ > 0, ∀ (J : ℂ → AlmostComplexStructure ℂ)
      (hJ : ∀ z ∈ closedBall c r, stdComplexSymplecticForm.Tames (J z)),
      ∀ μ ∈ supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r),
      (∀ z (hz : z ∈ closedBall c r), μ z = (coefficientEquiv ⟨J z, hJ z hz⟩).val) →
      ‖μ‖ < δ →
      ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e.source ⊆ ball c r ∧
        ContDiffOn ℝ (k + 1) e e.source ∧
        (∀ z ∈ e.source, (fderiv ℝ e z).IsInvertible) ∧
        ∀ z ∈ e.source, ∀ v, fderiv ℝ e z (J z v) = I * fderiv ℝ e z v := by
  obtain ⟨δ, hδ, _C, hsol⟩ := exists_ckHolder_conjWirtingerDeriv_eq_mul_wirtingerDeriv k hα hα1 c r
  refine ⟨δ, hδ, fun J hJ μ hμ hμJ hμδ ↦ ?_⟩
  obtain ⟨h, -, -, hψC, -, hbel, -, -, -, hstrict⟩ := hsol μ hμ hμδ
  -- The solver states its conclusions for the explicit map `w ↦ w + T h(w)`; fold it.
  have hfold : (fun w ↦ w + cauchyTransform h w) = cauchySolution h :=
    funext fun w ↦ (cauchySolution_apply h w).symm
  rw [hfold] at hψC hbel hstrict
  set ψ := cauchySolution h
  -- The differential of `ψ` is invertible, and complex linear from `J` to `i`, on the disc.
  have hinv (z : ℂ) (hz : z ∈ closedBall c r) : (fderiv ℝ ψ z).IsInvertible := by
    obtain ⟨L, hL⟩ := hstrict z hz
    exact ⟨L, hL.hasFDerivAt.fderiv.symm⟩
  have hlin (z : ℂ) (hz : z ∈ closedBall c r) (v : ℂ) :
      fderiv ℝ ψ z (J z v) = I * fderiv ℝ ψ z v := by
    have := ((isComplexLinear_iff_conjWirtingerDeriv_eq (J z) (hJ z hz) ψ z).mpr
      (by rw [← hμJ z hz]; exact hbel z)).apply v
    simpa only [ContinuousLinearMap.coe_coe, AlmostComplexStructure.ofComplexModule_apply,
      smul_eq_mul] using this
  -- The inverse function theorem at `c`, restricted to `ball c r`.
  obtain ⟨L, hL⟩ := hstrict c (mem_closedBall_self hr.le)
  let e := (hL.toOpenPartialHomeomorph ψ).restrOpen (ball c r) isOpen_ball
  have he : ⇑e = ψ := by
    rw [OpenPartialHomeomorph.coe_restrOpen]
    exact hL.toOpenPartialHomeomorph_coe
  have hs : e.source ⊆ ball c r := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_subset_right
  refine ⟨e, ?_, hs, ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hL.mem_toOpenPartialHomeomorph_source, mem_ball_self hr⟩
  · rw [he]
    exact_mod_cast hψC.contDiffOn
  · rw [he]
    exact hinv z (ball_subset_closedBall (hs hz))
  · rw [he]
    exact hlin z (ball_subset_closedBall (hs hz))

end TauCeti.Beltrami

end
