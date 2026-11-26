/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import TauCeti.Geometry.Manifold.Morse.Hessian

/-!
# Positive directions of the critical Hessian in charts

At a critical point `x` of a function `f` that is `C²` at `x`, Tau Ceti's critical Hessian
`TauCeti.criticalHessian I f x` is the Hessian of a coordinate expression of `f`, transported by
the chart derivative (`TauCeti.criticalHessian_apply_eq_of_mem_maximalAtlas`). Since the chart
derivative is invertible (`TauCeti.isInvertible_mvfderiv_extend`), the critical Hessian is positive
on some tangent vector exactly when the coordinate Hessian is positive on some vector, in any chart
of the `C²` maximal atlas (`TauCeti.exists_criticalHessian_pos_iff_of_mem_maximalAtlas`).

It also says how the critical Hessian meets sums and products at an interior point where the
functions are `C²`: it is additive (`TauCeti.criticalHessian_add`,
`TauCeti.criticalHessian_sum`), and at a point where `g` and its differential vanish, the
critical Hessian of `f * g` is `f x` times that of `g`
(`TauCeti.criticalHessian_mul_of_mem_criticalPoints`), by the Leibniz rule for the second
derivative of the coordinate expressions.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2, for the Hessian at a critical point.
-/

public section

open Filter Topology
open scoped Manifold

namespace TauCeti

section Algebra

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {f g : M → ℝ} {x : M}

/-- The critical Hessian of the zero function vanishes. -/
@[simp]
theorem criticalHessian_zero : criticalHessian I (0 : M → ℝ) x = 0 := by
  have h : (0 : M → ℝ) ∘ (extChartAt I x).symm = fun _ ↦ 0 := rfl
  rw [criticalHessian_def, h, fderiv_fun_const, Pi.zero_def, fderiv_const_apply]
  -- The two sides differ only in reading `E` as the tangent space at `x`.
  rfl

/-- At an interior point where `f` and `g` are `C²`, the critical Hessian of `f + g` is the sum
of their critical Hessians. -/
theorem criticalHessian_add (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hg : ContMDiffAt I 𝓘(ℝ) 2 g x)
    (hx : I.IsInteriorPoint x) :
    criticalHessian I (f + g) x = criticalHessian I f x + criticalHessian I g x := by
  have hF := hf.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hx
  have hG := hg.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hx
  have hsum : fderiv ℝ ((f + g) ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)]
      fderiv ℝ (f ∘ (extChartAt I x).symm) + fderiv ℝ (g ∘ (extChartAt I x).symm) := by
    filter_upwards [hF.eventually (by simp), hG.eventually (by simp)] with p hp hq
    exact fderiv_add (hp.differentiableAt two_ne_zero) (hq.differentiableAt two_ne_zero)
  rw [criticalHessian_def, criticalHessian_def, criticalHessian_def, hsum.fderiv_eq]
  exact fderiv_add ((hF.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)
    ((hG.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)

/-- At an interior point where the functions `f i`, `i ∈ s`, are `C²`, the critical Hessian of
their sum is the sum of their critical Hessians. -/
theorem criticalHessian_sum {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i ∈ s, ContMDiffAt I 𝓘(ℝ) 2 (f i) x) (hx : I.IsInteriorPoint x) :
    criticalHessian I (∑ i ∈ s, f i) x = ∑ i ∈ s, criticalHessian I (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      criticalHessian_add (hf i (Finset.mem_insert_self i s))
        (contMDiffAt_finsetSum' fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)) hx,
      ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]

/-- **The critical Hessian of a product with a function vanishing to second order.** At an
interior point `x` where `f` and `g` are `C²`, if `g x = 0` and `x` is a critical point of `g`,
then the critical Hessian of `f * g` at `x` is `f x` times that of `g`. -/
theorem criticalHessian_mul_of_mem_criticalPoints (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hg : ContMDiffAt I 𝓘(ℝ) 2 g x) (hx : I.IsInteriorPoint x) (hg0 : g x = 0)
    (hgc : x ∈ criticalPoints I g) :
    criticalHessian I (f * g) x = f x • criticalHessian I g x := by
  set F := f ∘ (extChartAt I x).symm
  set G := g ∘ (extChartAt I x).symm
  set p := extChartAt I x x
  have hF : ContDiffAt ℝ 2 F p := hf.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hx
  have hG : ContDiffAt ℝ 2 G p := hg.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hx
  have hFp : F p = f x := by simp [F, p]
  have hGp : G p = 0 := by simp [G, p, hg0]
  have hdG : fderiv ℝ G p = 0 := fderiv_comp_extChartAt_symm_eq_zero_of_mem_criticalPoints hgc
  -- The Leibniz rule for the first derivative, near `p`.
  have hmul : fderiv ℝ ((f * g) ∘ (extChartAt I x).symm) =ᶠ[𝓝 p]
      F • fderiv ℝ G + G • fderiv ℝ F := by
    filter_upwards [hF.eventually (by simp), hG.eventually (by simp)] with q hq hq'
    exact fderiv_mul (hq.differentiableAt two_ne_zero) (hq'.differentiableAt two_ne_zero)
  -- Its derivative at `p`, where `G` and `dG` vanish.
  have hd := ((hF.differentiableAt two_ne_zero).hasFDerivAt.smul
      ((hG.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt).add
    ((hG.differentiableAt two_ne_zero).hasFDerivAt.smul
      ((hF.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt)
  rw [criticalHessian_def, criticalHessian_def, hmul.fderiv_eq, hd.fderiv, hFp, hGp, hdG]
  simp only [ContinuousLinearMap.smulRight_zero, ContinuousLinearMap.zero_smulRight, zero_smul,
    add_zero]
  -- The two sides differ only in reading `E` as the tangent space at `x`.
  rfl

end Algebra

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

/-- At a critical point `x` of a function `f` which is `C²` at `x`, on a boundaryless manifold,
the critical Hessian is positive on some tangent vector exactly when, in a chart `e` of the `C²`
maximal atlas whose source contains `x`, the Hessian of the coordinate expression of `f` at the
image of `x` is positive on some vector. -/
theorem exists_criticalHessian_pos_iff_of_mem_maximalAtlas {f : M → ℝ} {x : M}
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 2 M) (hx : x ∈ e.source)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : x ∈ criticalPoints I f) :
    (∃ v, 0 < criticalHessian I f x v v) ↔
      ∃ w : E, 0 < fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm)) (e.extend I x) w w := by
  obtain ⟨D, hD⟩ :=
    isInvertible_mvfderiv_extend (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hx
  simp only [criticalHessian_apply_eq_of_mem_maximalAtlas he hx hf (mem_criticalPoints.mp hcrit)]
  refine ⟨fun ⟨v, hv⟩ ↦ ⟨_, hv⟩, fun ⟨w, hw⟩ ↦ ⟨D.symm w, ?_⟩⟩
  rwa [← hD, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

end TauCeti

end
