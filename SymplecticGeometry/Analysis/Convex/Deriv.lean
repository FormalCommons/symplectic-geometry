/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Convexity and derivatives

A real function `f` on a convex subset `s` of a real vector space, continuous on `s`, is strictly
convex on `s` if, for all distinct `x, y ∈ s`, the restriction `t ↦ f (x + t • (y - x))` has a
positive second derivative at every `t ∈ (0, 1)`. This extends Mathlib's
`strictConvexOn_of_deriv2_pos` from `ℝ` to any real topological vector space, by restricting `f`
to segments.

As an application, for a `C²` map `ψ` from a real normed space to a real inner product space, the
squared distance `u ↦ ‖ψ u - c‖ ^ 2` to a point `c` is strictly convex on an open convex set where
the differential of `ψ` does not shrink vectors and `‖ψ u - c‖` times the norm of the second
derivative of `ψ` stays below `1`: its second derivative along `v` is
`2 ‖Dψ v‖ ^ 2 + 2 ⟪ψ u - c, D²ψ v v⟫`.

Finally, a real function that is convex on `[x, ∞)` and has a positive right derivative at `x`
tends to `∞` at `∞`, since there it lies above its tangent line at `x`.

## Main results

* `SymplecticGeometry.strictConvexOn_of_deriv2_add_smul_pos`.
* `ContDiffOn.strictConvexOn_norm_sub_sq`.
* `ConvexOn.tendsto_atTop_of_hasDerivWithinAt_Ioi_pos`: a convex function with a positive right
  derivative at a point tends to `∞` at `∞`.

The first proof adapts that of Tau Ceti's `TauCeti.convexOn_of_hasFDerivAt_gradient` (convexity
from a nonnegative Hessian along segments) to strict convexity, with the second derivative along
each segment as hypothesis instead of a Hessian.
-/

public section

open Set Filter Topology
open scoped RealInnerProductSpace

namespace SymplecticGeometry

/-- **Strict convexity from second derivatives along segments.** Let `f` be continuous on a convex
set `s` of a real topological vector space. If, for all distinct `x, y ∈ s`, the function
`t ↦ f (x + t • (y - x))` has a positive second derivative at every `t ∈ (0, 1)`, then `f` is
strictly convex on `s`. -/
theorem strictConvexOn_of_deriv2_add_smul_pos {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] {s : Set E} {f : E → ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hf'' : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < deriv^[2] (fun t : ℝ ↦ f (x + t • (y - x))) t) :
    StrictConvexOn ℝ s f := by
  refine ⟨hs, fun x hx y hy hxy a b ha hb hab ↦ ?_⟩
  -- Restrict `f` to the segment `t ↦ x + t • (y - x)`, `t ∈ [0, 1]`.
  set g : ℝ → ℝ := fun t ↦ f (x + t • (y - x))
  have hg : StrictConvexOn ℝ (Icc 0 1) g :=
    strictConvexOn_of_deriv2_pos (convex_Icc 0 1)
      (hf.comp (by fun_prop) fun t ht ↦ hs.add_smul_sub_mem hx hy ht) fun t ht ↦
        hf'' x hx y hy hxy t (by rwa [interior_Icc] at ht)
  have h := hg.2 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    (by simp) ha hb hab
  have hab' : a = 1 - b := by linarith
  simp only [g, smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul,
    add_sub_cancel] at h
  convert h using 2
  rw [hab', sub_smul, one_smul, smul_sub]
  abel

end SymplecticGeometry

/-- **Strict convexity of a squared distance.** Let `ψ` be a `C²` map from a real normed space to a
real inner product space, on an open convex set `s`, and `c` a point. If the differential of `ψ`
does not shrink vectors on `s`, and `‖ψ u - c‖ * ‖D²ψ u‖ < 1` for every `u ∈ s` (where `D²ψ u` is
the second iterated derivative `iteratedFDeriv ℝ 2 ψ u`), then
`u ↦ ‖ψ u - c‖ ^ 2` is strictly convex on `s`. -/
theorem ContDiffOn.strictConvexOn_norm_sub_sq {T F : Type*} [NormedAddCommGroup T]
    [NormedSpace ℝ T] [NormedAddCommGroup F] [InnerProductSpace ℝ F] {s : Set T} {ψ : T → F}
    (hψ : ContDiffOn ℝ 2 ψ s) (hs : Convex ℝ s) (hso : IsOpen s) (c : F)
    (h₁ : ∀ u ∈ s, ∀ v, ‖v‖ ≤ ‖fderiv ℝ ψ u v‖)
    (h₂ : ∀ u ∈ s, ‖ψ u - c‖ * ‖iteratedFDeriv ℝ 2 ψ u‖ < 1) :
    StrictConvexOn ℝ s fun u ↦ ‖ψ u - c‖ ^ 2 := by
  refine SymplecticGeometry.strictConvexOn_of_deriv2_add_smul_pos hs
    ((hψ.continuousOn.sub continuousOn_const).norm.pow 2) fun x hx y hy hxy t ht ↦ ?_
  set v := y - x
  set p := x + t • v
  have hp : p ∈ s := hs.add_smul_sub_mem hx hy (Ioo_subset_Icc_self ht)
  have hv : v ≠ 0 := sub_ne_zero.2 hxy.symm
  have hℓ : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ x + t • v) v t := fun t ↦ by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hU : ∀ᶠ t' in 𝓝 t, x + t' • v ∈ s :=
    (hℓ t).continuousAt.preimage_mem_nhds (hso.mem_nhds hp)
  -- The curve `γ`, its velocity `D` and its acceleration `D'`, near `t`.
  set γ : ℝ → F := fun t ↦ ψ (x + t • v) - c
  set D : ℝ → F := fun t ↦ fderiv ℝ ψ (x + t • v) v
  set D' : ℝ → F := fun t ↦ fderiv ℝ (fderiv ℝ ψ) (x + t • v) v v
  have hγ : ∀ t, x + t • v ∈ s → HasDerivAt γ (D t) t := fun t ht ↦
    (((hψ.contDiffAt (hso.mem_nhds ht)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      t (hℓ t)).sub_const c
  have hD : ∀ t, x + t • v ∈ s → HasDerivAt D (D' t) t := fun t ht ↦ by
    have h := (((hψ.contDiffAt (hso.mem_nhds ht)).fderiv_right (m := 1) (by norm_num)
      ).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt t (hℓ t)
    simpa using h.clm_apply (hasDerivAt_const t v)
  have hsq : (fun t : ℝ ↦ ‖ψ (x + t • v) - c‖ ^ 2) = fun t ↦ ⟪γ t, γ t⟫ := by
    ext t
    exact (real_inner_self_eq_norm_sq _).symm
  have hd : deriv (fun t ↦ ⟪γ t, γ t⟫) =ᶠ[𝓝 t] fun t ↦ ⟪γ t, D t⟫ + ⟪D t, γ t⟫ :=
    hU.mono fun t ht ↦ ((hγ t ht).inner ℝ (hγ t ht)).deriv
  rw [hsq, Function.iterate_succ_apply, Function.iterate_one, hd.deriv_eq,
    (((hγ t hp).inner ℝ (hD t hp)).fun_add ((hD t hp).inner ℝ (hγ t hp))).deriv]
  simp only [γ, D, D']
  -- The second derivative is `2 ‖Dψ v‖ ^ 2 + 2 ⟪ψ p - c, D²ψ v v⟫`.
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hacc : |⟪ψ p - c, fderiv ℝ (fderiv ℝ ψ) p v v⟫| < ‖v‖ * ‖v‖ := by
    refine (abs_real_inner_le_norm _ _).trans_lt ?_
    calc ‖ψ p - c‖ * ‖fderiv ℝ (fderiv ℝ ψ) p v v‖
        ≤ ‖ψ p - c‖ * (‖fderiv ℝ (fderiv ℝ ψ) p‖ * ‖v‖ * ‖v‖) := by
          gcongr
          exact (fderiv ℝ (fderiv ℝ ψ) p).le_opNorm₂ v v
      _ = ‖ψ p - c‖ * ‖fderiv ℝ (fderiv ℝ ψ) p‖ * (‖v‖ * ‖v‖) := by ring
      _ < 1 * (‖v‖ * ‖v‖) := by
          gcongr
          rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
          exact h₂ p hp
      _ = ‖v‖ * ‖v‖ := one_mul _
  have hvel : ‖v‖ * ‖v‖ ≤ ⟪fderiv ℝ ψ p v, fderiv ℝ ψ p v⟫ := by
    rw [real_inner_self_eq_norm_mul_norm]
    exact mul_self_le_mul_self hv0.le (h₁ p hp v)
  have := neg_abs_le ⟪ψ p - c, fderiv ℝ (fderiv ℝ ψ) p v v⟫
  rw [real_inner_comm (ψ p - c)]
  linarith

/-- A function on `ℝ`, convex on `[x, ∞)` and with a positive right derivative at `x`, tends to
`∞` at `∞`: it lies above its tangent line at `x` there. -/
theorem ConvexOn.tendsto_atTop_of_hasDerivWithinAt_Ioi_pos {f : ℝ → ℝ} {x f' : ℝ}
    (hfc : ConvexOn ℝ (Ici x) f) (hf : HasDerivWithinAt f f' (Ioi x) x) (hf' : 0 < f') :
    Tendsto f atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ <| tendsto_atTop_add_const_left _ (f x) <|
    (tendsto_atTop_add_const_right _ (-x) tendsto_id).const_mul_atTop hf'
  filter_upwards [eventually_gt_atTop x] with y hy
  have h := hfc.le_slope_of_hasDerivWithinAt_Ioi self_mem_Ici hy.le hy hf
  rw [slope_def_field, le_div_iff₀ (sub_pos.2 hy)] at h
  simp only [id, ← sub_eq_add_neg]
  linarith
