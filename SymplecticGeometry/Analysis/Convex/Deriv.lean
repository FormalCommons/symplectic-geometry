/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Strict convexity from second derivatives along lines

A real function on a convex subset `s` of a real vector space, continuous on `s`, is strictly
convex on `s` if, at every point `x ∈ s` and in every direction `v ≠ 0`, the second derivative of
`t ↦ f (x + t • v)` at `0` is positive. This extends Mathlib's `strictConvexOn_of_deriv2_pos` from
`ℝ` to any real topological vector space, by restricting `f` to segments.

As an application, for a `C²` map `ψ` from a real normed space to a real inner product space, the
squared distance `u ↦ ‖ψ u - c‖ ^ 2` to a point `c` is strictly convex on an open convex set where
the differential of `ψ` does not shrink vectors and `‖ψ u - c‖` times the norm of the second
derivative of `ψ` stays below `1`: its second derivative along `v` is
`2 ‖Dψ v‖ ^ 2 + 2 ⟪ψ u - c, D²ψ v v⟫`.

## Main results

* `strictConvexOn_of_deriv2_add_smul_pos`.
* `ContDiffOn.strictConvexOn_norm_sub_sq`.

The first proof adapts that of Tau Ceti's `TauCeti.convexOn_of_hasFDerivAt_gradient` (convexity
from a nonnegative Hessian along segments) to strict convexity, with the second derivative along
each line as hypothesis instead of a Hessian.
-/

public section

open Set Filter Topology
open scoped RealInnerProductSpace

/-- **Strict convexity from second derivatives along lines.** Let `f` be continuous on a convex set
`s` of a real topological vector space. If, for every `x ∈ s` and `v ≠ 0`, the function
`t ↦ f (x + t • v)` has a positive second derivative at `0`, then `f` is strictly convex on `s`. -/
theorem strictConvexOn_of_deriv2_add_smul_pos {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] {s : Set E} {f : E → ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hf'' : ∀ x ∈ s, ∀ v ≠ 0, 0 < deriv^[2] (fun t : ℝ ↦ f (x + t • v)) 0) :
    StrictConvexOn ℝ s f := by
  refine ⟨hs, fun x hx y hy hxy a b ha hb hab ↦ ?_⟩
  -- Restrict `f` to the segment `t ↦ x + t • (y - x)`, `t ∈ [0, 1]`.
  set g : ℝ → ℝ := fun t ↦ f (x + t • (y - x))
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ s := fun t ht ↦
    hs.add_smul_sub_mem hx hy ht
  have hg : StrictConvexOn ℝ (Icc 0 1) g := by
    refine strictConvexOn_of_deriv2_pos (convex_Icc 0 1)
      (hf.comp (by fun_prop) hseg) fun t ht ↦ ?_
    rw [interior_Icc] at ht
    have hv : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
    have key := hf'' _ (hseg t (Ioo_subset_Icc_self ht)) _ hv
    -- The line through `x + t • (y - x)` is `g` shifted by `t`.
    have hshift : (fun u : ℝ ↦ f (x + t • (y - x) + u • (y - x))) = fun u ↦ g (u + t) := by
      ext u
      simp only [g, add_smul, add_assoc, add_comm (t • (y - x))]
    have hd : deriv (fun u ↦ g (u + t)) = fun u ↦ deriv g (u + t) := by
      ext u
      exact deriv_comp_add_const (f := g) (a := t) (x := u)
    rw [hshift, Function.iterate_succ_apply, Function.iterate_one, hd,
      deriv_comp_add_const, zero_add] at key
    simpa using key
  have h := hg.2 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    (by simp) ha hb hab
  have hab' : a = 1 - b := by linarith
  simp only [g, smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul,
    add_sub_cancel] at h
  convert h using 2
  rw [hab', sub_smul, one_smul, smul_sub]
  abel

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
  refine strictConvexOn_of_deriv2_add_smul_pos hs
    ((hψ.continuousOn.sub continuousOn_const).norm.pow 2) fun p hp v hv ↦ ?_
  have hℓ : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ p + t • v) v t := fun t ↦ by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hU : ∀ᶠ t in 𝓝 (0 : ℝ), p + t • v ∈ s :=
    (hℓ 0).continuousAt.preimage_mem_nhds (by simpa using hso.mem_nhds hp)
  -- The curve `γ`, its velocity `D` and its acceleration `D'`, near `t = 0`.
  set γ : ℝ → F := fun t ↦ ψ (p + t • v) - c
  set D : ℝ → F := fun t ↦ fderiv ℝ ψ (p + t • v) v
  set D' : ℝ → F := fun t ↦ fderiv ℝ (fderiv ℝ ψ) (p + t • v) v v
  have hγ : ∀ t, p + t • v ∈ s → HasDerivAt γ (D t) t := fun t ht ↦
    (((hψ.contDiffAt (hso.mem_nhds ht)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      t (hℓ t)).sub_const c
  have hD : ∀ t, p + t • v ∈ s → HasDerivAt D (D' t) t := fun t ht ↦ by
    have h := (((hψ.contDiffAt (hso.mem_nhds ht)).fderiv_right (m := 1) (by norm_num)
      ).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt t (hℓ t)
    simpa using h.clm_apply (hasDerivAt_const t v)
  have hsq : (fun t : ℝ ↦ ‖ψ (p + t • v) - c‖ ^ 2) = fun t ↦ ⟪γ t, γ t⟫ := by
    ext t
    exact (real_inner_self_eq_norm_sq _).symm
  have hd : deriv (fun t ↦ ⟪γ t, γ t⟫) =ᶠ[𝓝 0] fun t ↦ ⟪γ t, D t⟫ + ⟪D t, γ t⟫ :=
    hU.mono fun t ht ↦ ((hγ t ht).inner ℝ (hγ t ht)).deriv
  have hp0 : p + (0 : ℝ) • v ∈ s := by simpa using hp
  rw [hsq, Function.iterate_succ_apply, Function.iterate_one, hd.deriv_eq,
    (((hγ 0 hp0).inner ℝ (hD 0 hp0)).fun_add ((hD 0 hp0).inner ℝ (hγ 0 hp0))).deriv]
  simp only [γ, D, D', zero_smul, add_zero]
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
