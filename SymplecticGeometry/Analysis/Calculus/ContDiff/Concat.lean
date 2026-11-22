/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Concatenation of curves at double speed

For `Z₁ Z₂ : ℝ → E`, `SymplecticGeometry.curveTrans Z₁ Z₂` is the curve equal to `Z₁ (2 * s)`
for `s ≤ 1 / 2` and to `Z₂ (2 * s - 1)` after: the parametrization of Mathlib's `Path.trans`,
on all of `ℝ`. Near every time other than `1 / 2` it agrees with one of the two rescaled curves
(`curveTrans_eventuallyEq_left`, `curveTrans_eventuallyEq_right`), so it has their derivatives
there, doubled (`HasDerivAt.curveTrans_of_lt_half`, `HasDerivAt.curveTrans_of_half_lt`). If
`Z₁` is constant near `1`, `Z₂` constant near `0`, and `Z₁ 1 = Z₂ 0`, the curve is constant near
`1 / 2` (`curveTrans_eventuallyEq_half`), hence `C^n` when `Z₁` and `Z₂` are
(`ContDiff.curveTrans`). It is constant near `0` when `Z₁` is, and near `1` when `Z₂` is.

Tau Ceti's `TauCeti.curveConcat` and `ContMDiff.curveConcat` do the same for the parametrization
`3 * s`, `3 * s - 2`, which rests between `1 / 3` and `2 / 3` and does not match
`Path.trans`.
-/

public section

namespace SymplecticGeometry

open Filter Topology

variable {E : Type*}

/-- The concatenation of two curves `Z₁ Z₂ : ℝ → E` at double speed: `Z₁ (2 * s)` for
`s ≤ 1 / 2`, then `Z₂ (2 * s - 1)`, as in `Path.trans`. -/
noncomputable def curveTrans (Z₁ Z₂ : ℝ → E) (s : ℝ) : E :=
  if s ≤ 1 / 2 then Z₁ (2 * s) else Z₂ (2 * s - 1)

theorem curveTrans_def (Z₁ Z₂ : ℝ → E) (s : ℝ) :
    curveTrans Z₁ Z₂ s = if s ≤ 1 / 2 then Z₁ (2 * s) else Z₂ (2 * s - 1) :=
  (rfl)

variable {Z₁ Z₂ : ℝ → E} {s t : ℝ}

theorem curveTrans_of_le_half (hs : s ≤ 1 / 2) : curveTrans Z₁ Z₂ s = Z₁ (2 * s) := by
  rw [curveTrans_def, ite_eq_left hs]

theorem curveTrans_of_half_lt (hs : 1 / 2 < s) : curveTrans Z₁ Z₂ s = Z₂ (2 * s - 1) := by
  rw [curveTrans_def, ite_eq_right (not_le.2 hs)]

@[simp]
theorem curveTrans_zero : curveTrans Z₁ Z₂ 0 = Z₁ 0 := by
  rw [curveTrans_of_le_half (by norm_num), mul_zero]

@[simp]
theorem curveTrans_one : curveTrans Z₁ Z₂ 1 = Z₂ 1 := by
  rw [curveTrans_of_half_lt (by norm_num)]
  norm_num

/-- Before time `1 / 2`, the concatenation agrees near `t` with `Z₁` at double speed. -/
theorem curveTrans_eventuallyEq_left (ht : t < 1 / 2) :
    curveTrans Z₁ Z₂ =ᶠ[𝓝 t] fun s ↦ Z₁ (2 * s) := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact curveTrans_of_le_half hs.le

/-- After time `1 / 2`, the concatenation agrees near `t` with `Z₂` at double speed. -/
theorem curveTrans_eventuallyEq_right (ht : 1 / 2 < t) :
    curveTrans Z₁ Z₂ =ᶠ[𝓝 t] fun s ↦ Z₂ (2 * s - 1) := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact curveTrans_of_half_lt hs

/-- The concatenation is constant near `0` when `Z₁` is. -/
theorem curveTrans_eventuallyEq_zero (h : Z₁ =ᶠ[𝓝 0] fun _ ↦ Z₁ 0) :
    curveTrans Z₁ Z₂ =ᶠ[𝓝 0] fun _ ↦ curveTrans Z₁ Z₂ 0 := by
  have ht : Tendsto (fun s : ℝ ↦ 2 * s) (𝓝 0) (𝓝 0) :=
    (by fun_prop : Continuous fun s : ℝ ↦ 2 * s).tendsto' 0 0 (by norm_num)
  filter_upwards [curveTrans_eventuallyEq_left (Z₁ := Z₁) (Z₂ := Z₂)
    (by norm_num : (0 : ℝ) < 1 / 2), ht.eventually h] with s hs hs'
  rw [hs, hs', curveTrans_zero]

/-- The concatenation is constant near `1` when `Z₂` is. -/
theorem curveTrans_eventuallyEq_one (h : Z₂ =ᶠ[𝓝 1] fun _ ↦ Z₂ 1) :
    curveTrans Z₁ Z₂ =ᶠ[𝓝 1] fun _ ↦ curveTrans Z₁ Z₂ 1 := by
  have ht : Tendsto (fun s : ℝ ↦ 2 * s - 1) (𝓝 1) (𝓝 1) :=
    (by fun_prop : Continuous fun s : ℝ ↦ 2 * s - 1).tendsto' 1 1 (by norm_num)
  filter_upwards [curveTrans_eventuallyEq_right (Z₁ := Z₁) (Z₂ := Z₂)
    (by norm_num : (1 / 2 : ℝ) < 1), ht.eventually h] with s hs hs'
  rw [hs, hs', curveTrans_one]

/-- If `Z₁` is constant near `1`, `Z₂` constant near `0`, and `Z₁ 1 = Z₂ 0`, the concatenation is
constant, equal to `Z₁ 1`, near `1 / 2`. -/
theorem curveTrans_eventuallyEq_half (h₁ : Z₁ =ᶠ[𝓝 1] fun _ ↦ Z₁ 1)
    (h₂ : Z₂ =ᶠ[𝓝 0] fun _ ↦ Z₂ 0) (h₁₂ : Z₁ 1 = Z₂ 0) :
    curveTrans Z₁ Z₂ =ᶠ[𝓝 (1 / 2)] fun _ ↦ Z₁ 1 := by
  have t₁ : Tendsto (fun s : ℝ ↦ 2 * s) (𝓝 (1 / 2)) (𝓝 1) :=
    (by fun_prop : Continuous fun s : ℝ ↦ 2 * s).tendsto' _ _ (by norm_num)
  have t₂ : Tendsto (fun s : ℝ ↦ 2 * s - 1) (𝓝 (1 / 2)) (𝓝 0) :=
    (by fun_prop : Continuous fun s : ℝ ↦ 2 * s - 1).tendsto' _ _ (by norm_num)
  filter_upwards [t₁.eventually h₁, t₂.eventually h₂] with s hs₁ hs₂
  rcases le_or_gt s (1 / 2) with h | h
  · rw [curveTrans_of_le_half h, hs₁]
  · rw [curveTrans_of_half_lt h, hs₂, h₁₂]

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The concatenation of two `C^n` curves, the first constant near `1`, the second constant near
`0`, with `Z₁ 1 = Z₂ 0`, is `C^n`. -/
theorem _root_.ContDiff.curveTrans {n : WithTop ℕ∞} (hZ₁ : ContDiff ℝ n Z₁)
    (hZ₂ : ContDiff ℝ n Z₂) (h₁ : Z₁ =ᶠ[𝓝 1] fun _ ↦ Z₁ 1) (h₂ : Z₂ =ᶠ[𝓝 0] fun _ ↦ Z₂ 0)
    (h₁₂ : Z₁ 1 = Z₂ 0) : ContDiff ℝ n (curveTrans Z₁ Z₂) := by
  refine contDiff_iff_contDiffAt.2 fun t ↦ ?_
  rcases lt_trichotomy t (1 / 2) with h | rfl | h
  · exact (hZ₁.comp (contDiff_const.mul contDiff_id)).contDiffAt.congr_of_eventuallyEq
      (curveTrans_eventuallyEq_left h)
  · exact contDiffAt_const.congr_of_eventuallyEq (curveTrans_eventuallyEq_half h₁ h₂ h₁₂)
  · exact (hZ₂.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).contDiffAt
      |>.congr_of_eventuallyEq (curveTrans_eventuallyEq_right h)

/-- Before time `1 / 2`, the concatenation has twice the derivative of `Z₁` at `2 * t`. -/
theorem _root_.HasDerivAt.curveTrans_of_lt_half {Z₁' : E} (hZ₁ : HasDerivAt Z₁ Z₁' (2 * t))
    (ht : t < 1 / 2) : HasDerivAt (curveTrans Z₁ Z₂) ((2 : ℝ) • Z₁') t := by
  have hd := hZ₁.scomp t ((hasDerivAt_id' t).const_mul 2)
  rw [mul_one] at hd
  exact hd.congr_of_eventuallyEq (curveTrans_eventuallyEq_left ht)

/-- After time `1 / 2`, the concatenation has twice the derivative of `Z₂` at `2 * t - 1`. -/
theorem _root_.HasDerivAt.curveTrans_of_half_lt {Z₂' : E} (hZ₂ : HasDerivAt Z₂ Z₂' (2 * t - 1))
    (ht : 1 / 2 < t) : HasDerivAt (curveTrans Z₁ Z₂) ((2 : ℝ) • Z₂') t := by
  have hd := hZ₂.scomp t (((hasDerivAt_id' t).const_mul 2).sub_const 1)
  rw [mul_one] at hd
  exact hd.congr_of_eventuallyEq (curveTrans_eventuallyEq_right ht)

end SymplecticGeometry

end
