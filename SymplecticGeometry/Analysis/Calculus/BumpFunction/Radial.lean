/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Radial smooth cut-offs on a real inner product space

For `0 ≤ a < b` there is a function `h : ℝ → ℝ` with values in `[0, 1]`, equal to `1` on
`[-a, a]` and to `0` outside `[-b, b]`, such that `z ↦ h ‖z‖` is smooth on any real inner
product space (`SymplecticGeometry.exists_contDiff_norm_cutoff`). It is
`t ↦ Real.smoothTransition ((b² - t²) / (b² - a²))`, which is smooth in `‖z‖²`. Being a
function of the norm, it is invariant under every map that preserves the norm, which Mathlib's
`ContDiffBump`, built from a chosen `ContDiffBumpBase`, is not known to be.

The profile is that of Tau Ceti's private `smoothTransition_radial_cutoff`
(`TauCeti/Analysis/Calculus/BumpFunction/Cutoff.lean`), centred at `0`.
-/

public section

open Set
open scoped ContDiff

namespace SymplecticGeometry

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For `0 ≤ a < b`, a function `h : ℝ → ℝ` with values in `[0, 1]`, equal to `1` where
`|t| ≤ a` and to `0` where `b < |t|`, such that `z ↦ h ‖z‖` is smooth on the real inner product
space `V`. -/
theorem exists_contDiff_norm_cutoff {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ (fun z : V ↦ h ‖z‖) ∧ (∀ t, h t ∈ Icc 0 1) ∧
      (∀ t, |t| ≤ a → h t = 1) ∧ ∀ t, b < |t| → h t = 0 := by
  have hD : 0 < b ^ 2 - a ^ 2 := by nlinarith
  refine ⟨fun t ↦ Real.smoothTransition ((b ^ 2 - t ^ 2) / (b ^ 2 - a ^ 2)),
    Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _),
    fun t ↦ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    fun t ht ↦ Real.smoothTransition.one_of_one_le ?_,
    fun t ht ↦ Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ?_ hD.le)⟩
  · rw [le_div_iff₀ hD, one_mul, ← sq_abs t]
    nlinarith [abs_nonneg t]
  · rw [← sq_abs t]
    nlinarith

end SymplecticGeometry

end
