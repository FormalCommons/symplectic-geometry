/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.Differentiable
public import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.Growth
import Mathlib.Analysis.Asymptotics.Lemmas
import SymplecticGeometry.Analysis.SpecialFunctions.Log.Unbounded

/-!
# The derivative of a bounded one-variable semialgebraic function near `0⁺`

Let `f` be a real function of one variable that is semialgebraic and bounded on the points
`![t]`, `0 < t < ε₀`. Then the derivative of `t ↦ f ![t]` is bounded by a multiple of
`t ^ (p - 1)` near `0⁺`, for some `p > 0`
(`TauCeti.IsSemialgebraicOn.exists_abs_deriv_le_mul_rpow`). So the derivative may blow up at
`0`, but strictly slower than `t⁻¹`.

The proof: by `TauCeti.IsSemialgebraicOn.exists_pos_differentiableOn_Ioo` the function is
differentiable on some `(0, ε)` with a semialgebraic derivative `D`. If `D` vanishes near
`0⁺` there is nothing to show. Otherwise `D t / t ^ r → a ≠ 0` for some rational `r`
(`TauCeti.IsSemialgebraicOn.exists_tendsto_div_rpow_nhdsGT`), and `p = r + 1` works once
`r > -1`, which holds for every bounded function whose derivative behaves so
(`Real.neg_one_lt_of_tendsto_deriv_div_rpow`). The bound `|D t| ≤ C * t ^ r` near `0⁺` then
follows from `Asymptotics.isBigO_of_div_tendsto_nhds`.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Section 2.6.
* L. van den Dries, *Tame Topology and o-minimal Structures*, Cambridge University Press, 1998,
  Chapter 7.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- Let `f` be a real function of one variable that is semialgebraic and bounded on the points
`![t]`, `0 < t < ε₀`. Then near `0⁺` the derivative of `t ↦ f ![t]` is bounded by
`C * t ^ (p - 1)`, for some `p > 0` and some `C`. -/
theorem IsSemialgebraicOn.exists_abs_deriv_le_mul_rpow {f : (Fin 1 → ℝ) → ℝ}
    {s : Set (Fin 1 → ℝ)} (hf : IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s) {ε₀ M : ℝ}
    (hε₀ : 0 < ε₀) (hs : ∀ t ∈ Ioo 0 ε₀, ![t] ∈ s) (hM : ∀ t ∈ Ioo 0 ε₀, |f ![t]| ≤ M) :
    ∃ p : ℝ, 0 < p ∧ ∃ C ε : ℝ, 0 < ε ∧
      ∀ t ∈ Ioo 0 ε, |_root_.deriv (fun t ↦ f ![t]) t| ≤ C * t ^ (p - 1) := by
  obtain ⟨ε₁, hε₁, hd, hds⟩ := hf.exists_pos_differentiableOn_Ioo hε₀ hs
  set D := _root_.deriv (fun t ↦ f ![t])
  by_cases hne : ∃ᶠ t in 𝓝[>] 0, D t ≠ 0
  swap
  · -- `D` vanishes on some interval `(0, ε)`.
    obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (not_frequently.1 hne)
    refine ⟨1, one_pos, 0, ε, hε, fun t ht ↦ ?_⟩
    simp [show D t = 0 by simpa using hsub ht]
  obtain ⟨q, a, ha, hlim⟩ := hds.exists_tendsto_div_rpow_nhdsGT
    (eventually_of_mem (Ioo_mem_nhdsGT hε₁) fun t ht ↦ by simpa using ht) (by simpa using hne)
  simp only [Matrix.cons_val_zero] at hlim
  set r : ℝ := (q : ℝ)
  have hr : -1 < r := Real.neg_one_lt_of_tendsto_deriv_div_rpow (lt_min hε₀ hε₁)
    (hd.mono (Ioo_subset_Ioo_right (min_le_right _ _)))
    (fun t ht ↦ hM t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩) ha hlim
  -- `D t / t ^ r` converges, so `D t = O(t ^ r)` near `0⁺`.
  obtain ⟨C, hC⟩ := (Asymptotics.isBigO_of_div_tendsto_nhds (eventually_mem_nhdsWithin.mono
    fun t (ht : 0 < t) h ↦ absurd h (Real.rpow_pos_of_pos ht r).ne') a hlim).bound
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hC
  refine ⟨r + 1, by linarith, C, ε, hε, fun t ht ↦ ?_⟩
  have h : ‖D t‖ ≤ C * ‖t ^ r‖ := hsub ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht.1 r)] at h
  rwa [add_sub_cancel_right]

end TauCeti

end
