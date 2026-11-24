/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Wedge.Basic
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Contracting a wedge power of a two-form in top degree

Let `ω` be a real alternating two-form and `γ` a one-form on a real vector space `E` of dimension
`2 n + 2`, and let `v ∈ E` with `γ(v) = 0`. Then the top-degree form `γ ∧ ι_v ω ∧ ω ^ n` is zero.
Indeed, `γ ∧ ω ^ (n + 1)` has degree `2 n + 3 > dim E`, so it vanishes, and so does its contraction
with `v`. Since contraction is an antiderivation
(`ContinuousAlternatingMap.curryLeftTopological_pairedWedge`) this contraction is
`γ(v) ω ^ (n + 1) - γ ∧ ι_v (ω ^ (n + 1))`, and the power rule
`ι_v (ω ^ (n + 1)) = (n + 1) ι_v ω ∧ ω ^ n`
(`ContinuousAlternatingMap.wedgePow_succ_apply_vecCons`) gives the claim, since
`γ(v) = 0` and `n + 1 ≠ 0`. The power rule changes the degree `2 n + 1` into `1 + 2 n`, which
`ContinuousAlternatingMap.pairedWedge_apply_of_right_eq_smul_cast` handles.

## Main results

* `ContinuousAlternatingMap.pairedWedge_curryLeftTopological_wedgePow_eq_zero`: in dimension
  `2 n + 2`, `γ ∧ ι_v ω ∧ ω ^ n = 0` when `γ(v) = 0`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  proof of Theorem 5.1.6.
-/

public section

open TauCeti

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- **Contracting a wedge power in top degree.** On a real vector space of dimension `2 n + 2`,
for a two-form `ω`, a one-form `γ` and a vector `v` with `γ(v) = 0`, the top-degree form
`γ ∧ (ι_v ω ∧ ω ^ n)` is zero. -/
theorem pairedWedge_curryLeftTopological_wedgePow_eq_zero [Module.Finite ℝ E] {n : ℕ}
    (hE : Module.finrank ℝ E = 2 * n + 2) (γ : E [⋀^Fin 1]→L[ℝ] ℝ) (ω : E [⋀^Fin 2]→L[ℝ] ℝ)
    (v : E) (hγ : γ ![v] = 0) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ γ
      (pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (curryLeftTopological (n := 1) ω v) (wedgePow ω n)) = 0 := by
  set mul := ContinuousLinearMap.mul ℝ ℝ
  -- `γ ∧ ω ^ (n + 1)` has degree `2 n + 3 > dim E`, so it vanishes.
  have h0 : pairedWedge (k := 0 + 1) (l := 2 * n + 1 + 1) mul mul.continuous₂ γ
      (wedgePow ω (n + 1)) = 0 := eq_zero_of_finrank_lt _ (by simp; omega)
  -- Contracting with `v`: `0 = γ(v) ω ^ (n + 1) - γ ∧ ι_v (ω ^ (n + 1))`, and `γ(v) = 0`.
  have h1 (w : Fin (1 + (2 * n + 1)) → E) :
      pairedWedge (k := 1) (l := 2 * n + 1) mul mul.continuous₂ γ
        (curryLeftTopological (n := 2 * n + 1) (wedgePow ω (n + 1)) v) w = 0 := by
    have key := curryLeftTopological_pairedWedge (k := 0) (l := 2 * n + 1) mul mul.continuous₂
      γ (wedgePow ω (n + 1)) v w
    have hγv : curryLeftTopological (n := 0) γ v 0 = 0 := by
      rw [curryLeftTopological_apply_apply, ← hγ]
      congr 1
      ext i
      fin_cases i
      rfl
    rw [h0, pairedWedge_apply_zero_left, hγv] at key
    simpa using key.symm
  -- The power rule `ι_v (ω ^ (n + 1)) = (n + 1) ι_v ω ∧ ω ^ n`.
  ext w
  have h2 := pairedWedge_apply_of_right_eq_smul_cast (k := 1) mul mul.continuous₂
    (show 1 + 2 * n = 2 * n + 1 by omega) (A := curryLeftTopological (wedgePow ω (n + 1)) v)
    ((n : ℝ) + 1) (fun u ↦ by
      rw [curryLeftTopological_apply_apply, wedgePow_succ_apply_vecCons, smul_eq_mul]) γ
    (w ∘ Fin.cast (by omega))
  rw [h1] at h2
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  simpa [hn, Function.comp_def] using h2.symm

end ContinuousAlternatingMap

end
