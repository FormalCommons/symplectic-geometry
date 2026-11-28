/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Basic
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Wedge.Basic
import SymplecticGeometry.Topology.Algebra.Module.Alternating.TopDegree
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Covector

/-!
# Wedge powers of a two-form

Let `ω` be a real alternating two-form and `γ` a one-form on a real vector space `E` of dimension
`2 n + 2`, and let `v ∈ E` with `γ(v) = 0`. Then the top-degree form `γ ∧ ι_v ω ∧ ω ^ n` is zero.
Indeed, `γ ∧ ω ^ (n + 1)` has degree `2 n + 3 > dim E`, so it vanishes, and so does its contraction
with `v`. By Tau Ceti's homotopy formula for a covector
(`ContinuousAlternatingMap.curryLeftTopological_pairedWedge_add_pairedWedge_curryLeftTopological`)
this contraction is `γ(v) ω ^ (n + 1) - γ ∧ ι_v (ω ^ (n + 1))`, and the power rule
`ι_v (ω ^ (n + 1)) = (n + 1) ι_v ω ∧ ω ^ n`
(`ContinuousAlternatingMap.wedgePow_succ_apply_vecCons`) gives the claim, since
`γ(v) = 0` and `n + 1 ≠ 0`. The power rule changes the degree `2 n + 1` into `1 + 2 n`, which
`ContinuousAlternatingMap.pairedWedge_apply_of_right_eq_smul_cast` handles.

The file also evaluates a wedge power of a two-form on a pair followed by vectors that the
first vector of the pair pairs to zero with.

## Main results

* `ContinuousAlternatingMap.pairedWedge_curryLeftTopological_wedgePow_eq_zero`: in dimension
  `2 n + 2`, `γ ∧ ι_v ω ∧ ω ^ n = 0` when `γ(v) = 0`.
* `ContinuousAlternatingMap.wedgePow_compContinuousLinearMap_eq_det_smul`: in dimension `2 n`,
  `(A^* ω) ^ n = det A • ω ^ n`, by Tau Ceti's
  `ContinuousAlternatingMap.wedgePow_compContinuousLinearMap` and
  `ContinuousAlternatingMap.compContinuousLinearMap_eq_det_smul`, since `ω ^ n` has top degree.
* `ContinuousAlternatingMap.wedgePow_succ_apply_append_of_eq_zero`: if `φ(u 0, ·)` vanishes on
  `w : Fin (2 * k) → E`, then `φ ^ (k + 1)` takes the value `(k + 1) φ(u) φ ^ k (w)` on the
  concatenation of the pair `u` and `w`, by Tau Ceti's
  `ContinuousAlternatingMap.wedgePow_succ_apply_vecCons_vecCons`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  proof of Theorem 5.1.6, and §6.4 (the computation behind (6.4.3)–(6.4.4)).
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
  -- Contracting with `v`: `ι_v (γ ∧ ω ^ (n + 1)) + γ ∧ ι_v (ω ^ (n + 1)) = γ(v) ω ^ (n + 1)`,
  -- and `γ ∧ ω ^ (n + 1) = 0`, `γ(v) = 0`.
  have h1 (w : Fin (1 + (2 * n + 1)) → E) :
      pairedWedge (k := 1) (l := 2 * n + 1) mul mul.continuous₂ γ
        (curryLeftTopological (n := 2 * n + 1) (wedgePow ω (n + 1)) v) w = 0 := by
    have key := curryLeftTopological_pairedWedge_add_pairedWedge_curryLeftTopological γ
      (wedgePow ω (n + 1)) v w
    rwa [h0, curryLeftTopological_apply_apply, coe_zero, Pi.zero_apply, zero_add, hγ,
      zero_mul] at key
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

/-- **Top wedge power of a pullback.** On a real vector space of dimension `2 n`, the `n`-th
wedge power of the pullback of a two-form `ω` along an endomorphism `A` is `det A` times the
`n`-th wedge power of `ω`. -/
theorem wedgePow_compContinuousLinearMap_eq_det_smul {n : ℕ}
    (hE : Module.finrank ℝ E = 2 * n) (ω : E [⋀^Fin 2]→L[ℝ] ℝ) (A : E →L[ℝ] E) :
    (ω.compContinuousLinearMap A).wedgePow n = A.toLinearMap.det • ω.wedgePow n := by
  by_cases hfin : Module.Finite ℝ E
  · rw [← wedgePow_compContinuousLinearMap,
      compContinuousLinearMap_eq_det_smul _ (Module.finBasisOfFinrankEq ℝ E hE)]
  · -- Otherwise `finrank ℝ E = 0`, so `n = 0`, and `det A = 1`.
    obtain rfl : n = 0 := by rw [Module.finrank_of_not_finite hfin] at hE; omega
    rw [LinearMap.det_eq_one_of_not_module_finite hfin, one_smul]
    ext v
    exact (wedgePow_zero_apply _ v).trans (wedgePow_zero_apply _ v).symm

/-- **Wedge power on a block orthogonal to a pair.** For a two-form `φ`, a pair `u` and vectors
`w : Fin (2 * k) → E` with `φ(u 0, w j) = 0` for all `j`, the `(k + 1)`-st wedge power of `φ`
takes the value `(k + 1) φ(u) φ ^ k (w)` on the concatenation of `u` and `w`. -/
theorem wedgePow_succ_apply_append_of_eq_zero (φ : E [⋀^Fin 2]→L[ℝ] ℝ) {k : ℕ}
    {u : Fin 2 → E} {w : Fin (2 * k) → E} (h : ∀ j, φ ![u 0, w j] = 0) :
    φ.wedgePow (k + 1) (Fin.append u w ∘ Fin.cast (by omega)) =
      (k + 1) * φ u * φ.wedgePow k w := by
  have hu : Fin.append u w ∘ Fin.cast (by omega) =
      Matrix.vecCons (u 0) (Matrix.vecCons (u 1) w) := by
    ext i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ ?_) i) i
    · exact (congrArg (Fin.append u w) (Fin.ext rfl)).trans (Fin.append_left u w 0)
    · exact (congrArg (Fin.append u w) (Fin.ext rfl)).trans (Fin.append_left u w 1)
    · exact (congrArg (Fin.append u w) (Fin.ext (by simp; omega))).trans
        (Fin.append_right u w j)
  rw [hu, wedgePow_succ_apply_vecCons_vecCons φ k (u 1) h, ← mul_assoc]
  congr 2
  exact congrArg φ (by ext i; fin_cases i <;> simp)

end ContinuousAlternatingMap

end
