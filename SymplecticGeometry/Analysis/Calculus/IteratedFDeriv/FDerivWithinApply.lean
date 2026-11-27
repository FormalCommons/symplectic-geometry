/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# Iterated derivatives of the derivative as a function of point and direction

For `g : E → F` and `s : Set E`, consider the map `(z, v) ↦ fderivWithin 𝕜 g s z v` on
`s ×ˢ univ`. In a chart, this is the second component of the tangent map of `g`. This file bounds
its iterated derivatives at `(z, v)` by those of `g` at `z` of one order more, with a factor
`1 + ‖v‖`.

## Main results

* `norm_iteratedFDerivWithin_comp_fst_le`: the iterated derivatives of `f ∘ Prod.fst` within
  `s ×ˢ univ` are bounded by those of `f` within `s`. This is the within-a-set form of Tau Ceti's
  `Prod.norm_iteratedFDeriv_comp_fst`.
* `norm_iteratedFDerivWithin_fderivWithin_apply_le`: for `g` of class `C^{j+1}` on a set `s`
  of unique differentiability and `z ∈ s`, the `j`-th derivative of `(z, v) ↦ Dg(z) v` within
  `s ×ˢ univ` at `(z, v)` has norm at most
  `(1 + ‖v‖) * ∑ i ∈ range (j + 1), j.choose i * ‖D^{i+1} g(z)‖`.

The proof writes the map as `q ↦ (Dg ∘ Prod.fst) q (Prod.snd q)` and applies Mathlib's Leibniz
bound `norm_iteratedFDerivWithin_clm_apply`; the derivatives of `Prod.snd` are bounded by Tau
Ceti's `TauCeti.norm_iteratedFDeriv_snd_le_one`.
-/

public section

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The iterated derivatives of `f ∘ Prod.fst` within `s ×ˢ univ` at `p`, for `f` of class `C^n`
on a set `s` of unique differentiability and `p.1 ∈ s`, are bounded, up to order `n`, by those of
`f` within `s` at `p.1`. -/
theorem norm_iteratedFDerivWithin_comp_fst_le {f : E → F} {s : Set E} {n : WithTop ℕ∞}
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) {i : ℕ} (hi : i ≤ n) {p : E × G}
    (hp : p.1 ∈ s) :
    ‖iteratedFDerivWithin 𝕜 i (f ∘ Prod.fst) (s ×ˢ univ) p‖ ≤
      ‖iteratedFDerivWithin 𝕜 i f s p.1‖ := by
  have hpre : (ContinuousLinearMap.fst 𝕜 E G) ⁻¹' s = s ×ˢ univ := by
    ext; simp
  have hS : UniqueDiffOn 𝕜 ((ContinuousLinearMap.fst 𝕜 E G) ⁻¹' s) :=
    hpre ▸ hs.prod uniqueDiffOn_univ
  rw [← ContinuousLinearMap.coe_fst' (R := 𝕜) (M₂ := G), ← hpre,
    ContinuousLinearMap.iteratedFDerivWithin_comp_right _ hf hs hS hp hi]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
    fun _ _ ↦ ContinuousLinearMap.norm_fst_le 𝕜 E G

/-- The iterated derivatives of `(z, v) ↦ Dg(z) v` within `s ×ˢ univ` at `(z, v)`, for `g` of
class `C^{j+1}` on a set `s` of unique differentiability and `z ∈ s`, are bounded by those of `g`
at `z` of one order more:
`‖Dʲ (q ↦ Dg(q.1) q.2) (z, v)‖ ≤ (1 + ‖v‖) * ∑_{i ≤ j} (j choose i) ‖D^{i+1} g(z)‖`. -/
theorem norm_iteratedFDerivWithin_fderivWithin_apply_le {g : E → F} {s : Set E}
    (hs : UniqueDiffOn 𝕜 s) {j : ℕ} (hg : ContDiffOn 𝕜 (j + 1) g s) {z : E} (hz : z ∈ s)
    (v : E) :
    ‖iteratedFDerivWithin 𝕜 j (fun q : E × E ↦ fderivWithin 𝕜 g s q.1 q.2) (s ×ˢ univ) (z, v)‖ ≤
      (1 + ‖v‖) * ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 (i + 1) g s z‖ := by
  have hS : UniqueDiffOn 𝕜 (s ×ˢ (univ : Set E)) := hs.prod uniqueDiffOn_univ
  have hzS : (z, v) ∈ s ×ˢ (univ : Set E) := ⟨hz, mem_univ v⟩
  have hDg : ContDiffOn 𝕜 j (fderivWithin 𝕜 g s) s := hg.fderivWithin hs le_rfl
  have hA : ContDiffOn 𝕜 j (fderivWithin 𝕜 g s ∘ Prod.fst) (s ×ˢ (univ : Set E)) :=
    hDg.comp contDiffOn_fst fun _ hq ↦ hq.1
  -- Derivatives of the first factor: those of `Dg` at `z`, hence of `g` of one order more.
  have hAi (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 g s ∘ Prod.fst) (s ×ˢ (univ : Set E)) (z, v)‖ ≤
        ‖iteratedFDerivWithin 𝕜 (i + 1) g s z‖ :=
    (norm_iteratedFDerivWithin_comp_fst_le hDg hs (by exact_mod_cast hi) hz).trans_eq
      (norm_iteratedFDerivWithin_fderivWithin hs hz)
  -- Derivatives of the second factor: `v` at order zero, then at most one.
  have hBk (k : ℕ) :
      ‖iteratedFDerivWithin 𝕜 k (Prod.snd : E × E → E) (s ×ˢ univ) (z, v)‖ ≤ 1 + ‖v‖ := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hS (contDiff_snd.contDiffAt (n := k)) hzS]
    rcases k with _ | k
    · simp
    · exact (TauCeti.norm_iteratedFDeriv_snd_le_one (Nat.succ_pos k) (z, v)).trans
        (le_add_of_nonneg_right (norm_nonneg v))
  refine (norm_iteratedFDerivWithin_clm_apply hA contDiffOn_snd hS hzS le_rfl).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hi : i ≤ j := Finset.mem_range_succ_iff.mp hi
  calc _ ≤ (j.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 (i + 1) g s z‖ * (1 + ‖v‖) := by
        gcongr
        · exact hAi i hi
        · exact hBk _
    _ = _ := by ring
