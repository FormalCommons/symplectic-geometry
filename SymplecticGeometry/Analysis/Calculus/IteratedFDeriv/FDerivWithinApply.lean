/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.TangentCone.Prod
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# Iterated derivatives of the derivative as a function of point and direction

For `g : E → F` and `s : Set E`, consider the map `(z, v) ↦ fderivWithin 𝕜 g s z v` on
`s ×ˢ univ`. In a chart, this is the second component of the tangent map of `g`. This file bounds
its iterated derivatives at `(z, v)` by those of `g` at `z` of one order more, with a factor
`1 + ‖v‖`.

## Main results

* `norm_iteratedFDerivWithin_fderivWithin_apply_le`: for `g` of class `C^{j+1}` on a set `s`
  of unique differentiability and `z ∈ s`, the `j`-th derivative of `(z, v) ↦ Dg(z) v` within
  `s ×ˢ univ` at `(z, v)` has norm at most
  `(1 + ‖v‖) * ∑ i ∈ range (j + 1), j.choose i * ‖D^{i+1} g(z)‖`.
* `norm_iteratedFDerivWithin_comp_fst_sub_le`,
  `norm_iteratedFDerivWithin_fderivWithin_apply_sub_le`: the same bounds for the difference of
  two such maps, by the differences of the derivatives of `f₁` and `f₂`, or of `g₁` and `g₂`.

The proof writes the map as `q ↦ (Dg ∘ Prod.fst) q (Prod.snd q)` and applies Mathlib's Leibniz
bound `norm_iteratedFDerivWithin_clm_apply`; the derivatives of `Prod.snd` are bounded by Tau
Ceti's `TauCeti.norm_iteratedFDeriv_snd_le_one`.
-/

public section

open Set

namespace SymplecticGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

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
    (Prod.norm_iteratedFDerivWithin_comp_fst hDg hs (by exact_mod_cast hi) hz).le.trans_eq
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

/-- The iterated derivatives of `f₁ ∘ Prod.fst - f₂ ∘ Prod.fst` within `s ×ˢ univ` at `p`, for
`f₁` and `f₂` of class `C^n` on a set `s` of unique differentiability and `p.1 ∈ s`, are bounded,
up to order `n`, by those of `f₁ - f₂` within `s` at `p.1`. -/
theorem norm_iteratedFDerivWithin_comp_fst_sub_le {f₁ f₂ : E → F} {s : Set E} {n : WithTop ℕ∞}
    (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s) (hs : UniqueDiffOn 𝕜 s) {i : ℕ}
    (hi : i ≤ n) {p : E × G} (hp : p.1 ∈ s) :
    ‖iteratedFDerivWithin 𝕜 i (f₁ ∘ Prod.fst) (s ×ˢ univ) p -
        iteratedFDerivWithin 𝕜 i (f₂ ∘ Prod.fst) (s ×ˢ univ) p‖ ≤
      ‖iteratedFDerivWithin 𝕜 i f₁ s p.1 - iteratedFDerivWithin 𝕜 i f₂ s p.1‖ := by
  have hS : UniqueDiffOn 𝕜 (s ×ˢ (univ : Set G)) := hs.prod uniqueDiffOn_univ
  have hpS : p ∈ s ×ˢ (univ : Set G) := ⟨hp, mem_univ _⟩
  have hc (f : E → F) (hf : ContDiffOn 𝕜 n f s) :
      ContDiffWithinAt 𝕜 i (f ∘ Prod.fst) (s ×ˢ (univ : Set G)) p :=
    ((hf.comp contDiffOn_fst fun (q : E × G) (hq : q ∈ s ×ˢ univ) ↦ hq.1).of_le hi) p hpS
  rw [← iteratedFDerivWithin_sub_apply (hc f₁ hf₁) (hc f₂ hf₂) hS hpS,
    ← iteratedFDerivWithin_sub_apply ((hf₁.of_le hi) _ hp) ((hf₂.of_le hi) _ hp) hs hp]
  exact (Prod.norm_iteratedFDerivWithin_comp_fst (hf₁.sub hf₂) hs hi hp).le

/-- The iterated derivatives of the difference of `(z, v) ↦ Dg₁(z) v` and `(z, v) ↦ Dg₂(z) v`
within `s ×ˢ univ` at `(z, v)`, for `g₁` and `g₂` of class `C^{j+1}` on a set `s` of unique
differentiability and `z ∈ s`, are bounded by the differences of the derivatives of `g₁` and `g₂`
at `z` of one order more. -/
theorem norm_iteratedFDerivWithin_fderivWithin_apply_sub_le {g₁ g₂ : E → F} {s : Set E}
    (hs : UniqueDiffOn 𝕜 s) {j : ℕ} (hg₁ : ContDiffOn 𝕜 (j + 1) g₁ s)
    (hg₂ : ContDiffOn 𝕜 (j + 1) g₂ s) {z : E} (hz : z ∈ s) (v : E) :
    ‖iteratedFDerivWithin 𝕜 j (fun q : E × E ↦ fderivWithin 𝕜 g₁ s q.1 q.2) (s ×ˢ univ) (z, v) -
        iteratedFDerivWithin 𝕜 j (fun q : E × E ↦ fderivWithin 𝕜 g₂ s q.1 q.2) (s ×ˢ univ)
          (z, v)‖ ≤
      (1 + ‖v‖) * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDerivWithin 𝕜 (i + 1) g₁ s z - iteratedFDerivWithin 𝕜 (i + 1) g₂ s z‖ := by
  have hS : UniqueDiffOn 𝕜 (s ×ˢ (univ : Set E)) := hs.prod uniqueDiffOn_univ
  have hzS : (z, v) ∈ s ×ˢ (univ : Set E) := ⟨hz, mem_univ v⟩
  have hG (g : E → F) (hg : ContDiffOn 𝕜 (j + 1) g s) :
      ContDiffOn 𝕜 j (fun q : E × E ↦ fderivWithin 𝕜 g s q.1 q.2) (s ×ˢ univ) :=
    ((hg.fderivWithin hs le_rfl).comp contDiffOn_fst
      fun (q : E × E) (hq : q ∈ s ×ˢ univ) ↦ hq.1).clm_apply contDiffOn_snd
  have hd (g : E → F) (hg : ContDiffOn 𝕜 (j + 1) g s) : DifferentiableOn 𝕜 g s :=
    hg.differentiableOn (by simp)
  rw [← iteratedFDerivWithin_sub_apply (hG g₁ hg₁ _ hzS) (hG g₂ hg₂ _ hzS) hS hzS,
    iteratedFDerivWithin_congr (f := fun q : E × E ↦ fderivWithin 𝕜 (g₁ - g₂) s q.1 q.2)
      (fun q hq ↦ by
        simp only [Pi.sub_apply]
        rw [fderivWithin_sub (hs _ hq.1) (hd g₁ hg₁ _ hq.1) (hd g₂ hg₂ _ hq.1)]
        rfl) hzS]
  refine (norm_iteratedFDerivWithin_fderivWithin_apply_le hs (hg₁.sub hg₂) hz v).trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi : ((i + 1 : ℕ) : WithTop ℕ∞) ≤ j + 1 := by
    exact_mod_cast Nat.succ_le_succ (Finset.mem_range_succ_iff.mp hi)
  rw [← Pi.sub_def, iteratedFDerivWithin_sub_apply ((hg₁.of_le hi) _ hz)
    ((hg₂.of_le hi) _ hz) hs hz]

end SymplecticGeometry

end
