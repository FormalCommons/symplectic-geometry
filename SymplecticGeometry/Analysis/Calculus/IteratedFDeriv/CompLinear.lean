/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Iterated derivatives within a set of a composition with a continuous linear map

This file gives within-a-set forms of three of the norm bounds of Tau Ceti's
`TauCeti/Analysis/Calculus/IteratedFDeriv/CompLinear.lean`.

## Main results

* `ContinuousLinearMap.norm_iteratedFDerivWithin_comp_right_le`: precomposition with a continuous
  linear map `g` multiplies the norm of the `i`-th derivative within `g ⁻¹' s` by at most
  `‖g‖ ^ i`. This is the within-a-set form of Tau Ceti's
  `ContinuousLinearMap.norm_iteratedFDeriv_comp_right_le`, with the same proof.
* `ContinuousLinearMap.norm_iteratedFDerivWithin_le_norm_comp_right_mul_of_rightInverse`: if `g`
  has a continuous linear right inverse `r`, the reverse bound holds with the factor `‖r‖ ^ i`.
  This is the within-a-set form of Tau Ceti's
  `ContinuousLinearMap.norm_iteratedFDeriv_le_norm_comp_right_mul_of_rightInverse`, with the same
  proof.
* `Prod.norm_iteratedFDerivWithin_comp_fst`: the iterated derivatives of `f ∘ Prod.fst` within
  `s ×ˢ univ` have the same norms as those of `f` within `s`. This is the within-a-set form of Tau
  Ceti's `Prod.norm_iteratedFDeriv_comp_fst`, derived as Tau Ceti derives it, from the two bounds
  above applied to `ContinuousLinearMap.fst` and its right inverse `ContinuousLinearMap.inl`.
* `Prod.norm_iteratedFDerivWithin_comp_fst_sub`: the same equality for the difference of the
  iterated derivatives of two maps `f₁ ∘ Prod.fst` and `f₂ ∘ Prod.fst`.
-/

public section

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Precomposition with a continuous linear map `g` multiplies the norm of the `i`-th iterated
derivative within `g ⁻¹' s` by at most `‖g‖ ^ i`, for `f` of class `C^n` on a set `s` of unique
differentiability, `g ⁻¹' s` of unique differentiability, `g x ∈ s` and `i ≤ n`. -/
theorem ContinuousLinearMap.norm_iteratedFDerivWithin_comp_right_le (g : G →L[𝕜] E) {f : E → F}
    {s : Set E} {n : WithTop ℕ∞} (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (h's : UniqueDiffOn 𝕜 (g ⁻¹' s)) {x : G} (hx : g x ∈ s) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x‖ ≤
      ‖iteratedFDerivWithin 𝕜 i f s (g x)‖ * ‖g‖ ^ i := by
  rw [g.iteratedFDerivWithin_comp_right hf hs h's hx hi]
  exact ((iteratedFDerivWithin 𝕜 i f s (g x)).norm_compContinuousLinearMap_le _).trans_eq
    (by rw [Fin.prod_const])

/-- If a continuous linear map `g` has a continuous linear right inverse `r`, the norm of the
`i`-th iterated derivative of `f` within `s` at `g x` is at most that of `f ∘ g` within `g ⁻¹' s`
at `x` times `‖r‖ ^ i`, for `f` of class `C^n` on a set `s` of unique differentiability,
`g ⁻¹' s` of unique differentiability, `g x ∈ s` and `i ≤ n`. -/
theorem ContinuousLinearMap.norm_iteratedFDerivWithin_le_norm_comp_right_mul_of_rightInverse
    (g : G →L[𝕜] E) (r : E →L[𝕜] G) (hgr : Function.RightInverse r g) {f : E → F} {s : Set E}
    {n : WithTop ℕ∞} (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (h's : UniqueDiffOn 𝕜 (g ⁻¹' s)) {x : G} (hx : g x ∈ s) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDerivWithin 𝕜 i f s (g x)‖ ≤
      ‖iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x‖ * ‖r‖ ^ i := by
  rw [g.iteratedFDerivWithin_comp_right hf hs h's hx hi]
  set M := iteratedFDerivWithin 𝕜 i f s (g x)
  -- precomposing with `r` in every slot recovers `M`, since `g ∘ r = id`
  calc ‖M‖ = ‖(M.compContinuousLinearMap fun _ ↦ g).compContinuousLinearMap fun _ ↦ r‖ := by
        congr 1
        ext m
        simp [hgr _]
    _ ≤ _ := ((M.compContinuousLinearMap _).norm_compContinuousLinearMap_le _).trans_eq
        (by rw [Fin.prod_const])

/-- The iterated derivatives of `f ∘ Prod.fst` within `s ×ˢ univ` at `p`, for `f` of class `C^n`
on a set `s` of unique differentiability and `p.1 ∈ s`, have, up to order `n`, the same norms as
those of `f` within `s` at `p.1`. -/
theorem Prod.norm_iteratedFDerivWithin_comp_fst {f : E → F} {s : Set E} {n : WithTop ℕ∞}
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) {i : ℕ} (hi : i ≤ n) {p : E × G}
    (hp : p.1 ∈ s) :
    ‖iteratedFDerivWithin 𝕜 i (f ∘ Prod.fst) (s ×ˢ univ) p‖ =
      ‖iteratedFDerivWithin 𝕜 i f s p.1‖ := by
  have hpre : (ContinuousLinearMap.fst 𝕜 E G) ⁻¹' s = s ×ˢ univ := by
    ext; simp
  have hS : UniqueDiffOn 𝕜 ((ContinuousLinearMap.fst 𝕜 E G) ⁻¹' s) :=
    hpre ▸ hs.prod uniqueDiffOn_univ
  rw [← ContinuousLinearMap.coe_fst' (R := 𝕜) (M₂ := G), ← hpre]
  refine le_antisymm (((ContinuousLinearMap.fst 𝕜 E G).norm_iteratedFDerivWithin_comp_right_le
    hf hs hS hp hi).trans (mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le 𝕜 E G)))) ?_
  exact (ContinuousLinearMap.norm_iteratedFDerivWithin_le_norm_comp_right_mul_of_rightInverse
    (ContinuousLinearMap.fst 𝕜 E G) (ContinuousLinearMap.inl 𝕜 E G) (fun _ ↦ by simp) hf hs hS
      hp hi).trans (mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one 𝕜 E G)))

/-- The difference of the iterated derivatives of `f₁ ∘ Prod.fst` and `f₂ ∘ Prod.fst` within
`s ×ˢ univ` at `p`, for `f₁` and `f₂` of class `C^n` on a set `s` of unique differentiability and
`p.1 ∈ s`, has, up to order `n`, the same norm as the difference of those of `f₁` and `f₂` within
`s` at `p.1`. -/
theorem Prod.norm_iteratedFDerivWithin_comp_fst_sub {f₁ f₂ : E → F} {s : Set E}
    {n : WithTop ℕ∞} (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s)
    (hs : UniqueDiffOn 𝕜 s) {i : ℕ} (hi : i ≤ n) {p : E × G} (hp : p.1 ∈ s) :
    ‖iteratedFDerivWithin 𝕜 i (f₁ ∘ Prod.fst) (s ×ˢ univ) p -
        iteratedFDerivWithin 𝕜 i (f₂ ∘ Prod.fst) (s ×ˢ univ) p‖ =
      ‖iteratedFDerivWithin 𝕜 i f₁ s p.1 - iteratedFDerivWithin 𝕜 i f₂ s p.1‖ := by
  have hS : UniqueDiffOn 𝕜 (s ×ˢ (univ : Set G)) := hs.prod uniqueDiffOn_univ
  have hpS : p ∈ s ×ˢ (univ : Set G) := ⟨hp, mem_univ _⟩
  have hc (f : E → F) (hf : ContDiffOn 𝕜 n f s) :
      ContDiffWithinAt 𝕜 i (f ∘ Prod.fst) (s ×ˢ (univ : Set G)) p :=
    ((hf.comp contDiffOn_fst fun (q : E × G) (hq : q ∈ s ×ˢ univ) ↦ hq.1).of_le hi) p hpS
  rw [← iteratedFDerivWithin_sub_apply (hc f₁ hf₁) (hc f₂ hf₂) hS hpS,
    ← iteratedFDerivWithin_sub_apply ((hf₁.of_le hi) _ hp) ((hf₂.of_le hi) _ hp) hs hp]
  exact Prod.norm_iteratedFDerivWithin_comp_fst (hf₁.sub hf₂) hs hi hp

end
