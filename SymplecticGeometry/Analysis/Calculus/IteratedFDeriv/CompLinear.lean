/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Iterated derivatives within a set of a composition with a continuous linear map

This file gives within-a-set forms of two of the norm bounds of Tau Ceti's
`TauCeti/Analysis/Calculus/IteratedFDeriv/CompLinear.lean`.

## Main results

* `ContinuousLinearMap.norm_iteratedFDerivWithin_comp_right_le`: precomposition with a continuous
  linear map `g` multiplies the norm of the `i`-th derivative within `g ⁻¹' s` by at most
  `‖g‖ ^ i`. This is the within-a-set form of Tau Ceti's
  `ContinuousLinearMap.norm_iteratedFDeriv_comp_right_le`, with the same proof.
* `Prod.norm_iteratedFDerivWithin_comp_fst`: the iterated derivatives of `f ∘ Prod.fst` within
  `s ×ˢ univ` have the same norms as those of `f` within `s`. This is the within-a-set form of Tau
  Ceti's `Prod.norm_iteratedFDeriv_comp_fst`. The reverse inequality adapts the proof of Tau
  Ceti's `ContinuousLinearMap.norm_iteratedFDeriv_le_norm_comp_right_mul_of_rightInverse`,
  precomposing with `ContinuousLinearMap.inl`.
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
  rw [ContinuousLinearMap.iteratedFDerivWithin_comp_right _ hf hs hS hp hi]
  set M := iteratedFDerivWithin 𝕜 i f s p.1
  -- precomposing with `inl` in every slot recovers `M`, since `fst ∘ inl = id`
  calc ‖M‖ = ‖(M.compContinuousLinearMap fun _ ↦ ContinuousLinearMap.fst 𝕜 E G)
        |>.compContinuousLinearMap fun _ ↦ ContinuousLinearMap.inl 𝕜 E G‖ := by
        refine congrArg norm ?_
        ext m
        simp
    _ ≤ _ := ((M.compContinuousLinearMap _).norm_compContinuousLinearMap_le _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
          fun _ _ ↦ ContinuousLinearMap.norm_inl_le_one 𝕜 E G))

end
