/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Gluing sections of a vector bundle with a smooth partition of unity

Let `ρ` be a smooth partition of unity on a manifold `N`, subordinate to an open cover `U`, let
`p : M → N` be a `C^n` map, and let `V` be a vector bundle on `M`. If each section `t i` of `V`
is `C^n` over `p ⁻¹' U i`, then the locally finite sum `∑ᶠ i, (ρ i ∘ p) • t i` is a `C^n`
section of `V`. With `p` the identity this is the usual gluing of local sections; with `p` the
projection of a bundle it glues sections defined over the preimages of open sets of the base.

## Main results

* `SmoothPartitionOfUnity.IsSubordinate.contMDiff_finsum_smul_comp_section`: the glued section
  is `C^n`. The proof is that of Mathlib's `exists_contMDiffSection_forall_mem_convex_of_local`
  (through `ContMDiffOn.smul_section_of_tsupport` and
  `ContMDiff.finsum_section_of_locallyFinite`), with the weights pulled back along `p`.
  For functions into a normed space and `p` the identity, it is Mathlib's
  `SmoothPartitionOfUnity.IsSubordinate.contMDiff_finsum_smul`.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace SmoothPartitionOfUnity

variable {E H M EN HN N F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞}

/-- **Gluing sections with a partition of unity.** Let `ρ` be a smooth partition of unity on
`N` subordinate to a family `U` of open sets, and `p : M → N` a `C^n` map. If each section
`t i` of a vector bundle `V` on `M` is `C^n` on `p ⁻¹' U i`, then the section
`x ↦ ∑ᶠ i, ρ i (p x) • t i x` of `V` is `C^n` on `M`. -/
theorem IsSubordinate.contMDiff_finsum_smul_comp_section {s : Set N}
    {ρ : SmoothPartitionOfUnity ι J N s} {U : ι → Set N} (hρ : ρ.IsSubordinate U)
    (hU : ∀ i, IsOpen (U i)) {p : M → N} (hp : ContMDiff I J n p) {t : ι → (x : M) → V x}
    (ht : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (t i x))
      (p ⁻¹' U i)) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) n
      (fun x ↦ TotalSpace.mk' F x (∑ᶠ i, ρ i (p x) • t i x)) := by
  refine ContMDiff.finsum_section_of_locallyFinite (t := fun i x ↦ ρ i (p x) • t i x)
    ((ρ.locallyFinite.preimage_continuous hp.continuous).subset
      fun i x hx ↦ left_ne_zero_of_smul hx) fun i ↦ ?_
  exact ContMDiffOn.smul_section_of_tsupport (ψ := fun x ↦ ρ i (p x))
    ((((ρ i).contMDiff.of_le (mod_cast le_top)).comp hp).contMDiffOn)
    ((hU i).preimage hp.continuous)
    ((tsupport_comp_subset_preimage _ hp.continuous).trans (preimage_mono (hρ i))) (ht i)

end SmoothPartitionOfUnity
