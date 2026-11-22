/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Order.SupClosed
public import Mathlib.Topology.Sets.Opens

/-!
# Open sets with convex image

For a map `j : X → E` into a module, the open sets `W` of `X` whose image `j '' W` is convex are
closed under intersection when `j` is injective
(`TopologicalSpace.Opens.infClosed_setOf_convex_image`). For an open embedding `j` into a real
normed space they cover `X`, and so do their finite unions
(`Topology.IsOpenEmbedding.iSup_finset_sup_convex_image_eq_top`): every point has such a
neighbourhood, the preimage of a ball contained in the image of `j`.

These are the cover of an open subset of a normed space by convex open sets over which
Mayer–Vietoris arguments induct, as in Hatcher's proof of Lemma 3.36.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, Lemma 3.36.
-/

public section

open Set Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

namespace TopologicalSpace.Opens

/-- For an injective map `j`, the open sets of `X` with convex image under `j` are closed under
intersection. -/
theorem infClosed_setOf_convex_image {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] {j : X → E} (hj : Function.Injective j) :
    InfClosed {W : Opens X | Convex 𝕜 (j '' W)} := by
  rintro V hV W hW
  simp only [mem_ofPred_eq, Opens.coe_inf, image_inter hj] at hV hW ⊢
  exact hV.inter hW

end TopologicalSpace.Opens

namespace Topology.IsOpenEmbedding

/-- For an open embedding `j` of `X` into a real normed space, the finite unions of open sets of
`X` with convex image under `j` cover `X`. -/
theorem iSup_finset_sup_convex_image_eq_top {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {j : X → E} (hj : IsOpenEmbedding j) :
    ⨆ s : Finset {W : Opens X | Convex ℝ (j '' W)}, s.sup Subtype.val = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hj.isOpen_range (j x) ⟨x, rfl⟩
  let W : Opens X := ⟨j ⁻¹' Metric.ball (j x) r, Metric.isOpen_ball.preimage hj.continuous⟩
  have hW : j '' W = Metric.ball (j x) r := image_preimage_eq_of_subset hball
  refine Opens.mem_iSup.2 ⟨{⟨W, by simpa [hW] using convex_ball (j x) r⟩}, ?_⟩
  simpa [W] using hr

end Topology.IsOpenEmbedding

end
