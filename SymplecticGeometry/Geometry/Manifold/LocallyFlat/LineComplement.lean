/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
import SymplecticGeometry.Analysis.Convex.Hyperplane
import SymplecticGeometry.Geometry.Manifold.Immersion.Complement
import SymplecticGeometry.Geometry.Manifold.LocallyFlat.LineChart
import TauCeti.Geometry.Manifold.LocallyFlat.Smooth

/-!
# Small neighbourhoods minus the image of a set under an embedding of `ℝ`

Let `f : ℝ → M` be a locally flat embedding with a nontrivial complementary model `F'`, for
instance a `C^n` embedding into a boundaryless manifold of dimension at least two, and let
`J : Set ℝ`. This file describes how `A := f '' J` sits near a point `f t`, inside any prescribed
neighbourhood `W` of it:

* some neighbourhood `V ⊆ W` of `f t` has `V \ A` the union of two preconnected sets whose
  closures both contain `V ∩ A`;
* if `t` bounds `J` from above or from below, some neighbourhood `V ⊆ W` of `f t` has `V \ A`
  preconnected.

The neighbourhood `V` is the source of the convex slice chart of
`TauCeti.IsLocallyFlat.exists_isSliceChart_convex`, in which `A` reads as a piece
`K ×ˢ {0}` of the line `ℝ × {0}`. The two statements then follow from their counterparts in the
model space, `Convex.exists_isPreconnected_diff_prod_zero` and
`Convex.isPreconnected_diff_prod_zero_of_subset_Iic` (or `_Ici`), carried back to `M` by the
inverse of the chart, which is continuous on the target.

## Main results

* `TauCeti.IsLocallyFlat.exists_isPreconnected_diff_image`,
  `TauCeti.IsLocallyFlat.exists_isPreconnected_diff_image_of_mem_bounds`: the two
  statements for a locally flat embedding of `ℝ`.
* `Manifold.IsSmoothEmbedding.exists_isPreconnected_diff_image`,
  `Manifold.IsSmoothEmbedding.exists_isPreconnected_diff_image_of_mem_bounds`: the same for a
  `C^n` embedding of `ℝ` into a boundaryless manifold whose model space has rank greater than one.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 5, for slice charts of embedded submanifolds.
-/

public section

open Set Topology

namespace TauCeti.IsLocallyFlat

variable {M : Type*} [TopologicalSpace M] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [Nontrivial F'] {f : ℝ → M}

/-- **Near a point, the image of a set under a locally flat embedding of `ℝ` separates at most
two ways.** Let `f : ℝ → M` be locally flat with nontrivial complementary model, `J : Set ℝ`,
`t : ℝ` and `W` a neighbourhood of `f t`. Then some neighbourhood `V ⊆ W` of `f t` has
`V \ f '' J = P ∪ Q` for preconnected sets `P`, `Q` whose closures both contain `V ∩ f '' J`. -/
theorem exists_isPreconnected_diff_image (h : IsLocallyFlat ℝ F' f) (J : Set ℝ) (t : ℝ)
    {W : Set M} (hW : W ∈ 𝓝 (f t)) :
    ∃ V ∈ 𝓝 (f t), V ⊆ W ∧ ∃ P Q : Set M, IsPreconnected P ∧ IsPreconnected Q ∧
      V \ f '' J = P ∪ Q ∧ V ∩ f '' J ⊆ closure P ∩ closure Q := by
  obtain ⟨ψ, O, g, hft, hψW, hψc, -, -, -, -, -, -, -, hJ⟩ := h.exists_isSliceChart_convex t hW
  obtain ⟨P, Q, hP, hQ, hPQ, hcl⟩ :=
    hψc.exists_isPreconnected_diff_prod_zero (F := F') ψ.open_target (g '' (J ∩ O))
  have hPT : P ⊆ ψ.target := fun y hy => (hPQ.symm ▸ mem_union_left Q hy : y ∈ ψ.target \ _).1
  have hQT : Q ⊆ ψ.target := fun y hy => (hPQ.symm ▸ mem_union_right P hy : y ∈ ψ.target \ _).1
  refine ⟨ψ.source, ψ.open_source.mem_nhds hft, hψW, ψ.symm '' P, ψ.symm '' Q,
    hP.image _ (ψ.continuousOn_symm.mono hPT), hQ.image _ (ψ.continuousOn_symm.mono hQT), ?_, ?_⟩
  · rw [sdiff_eq, ← ((OpenPartialHomeomorph.IsImage.of_image_eq (hJ J)).compl.symm_image_eq),
      ← sdiff_eq, hPQ, image_union]
  · intro x hx
    have hy : ψ x ∈ ψ.target ∩ (g '' (J ∩ O)) ×ˢ {0} := hJ J ▸ mem_image_of_mem ψ hx
    rw [← ψ.left_inv hx.1]
    exact ⟨(ψ.continuousAt_symm hy.1).continuousWithinAt.mem_closure_image (hcl hy).1,
      (ψ.continuousAt_symm hy.1).continuousWithinAt.mem_closure_image (hcl hy).2⟩

/-- **Near an end, the image of a set under a locally flat embedding of `ℝ` does not separate.**
Let `f : ℝ → M` be locally flat with nontrivial complementary model, `J : Set ℝ`, `t` an upper or
a lower bound of `J` (for instance its greatest or least element) and `W` a neighbourhood of
`f t`. Then some neighbourhood `V ⊆ W` of `f t` has `V \ f '' J` preconnected. -/
theorem exists_isPreconnected_diff_image_of_mem_bounds (h : IsLocallyFlat ℝ F' f)
    {J : Set ℝ} {t : ℝ} (ht : t ∈ upperBounds J ∨ t ∈ lowerBounds J) {W : Set M}
    (hW : W ∈ 𝓝 (f t)) :
    ∃ V ∈ 𝓝 (f t), V ⊆ W ∧ IsPreconnected (V \ f '' J) := by
  obtain ⟨ψ, O, g, hft, hψW, hψc, -, -, -, htO, -, hψg, hg, hJ⟩ :=
    h.exists_isSliceChart_convex t hW
  refine ⟨ψ.source, ψ.open_source.mem_nhds hft, hψW, ?_⟩
  rw [sdiff_eq, ← ((OpenPartialHomeomorph.IsImage.of_image_eq (hJ J)).compl.symm_image_eq),
    ← sdiff_eq]
  refine IsPreconnected.image ?_ _ (ψ.continuousOn_symm.mono sdiff_subset)
  have hT : ((g t, 0) : ℝ × F') ∈ ψ.target := hψg t htO ▸ ψ.map_source hft
  rcases ht with ht | ht <;> rcases hg with hg | hg
  · exact hψc.isPreconnected_diff_prod_zero_of_subset_Iic ψ.open_target
      (image_subset_iff.2 fun s hs => hg.monotoneOn hs.2 htO (ht hs.1)) hT
  · exact hψc.isPreconnected_diff_prod_zero_of_subset_Ici ψ.open_target
      (image_subset_iff.2 fun s hs => hg.antitoneOn hs.2 htO (ht hs.1)) hT
  · exact hψc.isPreconnected_diff_prod_zero_of_subset_Ici ψ.open_target
      (image_subset_iff.2 fun s hs => hg.monotoneOn htO hs.2 (ht hs.1)) hT
  · exact hψc.isPreconnected_diff_prod_zero_of_subset_Iic ψ.open_target
      (image_subset_iff.2 fun s hs => hg.antitoneOn htO hs.2 (ht hs.1)) hT

end TauCeti.IsLocallyFlat

namespace Manifold.IsSmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {n : WithTop ℕ∞} {f : ℝ → M}

/-- **Near a point, the image of a set under a smooth embedding of `ℝ` separates at most two
ways.** Let `f : ℝ → M` be a `C^n` embedding into a boundaryless manifold whose model space has
rank greater than one, `J : Set ℝ`, `t : ℝ` and `W` a neighbourhood of `f t`. Then some
neighbourhood `V ⊆ W` of `f t` has `V \ f '' J = P ∪ Q` for preconnected sets `P`, `Q` whose
closures both contain `V ∩ f '' J`. -/
theorem exists_isPreconnected_diff_image (h : IsSmoothEmbedding 𝓘(ℝ) I n f)
    (hE : 1 < Module.rank ℝ E) (J : Set ℝ) (t : ℝ) {W : Set M} (hW : W ∈ 𝓝 (f t)) :
    ∃ V ∈ 𝓝 (f t), V ⊆ W ∧ ∃ P Q : Set M, IsPreconnected P ∧ IsPreconnected Q ∧
      V \ f '' J = P ∪ Q ∧ V ∩ f '' J ⊆ closure P ∩ closure Q :=
  have := h.isImmersion.nontrivial_complement (by simpa using hE)
  (TauCeti.IsLocallyFlat.of_isSmoothEmbedding h).exists_isPreconnected_diff_image J t hW

/-- **Near an end, the image of a set under a smooth embedding of `ℝ` does not separate.** Let
`f : ℝ → M` be a `C^n` embedding into a boundaryless manifold whose model space has rank greater
than one, `J : Set ℝ`, `t` an upper or a lower bound of `J` (for instance its greatest or least
element) and `W` a neighbourhood of `f t`. Then some neighbourhood `V ⊆ W` of `f t` has
`V \ f '' J` preconnected. -/
theorem exists_isPreconnected_diff_image_of_mem_bounds (h : IsSmoothEmbedding 𝓘(ℝ) I n f)
    (hE : 1 < Module.rank ℝ E) {J : Set ℝ} {t : ℝ}
    (ht : t ∈ upperBounds J ∨ t ∈ lowerBounds J) {W : Set M} (hW : W ∈ 𝓝 (f t)) :
    ∃ V ∈ 𝓝 (f t), V ⊆ W ∧ IsPreconnected (V \ f '' J) :=
  have := h.isImmersion.nontrivial_complement (by simpa using hE)
  (TauCeti.IsLocallyFlat.of_isSmoothEmbedding h).exists_isPreconnected_diff_image_of_mem_bounds
    ht hW

end Manifold.IsSmoothEmbedding

end
