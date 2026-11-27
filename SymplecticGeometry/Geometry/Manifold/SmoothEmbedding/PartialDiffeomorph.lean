/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# Partial diffeomorphisms defined everywhere are smooth embeddings

A partial diffeomorphism `Φ : M → N` whose source is all of `M` is a diffeomorphism of `M` onto
the open subset `Φ.target` of `N`, followed by the inclusion of that subset. So, when `M` and `N`
have the same model, it is a smooth embedding, whose range is `Φ.target`
(`PartialEquiv.range_eq_target_of_source_eq_univ`). The same holds for an open partial
homeomorphism of a normed space into itself, defined everywhere and `C^n` both ways, which Tau
Ceti's `TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph` makes a partial diffeomorphism.

The proof reads `Φ` as Tau Ceti's `PartialDiffeomorph.toDiffeomorphSourceTarget` after the
inverse of Tau Ceti's `Diffeomorph.ofTop`, followed by the inclusion of the target, a smooth
embedding by Mathlib's `Manifold.IsSmoothEmbedding.of_opens`.

## Main results

* `PartialDiffeomorph.isSmoothEmbedding_of_source_eq_univ`: a partial diffeomorphism with source
  `univ` is a smooth embedding.
* `OpenPartialHomeomorph.isSmoothEmbedding_of_source_eq_univ`: an open partial homeomorphism of a
  normed space into itself with source `univ`, `C^n` with `C^n` inverse on its target, is a
  smooth embedding.
-/

public section

open Set Manifold

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H N]
  {n : WithTop ℕ∞}

/-- A `C^n` partial diffeomorphism `Φ : M → N` between `C^n` manifolds on the same model whose
source is all of `M` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_of_source_eq_univ [IsManifold I n M] [IsManifold I n N]
    (Φ : PartialDiffeomorph I I M N n) (h : Φ.source = univ) :
    IsSmoothEmbedding I I n Φ := by
  have htop : (⟨Φ.source, Φ.open_source⟩ : TopologicalSpace.Opens M) = ⊤ := by
    ext x
    simp [h]
  have hΦ : (Subtype.val ∘ Φ.toDiffeomorphSourceTarget) ∘
      (Diffeomorph.ofTop (I := I) (n := n) _ htop).symm = Φ := by
    ext x
    simp
  rw [← hΦ, Function.comp_assoc, ← Diffeomorph.coe_trans]
  exact TauCeti.isSmoothEmbedding_comp_diffeomorph _ (IsSmoothEmbedding.of_opens _)

end PartialDiffeomorph

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {n : WithTop ℕ∞}

/-- An open partial homeomorphism `Θ` of a normed space `E` into itself whose source is all of
`E`, which is `C^n`, and whose inverse is `C^n` on the target, is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_of_source_eq_univ (Θ : OpenPartialHomeomorph E E)
    (h : Θ.source = univ) (hΘ : ContDiff 𝕜 n Θ) (hΘsymm : ContDiffOn 𝕜 n Θ.symm Θ.target) :
    IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, E) n Θ := by
  let Φ := TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph Θ hΘ.contDiffOn hΘsymm
  have hcoe : ⇑Φ = Θ := by
    ext x
    simp [Φ]
  rw [← hcoe]
  exact Φ.isSmoothEmbedding_of_source_eq_univ (by simpa [Φ] using h)

end OpenPartialHomeomorph

end
