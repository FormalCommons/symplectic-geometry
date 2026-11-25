/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Composition of smooth embeddings between boundaryless manifolds

Mathlib lists the composition of immersions, and of smooth embeddings, as a `TODO`
(`Manifold.IsImmersion.comp`, `Manifold.IsSmoothEmbedding.comp`). Between manifolds without
boundary whose last model space is finite-dimensional, the composite `g ∘ f` of two immersions
is an immersion: its differential `dg ∘ df` has a continuous linear left inverse, the composite
of those of `dg` and `df` (`Manifold.IsDiffImmersionAt.comp`), so it is an immersion at every
point by Tau Ceti's `ContMDiffOn.isImmersionAt_of_hasLeftInverse_mfderiv`, hence an immersion
(`TauCeti.isImmersion_iff_forall_isImmersionAt`). The models of the three manifolds may differ.
The proof follows that of Tau Ceti's `Diffeomorph.isImmersion_comp`, with the second map an
immersion instead of a diffeomorphism.

## Main results

* `Manifold.IsImmersion.comp_of_boundaryless`: the composite of two immersions is an immersion.
* `Manifold.IsSmoothEmbedding.comp_of_boundaryless`: the composite of two smooth embeddings is a
  smooth embedding.
-/

public section

open Set
open scoped Manifold ContDiff

namespace Manifold

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' E'' H G G' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [FiniteDimensional 𝕜 E'']
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G} {K : ModelWithCorners 𝕜 E'' G'}
  [I.Boundaryless] [K.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace P] [ChartedSpace G' P]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold K n P] {f : M → N} {g : N → P}

/-- Between manifolds without boundary, the last with a finite-dimensional model, the composite of
two `C^n` immersions, `1 ≤ n`, is an immersion. -/
theorem IsImmersion.comp_of_boundaryless (hg : IsImmersion J K n g) (hf : IsImmersion I J n f)
    (hn : 1 ≤ n) : IsImmersion I K n (g ∘ f) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have : CompleteSpace E'' := FiniteDimensional.completeSpace 𝕜 E''
  exact TauCeti.isImmersion_iff_forall_isImmersionAt.2 fun x ↦
    (hg.contMDiff.comp hf.contMDiff).contMDiffOn.isImmersionAt_of_hasLeftInverse_mfderiv
      isOpen_univ (mem_univ x) hn (isDiffImmersionAt_iff.mp
        ((hg.isDiffImmersionAt hn0 (f x)).comp (hf.isDiffImmersionAt hn0 x)))

/-- Between manifolds without boundary, the last with a finite-dimensional model, the composite of
two `C^n` smooth embeddings, `1 ≤ n`, is a smooth embedding. -/
theorem IsSmoothEmbedding.comp_of_boundaryless (hg : IsSmoothEmbedding J K n g)
    (hf : IsSmoothEmbedding I J n f) (hn : 1 ≤ n) : IsSmoothEmbedding I K n (g ∘ f) :=
  ⟨hg.isImmersion.comp_of_boundaryless hf.isImmersion hn, hg.isEmbedding.comp hf.isEmbedding⟩

end Manifold

end
