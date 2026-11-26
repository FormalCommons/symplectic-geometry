/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Representative

/-!
# Complement representatives as projections

For an embedding `f` and a topological complement `W` of the tangent image `df_x (T_x M)`, Tau
Ceti's `TauCeti.SmoothEmbedding.complementRepresentative` picks in each normal class the vector
that lies in `W`. This file identifies the representative of the class of an ambient tangent
vector `v` with the projection of `v` onto `W` along the tangent image.

## Main results

* `TauCeti.SmoothEmbedding.complementRepresentative_normalClass`: the representative of the class
  of `v` is the projection of `v` onto `W` along the tangent image.
-/

public section

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞}

/-- The representative in a complement `W` of the tangent image of the normal class of `v` is the
projection of `v` onto `W` along the tangent image. -/
theorem complementRepresentative_normalClass (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) {W : Submodule 𝕜 (TangentSpace J (f x))}
    (hW : (f.isImmersion.tangentRange x hn).IsTopCompl W) (v : TangentSpace J (f x)) :
    f.complementRepresentative x hn hW (f.isImmersion.normalClass x hn v) =
      W.projection (f.isImmersion.tangentRange x hn) hW.isCompl.symm v := by
  rw [complementRepresentative_eq_iff]
  refine ⟨Submodule.projection_apply_mem _ _, ?_⟩
  rw [normalClass_eq_iff, Submodule.projection_eq_self_sub_projection hW.isCompl,
    sub_sub_cancel_left]
  exact neg_mem (Submodule.projection_apply_mem _ _)

end TauCeti.SmoothEmbedding

end
