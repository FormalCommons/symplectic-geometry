/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Extension

/-!
# Extension of compactly supported classes along a homeomorphism

Extension by zero along an open embedding `f : U ⟶ X` (`TopCat.compactSupportCohomologyExtend`)
is functorial. So when `f` is an isomorphism, extension along `f` is an isomorphism, with inverse
the extension along `inv f` (`TopCat.isIso_compactSupportCohomologyExtend`).

This lemma is from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Cohomology/CompactSupport/Extension.lean`, same name), not yet in the
pinned release; it is stated here under its Tau Ceti name, so that moving Tau Ceti past it deletes
this file without renames.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

universe v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] {R : C}
  {k : Type v} [Ring k] [Linear k C] {M : C} {U X : TopCat.{v}} [T2Space X]

/-- Extension along a homeomorphism is an isomorphism; its inverse is the extension along the
inverse homeomorphism. -/
lemma isIso_compactSupportCohomologyExtend [T2Space U] {f : U ⟶ X} [IsIso f]
    (hf : IsOpenEmbedding f) (n : ℕ) :
    IsIso (compactSupportCohomologyExtend (R := R) (k := k) (M := M) hf n) := by
  have hg : IsOpenEmbedding (inv f) := (homeoOfIso (asIso f)).symm.isOpenEmbedding
  refine ⟨compactSupportCohomologyExtend hg n, ?_, ?_⟩
  · rw [← compactSupportCohomologyExtend_comp hf hg n (by simpa using IsOpenEmbedding.id),
      compactSupportCohomologyExtend_congr (IsIso.hom_inv_id f) _
        (by simpa using IsOpenEmbedding.id),
      compactSupportCohomologyExtend_id]
  · rw [← compactSupportCohomologyExtend_comp hg hf n (by simpa using IsOpenEmbedding.id),
      compactSupportCohomologyExtend_congr (IsIso.inv_hom_id f) _
        (by simpa using IsOpenEmbedding.id),
      compactSupportCohomologyExtend_id]

end TopCat

end
