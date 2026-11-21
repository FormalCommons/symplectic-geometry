/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Differentials of open-subset inclusions

The differential of the inclusion `Subtype.val : U → M` of an open subset is bijective at every
point. This complements Tau Ceti's `TauCeti.Manifold.mfderiv_subtype_val`, which identifies the
differential with the canonical identification of tangent spaces
`TauCeti.Manifold.tangentSpaceOpenEquiv`, and `TauCeti.Manifold.mfderiv_subtype_val_injective`.
It is the hypothesis under which Tau Ceti's pullback theorems for maps with bijective
differentials, such as `TauCeti.SmoothForm.IsContactForm.mpullback`, apply to restriction to an
open subset.

## Main results

* `TauCeti.Manifold.bijective_mfderiv_subtype_val`: the differential of an open-subset inclusion
  is bijective.
-/

public section

open TopologicalSpace

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The differential of the inclusion of an open subset is bijective at every point. -/
theorem bijective_mfderiv_subtype_val {U : Opens M} (x : U) :
    Function.Bijective (mfderiv I I (Subtype.val : U → M) x) := by
  rw [mfderiv_subtype_val]
  exact (tangentSpaceOpenEquiv (I := I) x).bijective

end TauCeti.Manifold

end
