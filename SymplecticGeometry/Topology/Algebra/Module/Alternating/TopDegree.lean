/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Algebra.Module.Alternating.Basic
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Pullback of top-degree continuous alternating maps

On a module `E` with a basis indexed by `ι`, pulling a continuous alternating map
`ω : E [⋀^ι]→L[R] F` back along a continuous linear endomorphism `A` multiplies it by `det A`
(`ContinuousAlternatingMap.compContinuousLinearMap_eq_det_smul`). This is the form-level
statement behind Tau Ceti's pointwise
`ContinuousAlternatingMap.compContinuousLinearMap_apply_basis`, and it follows from Tau Ceti's
`AlternatingMap.compLinearMap_eq_det_smul` for the underlying alternating map.

The file mirrors Tau Ceti's `TauCeti/Topology/Algebra/Module/Alternating/TopDegree.lean`.
-/

public section

namespace ContinuousAlternatingMap

variable {R E F ι : Type*} [CommRing R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F] [ContinuousConstSMul R F]

/-- **Pullback of a top-degree form by an endomorphism.** If `E` has a basis indexed by the
finite type `ι`, then pulling a continuous alternating map `ω` in `ι` variables back along a
continuous linear endomorphism `A` of `E` gives `det A • ω`. The basis only witnesses that `ι`
indexes a basis; it does not occur in the conclusion. -/
theorem compContinuousLinearMap_eq_det_smul [Finite ι] (ω : E [⋀^ι]→L[R] F)
    (b : Module.Basis ι R E) (A : E →L[R] E) :
    ω.compContinuousLinearMap A = A.toLinearMap.det • ω := by
  ext v
  simpa [Function.comp_def] using
    DFunLike.congr_fun (AlternatingMap.compLinearMap_eq_det_smul b ω.toAlternatingMap
      A.toLinearMap) v

end ContinuousAlternatingMap

end
