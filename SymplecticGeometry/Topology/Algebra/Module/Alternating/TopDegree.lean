/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Pullback of top-degree continuous alternating maps

On a module `E` with a basis indexed by `ι`, pulling a continuous alternating map
`ω : E [⋀^ι]→L[R] F` back along a continuous linear endomorphism `A` multiplies it by `det A`
(`ContinuousAlternatingMap.compContinuousLinearMap_eq_det_smul`). This is the form-level
statement behind Tau Ceti's pointwise
`ContinuousAlternatingMap.compContinuousLinearMap_apply_basis`, and it follows from Tau Ceti's
`AlternatingMap.compLinearMap_eq_det_smul` for the underlying alternating map.

A scalar-valued top-degree form `ω` is its value `ω b` on a basis `b` times the determinant form
of `b`, and so are their pull-backs along any continuous linear map
(`ContinuousAlternatingMap.compContinuousLinearMap_eq_apply_smul_continuousDet`).

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

/-- **A top-degree form in a basis.** A scalar-valued continuous alternating map `ω` in `ι`
variables on a space `E` with a basis `b` indexed by `ι`, pulled back along a continuous linear
map `A : V → E`, is `ω b` times the determinant form of `b` pulled back along `A`. For
`A = id` this says `ω = ω b • b.continuousDet`. -/
theorem compContinuousLinearMap_eq_apply_smul_continuousDet {𝕜 V : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Module 𝕜 E] [IsTopologicalAddGroup E]
    [T2Space E] [ContinuousSMul 𝕜 E] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
    [Fintype ι] [DecidableEq ι] (ω : E [⋀^ι]→L[𝕜] 𝕜) (b : Module.Basis ι 𝕜 E) (A : V →L[𝕜] E) :
    ω.compContinuousLinearMap A = ω b • b.continuousDet.compContinuousLinearMap A := by
  ext v
  simp only [compContinuousLinearMap_apply, smul_apply, smul_eq_mul,
    Module.Basis.continuousDet_apply]
  rw [ω.apply_eq_det_mul b, mul_comm]

end ContinuousAlternatingMap

end
