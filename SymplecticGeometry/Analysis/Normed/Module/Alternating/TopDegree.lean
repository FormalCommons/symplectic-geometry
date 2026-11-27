/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Top-degree forms in a basis

On a space `E` over a complete nontrivially normed field `𝕜` with a basis `b` indexed by `ι`, a
scalar continuous alternating map `ω` in `ι` variables is `ω b` times Tau Ceti's determinant form
`b.continuousDet`, and so is its pull-back along any continuous linear map `A : V →L[𝕜] E`
(`ContinuousAlternatingMap.compContinuousLinearMap_eq_apply_smul_continuousDet`). It follows from
Tau Ceti's `ContinuousAlternatingMap.apply_eq_det_mul`. Pulled back along an endomorphism `L`,
the determinant form becomes `det L • b.continuousDet`
(`Module.Basis.continuousDet_compContinuousLinearMap`), so it stays nonzero when `L` is
invertible (`Module.Basis.continuousDet_compContinuousLinearMap_ne_zero`).

The file mirrors Tau Ceti's `TauCeti/Analysis/Normed/Module/Alternating/TopDegree.lean`, which
defines `Module.Basis.continuousDet`.
-/

public section

namespace ContinuousAlternatingMap

/-- **A top-degree form in a basis.** A scalar-valued continuous alternating map `ω` in `ι`
variables on a space `E` with a basis `b` indexed by `ι`, pulled back along a continuous linear
map `A : V → E`, is `ω b` times the determinant form of `b` pulled back along `A`. For
`A = id` this says `ω = ω b • b.continuousDet`. -/
theorem compContinuousLinearMap_eq_apply_smul_continuousDet {𝕜 E V ι : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] [ContinuousSMul 𝕜 E]
    [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [Fintype ι] [DecidableEq ι]
    (ω : E [⋀^ι]→L[𝕜] 𝕜) (b : Module.Basis ι 𝕜 E) (A : V →L[𝕜] E) :
    ω.compContinuousLinearMap A = ω b • b.continuousDet.compContinuousLinearMap A := by
  ext v
  simp only [compContinuousLinearMap_apply, smul_apply, smul_eq_mul,
    Module.Basis.continuousDet_apply]
  rw [ω.apply_eq_det_mul b, mul_comm]

end ContinuousAlternatingMap

namespace Module.Basis

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [T2Space E] [ContinuousSMul 𝕜 E]
  [Fintype ι] [DecidableEq ι]

/-- The determinant form of `b` pulled back along an endomorphism `L` is `det L` times the
determinant form of `b`. -/
theorem continuousDet_compContinuousLinearMap (b : Module.Basis ι 𝕜 E) (L : E →L[𝕜] E) :
    b.continuousDet.compContinuousLinearMap L =
      LinearMap.det (L : E →ₗ[𝕜] E) • b.continuousDet := by
  ext v
  rw [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    continuousDet_apply, continuousDet_apply, smul_eq_mul]
  exact b.det_comp L v

/-- The determinant form of a basis is nonzero. -/
theorem continuousDet_ne_zero (b : Module.Basis ι 𝕜 E) : b.continuousDet ≠ 0 := fun h ↦
  b.det_ne_zero (by rw [← continuousDet_toAlternatingMap, h]; rfl)

/-- The determinant form of a basis, pulled back along an invertible endomorphism, is nonzero. -/
theorem continuousDet_compContinuousLinearMap_ne_zero (b : Module.Basis ι 𝕜 E) {L : E →L[𝕜] E}
    (hL : L.IsInvertible) : b.continuousDet.compContinuousLinearMap L ≠ 0 := by
  obtain ⟨L, rfl⟩ := hL
  rw [b.continuousDet_compContinuousLinearMap]
  exact smul_ne_zero L.toLinearEquiv.isUnit_det'.ne_zero b.continuousDet_ne_zero

end Module.Basis

end
