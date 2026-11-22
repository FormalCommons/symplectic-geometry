/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.Topology.Algebra.Module.Trace

/-!
# The trace form of the continuous endomorphisms

For a finite-dimensional Hausdorff topological vector space `V` over a complete nontrivially
normed field `𝕜`, the trace pairing `(P, Q) ↦ tr (P Q)` of `V →L[𝕜] V` is a continuous bilinear
form, `ContinuousLinearMap.traceForm 𝕜 V`. It is built from Tau Ceti's continuous trace
`TauCeti.traceCLM` and the multiplication `LinearMap.mul` of the algebra `V →L[𝕜] V`; it is
continuous because `V →L[𝕜] V` is finite-dimensional (`LinearMap.toContinuousBilinearMap`). It is
symmetric since the trace of a product does not depend on the order of the factors
(`ContinuousLinearMap.traceCLM_comp_comm`).

## Main definitions and results

* `ContinuousLinearMap.traceForm`: the continuous bilinear form `(P, Q) ↦ tr (P Q)`, with
  `traceForm_def`, `traceForm_apply`, and its symmetry `traceForm_comm` and `smul_traceForm_comm`.
-/

public section

namespace ContinuousLinearMap

variable (𝕜 V : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]

/-- The trace form `(P, Q) ↦ tr (P Q)` of the continuous endomorphisms of a finite-dimensional
Hausdorff topological vector space, a symmetric continuous bilinear form. -/
noncomputable def traceForm : (V →L[𝕜] V) →L[𝕜] (V →L[𝕜] V) →L[𝕜] 𝕜 :=
  ((LinearMap.mul 𝕜 (V →L[𝕜] V)).compr₂ (TauCeti.traceCLM 𝕜 V).toLinearMap).toContinuousBilinearMap

variable {𝕜 V}

theorem traceForm_def :
    traceForm 𝕜 V =
      ((LinearMap.mul 𝕜 (V →L[𝕜] V)).compr₂
        (TauCeti.traceCLM 𝕜 V).toLinearMap).toContinuousBilinearMap :=
  (rfl)

/-- The trace form at `(P, Q)` is `tr (P Q)`. -/
@[simp]
theorem traceForm_apply (P Q : V →L[𝕜] V) :
    traceForm 𝕜 V P Q = LinearMap.trace 𝕜 V ↑(P * Q) := by
  simp [traceForm_def]

/-- The trace form is symmetric. -/
theorem traceForm_comm (P Q : V →L[𝕜] V) : traceForm 𝕜 V P Q = traceForm 𝕜 V Q P := by
  rw [traceForm_apply, traceForm_apply, ← TauCeti.traceCLM_apply, ← TauCeti.traceCLM_apply,
    mul_def, mul_def, traceCLM_comp_comm]

/-- A scalar multiple of the trace form is symmetric. -/
theorem smul_traceForm_comm (c : 𝕜) (P Q : V →L[𝕜] V) :
    (c • traceForm 𝕜 V) P Q = (c • traceForm 𝕜 V) Q P := by
  simp only [smul_apply, traceForm_comm P Q]

end ContinuousLinearMap

end
