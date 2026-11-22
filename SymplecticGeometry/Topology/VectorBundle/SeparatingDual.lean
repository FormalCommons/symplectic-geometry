/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import SymplecticGeometry.Analysis.LocallyConvex.SeparatingDual

/-!
# Separating duals of the fibres of a vector bundle

The trivialization of a topological vector bundle at `b` restricts to a continuous linear
equivalence of the fibre `E b` with the model fibre `F`. So the fibres have a separating dual
when `F` does (`VectorBundle.separatingDual`).

The theorem follows the form of Tau Ceti's `VectorBundle.isTopologicalAddGroup` and
`VectorBundle.continuousSMul`, which give the fibres the other linear-topological structure:
since `F` cannot be found from `E b`, it takes `b` and is not an instance.

## Main results

* `VectorBundle.separatingDual`: the fibres of a vector bundle whose model fibre has separating
  dual have separating dual.
-/

public section

open Bundle

namespace VectorBundle

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (E : B → Type*)
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [VectorBundle 𝕜 F E]

/-- The fibres of a topological vector bundle whose model fibre has separating dual have
separating dual. -/
protected theorem separatingDual [SeparatingDual 𝕜 F] (b : B) : SeparatingDual 𝕜 (E b) :=
  let e := (trivializationAt F E b).continuousLinearEquivAt 𝕜 b
    (FiberBundle.mem_baseSet_trivializationAt' b)
  .of_injective (e : E b →L[𝕜] F) e.injective

end VectorBundle

end
