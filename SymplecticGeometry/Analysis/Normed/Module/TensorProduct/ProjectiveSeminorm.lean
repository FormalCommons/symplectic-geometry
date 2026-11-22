/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm

/-!
# The rank of the projective tensor product

Tau Ceti's projective tensor product `TauCeti.ProjectiveTensor 𝕜 E F` of two normed spaces is the
algebraic tensor product `E ⊗[𝕜] F` with the projective seminorm, and the two are linearly
equivalent (`TauCeti.ProjectiveTensor.linearEquiv`). This file records the consequence for ranks:
`TauCeti.ProjectiveTensor.finrank_eq_mul`, the counterpart of Mathlib's
`Module.finrank_tensorProduct`.
-/

public section

open Module

namespace TauCeti.ProjectiveTensor

/-- The projective tensor product of two normed spaces `E` and `F` has rank
`finrank 𝕜 E * finrank 𝕜 F`. -/
@[simp]
theorem finrank_eq_mul (𝕜 E F : Type*) [NormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    finrank 𝕜 (ProjectiveTensor 𝕜 E F) = finrank 𝕜 E * finrank 𝕜 F := by
  rw [(linearEquiv 𝕜 E F).finrank_eq, finrank_tensorProduct]

end TauCeti.ProjectiveTensor

end
