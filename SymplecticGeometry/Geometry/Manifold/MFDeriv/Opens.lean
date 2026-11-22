/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Differentiability of the inclusion of an open subset

The inclusion `Subtype.val : U → M` of an open subset `U` of a charted space `M` is differentiable
(`mdifferentiableAt_subtypeVal`, `mdifferentiable_subtypeVal`), since it is smooth at every
regularity (Mathlib's `contMDiff_subtypeVal`). Its differential is Tau Ceti's
`TauCeti.Manifold.mfderiv_subtype_val`.
-/

public section

open TopologicalSpace

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {U : Opens M}

/-- The inclusion of an open subset is differentiable at each point. -/
theorem mdifferentiableAt_subtypeVal {x : U} : MDifferentiableAt I I (Subtype.val : U → M) x :=
  (contMDiff_subtypeVal (n := 1) x).mdifferentiableAt one_ne_zero

/-- The inclusion of an open subset is differentiable. -/
theorem mdifferentiable_subtypeVal : MDifferentiable I I (Subtype.val : U → M) :=
  fun _ ↦ mdifferentiableAt_subtypeVal

end
