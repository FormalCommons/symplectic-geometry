/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Basic

/-!
# Rough differential forms

Facts about Tau Ceti's rough forms `TauCeti.RoughForm` that Tau Ceti does not state.

A rough form cast along an equality of degrees `p = q` by `LinearEquiv.cast` evaluates as the
original form on the reindexed vectors (`TauCeti.RoughForm.cast_apply`), as Tau Ceti's
`TauCeti.SmoothForm.cast_apply` says for smooth forms.
-/

public section

namespace TauCeti.RoughForm

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul ℝ V]

/-- A rough form cast along an equality of degrees `p = q` takes on `w` the value of the
original form on `w` reindexed along `Fin.cast h`, as `TauCeti.SmoothForm.cast_apply` says for
smooth forms. -/
theorem cast_apply {p q : ℕ} (h : p = q) (α : RoughForm I M V p) (x : M)
    (w : Fin q → TangentSpace I x) :
    LinearEquiv.cast (R := ℝ) (M := fun k ↦ RoughForm I M V k) h α x w =
      α x (w ∘ Fin.cast h) := by
  subst h
  simp only [LinearEquiv.cast_apply, cast_eq, Function.comp_def, Fin.cast_eq_self]

end TauCeti.RoughForm

end
