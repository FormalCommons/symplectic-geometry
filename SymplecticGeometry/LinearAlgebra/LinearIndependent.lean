/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Spanning and linearly independent families under a linear equivalence

A linear equivalence `e : M ≃ₗ[R] N` sends a family `v : ι → M` to a family `e ∘ v` that spans
`N` exactly when `v` spans `M` (`LinearEquiv.top_le_span_range_comp_iff`), and that is linearly
independent and spanning exactly when `v` is
(`LinearEquiv.linearIndependent_comp_and_top_le_span_iff`). The second statement is the form
in which the hypotheses of the Leray–Hirsch theorem ask for a basis, without choosing one.
-/

public section

open Set Submodule

namespace LinearEquiv

variable {ι R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- The image of a family under a linear equivalence spans the target exactly when the family
spans the source. -/
theorem top_le_span_range_comp_iff (e : M ≃ₗ[R] N) (v : ι → M) :
    ⊤ ≤ span R (range (e ∘ v)) ↔ ⊤ ≤ span R (range v) := by
  rw [top_le_iff, top_le_iff, Set.range_comp, ← e.coe_coe, span_image, Submodule.map_eq_top_iff]

/-- The image of a family under a linear equivalence is linearly independent and spans the target
exactly when the family is linearly independent and spans the source. -/
theorem linearIndependent_comp_and_top_le_span_iff (e : M ≃ₗ[R] N) (v : ι → M) :
    (LinearIndependent R (e ∘ v) ∧ ⊤ ≤ span R (range (e ∘ v))) ↔
      LinearIndependent R v ∧ ⊤ ≤ span R (range v) :=
  and_congr ((e : M →ₗ[R] N).linearIndependent_iff_of_injOn e.injective.injOn)
    (e.top_le_span_range_comp_iff v)

end LinearEquiv

end
