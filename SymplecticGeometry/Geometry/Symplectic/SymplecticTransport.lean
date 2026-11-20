/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Linear maps that pull a symplectic form back to plus or minus itself

A linear endomorphism `Ψ` of a real symplectic vector space `(V, ω)` with `Ψ^* ω = ω` or
`Ψ^* ω = -ω` is injective, since `ω` is nondegenerate, and hence bijective when `V` has finite
dimension: `TauCeti.SymplecticForm.bijective_of_forall_apply_eq_or_forall_apply_eq_neg`. Such a
map, symplectic or anti-symplectic, is therefore a linear equivalence
(`LinearEquiv.ofBijective`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A linear endomorphism `Ψ` of a finite-dimensional real symplectic vector space `(V, ω)` with
`ω(Ψ v, Ψ w) = ω(v, w)` for all `v, w`, or `ω(Ψ v, Ψ w) = -ω(v, w)` for all `v, w`, is
bijective. -/
theorem bijective_of_forall_apply_eq_or_forall_apply_eq_neg [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) {Ψ : V →ₗ[ℝ] V}
    (hΨ : (∀ v w, ω (Ψ v) (Ψ w) = ω v w) ∨ ∀ v w, ω (Ψ v) (Ψ w) = -ω v w) :
    Function.Bijective Ψ := by
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine ω.nondegenerate.1 v fun w ↦ ?_
    change ω v w = 0
    rcases hΨ with h | h
    · rw [← h, hv]
      exact LinearMap.map_zero₂ _ _
    · rw [← neg_eq_zero, ← h, hv]
      exact LinearMap.map_zero₂ _ _
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

end TauCeti.SymplecticForm

end
