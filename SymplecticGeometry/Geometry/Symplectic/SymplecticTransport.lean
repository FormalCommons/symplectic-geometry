/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport
import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Linear maps that pull a symplectic form back to plus or minus itself

A linear endomorphism `Ψ` of a real symplectic vector space `(V, ω)` with `Ψ^* ω = ω` or
`Ψ^* ω = -ω` is injective, since `ω` is nondegenerate, and hence bijective when `V` has finite
dimension: `TauCeti.SymplecticForm.bijective_of_forall_apply_eq_or_forall_apply_eq_neg`. Its
injectivity is Tau Ceti's `TauCeti.SymplecticForm.injective_of_map_eq_mul`, with multiplier `1`
or `-1`. Such a map, symplectic or anti-symplectic, is therefore a linear equivalence
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
    rcases hΨ with h | h
    · exact ω.injective_of_map_eq_mul one_ne_zero fun v w ↦ (h v w).trans (one_mul _).symm
    · exact ω.injective_of_map_eq_mul (neg_ne_zero.2 one_ne_zero) fun v w ↦
        (h v w).trans (neg_one_mul _).symm
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

end TauCeti.SymplecticForm

end
