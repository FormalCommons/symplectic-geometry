/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of the self-adjoint elements of a star module

For a star module `A` over a Noetherian ring `R` with trivial star, the self-adjoint elements of
`A` form a finite `R`-module whenever `A` is one: they are the carrier of Mathlib's submodule
`selfAdjoint.submodule R A`, and a submodule of a finite module over a Noetherian ring is finite.

## Main results

* `selfAdjoint.instModuleFinite`: `Module.Finite R (selfAdjoint A)`. For instance, the
  symmetric matrices over a field, or the complex Hermitian matrices over `ℝ`, form a
  finite-dimensional space.
-/

public section

variable {R A : Type*} [Ring R] [StarMul R] [TrivialStar R] [IsNoetherianRing R]
  [AddCommGroup A] [StarAddMonoid A] [Module R A] [StarModule R A]

/-- Over a Noetherian ring with trivial star, the self-adjoint elements of a finite star module
form a finite module. -/
instance selfAdjoint.instModuleFinite [Module.Finite R A] : Module.Finite R (selfAdjoint A) :=
  -- `selfAdjoint A` is only an additive subgroup; its carrier is that of `selfAdjoint.submodule`.
  inferInstanceAs (Module.Finite R (selfAdjoint.submodule R A))

end
