/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# The special linear group acting on a projective space, and the projective line

Algebraic facts about projective spaces of coordinate vector spaces that complement Mathlib's
`Mathlib/LinearAlgebra/Projectivization/Action.lean` and
`Mathlib/LinearAlgebra/Projectivization/Cardinality.lean`.

## Main results

* `Matrix.SpecialLinearGroup.toGL_smul_projectivization`: `SL_n(K)` acts on `ℙ K (n → K)`
  through its image in `GL_n(K)`.
* `Projectivization.infinite_projectiveLine`: the projective line `ℙ K (Fin 2 → K)` over an
  infinite division ring is infinite.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Matrix.SpecialLinearGroup

/-- A special linear matrix acts on the projective space `ℙ K (n → K)` as its image in the general
linear group does. -/
@[simp]
theorem toGL_smul_projectivization {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (g : SpecialLinearGroup n K) (x : ℙ K (n → K)) : toGL g • x = g • x := by
  induction x using Projectivization.ind with
  | h v hv => simp [Projectivization.smul_mk, SpecialLinearGroup.smul_def, Units.smul_def]

end Matrix.SpecialLinearGroup

namespace Projectivization

/-- The projective line `ℙ K (Fin 2 → K)` over an infinite division ring `K` is infinite: the
affine coordinate `t ↦ [1 : t]` is injective. -/
instance infinite_projectiveLine {K : Type*} [DivisionRing K] [Infinite K] :
    Infinite (ℙ K (Fin 2 → K)) :=
  Infinite.of_injective (fun t : K ↦ mk K ![1, t] (by simp)) fun s t hst ↦ by
    obtain ⟨a, ha⟩ := (mk_eq_mk_iff' K _ _ _ _).1 hst
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    simp at h0 h1
    simpa [h0] using h1.symm

end Projectivization

end
