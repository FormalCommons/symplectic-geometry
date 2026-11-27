/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# Signs of top-degree alternating maps

Over an ordered commutative ring, an alternating map `f` of `n` vectors of a module with a basis
`e` of `n` elements is the multiple `f e • e.det` of the determinant in that basis
(`AlternatingMap.eq_smul_basis_det`). So two such maps `f` and `g` compare in the same way on
every family: if both are positive on one family `v`, then the sign of `e.det v` is that of
`f e` and of `g e`, so `f` and `g` have the same sign on `e`
(`AlternatingMap.pos_apply_basis_of_pos`). On a plane, this says that two area forms positive on
one pair of vectors are positive on the same oriented bases.
-/

public section

namespace AlternatingMap

variable {R M ι : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [Module R M] [Finite ι]

/-- Two alternating maps `f` and `g` of top degree that are both positive on some family `v` have
the same sign on every basis: if `f` is positive on the basis `e`, so is `g`. -/
theorem pos_apply_basis_of_pos {f g : M [⋀^ι]→ₗ[R] R} (e : Module.Basis ι R M) {v : ι → M}
    (hf : 0 < f v) (hg : 0 < g v) (he : 0 < f e) : 0 < g e := by
  classical
  have := Fintype.ofFinite ι
  rw [f.eq_smul_basis_det e, smul_apply, smul_eq_mul] at hf
  rw [g.eq_smul_basis_det e, smul_apply, smul_eq_mul] at hg
  exact pos_of_mul_pos_left hg (pos_of_mul_pos_right hf he.le).le

end AlternatingMap

end
