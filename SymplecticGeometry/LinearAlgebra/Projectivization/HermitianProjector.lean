/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Projectivization.Basic
public import TauCeti.LinearAlgebra.Projectivization.HermitianProjector

/-!
# The Hermitian projector in the standard affine charts

Tau Ceti's `Projectivization.hermitianProjector x` is the orthogonal projection of `ι → K` onto
the line `x`, for the standard Hermitian form. This file computes it from the homogeneous
coordinates `[1 : z]` of `x` in a standard affine chart, and records that it fixes the line.

## Main results

* `Projectivization.hermitianProjector_eq_rankOneHermitianProjector_of_mem_submodule`: the
  Hermitian projector of a line is the rank-one Hermitian projector of any nonzero vector of it.
* `Projectivization.hermitianProjector_eq_rankOneHermitianProjector_insertNth`: on the standard
  affine open `U_i`, the Hermitian projector of a point is the rank-one Hermitian projector of its
  homogeneous coordinates `[1 : z]`.
* `Projectivization.one_sub_hermitianProjector_mulVec`: on `U_i`, `1 - hermitianProjector x`
  subtracts from a vector its orthogonal projection onto the line, written through `[1 : z]`.
* `Projectivization.hermitianProjector_mulVec_of_mem_submodule` and
  `Projectivization.one_sub_hermitianProjector_mulVec_of_mem_submodule`: over `ℝ` or `ℂ`, the
  Hermitian projector fixes the vectors of the line, and `1 - hermitianProjector x` kills them.
-/

public section

open Matrix
open scoped LinearAlgebra.Projectivization ComplexOrder

namespace Projectivization

section Field

variable {n : ℕ} {K : Type*} [Field K] [StarRing K]

/-- The Hermitian projector of a line is the rank-one Hermitian projector of any nonzero vector
of the line. -/
theorem hermitianProjector_eq_rankOneHermitianProjector_of_mem_submodule {ι : Type*} [Fintype ι]
    {x : ℙ K (ι → K)} {v : ι → K} (hv : v ≠ 0) (hx : v ∈ x.submodule) :
    hermitianProjector x = TauCeti.rankOneHermitianProjector v := by
  rw [← mem_submodule_iff.1 hx hv, hermitianProjector_mk]

/-- On the standard affine open `U_i`, the Hermitian projector of a point is the rank-one
Hermitian projector of its homogeneous coordinates `[1 : z]`, with `1` in position `i`. -/
theorem hermitianProjector_eq_rankOneHermitianProjector_insertNth (i : Fin (n + 1))
    {x : ℙ K (Fin (n + 1) → K)} (hx : x ∈ affineOpen i) :
    hermitianProjector x =
      TauCeti.rankOneHermitianProjector (Fin.insertNth (α := fun _ ↦ K) i 1 (affineChart i x)) :=
  hermitianProjector_eq_rankOneHermitianProjector_of_mem_submodule (Fin.insertNth_one_ne_zero i _)
    (insertNth_one_affineChart_eq_normalizedRep i hx ▸ normalizedRep_mem_submodule _ x)

/-- On the standard affine open `U_i`, `1 - hermitianProjector x` subtracts from a vector `u` its
orthogonal projection `((v* u) / (v* v)) • v` onto the line spanned by the homogeneous
coordinates `v = [1 : z]` of `x`, with `1` in position `i`. -/
theorem one_sub_hermitianProjector_mulVec (i : Fin (n + 1)) {x : ℙ K (Fin (n + 1) → K)}
    (hx : x ∈ affineOpen i) (u : Fin (n + 1) → K) :
    (1 - hermitianProjector x) *ᵥ u = u -
      ((star (Fin.insertNth (α := fun _ ↦ K) i 1 (affineChart i x)) ⬝ᵥ u) /
        (star (Fin.insertNth (α := fun _ ↦ K) i 1 (affineChart i x)) ⬝ᵥ
          Fin.insertNth (α := fun _ ↦ K) i 1 (affineChart i x))) •
        Fin.insertNth (α := fun _ ↦ K) i 1 (affineChart i x) := by
  rw [sub_mulVec, one_mulVec, hermitianProjector_eq_rankOneHermitianProjector_insertNth i hx,
    TauCeti.rankOneHermitianProjector_mulVec]

end Field

section RCLike

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]

/-- Over `ℝ` or `ℂ`, the Hermitian projector of a line fixes the vectors of the line. -/
theorem hermitianProjector_mulVec_of_mem_submodule {x : ℙ 𝕜 (ι → 𝕜)} {v : ι → 𝕜}
    (hv : v ∈ x.submodule) : hermitianProjector x *ᵥ v = v := by
  rw [submodule_eq, Submodule.mem_span_singleton] at hv
  obtain ⟨c, rfl⟩ := hv
  rw [hermitianProjector_eq_rankOneHermitianProjector_of_mem_submodule x.rep_ne_zero
      (x.submodule_eq ▸ Submodule.mem_span_singleton_self _), mulVec_smul,
    TauCeti.rankOneHermitianProjector_mulVec_self
      (dotProduct_star_self_eq_zero.not.2 x.rep_ne_zero)]

/-- Over `ℝ` or `ℂ`, `1 - hermitianProjector x`, the orthogonal projection onto the orthogonal
complement of the line `x`, kills the vectors of the line. -/
theorem one_sub_hermitianProjector_mulVec_of_mem_submodule [DecidableEq ι] {x : ℙ 𝕜 (ι → 𝕜)}
    {v : ι → 𝕜} (hv : v ∈ x.submodule) : (1 - hermitianProjector x) *ᵥ v = 0 := by
  rw [sub_mulVec, one_mulVec, hermitianProjector_mulVec_of_mem_submodule hv, sub_self]

end RCLike

end Projectivization

end
