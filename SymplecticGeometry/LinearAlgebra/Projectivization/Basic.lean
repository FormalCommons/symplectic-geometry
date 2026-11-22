/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Projectivization.AffineChart
public import TauCeti.LinearAlgebra.Projectivization.Basic

/-!
# The representative of a point of a projective space normalized by a linear form

For a linear form `φ` on a vector space `V` over a field `K`, every point `x` of `ℙ K V` on which
`φ` does not vanish has exactly one representative `v` with `φ v = 1`. This file names it
`Projectivization.normalizedRep φ x`, and relates nonzero vectors to the lines they span.

## Main definitions

* `Projectivization.normalizedRep φ x`: the representative of `x` on which `φ` is `1` (and `0`
  if `φ` vanishes on `x`).

## Main results

* `Projectivization.apply_normalizedRep`: `φ` takes the value `1` on the normalized
  representative, on `Projectivization.linearProjectionDomain φ`.
* `Projectivization.apply_smul_normalizedRep`: a vector `u` of the line `x` is
  `φ u • normalizedRep φ x`.
* `Projectivization.mk_eq_of_mem_submodule`: a nonzero vector of a line spans it.
* `Projectivization.affineOpen_eq_linearProjectionDomain`: the standard affine open `U_i` of
  `ℙ K (ι → K)`, over a division ring `K`, is the set where the `i`-th coordinate form does not
  vanish.
* `Projectivization.insertNth_one_affineChart_eq_normalizedRep`: on the standard affine open
  `U_i` of `ℙ K (Fin (n + 1) → K)`, the homogeneous coordinates `[1 : z]` of a point are its
  representative normalized by the `i`-th coordinate.
-/

public section

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

/-- The standard affine open `U_i` of `ℙ K (ι → K)`, over a division ring `K`, is the set of
points on which the `i`-th coordinate form `LinearMap.proj i` does not vanish. -/
theorem affineOpen_eq_linearProjectionDomain {K : Type*} [DivisionRing K] {ι : Type*} (i : ι) :
    affineOpen (K := K) i = linearProjectionDomain (LinearMap.proj (R := K) i) := by
  ext x
  rw [mem_affineOpen_iff, mem_linearProjectionDomain_iff, LinearMap.proj_apply]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The representative of a point `x` of `ℙ K V` on which the linear form `φ` takes the value
`1`, if `φ` does not vanish on `x`; it is `0` otherwise. -/
def normalizedRep (φ : V →ₗ[K] K) (x : ℙ K V) : V :=
  (φ x.rep)⁻¹ • x.rep

theorem normalizedRep_def (φ : V →ₗ[K] K) (x : ℙ K V) : normalizedRep φ x = (φ x.rep)⁻¹ • x.rep :=
  (rfl)

@[simp]
theorem normalizedRep_mk (φ : V →ₗ[K] K) {v : V} (hv : v ≠ 0) :
    normalizedRep φ (mk K v hv) = (φ v)⁻¹ • v := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv
  rw [normalizedRep_def, ← ha, Units.smul_def, map_smul, smul_eq_mul, smul_smul, mul_inv]
  congr 1
  field_simp

theorem normalizedRep_mem_submodule (φ : V →ₗ[K] K) (x : ℙ K V) :
    normalizedRep φ x ∈ x.submodule := by
  rw [normalizedRep_def, submodule_eq]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem apply_normalizedRep {φ : V →ₗ[K] K} {x : ℙ K V} (hx : x ∈ linearProjectionDomain φ) :
    φ (normalizedRep φ x) = 1 := by
  rw [mem_linearProjectionDomain_iff] at hx
  rw [normalizedRep_def, map_smul, smul_eq_mul, inv_mul_cancel₀ hx]

/-- A vector of the line `x` is the multiple of the normalized representative by its value
under `φ`. -/
theorem apply_smul_normalizedRep {φ : V →ₗ[K] K} {x : ℙ K V} (hx : x ∈ linearProjectionDomain φ)
    {u : V} (hu : u ∈ x.submodule) : φ u • normalizedRep φ x = u := by
  rw [submodule_eq, Submodule.mem_span_singleton] at hu
  obtain ⟨c, rfl⟩ := hu
  rw [mem_linearProjectionDomain_iff] at hx
  rw [normalizedRep_def, smul_smul, map_smul, smul_eq_mul, mul_assoc, mul_inv_cancel₀ hx,
    mul_one]

theorem mem_submodule_mk {v : V} (hv : v ≠ 0) : v ∈ (mk K v hv).submodule := by
  rw [submodule_mk]
  exact Submodule.mem_span_singleton_self v

/-- A nonzero vector of a line spans it. -/
theorem mk_eq_of_mem_submodule {x : ℙ K V} {v : V} (hv : v ≠ 0) (hx : v ∈ x.submodule) :
    mk K v hv = x := by
  rw [submodule_eq, Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  conv_rhs => rw [← mk_rep x]
  exact (mk_eq_mk_iff' K _ _ hv x.rep_ne_zero).2 ⟨c, rfl⟩

/-- On the standard affine open `U_i`, the homogeneous coordinates `[1 : z]` of a point, with `1`
in position `i` and `z` its affine coordinates, are its representative on which the `i`-th
coordinate is `1`. -/
theorem insertNth_one_affineChart_eq_normalizedRep {n : ℕ} (i : Fin (n + 1))
    {x : ℙ K (Fin (n + 1) → K)} (hx : x ∈ affineOpen i) :
    Fin.insertNth (α := fun _ ↦ K) i 1 (affineChart i x) = normalizedRep (LinearMap.proj i) x := by
  ext l
  rw [← rep_div_rep_eq_insertNth_affineChart l hx, normalizedRep_def, LinearMap.proj_apply,
    Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

end Projectivization

end

end
