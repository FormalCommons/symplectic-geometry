/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Projectivization.AffineChart
public import TauCeti.LinearAlgebra.Projectivization.Basic
public import SymplecticGeometry.Algebra.Notation.Pi.Basic

/-!
# The representative of a point of a projective space normalized by a linear form

For a linear form `φ` on a vector space `V` over a field `K`, every point `x` of `ℙ K V` on which
`φ` does not vanish has exactly one representative `v` with `φ v = 1`. This file names it
`Projectivization.normalizedRep φ x`.

## Main definitions

* `Projectivization.normalizedRep φ x`: the representative of `x` on which `φ` is `1` (and `0`
  if `φ` vanishes on `x`).

## Main results

* `Projectivization.apply_normalizedRep`: `φ` takes the value `1` on the normalized
  representative, on `Projectivization.linearProjectionDomain φ`.
* `Projectivization.normalizedRep_ne_zero`: the normalized representative is nonzero there.
* `Projectivization.normalizedRep_eq_zero_iff`: it is `0` exactly off
  `Projectivization.linearProjectionDomain φ`.
* `Projectivization.apply_smul_normalizedRep`: a vector `u` of the line `x` is
  `φ u • normalizedRep φ x`.
* `Projectivization.mem_range_map_iff`: over a division ring, a point is in the image of the map
  induced by an injective linear map `f` exactly when its representative is in the range of
  `f`.
* `Projectivization.affineOpen_eq_linearProjectionDomain`: the standard affine open `U_i` of
  `ℙ K (ι → K)`, over a division ring `K`, is the set where the `i`-th coordinate form does not
  vanish.
* `Projectivization.affineOpen_injective`: distinct indices give distinct standard affine opens.
* `Projectivization.insertNth_one_affineChart_eq_normalizedRep`: on the standard affine open
  `U_i` of `ℙ K (Fin (n + 1) → K)`, the homogeneous coordinates `[1 : z]` of a point are its
  representative normalized by the `i`-th coordinate.
* `Projectivization.affineChart_symm_removeNth`: the inverse of the standard affine chart at `i`
  sends the coordinates of `w` other than `i` to the line spanned by `update w i 1`.
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

/-- Distinct indices give distinct standard affine opens of `ℙ K (ι → K)`: the coordinate point
`[eᵢ]` lies in the standard affine open of `i` and of no other index. -/
theorem affineOpen_injective {K : Type*} [DivisionRing K] {ι : Type*} :
    Function.Injective (affineOpen (K := K) (ι := ι)) := by
  classical
  intro i j h
  exact ((mk_single_mem_affineOpen_iff (K := K) i j).1
    (h ▸ (mk_single_mem_affineOpen_iff i i).2 rfl)).symm

/-- A point of `ℙ K W` lies in the image of the map induced by an injective linear map `f`
exactly when its representative lies in the range of `f`. -/
theorem mem_range_map_iff {K V W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {f : V →ₗ[K] W} (hf : Function.Injective f) {x : ℙ K W} :
    x ∈ Set.range (map f hf) ↔ x.rep ∈ LinearMap.range f := by
  constructor
  · rintro ⟨y, rfl⟩
    refine LinearMap.map_le_range (p := y.submodule) ?_
    rw [← submodule_map f hf y, submodule_eq]
    exact Submodule.mem_span_singleton_self _
  · rintro ⟨u, hu⟩
    have hu0 : u ≠ 0 := by rintro rfl; exact x.rep_ne_zero (by simp [← hu])
    refine ⟨mk K u hu0, ?_⟩
    rw [map_mk]
    conv_rhs => rw [← mk_rep x]
    simp_rw [hu]

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

/-- The normalized representative of a point of `linearProjectionDomain φ`, where `φ` does not
vanish, is nonzero. -/
theorem normalizedRep_ne_zero {φ : V →ₗ[K] K} {x : ℙ K V} (hx : x ∈ linearProjectionDomain φ) :
    normalizedRep φ x ≠ 0 := fun h ↦ one_ne_zero (by rw [← apply_normalizedRep hx, h, map_zero])

/-- The normalized representative of a point outside `linearProjectionDomain φ`, where `φ`
vanishes, is `0`. -/
theorem normalizedRep_of_notMem {φ : V →ₗ[K] K} {x : ℙ K V}
    (hx : x ∉ linearProjectionDomain φ) : normalizedRep φ x = 0 := by
  rw [mem_linearProjectionDomain_iff, not_not] at hx
  rw [normalizedRep_def, hx, inv_zero, zero_smul]

/-- The normalized representative of `x` is `0` exactly when `x` lies outside
`linearProjectionDomain φ`, that is, when `φ` vanishes on `x`. -/
@[simp]
theorem normalizedRep_eq_zero_iff {φ : V →ₗ[K] K} {x : ℙ K V} :
    normalizedRep φ x = 0 ↔ x ∉ linearProjectionDomain φ :=
  ⟨fun h hx ↦ normalizedRep_ne_zero hx h, normalizedRep_of_notMem⟩

/-- A vector of the line `x` is the multiple of the normalized representative by its value
under `φ`. -/
theorem apply_smul_normalizedRep {φ : V →ₗ[K] K} {x : ℙ K V} (hx : x ∈ linearProjectionDomain φ)
    {u : V} (hu : u ∈ x.submodule) : φ u • normalizedRep φ x = u := by
  rw [submodule_eq, Submodule.mem_span_singleton] at hu
  obtain ⟨c, rfl⟩ := hu
  rw [mem_linearProjectionDomain_iff] at hx
  rw [normalizedRep_def, smul_smul, map_smul, smul_eq_mul, mul_assoc, mul_inv_cancel₀ hx,
    mul_one]

/-- On the standard affine open `U_i`, the homogeneous coordinates `[1 : z]` of a point, with `1`
in position `i` and `z` its affine coordinates, are its representative on which the `i`-th
coordinate is `1`. -/
theorem insertNth_one_affineChart_eq_normalizedRep {n : ℕ} (i : Fin (n + 1))
    {x : ℙ K (Fin (n + 1) → K)} (hx : x ∈ affineOpen i) :
    Fin.insertNth (α := fun _ ↦ K) i 1 (affineChart i x) = normalizedRep (LinearMap.proj i) x := by
  conv_lhs => rw [← mk_rep x, affineChart_mk]
  rw [Fin.insertNth_one_div_eq_inv_smul i _ ((mem_affineOpen_iff i x).1 hx), normalizedRep_def,
    LinearMap.proj_apply]

/-- The inverse of the standard affine chart at `i`, applied to the coordinates of `w` other than
the `i`-th, is the line spanned by `w` with its `i`-th coordinate replaced by `1`. -/
theorem affineChart_symm_removeNth {n : ℕ} (i : Fin (n + 1)) (w : Fin (n + 1) → K) :
    (affineChart i).symm (Fin.removeNth i w) =
      mk K (Function.update w i 1) (Function.update_ne_zero w i one_ne_zero) := by
  simp only [affineChart_symm_apply, Fin.insertNth_removeNth]

end Projectivization

end

end
