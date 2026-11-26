/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic

/-!
# Periods of the exponential of a Lie group

For a Lie group `G` with Lie algebra `𝔤`, the set `nonzeroPeriods I G` consists of the nonzero
`ξ ∈ 𝔤` with `exp ξ = 1`: the nonzero generators of one-parameter subgroups `t ↦ exp (t ξ)` that
have period `1`. It is written `Λ` in [GeorgoulasRobbinSalamon2021]. For a commutative `G`,
`Λ ∪ {0}` is the kernel of the exponential, Tau Ceti's `lieExpAddMonoidHom.ker` transported to
`GroupLieAlgebra I G` by `leftInvariantDerivationEquivGroupLieAlgebra`; it is `2π` times Tau
Ceti's `periodLattice`, which is normalized by `exp (2π X) = 1`. For a noncommutative `G`, such
as `SU(2)`, `Λ ∪ {0}` need not be closed under addition, so it is a set and not a lattice.
It is invariant under the adjoint action of `G`, under negation and under
multiplication by nonzero integers.

## Main definitions

* `SymplecticGeometry.nonzeroPeriods I G`: the nonzero `ξ` in the Lie algebra with
  `mulInvariantExp ξ = 1`.

## Main results

* `SymplecticGeometry.tangentAd_mem_nonzeroPeriods`: `nonzeroPeriods I G` is invariant under
  the adjoint action.
* `SymplecticGeometry.nsmul_mem_nonzeroPeriods`, `SymplecticGeometry.zsmul_mem_nonzeroPeriods`:
  `nonzeroPeriods I G` is invariant under multiplication by nonzero natural numbers and integers.
* `SymplecticGeometry.neg_mem_nonzeroPeriods`: `nonzeroPeriods I G` is invariant under negation.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021].
-/

public section

open TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [BoundarylessManifold I G]

/-- The nonzero elements `ξ` of the Lie algebra of `G` with `exp ξ = 1`, that is, the nonzero
generators of the one-parameter subgroups `t ↦ exp (t • ξ)` of which `1` is a period. It is the set
`Λ` of the Hilbert–Mumford criterion. -/
def nonzeroPeriods : Set (GroupLieAlgebra I G) :=
  {ξ | ξ ≠ 0 ∧ mulInvariantExp ξ = 1}

variable {I G}

theorem mem_nonzeroPeriods {ξ : GroupLieAlgebra I G} :
    ξ ∈ nonzeroPeriods I G ↔ ξ ≠ 0 ∧ mulInvariantExp ξ = 1 :=
  Iff.rfl

@[simp]
theorem zero_notMem_nonzeroPeriods : (0 : GroupLieAlgebra I G) ∉ nonzeroPeriods I G :=
  fun h ↦ h.1 rfl

/-- `nonzeroPeriods I G` is invariant under the adjoint action of `G`. -/
theorem tangentAd_mem_nonzeroPeriods {ξ : GroupLieAlgebra I G} (hξ : ξ ∈ nonzeroPeriods I G)
    (u : G) : Lie.tangentAd (I := I) u ξ ∈ nonzeroPeriods I G := by
  refine ⟨(map_ne_zero_iff _ (Lie.tangentAd (I := I) u).injective).2 hξ.1, ?_⟩
  rw [← Lie.conj_mulInvariantExp, hξ.2, mul_one, mul_inv_cancel]

/-- An element lies in `nonzeroPeriods I G` exactly when its image under `Ad u` does. -/
theorem tangentAd_mem_nonzeroPeriods_iff {ξ : GroupLieAlgebra I G} (u : G) :
    Lie.tangentAd (I := I) u ξ ∈ nonzeroPeriods I G ↔ ξ ∈ nonzeroPeriods I G := by
  refine ⟨fun h ↦ ?_, fun h ↦ tangentAd_mem_nonzeroPeriods h u⟩
  have h' := tangentAd_mem_nonzeroPeriods h u⁻¹
  rwa [Lie.tangentAd_inv, LieEquiv.symm_apply_apply] at h'

/-- `nonzeroPeriods I G` is invariant under multiplication by positive integers. -/
theorem nsmul_mem_nonzeroPeriods {ξ : GroupLieAlgebra I G} (hξ : ξ ∈ nonzeroPeriods I G)
    {n : ℕ} (hn : n ≠ 0) : n • ξ ∈ nonzeroPeriods I G :=
  ⟨by rw [← Nat.cast_smul_eq_nsmul ℝ]; exact smul_ne_zero (Nat.cast_ne_zero.2 hn) hξ.1,
    by rw [mulInvariantExp_nsmul, hξ.2, one_pow]⟩

/-- `nonzeroPeriods I G` is invariant under negation. -/
theorem neg_mem_nonzeroPeriods {ξ : GroupLieAlgebra I G} (hξ : ξ ∈ nonzeroPeriods I G) :
    -ξ ∈ nonzeroPeriods I G :=
  ⟨neg_ne_zero.2 hξ.1, by rw [mulInvariantExp_neg, hξ.2, inv_one]⟩

/-- `-ξ` lies in `nonzeroPeriods I G` exactly when `ξ` does. -/
@[simp]
theorem neg_mem_nonzeroPeriods_iff {ξ : GroupLieAlgebra I G} :
    -ξ ∈ nonzeroPeriods I G ↔ ξ ∈ nonzeroPeriods I G :=
  ⟨fun h ↦ neg_neg ξ ▸ neg_mem_nonzeroPeriods h, neg_mem_nonzeroPeriods⟩

/-- `nonzeroPeriods I G` is invariant under multiplication by nonzero integers. -/
theorem zsmul_mem_nonzeroPeriods {ξ : GroupLieAlgebra I G} (hξ : ξ ∈ nonzeroPeriods I G)
    {n : ℤ} (hn : n ≠ 0) : n • ξ ∈ nonzeroPeriods I G := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [natCast_zsmul]
    exact nsmul_mem_nonzeroPeriods hξ (by exact_mod_cast hn)
  · rw [neg_zsmul, natCast_zsmul, neg_mem_nonzeroPeriods_iff]
    exact nsmul_mem_nonzeroPeriods hξ (by simpa using hn)

end SymplecticGeometry

end
