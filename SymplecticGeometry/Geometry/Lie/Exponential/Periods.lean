/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
public import TauCeti.Geometry.Lie.Subgroup.OneParameter
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import TauCeti.Geometry.Lie.Adjoint.Infinitesimal
import TauCeti.Geometry.Lie.Exponential.LocalInverse
import SymplecticGeometry.Analysis.RCLike.Basic
import SymplecticGeometry.Geometry.Lie.Exponential.Commute
import SymplecticGeometry.Geometry.Lie.Subgroup.OneParameter

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
* `exists_mulInvariantExp_eq_pow_of_mem_nhds`: in a compact Lie group, every neighbourhood of `0`
  contains some `η` whose exponential is a positive power of a given element.
* `SymplecticGeometry.mem_closure_smul_nonzeroPeriods`: for compact `G`, a nonzero `ξ` is a limit
  of positive multiples of periods that bracket to zero with everything that brackets to zero
  with `ξ`.
* `TauCeti.Lie.IsTorus.exists_mem_nonzeroPeriods_closedOneParameterSubgroup_le`: a nontrivial
  torus contains `T_λ` for some `λ ∈ nonzeroPeriods I G`.
* `SymplecticGeometry.exists_mem_nonzeroPeriods_closedOneParameterSubgroup_le`: in a compact Lie
  group, for each `ξ ≠ 0` some `λ ∈ nonzeroPeriods I G` has `T_λ ≤ T_ξ`.

## Implementation notes

The Hilbert–Mumford criterion uses `mem_closure_smul_nonzeroPeriods` to replace a direction of
positive weight by a positive multiple of a nearby period. The proof: some power `exp ξ ^ m`
with `m > 0` is close to `1` (Mathlib's `mapClusterPt_one_atTop_pow`), so it is `exp η` for a
small `η`. For `⁅ζ, ξ⁆ = 0`, each `exp (s • ζ)` commutes with `exp η`, so for small `s` it fixes
`η` under `Ad`, the exponential being injective near `0`; hence `⁅ζ, η⁆ = 0`. Then
`λ = m • ξ - η` is a period with `ξ - m⁻¹ • λ = m⁻¹ • η`. Smallness is measured by a balanced
neighbourhood of `0`, so no norm on the Lie algebra is needed.

Together with Tau Ceti's `TauCeti.Lie.mem_isotropy_fundamental_iff_closedOneParameterSubgroup_le`,
the last result turns a nonzero element of an isotropy algebra into a nonzero period in the
same isotropy algebra, for the stable case of the Hilbert–Mumford criterion of
[GeorgoulasRobbinSalamon2021]. Its proof is that of Tau Ceti's
`TauCeti.Lie.IsTorus.exists_closedOneParameterSubgroup_eq`, with an involution of the torus
(`TauCeti.Lie.IsTorus.exists_sq_eq_one_ne_one`) in place of a topological generator: if `exp X`
is that involution, with `X` in the Lie algebra of the torus, then `λ = 2 • X` is a period.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021].
-/

public section

open TauCeti Filter
open scoped Manifold ContDiff Topology

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

section Recurrence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [BoundarylessManifold I G] [CompactSpace G]

/-- In a compact Lie group, every neighbourhood `W` of `0` in the Lie algebra contains some `η`
whose exponential is a positive power of a given element `g`. -/
theorem exists_mulInvariantExp_eq_pow_of_mem_nhds (g : G) {W : Set (GroupLieAlgebra I G)}
    (hW : W ∈ 𝓝 0) : ∃ m : ℕ, 0 < m ∧ ∃ η ∈ W, mulInvariantExp η = g ^ m := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  -- Near `1`, the logarithm lands in `W` and is a right inverse of the exponential.
  have hlog : ∀ᶠ h in 𝓝 (1 : G), mulInvariantLog (I := I) h ∈ W ∧
      mulInvariantExp (mulInvariantLog (I := I) h) = h := by
    refine Eventually.and ?_ (eventually_mulInvariantExp_log (I := I) (G := G))
    have hcont := (contMDiffAt_mulInvariantLog_one (I := I) (G := G)).continuousAt
    exact hcont.preimage_mem_nhds (by rwa [mulInvariantLog_one])
  obtain ⟨m, hm, hmW, hmexp⟩ :=
    ((mapClusterPt_one_atTop_pow g).frequently hlog).forall_exists_of_atTop 1
  exact ⟨m, hm, _, hmW, hmexp⟩

end Recurrence

namespace SymplecticGeometry

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

/-- **Positive multiples of periods approximate a direction.** For a compact Lie group `G` and a
nonzero `ξ` in its Lie algebra, `ξ` lies in the closure of the positive multiples `c • λ` of
the periods `λ ∈ nonzeroPeriods I G` that bracket to zero with every `ζ` such that
`⁅ζ, ξ⁆ = 0`. -/
theorem mem_closure_smul_nonzeroPeriods [FiniteDimensional ℝ E] [CompactSpace G]
    {ξ : GroupLieAlgebra I G} (hξ : ξ ≠ 0) :
    ξ ∈ closure {x | ∃ c : ℝ, 0 < c ∧ ∃ l ∈ nonzeroPeriods I G,
      (∀ ζ : GroupLieAlgebra I G, ⁅ζ, ξ⁆ = 0 → ⁅ζ, l⁆ = 0) ∧ x = c • l} := by
  rw [mem_closure_iff_nhds]
  intro V hV
  -- `U` is a neighbourhood of `0` on which the logarithm inverts the exponential.
  set U := interior {v : GroupLieAlgebra I G | mulInvariantLog (mulInvariantExp v) = v}
  have hU : U ∈ 𝓝 0 := interior_mem_nhds.2 (eventually_mulInvariantLog_exp (I := I) (G := G))
  -- `W` is a balanced neighbourhood of `0` inside `U`, not containing `ξ`, with `ξ + W ⊆ V`.
  have hV' : {v : GroupLieAlgebra I G | ξ + v ∈ V} ∈ 𝓝 0 :=
    (continuous_const_add ξ).continuousAt.preimage_mem_nhds (by rwa [add_zero])
  set W := balancedCore ℝ (U ∩ {ξ}ᶜ ∩ {v | ξ + v ∈ V})
  have hW : W ∈ 𝓝 0 := balancedCore_mem_nhds_zero
    (inter_mem (inter_mem hU (isOpen_compl_singleton.mem_nhds (Ne.symm hξ))) hV')
  -- Some power `exp ξ ^ m` with `m > 0` is `exp η` for some `η ∈ W`.
  obtain ⟨m, hm, η, hηW, hηexp⟩ := exists_mulInvariantExp_eq_pow_of_mem_nhds (mulInvariantExp ξ) hW
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast hm
  have hexpη : mulInvariantExp η = mulInvariantExp (m • ξ) := by
    rw [hηexp, mulInvariantExp_nsmul]
  -- Since `W` is balanced, the multiples `c • η` with `|c| ≤ m⁻¹` stay in the set it is cut from.
  have hsmul : ∀ c : ℝ, ‖c‖ ≤ ‖(m : ℝ)⁻¹‖ → c • η ∈ U ∩ {ξ}ᶜ ∩ {v | ξ + v ∈ V} := by
    have hinv : ‖(m : ℝ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, Real.norm_natCast]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast hm)
    exact fun c hc ↦ balancedCore_subset _ <| (balancedCore.balanced _).smul_mem
      (hc.trans hinv) hηW
  -- Every `ζ` that commutes with `ξ` commutes with `η`.
  have hη : η ∈ U := (balancedCore_subset _ hηW).1.1
  have hinj : ∀ᶠ v in 𝓝 η, mulInvariantExp v = mulInvariantExp η → v = η := by
    filter_upwards [isOpen_interior.mem_nhds hη] with v hv he
    have h1 := interior_subset hv
    have h2 := interior_subset hη
    rw [Set.mem_ofPred_eq] at h1 h2
    rw [← h1, he, h2]
  have hcomm : ∀ ζ : GroupLieAlgebra I G, ⁅ζ, ξ⁆ = 0 → ⁅ζ, η⁆ = 0 := fun ζ hζ ↦
    Lie.lie_eq_zero_of_eventually_commute_mulInvariantExp_smul hinj <| .of_forall fun s ↦ by
      rw [hexpη]
      exact Lie.commute_mulInvariantExp_of_lie_eq_zero (by rw [smul_lie, lie_nsmul, hζ,
        smul_zero, smul_zero])
  -- The period is `λ = m • ξ - η`, with `m⁻¹ • λ = ξ - m⁻¹ • η`.
  have hl : (m : ℝ)⁻¹ • (m • ξ - η) = ξ + -(m : ℝ)⁻¹ • η := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_sub, inv_smul_smul₀ hm₀.ne', sub_eq_add_neg, ← neg_smul]
  refine ⟨(m : ℝ)⁻¹ • (m • ξ - η), ?_, (m : ℝ)⁻¹, inv_pos.2 hm₀, m • ξ - η, ⟨?_, ?_⟩, ?_, rfl⟩
  · have := (hsmul (-(m : ℝ)⁻¹) (by simp)).2
    rw [Set.mem_ofPred_eq] at this
    rwa [hl]
  · intro h
    rw [sub_eq_zero] at h
    refine (hsmul (m : ℝ)⁻¹ (by simp)).1.2 ?_
    rw [← h, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ hm₀.ne', Set.mem_singleton_iff]
  · have hadd := Lie.mulInvariantExp_add_of_lie_eq_zero (X := m • ξ - η) (Y := η) (by
      rw [sub_lie, lie_self, sub_zero, nsmul_lie, hcomm ξ (lie_self ξ), smul_zero])
    rwa [sub_add_cancel, hexpη, right_eq_mul] at hadd
  · intro ζ hζ
    rw [lie_sub, lie_nsmul, hζ, hcomm ζ hζ, smul_zero, sub_zero]

section ClosedOneParameterSubgroup

open Lie

variable [IsTopologicalGroup G]

variable [FiniteDimensional ℝ E]

variable (I) in
/-- A nontrivial torus `T` contains the closed one-parameter subgroup of a nonzero period: some
`λ ∈ nonzeroPeriods I G` has `T_λ ≤ T`. -/
theorem _root_.TauCeti.Lie.IsTorus.exists_mem_nonzeroPeriods_closedOneParameterSubgroup_le
    {T : Subgroup G} (hT : IsTorus T) (hT1 : T ≠ ⊥) :
    ∃ l ∈ nonzeroPeriods I G, closedOneParameterSubgroup l ≤ T := by
  -- An involution `k = exp X` of `T`, with `X` in the Lie algebra of `T`, gives `l = 2 • X`.
  obtain ⟨k, hkT, hk2, hk1⟩ := hT.exists_sq_eq_one_ne_one I hT1
  obtain ⟨X, hX, rfl⟩ := (Set.ext_iff.1 (hT.image_lieExp_lieSubalgebraOfSubgroup (I := I)) k).2 hkT
  rw [lieExp_eq_mulInvariantExp] at hk2 hk1
  refine ⟨(2 : ℝ) • _, ⟨fun h ↦ hk1 ?_, by rw [two_smul, ← two_nsmul, mulInvariantExp_nsmul, hk2]⟩,
    (closedOneParameterSubgroup_le hT.isClosed).2 fun t ↦ ?_⟩
  · rw [(smul_eq_zero.1 h).resolve_left two_ne_zero, mulInvariantExp_zero]
  · rw [smul_smul, ← map_smul, ← lieExp_eq_mulInvariantExp]
    exact (mem_lieSubalgebraOfSubgroup hT.isClosed).1 hX _

variable [CompactSpace G]

/-- In a compact Lie group, for `ξ ≠ 0` some `λ ∈ nonzeroPeriods I G` has its closed
one-parameter subgroup inside that of `ξ`: `T_λ ≤ T_ξ`. -/
theorem exists_mem_nonzeroPeriods_closedOneParameterSubgroup_le {ξ : GroupLieAlgebra I G}
    (hξ : ξ ≠ 0) :
    ∃ l ∈ nonzeroPeriods I G, closedOneParameterSubgroup l ≤ closedOneParameterSubgroup ξ :=
  (isTorus_closedOneParameterSubgroup ξ).exists_mem_nonzeroPeriods_closedOneParameterSubgroup_le I
    (closedOneParameterSubgroup_eq_bot_iff.not.2 hξ)

end ClosedOneParameterSubgroup

end SymplecticGeometry

end
