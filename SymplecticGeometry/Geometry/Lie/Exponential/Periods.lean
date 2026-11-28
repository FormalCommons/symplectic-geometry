/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import TauCeti.Geometry.Lie.Adjoint.Infinitesimal
import TauCeti.Geometry.Lie.Exponential.LocalInverse
import SymplecticGeometry.Analysis.RCLike.Basic
import SymplecticGeometry.Geometry.Lie.Exponential.Commute

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
* `SymplecticGeometry.mem_closure_smul_nonzeroPeriods`: for compact `G`, a nonzero `ξ` is a limit
  of positive multiples of periods that bracket to zero with everything that brackets to zero
  with `ξ`.

## Implementation notes

The Hilbert–Mumford criterion uses `mem_closure_smul_nonzeroPeriods` to replace a direction of
positive weight by a positive multiple of a nearby period. The proof: some power `exp ξ ^ m`
with `m > 0` is close to `1` (Mathlib's `mapClusterPt_one_atTop_pow`), so it is `exp η` for a
small `η`. For `⁅ζ, ξ⁆ = 0`, each `exp (s • ζ)` commutes with `exp η`, so for small `s` it fixes
`η` under `Ad`, the exponential being injective near `0`; hence `⁅ζ, η⁆ = 0`. Then
`λ = m • ξ - η` is a period with `ξ - m⁻¹ • λ = m⁻¹ • η`. Smallness is measured by a balanced
neighbourhood of `0`, so no norm on the Lie algebra is needed.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021].
-/

public section

open TauCeti Filter
open scoped Manifold ContDiff Topology

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

/-- **Periods approximate the double centralizer.** For a compact Lie group `G` and a nonzero `ξ`
in its Lie algebra, `ξ` lies in the closure of the positive multiples `c • λ` of the periods
`λ ∈ nonzeroPeriods I G` that lie in the double centralizer of `ξ`, that is, that bracket to zero
with every `ζ` such that `⁅ζ, ξ⁆ = 0`. -/
theorem mem_closure_smul_nonzeroPeriods [FiniteDimensional ℝ E] [CompactSpace G]
    {ξ : GroupLieAlgebra I G} (hξ : ξ ≠ 0) :
    ξ ∈ closure {x | ∃ c : ℝ, 0 < c ∧ ∃ l ∈ nonzeroPeriods I G,
      (∀ ζ : GroupLieAlgebra I G, ⁅ζ, ξ⁆ = 0 → ⁅ζ, l⁆ = 0) ∧ x = c • l} := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
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
  have hWsub := balancedCore_subset (𝕜 := ℝ) (U ∩ {ξ}ᶜ ∩ {v | ξ + v ∈ V})
  have hWbal : Balanced ℝ W := balancedCore.balanced _
  -- Some power `exp ξ ^ m` with `m > 0` is `exp η` for some `η ∈ W`.
  have hlog : ∀ᶠ g in 𝓝 (1 : G), mulInvariantLog (I := I) g ∈ W ∧
      mulInvariantExp (mulInvariantLog (I := I) g) = g := by
    refine (Filter.Eventually.and ?_ (eventually_mulInvariantExp_log (I := I) (G := G)))
    have hcont := (contMDiffAt_mulInvariantLog_one (I := I) (G := G)).continuousAt
    exact hcont.preimage_mem_nhds (by rwa [mulInvariantLog_one])
  obtain ⟨m, hm, hmW, hmexp⟩ :=
    ((mapClusterPt_one_atTop_pow (mulInvariantExp ξ)).frequently hlog).forall_exists_of_atTop 1
  set η := mulInvariantLog (I := I) (mulInvariantExp ξ ^ m)
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast hm
  have hexpη : mulInvariantExp η = mulInvariantExp (m • ξ) := by
    rw [hmexp, mulInvariantExp_nsmul]
  -- Every `ζ` that commutes with `ξ` commutes with `η`.
  have hcomm : ∀ ζ : GroupLieAlgebra I G, ⁅ζ, ξ⁆ = 0 → ⁅ζ, η⁆ = 0 := by
    intro ζ hζ
    refine Lie.lie_eq_zero_of_eventually_tangentAd_mulInvariantExp_smul_apply_eq_self ?_
    have hcont : ContinuousAt
        (fun s : ℝ ↦ Lie.tangentAd (I := I) (mulInvariantExp (s • ζ)) η) 0 :=
      (Lie.hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero (I := I) ζ η).continuousAt
    have hη : η ∈ U := (hWsub hmW).1.1
    filter_upwards [hcont.eventually_mem (by
      rw [zero_smul, mulInvariantExp_zero, Lie.tangentAd_one, LieEquiv.refl_apply]
      exact isOpen_interior.mem_nhds hη)] with s hs
    have hc : Commute (mulInvariantExp (s • ζ)) (mulInvariantExp η) := by
      rw [hexpη]
      exact Lie.commute_mulInvariantExp_of_lie_eq_zero (by rw [smul_lie, lie_nsmul, hζ,
        smul_zero, smul_zero])
    have he : mulInvariantExp (Lie.tangentAd (I := I) (mulInvariantExp (s • ζ)) η) =
        mulInvariantExp η := by
      rw [← Lie.conj_mulInvariantExp, hc.eq, mul_inv_cancel_right]
    have h1 := interior_subset hs
    have h2 := interior_subset hη
    rw [Set.mem_ofPred_eq] at h1 h2
    rw [← h1, he, h2]
  -- The period is `λ = m • ξ - η`.
  refine ⟨(m : ℝ)⁻¹ • (m • ξ - η), ?_, (m : ℝ)⁻¹, inv_pos.2 hm₀, m • ξ - η, ⟨?_, ?_⟩, ?_, rfl⟩
  · have hmem : -(m : ℝ)⁻¹ • η ∈ W :=
      hWbal.smul_mem (by rw [norm_neg, norm_inv, Real.norm_natCast]; exact
        inv_le_one_of_one_le₀ (by exact_mod_cast hm)) hmW
    have := (hWsub hmem).2
    rw [Set.mem_ofPred_eq] at this
    rwa [← Nat.cast_smul_eq_nsmul ℝ, smul_sub, inv_smul_smul₀ hm₀.ne', sub_eq_add_neg,
      ← neg_smul]
  · intro h
    rw [sub_eq_zero] at h
    have hmem : (m : ℝ)⁻¹ • η ∈ W :=
      hWbal.smul_mem (by rw [norm_inv, Real.norm_natCast]; exact
        inv_le_one_of_one_le₀ (by exact_mod_cast hm)) hmW
    rw [← h, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ hm₀.ne'] at hmem
    exact (hWsub hmem).1.2 rfl
  · have hadd := Lie.mulInvariantExp_add_of_lie_eq_zero (X := m • ξ - η) (Y := η) (by
      rw [sub_lie, lie_self, sub_zero, nsmul_lie, hcomm ξ (lie_self ξ), smul_zero])
    rwa [sub_add_cancel, hexpη, right_eq_mul] at hadd
  · intro ζ hζ
    rw [lie_sub, lie_nsmul, hζ, hcomm ζ hζ, smul_zero, sub_zero]

end SymplecticGeometry

end
