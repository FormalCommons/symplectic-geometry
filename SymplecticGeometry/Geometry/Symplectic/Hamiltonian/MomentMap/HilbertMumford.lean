/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic
public import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic

/-!
# Periods of the exponential and moment weights

For a Lie group `G` with Lie algebra `𝔤`, the set `nonzeroPeriods I G` consists of the nonzero
`ξ ∈ 𝔤` with `exp ξ = 1`: the nonzero generators of one-parameter subgroups `t ↦ exp (t ξ)` that
have period `1`. It is written `Λ` in [GeorgoulasRobbinSalamon2021]. For a torus, `Λ ∪ {0}` is
the integer lattice of `𝔤`; for a noncommutative `G`, such as `SU(2)`, `Λ ∪ {0}` need not be
closed under addition, so it is a set and not a lattice. It is invariant under the adjoint action
of `G` and under multiplication by positive integers.

For a complexified action of `Gc` on a compact manifold `M`, with `-μ` a moment map for `σ` and
the metric `g(u, w) = σ(u, J w)`, the function `t ↦ ⟨μ (exp (i t ξ) p), ξ⟩` is antitone
(`antitone_moment_expI`) and bounded below, since `M` is compact. Its limit as `t → ∞` is the
*moment weight* `w_μ(p, ξ)`, defined for every `ξ ∈ 𝔤`, following [GeorgoulasRobbinSalamon2021]
and [McDuffSalamon2017], §5.7.

## Main definitions

* `SymplecticGeometry.nonzeroPeriods I G`: the nonzero `ξ` in the Lie algebra with
  `mulInvariantExp ξ = 1`.
* `SymplecticGeometry.momentWeight C μ p ξ`: the limit of `μ (C.expI (t • ξ) • p) ξ` as
  `t → ∞`.

## Main results

* `SymplecticGeometry.tangentAd_mem_nonzeroPeriods`: `nonzeroPeriods I G` is invariant under
  the adjoint action.
* `SymplecticGeometry.nsmul_mem_nonzeroPeriods`: `nonzeroPeriods I G` is invariant under
  multiplication by positive integers.
* `SymplecticGeometry.tendsto_momentWeight`: on a compact manifold the limit defining the moment
  weight exists, for every `ξ`.
* `SymplecticGeometry.momentWeight_eq_iInf`: the moment weight is the infimum of
  `μ (C.expI (t • ξ) • p) ξ` over `t`.
* `SymplecticGeometry.momentWeight_le`: `w_μ(p, ξ) ≤ ⟨μ p, ξ⟩`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021].
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7.
-/

public section

noncomputable section

open Filter Topology TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-! ### The periods of the exponential -/

section Periods

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

end Periods

/-! ### Moment weights -/

section Weight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {M : Type*} [MulAction Gc M]

/-- The *moment weight* `w_μ(p, ξ)`: the limit of `⟨μ (exp (i t ξ) p), ξ⟩`, that is, of
`μ (C.expI (t • ξ) • p) ξ`, as `t → ∞`. It is a junk value where the limit does not exist; for a
complexified action on a compact manifold the limit exists for every `ξ`
(`tendsto_momentWeight`). -/
def momentWeight (C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) (p : M) (ξ : GroupLieAlgebra I G) : ℝ :=
  limUnder atTop fun t : ℝ ↦ μ (C.expI (t • ξ) • p) ξ

theorem momentWeight_def (C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) (p : M) (ξ : GroupLieAlgebra I G) :
    momentWeight C μ p ξ = limUnder atTop fun t : ℝ ↦ μ (C.expI (t • ξ) • p) ξ :=
  (rfl)

open _root_.Bundle
open scoped RealInnerProductSpace

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [CompactSpace M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {C : LieComplexification I G IC Gc} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- On a compact manifold, `t ↦ μ (C.expI (t • ξ) • p) ξ` converges, as `t → ∞`, to its infimum
over `t`. -/
private theorem tendsto_moment_expI_iInf (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    Tendsto (fun t : ℝ ↦ μ (C.expI (t • ξ) • p) ξ) atTop
      (𝓝 (⨅ t : ℝ, μ (C.expI (t • ξ) • p) ξ)) := by
  -- `x ↦ μ x ξ` is continuous on the compact space `M`, so the function is bounded below.
  have hc : Continuous fun x : M ↦ μ x ξ := by
    simpa using (hμ.contMDiff ξ).continuous.neg
  have hbdd : BddBelow (Set.range fun t : ℝ ↦ μ (C.expI (t • ξ) • p) ξ) := by
    obtain ⟨m, hm⟩ := isCompact_univ.bddBelow_image hc.continuousOn
    exact ⟨m, Set.forall_mem_range.2 fun t ↦ hm ⟨_, Set.mem_univ _, rfl⟩⟩
  exact tendsto_atTop_ciInf (antitone_moment_expI h hμ hg ξ p) hbdd

/-- The moment weight is the infimum of `μ (C.expI (t • ξ) • p) ξ` over `t`. -/
theorem momentWeight_eq_iInf (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    momentWeight C μ p ξ = ⨅ t : ℝ, μ (C.expI (t • ξ) • p) ξ := by
  rw [momentWeight_def]
  exact (tendsto_moment_expI_iInf h hμ hg p ξ).limUnder_eq

/-- **The moment weights exist.** For a complexified action on a compact manifold, with `-μ` a
moment map for `σ` and the metric `g(u, w) = σ(u, J w)`, the function
`t ↦ μ (C.expI (t • ξ) • p) ξ` converges to `momentWeight C μ p ξ` as `t → ∞`, for every `ξ`. -/
theorem tendsto_momentWeight (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    Tendsto (fun t : ℝ ↦ μ (C.expI (t • ξ) • p) ξ) atTop (𝓝 (momentWeight C μ p ξ)) := by
  rw [momentWeight_eq_iInf h hμ hg]
  exact tendsto_moment_expI_iInf h hμ hg p ξ

/-- The moment weight is at most `μ (C.expI (t • ξ) • p) ξ`, for every `t`. -/
theorem momentWeight_le_moment_expI_smul (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) (t : ℝ) :
    momentWeight C μ p ξ ≤ μ (C.expI (t • ξ) • p) ξ :=
  (antitone_moment_expI h hμ hg ξ p).le_of_tendsto (tendsto_momentWeight h hμ hg p ξ) t

/-- **The moment weight is at most the moment.** For a complexified action on a compact manifold,
with `-μ` a moment map for `σ` and the metric `g(u, w) = σ(u, J w)`,
`w_μ(p, ξ) ≤ ⟨μ p, ξ⟩`. -/
theorem momentWeight_le (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    momentWeight C μ p ξ ≤ μ p ξ := by
  simpa using momentWeight_le_moment_expI_smul h hμ hg p ξ 0

end Weight

end SymplecticGeometry

end
