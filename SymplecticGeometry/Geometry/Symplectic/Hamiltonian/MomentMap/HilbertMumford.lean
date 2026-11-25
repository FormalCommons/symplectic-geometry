/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic

/-!
# Moment weights

For a complexified action of `Gc` on a compact manifold `M`, with `-μ` a moment map for `σ` and
the metric `g(u, w) = σ(u, J w)`, the function `t ↦ ⟨μ (exp (i t ξ) p), ξ⟩` is antitone
(`antitone_moment_expI`) and bounded below, since `M` is compact. Its limit as `t → ∞` is the
*moment weight* `w_μ(p, ξ)`, defined for every `ξ ∈ 𝔤`, following [GeorgoulasRobbinSalamon2021]
and [McDuffSalamon2017], §5.7.

## Main definitions

* `SymplecticGeometry.momentWeight C μ p ξ`: the limit of `μ (C.expI (t • ξ) • p) ξ` as
  `t → ∞`.

## Main results

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
