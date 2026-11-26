/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

/-!
# Moment maps of commutative group actions

Let a commutative Lie group `G` act smoothly on a manifold `M` with a two-form `σ`. Conjugation in
`G` is trivial, so the coadjoint action of `G` on the dual of its Lie algebra is the identity
(`TauCeti.Lie.coadjointRepresentation_eq_one`). Coadjoint equivariance of a map `μ : M → 𝔤*` thus
reduces to invariance, `μ (g • x) = μ x`, and a moment map of the fundamental vector fields that is
invariant under the action is a group-level moment map in Tau Ceti's sense
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`), and conversely every group-level moment map is
invariant. No invariance of `σ` is needed.

Tau Ceti proves both directions inside `TauCeti.SmoothTwoForm.hamiltonianTorusData_iff` and
`TauCeti.SmoothTwoForm.HamiltonianTorusData.apply_smul_eq`, for a `CommGroup` and together with
invariance of `σ`; the lemmas here state them alone, for a `Group` with `IsMulCommutative`, with
the same proofs.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_of_apply_smul`: an invariant moment
  map of the action of a commutative Lie group is coadjoint-equivariant.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.apply_smul_eq_of_isMulCommutative`: conversely,
  a coadjoint-equivariant moment map of such an action is invariant.
* `TauCeti.SmoothTwoForm.isEquivariantMomentMap_iff_apply_smul_eq`: for a commutative Lie group,
  a group-level moment map is exactly an invariant moment map of the fundamental vector fields.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 5.2 (equivariance of moment maps).
-/

public section

open Manifold TauCeti
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [IsMulCommutative G]
  [LieGroup I (minSmoothness ℝ 3) G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

-- The coadjoint representation in `IsEquivariantMomentMap` is that of a `C¹` Lie group.
attribute [local instance] lieGroupOne

/-- **Invariant moment maps of commutative group actions are equivariant.** For a smooth action
of a commutative Lie group `G` on `M`, a moment map `μ` of the fundamental vector fields for a
two-form `σ` with `μ (g • x) = μ x` for all `g` and `x` is a coadjoint-equivariant moment map,
since the coadjoint action of `G` is trivial. -/
theorem IsMomentMap.isEquivariantMomentMap_of_apply_smul
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ)
    (hinv : ∀ (g : G) (x : M), μ (g • x) = μ x) : σ.IsEquivariantMomentMap μ where
  toIsMomentMap := hμ
  apply_smul g x := by
    rw [hinv, Lie.coadjointRepresentation_eq_one, one_apply_eq_self]

/-- **Equivariant moment maps of commutative group actions are invariant.** For a smooth action
of a commutative Lie group `G` on `M`, a coadjoint-equivariant moment map `μ` for a two-form `σ`
satisfies `μ (g • x) = μ x` for all `g` and `x`, since the coadjoint action of `G` is trivial. -/
theorem IsEquivariantMomentMap.apply_smul_eq_of_isMulCommutative
    (h : σ.IsEquivariantMomentMap μ) (g : G) (x : M) : μ (g • x) = μ x := by
  rw [h.apply_smul, Lie.coadjointRepresentation_eq_one, one_apply_eq_self]

/-- **Equivariance is invariance for commutative group actions.** For a smooth action of a
commutative Lie group `G` on `M` and a two-form `σ`, a map `μ : M → 𝔤*` is a
coadjoint-equivariant moment map exactly when it is a moment map of the fundamental vector fields
with `μ (g • x) = μ x` for all `g` and `x`. -/
theorem isEquivariantMomentMap_iff_apply_smul_eq :
    σ.IsEquivariantMomentMap μ ↔
      σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ ∧
        ∀ (g : G) (x : M), μ (g • x) = μ x :=
  ⟨fun h ↦ ⟨h.toIsMomentMap, h.apply_smul_eq_of_isMulCommutative⟩,
    fun h ↦ h.1.isEquivariantMomentMap_of_apply_smul h.2⟩

end TauCeti.SmoothTwoForm

end
