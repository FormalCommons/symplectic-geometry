/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.MorseBott
import TauCeti.Geometry.Manifold.Riemannian.Invariant
import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints.Submanifold

/-!
# The components of a moment map are Morse–Bott functions

Let a compact Lie group `G` act smoothly on a σ-compact manifold `M`, modelled on `𝓘(ℝ, E')`, with
moment map `μ` for a nondegenerate two-form `σ`, and fix `ξ` in the Lie algebra of `G`. This file
shows that the connected components of the critical set of `x ↦ μ x ξ`, each with a smooth
structure for which its inclusion into `M` is a smooth embedding, form a
`TauCeti.IsMorseBottFamily` for `x ↦ μ x ξ`.

The critical set is the fixed set `M^{T_ξ}` of the closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}`
(`TauCeti.SmoothTwoForm.IsMomentMap.criticalPoints_eq_fixedPoints`). The compact group `G`
preserves a smooth metric (`TauCeti.of_forall_riemannianBundle_inner_mfderiv`), so `T_ξ` acts by
isometries of it, and each connected component of `M^{T_ξ}` is an embedded submanifold whose
tangent spaces are the fixed tangent subspaces of `T_ξ`
(`TauCeti.exists_isSmoothEmbedding_connectedComponentIn_fixedPoints`), hence a nondegenerate
critical submanifold of `x ↦ μ x ξ`
(`TauCeti.SmoothTwoForm.IsMomentMap.isNondegenerateCriticalSubmanifold_of_fixedTangentSubspace_le`).
The components are connected, pairwise disjoint and cover the critical set, so they form a
Morse–Bott family by `TauCeti.IsMorseBottFamily.of_pairwise_disjoint`.

The family is indexed by the connected components of the critical set rather than by the
dimension `d` of the sets `M^{T_ξ}_d` that Tau Ceti uses
(`exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank_of_compactSpace`), since a
Morse–Bott family needs nonempty connected pieces, and `M^{T_ξ}_d` can be empty or disconnected.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.exists_isMorseBottFamily`: the connected components of the
  critical set of `x ↦ μ x ξ`, embedded by their inclusions, form a Morse–Bott family.

## References

* [M. F. Atiyah, *Convexity and commuting Hamiltonians*][Atiyah1982], §2.
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7.
-/

public section

namespace TauCeti.SmoothTwoForm.IsMomentMap

open _root_.Bundle _root_.Manifold Set _root_.MulAction
open scoped _root_.Manifold ContDiff

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E' M] [IsManifold 𝓘(ℝ, E') ∞ M] [T2Space M]
  [SigmaCompactSpace M] [MulAction G M] [ContMDiffSMul I 𝓘(ℝ, E') ∞ G M]
  {σ : SmoothTwoForm 𝓘(ℝ, E') M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- Each connected component of the critical set of `x ↦ μ x ξ` is a smooth manifold, modelled on
a subspace of the model, whose inclusion into `M` is a smooth embedding with tangent image the
fixed tangent subspace of `T_ξ` at every point. -/
private theorem exists_isSmoothEmbedding_carrierIn
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate) (ξ : GroupLieAlgebra I G)
    (c : ConnectedComponents (criticalPoints 𝓘(ℝ, E') fun x ↦ μ x ξ)) :
    ∃ (L : Submodule ℝ E') (C : ChartedSpace L c.carrierIn), letI := C
      IsManifold 𝓘(ℝ, L) ∞ c.carrierIn ∧
      IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E') ∞ (Subtype.val : c.carrierIn → M) ∧
      ∀ y : c.carrierIn,
        LinearMap.range (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E') Subtype.val y).toLinearMap =
          fixedTangentSubspace 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) (y : M) := by
  obtain ⟨p, hp⟩ := c.carrierIn_nonempty
  have hpfix : p ∈ fixedPoints (Lie.closedOneParameterSubgroup ξ) M := by
    rw [← h.criticalPoints_eq_fixedPoints hσ]
    exact c.carrierIn_subset hp
  rw [c.carrierIn_eq_connectedComponentIn hp, h.criticalPoints_eq_fixedPoints hσ]
  obtain ⟨L, hL⟩ : ∃ L : Submodule ℝ E', Module.finrank ℝ L =
      Module.finrank ℝ (fixedTangentSubspace 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) p) :=
    ⟨_, rfl⟩
  -- `G` preserves some smooth metric, so `T_ξ` acts by isometries of it.
  have : ContMDiffConstSMul 𝓘(ℝ, E') ∞ G M := ⟨ContMDiffSMul.contMDiff_const_smul (I := I)⟩
  refine of_forall_riemannianBundle_inner_mfderiv (I := 𝓘(ℝ, E')) (M := M) I G fun hG ↦ ?_
  exact ⟨L, exists_isSmoothEmbedding_connectedComponentIn_fixedPoints
    (K := Lie.closedOneParameterSubgroup ξ) (fun a x u w ↦ hG a x u w) hpfix hL⟩

/-- **The components of a moment map are Morse–Bott functions.** For a compact Lie group `G`
acting smoothly on a σ-compact manifold with moment map `μ` for a nondegenerate two-form `σ`, and
any `ξ` in the Lie algebra, each connected component of the critical set of `x ↦ μ x ξ` is a
smooth manifold, modelled on a subspace `L c` of the model, whose inclusion into `M` is a smooth
embedding, and these inclusions form a Morse–Bott family for `x ↦ μ x ξ`. -/
theorem exists_isMorseBottFamily
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate) (ξ : GroupLieAlgebra I G) :
    ∃ (L : ConnectedComponents (criticalPoints 𝓘(ℝ, E') fun x ↦ μ x ξ) → Submodule ℝ E')
      (C : ∀ c, ChartedSpace (L c) c.carrierIn), letI := C
      (∀ c, IsManifold 𝓘(ℝ, L c) ∞ c.carrierIn) ∧
      ∃ i : ∀ c, SmoothEmbedding 𝓘(ℝ, L c) 𝓘(ℝ, E') ∞ c.carrierIn M,
        (∀ c y, i c y = y) ∧ IsMorseBottFamily i fun x ↦ μ x ξ := by
  choose L C hman hemb hrange using h.exists_isSmoothEmbedding_carrierIn hσ ξ
  let := C
  let i c : SmoothEmbedding 𝓘(ℝ, L c) 𝓘(ℝ, E') ∞ c.carrierIn M :=
    .ofIsSmoothEmbedding _ (hemb c)
  have hi (c) : ⇑(i c) = Subtype.val := SmoothEmbedding.coe_ofIsSmoothEmbedding _ _
  have hrange_i (c) : range (i c) = c.carrierIn := by rw [hi, Subtype.range_coe]
  have (c : ConnectedComponents (criticalPoints 𝓘(ℝ, E') fun x ↦ μ x ξ)) :
      Nonempty c.carrierIn :=
    c.carrierIn_nonempty.to_subtype
  have (c : ConnectedComponents (criticalPoints 𝓘(ℝ, E') fun x ↦ μ x ξ)) :
      PreconnectedSpace c.carrierIn :=
    isPreconnected_iff_preconnectedSpace.1 c.isPreconnected_carrierIn
  refine ⟨L, C, hman, i, fun c y ↦ by rw [hi], ?_⟩
  refine IsMorseBottFamily.of_pairwise_disjoint (by simp) (h.contMDiff ξ) (fun c ↦ ?_) ?_ ?_
  · refine h.isNondegenerateCriticalSubmanifold_of_fixedTangentSubspace_le hσ (fun y ↦ ?_)
      (fun y ↦ ?_) <;> rw [hi]
    · rw [← h.criticalPoints_eq_fixedPoints hσ]
      exact c.carrierIn_subset y.property
    · exact (hrange c y).ge
  · simpa only [hrange_i] using ConnectedComponents.pairwise_disjoint_carrierIn
  · simp only [hrange_i, ConnectedComponents.iUnion_carrierIn, subset_rfl]

end TauCeti.SmoothTwoForm.IsMomentMap

end
