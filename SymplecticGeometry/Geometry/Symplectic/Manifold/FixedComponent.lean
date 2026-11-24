/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Invariant
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints.Components
public import TauCeti.Geometry.Symplectic.Manifold.Invariants.FixedLocus

/-!
# The fixed components of a compact group of symplectomorphisms

Let a group `K` act on a manifold `M`, modelled on a finite-dimensional real space `E`, by smooth
isometries of a Riemannian metric. Tau Ceti shows that the fixed set `M^K` is locally connected
(`TauCeti.locallyConnectedSpace_fixedPoints`), and that each part
`M^K_d = TauCeti.fixedPointsOfFinrank 𝓘(ℝ, E) K M d` of it, where the fixed tangent subspace has
dimension `d`, is an embedded submanifold, symplectic when `K` also preserves a nondegenerate
two-form (`IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_fixedPointsOfFinrank`).

This file passes from these parts to the connected components of `M^K`:

* a connected component of `M^K` is open in each part `M^K_d`, since it is open in `M^K`
  (Tau Ceti's `TauCeti.isOpen_preimage_val_connectedComponentIn_fixedPoints`);
* for a compact Lie group acting smoothly on a σ-compact manifold and preserving a nondegenerate
  two-form `σ`, the connected component of `M^K` through a fixed point `x` is a symplectic
  submanifold, modelled on any subspace of `E` of the dimension of the fixed tangent subspace at
  `x`, with tangent spaces the fixed tangent subspaces. Tau Ceti proves this for a group of
  isometries
  (`IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_connectedComponentIn_fixedPoints`);
  a compact group preserves the average of any metric
  (`TauCeti.of_forall_riemannianBundle_inner_mfderiv`), as in Tau Ceti's
  `TauCeti.finite_connectedComponents_fixedPoints_of_compactSpace`.

## Main results

* `TauCeti.isOpen_preimage_val_fixedPointsOfFinrank_connectedComponentIn`: a connected component
  of the fixed set of a group of isometries is open in each part `M^K_d`.
* `exists_isSymplecticSubmanifoldEmbedding_connectedComponentIn_fixedPoints_of_compactSpace`
  (in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`): the connected components of the
  fixed set of a compact group of symplectomorphisms are symplectic submanifolds.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Lemma 5.5.7.
-/

public section

open Bundle Manifold Set MulAction
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- **A component of the fixed set is open in each part of a given dimension.** For a group
acting by isometries, the connected component of the fixed set `M^K` through any point is open in
the part `M^K_d` of `M^K` where the fixed tangent subspace has dimension `d`, for every `d`. -/
theorem isOpen_preimage_val_fixedPointsOfFinrank_connectedComponentIn
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul 𝓘(ℝ, E) ∞ K M]
    (hK : ∀ (k : K) (x : M) (u w : TangentSpace 𝓘(ℝ, E) x),
      inner ℝ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (k • ·) x u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (k • ·) x w) =
        inner ℝ u w)
    (x : M) (d : ℕ) :
    IsOpen ((↑) ⁻¹' connectedComponentIn (fixedPoints K M) x :
      Set (fixedPointsOfFinrank 𝓘(ℝ, E) K M d)) := by
  by_cases hx : x ∈ fixedPoints K M
  · exact (isOpen_preimage_val_connectedComponentIn_fixedPoints hK hx).preimage
      (continuous_inclusion (fixedPointsOfFinrank_subset_fixedPoints d))
  · simp [connectedComponentIn_eq_empty hx]

namespace SmoothTwoForm

variable [SigmaCompactSpace M] {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [ChartedSpace HG G] [IsManifold IG ∞ G] [MulAction G M] [ContMDiffSMul IG 𝓘(ℝ, E) ∞ G M]
  {σ : SmoothTwoForm 𝓘(ℝ, E) M}

namespace IsNondegenerate

/-- **The fixed components of a compact group of symplectomorphisms are symplectic
submanifolds.** Let a compact Lie group `G` act smoothly on a σ-compact manifold `M`, preserving a
nondegenerate two-form `σ`, and let `x` be a fixed point. For a subspace `L` of the model whose
dimension is that of the fixed tangent subspace at `x`, the connected component of the fixed set
through `x` is a smooth manifold modelled on `L` whose inclusion into `M` is a symplectic
submanifold embedding, with tangent image the fixed tangent subspace at every point. -/
theorem exists_isSymplecticSubmanifoldEmbedding_connectedComponentIn_fixedPoints_of_compactSpace
    (hσ : σ.IsNondegenerate) (hσG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := IG) (I' := 𝓘(ℝ, E)) g) σ = σ)
    {x : M} (hx : x ∈ fixedPoints G M) {L : Submodule ℝ E}
    (hL : Module.finrank ℝ L = Module.finrank ℝ (fixedTangentSubspace 𝓘(ℝ, E) G x)) :
    ∃ C : ChartedSpace L (connectedComponentIn (fixedPoints G M) x), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (connectedComponentIn (fixedPoints G M) x) ∧
      hσ.IsSymplecticSubmanifoldEmbedding 𝓘(ℝ, L)
        (Subtype.val : connectedComponentIn (fixedPoints G M) x → M) ∧
      ∀ y : connectedComponentIn (fixedPoints G M) x,
        LinearMap.range (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) Subtype.val y).toLinearMap =
          fixedTangentSubspace 𝓘(ℝ, E) G (y : M) := by
  have : ContMDiffConstSMul 𝓘(ℝ, E) ∞ G M := ContMDiffSMul.contMDiffConstSMul IG
  refine of_forall_riemannianBundle_inner_mfderiv (I := 𝓘(ℝ, E)) (M := M) IG G fun hG ↦ ?_
  exact hσ.exists_isSymplecticSubmanifoldEmbedding_connectedComponentIn_fixedPoints hG hσG hx hL

end IsNondegenerate

end SmoothTwoForm

end TauCeti

end
