/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.PullbackGroupoid
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

* a connected component of `M^K` is open in each part `M^K_d`, since components of a locally
  connected space are open; it lies in the part whose `d` is the dimension of the fixed tangent
  subspace at any of its points (`TauCeti.subset_fixedPointsOfFinrank_of_isPreconnected`);
* for a compact Lie group acting smoothly on a σ-compact manifold and preserving a nondegenerate
  two-form `σ`, the connected component of `M^K` through a fixed point `x` is therefore a
  symplectic submanifold, modelled on any subspace of `E` of the dimension of the fixed tangent
  subspace at `x`, with tangent spaces the fixed tangent subspaces. Its manifold structure is that
  of an open subset of the part `M^K_d`, carried over to the component by Tau Ceti's
  `Homeomorph.pullbackChartedSpace`, and the invariant metric is an average
  (`TauCeti.of_forall_riemannianBundle_inner_mfderiv`), as in Tau Ceti's
  `TauCeti.finite_connectedComponents_fixedPoints_of_compactSpace`.

## Main results

* `TauCeti.isOpen_preimage_val_connectedComponentIn_fixedPoints`: a connected component of the
  fixed set of a group of isometries is open in each part `M^K_d`.
* `IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_connectedComponentIn_fixedPoints`:
  the connected components of the fixed set of a compact group of symplectomorphisms are
  symplectic submanifolds.

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
theorem isOpen_preimage_val_connectedComponentIn_fixedPoints
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul 𝓘(ℝ, E) ∞ K M]
    (hK : ∀ (k : K) (x : M) (u w : TangentSpace 𝓘(ℝ, E) x),
      inner ℝ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (k • ·) x u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (k • ·) x w) =
        inner ℝ u w)
    (x : M) (d : ℕ) :
    IsOpen ((↑) ⁻¹' connectedComponentIn (fixedPoints K M) x :
      Set (fixedPointsOfFinrank 𝓘(ℝ, E) K M d)) := by
  have := locallyConnectedSpace_fixedPoints hK
  -- The component is open in the fixed set, which is locally connected.
  have hopen : IsOpen ((↑) ⁻¹' connectedComponentIn (fixedPoints K M) x :
      Set (fixedPoints K M)) := by
    by_cases hx : x ∈ fixedPoints K M
    · rw [connectedComponentIn_eq_image hx,
        Subtype.val_injective.preimage_image]
      exact isOpen_connectedComponent
    · simp [connectedComponentIn_eq_empty hx]
  exact hopen.preimage (continuous_inclusion (fixedPointsOfFinrank_subset_fixedPoints d))

namespace SmoothTwoForm

variable [SigmaCompactSpace M] {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [ChartedSpace HG G] [IsManifold IG ∞ G] [MulAction G M] [ContMDiffSMul IG 𝓘(ℝ, E) ∞ G M]
  {σ : SmoothTwoForm 𝓘(ℝ, E) M}

/-- **The fixed components of a compact group of symplectomorphisms are symplectic
submanifolds.** Let a compact Lie group `G` act smoothly on a σ-compact manifold `M`, preserving a
nondegenerate two-form `σ`, and let `x` be a fixed point. For a subspace `L` of the model whose
dimension is that of the fixed tangent subspace at `x`, the connected component of the fixed set
through `x` is a smooth manifold modelled on `L` whose inclusion into `M` is a symplectic
submanifold embedding, with tangent image the fixed tangent subspace at every point. -/
theorem IsNondegenerate.exists_isSymplecticSubmanifoldEmbedding_connectedComponentIn_fixedPoints
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
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
  set S := connectedComponentIn (fixedPoints G M) x
  set d := Module.finrank ℝ (fixedTangentSubspace 𝓘(ℝ, E) G x)
  set N := fixedPointsOfFinrank 𝓘(ℝ, E) G M d
  have hSN : S ⊆ N := subset_fixedPointsOfFinrank_of_isPreconnected hG
    isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
    (mem_connectedComponentIn hx)
  obtain ⟨C, hman, hemb, hrange⟩ :=
    hσ.exists_isSymplecticSubmanifoldEmbedding_fixedPointsOfFinrank hG hσG hL
  let := C
  -- The component is an open subset `U` of the manifold `N`, homeomorphic to it by `e`.
  let U : TopologicalSpace.Opens N :=
    ⟨(↑) ⁻¹' S, isOpen_preimage_val_connectedComponentIn_fixedPoints hG x d⟩
  let e : S ≃ₜ U :=
    { toFun := fun y ↦ ⟨⟨y, hSN y.property⟩, y.property⟩
      invFun := fun y ↦ ⟨y.val, y.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _
      continuous_invFun := continuous_subtypeVal.subtypeVal.subtype_mk _ }
  let := e.pullbackChartedSpace (H := L)
  have hmanS : IsManifold 𝓘(ℝ, L) ∞ S := e.pullback_isManifold 𝓘(ℝ, L) ∞
  let φ := e.pullbackDiffeomorph 𝓘(ℝ, L) ∞
  -- The inclusion of `S` is that of `U` into `N`, then of `N` into `M`, after `φ`, whose
  -- underlying map is `e`.
  have hval : (Subtype.val : S → M) = ((Subtype.val : N → M) ∘ (Subtype.val : U → N)) ∘ φ := by
    rw [Homeomorph.coe_pullbackDiffeomorph]
    rfl
  refine ⟨_, hmanS, ?_, fun y ↦ ?_⟩
  · rw [hval, φ.isSymplecticSubmanifoldEmbedding_comp_diffeomorph_iff]
    exact hemb.comp_subtype_val U
  · rw [hval, φ.range_mfderiv_comp_diffeomorph (by simp),
      Manifold.range_mfderiv_comp_subtype_val]
    exact hrange _

end SmoothTwoForm

end TauCeti

end
