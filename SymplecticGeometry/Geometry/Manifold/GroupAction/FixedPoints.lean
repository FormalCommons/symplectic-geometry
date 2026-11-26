/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.GroupAction.CompactLinearization
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints.Submanifold
import SymplecticGeometry.Geometry.Manifold.GroupAction.BoundarylessModel
import TauCeti.Geometry.Manifold.Riemannian.Invariant
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Fixed points of compact group actions

This file proves two facts about the fixed set of a compact group acting smoothly on a manifold.

**Nearby fixed points.** Let a compact group `G` act smoothly on a manifold `M` without boundary,
and let `x` be a fixed point. If the derivatives at `x` of the maps `g • ·` all fix a nonzero
tangent vector `v`, then `x` is not isolated among the fixed points of `G`.

The proof reads the action in the linearizing chart `e` of Tau Ceti's
`TauCeti.exists_contMDiff_chart_fixedPoints`, in which the fixed points near `x` are the points
sent into the invariant vectors of the tangent representation at `x`
(`TauCeti.mem_invariants_tangentRepresentation_iff_of_mem_fixedPoints`). The points
`e⁻¹ (ε • v)`, for small real `ε ≠ 0`, are then fixed points other than `x` that tend to `x`,
since `e⁻¹` maps punctured neighbourhoods of `e x` into those of `x`
(`OpenPartialHomeomorph.tendsto_symm_nhdsNE`).

Tau Ceti's chart needs a model without boundary. For a manifold without boundary whose model may
have boundary, the action is carried to the copy `TauCeti.BoundarylessModel I M` with charts in
`E` (`SymplecticGeometry/Geometry/Manifold/GroupAction/BoundarylessModel.lean`), the vector `v`
to its image under the derivative of the identity diffeomorphism
`TauCeti.BoundarylessModel.interiorDiffeomorph`, and the fixed points found there back to `M`.

**Fixed components.** Let a compact Lie group `G` act smoothly on a σ-compact manifold `M`
without boundary, modelled on a finite-dimensional space, and let `K` be any subgroup of `G`.
Each connected component of the fixed set `M^K` is an embedded submanifold, whose tangent space
at each point is the fixed tangent subspace `TauCeti.fixedTangentSubspace I K` there. Tau Ceti
proves this for a group acting by isometries of a Riemannian metric
(`TauCeti.exists_isSmoothEmbedding_connectedComponentIn_fixedPoints`). Here no metric appears in
the statement: `G`, and with it `K`, preserves the Haar average of a smooth metric
(`TauCeti.of_forall_riemannianBundle_inner_mfderiv`).

## Main results

* `SymplecticGeometry.frequently_mem_fixedPoints_of_mfderiv_smul_eq_self`: a nonzero tangent
  vector at a fixed point `x` fixed by the derivatives of the action gives fixed points other
  than `x` in every neighbourhood of `x`.
* `SymplecticGeometry.exists_isSmoothEmbedding_connectedComponentIn_fixedPoints_of_compactSpace`:
  the connected components of the fixed set of a subgroup of a compact Lie group are embedded
  submanifolds, with tangent spaces the fixed tangent subspaces.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381.
* S. Kobayashi, *Fixed points of isometries*, Nagoya Mathematical Journal 13 (1958), 63–68.
* J. J. Duistermaat and J. A. C. Kolk, *Lie Groups*, Universitext, Springer, 2000, Section 2.2.
-/

public section

open Filter Topology MulAction TauCeti Manifold
open scoped Manifold ContDiff

namespace SymplecticGeometry

section NearbyFixedPoints

variable {E H M EG HG G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless] [TopologicalSpace G] [ChartedSpace HG G]
  [Group G] [IsTopologicalGroup G] [CompactSpace G] [MulAction G M] {n : ℕ∞}
  [IsManifold I n M] [IsManifold IG n G]

attribute [local instance] BoundarylessModel.interiorChartedSpace

variable (IG) in
/-- The case of `frequently_mem_fixedPoints_of_mfderiv_smul_eq_self` for a model without
boundary, read in Tau Ceti's linearizing chart. -/
private theorem frequently_mem_fixedPoints_of_mfderiv_smul_eq_self_of_boundaryless
    [I.Boundaryless] [ContMDiffSMul IG I n G M]
    (hn : 1 ≤ n) {x : M} (hx : x ∈ fixedPoints G M) {v : TangentSpace I x} (hv : v ≠ 0)
    (hfix : ∀ g : G, mfderiv I I (fun y : M ↦ g • y) x v = v) :
    ∃ᶠ y in 𝓝[≠] x, y ∈ fixedPoints G M := by
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hn).ne'
  have hd : ∀ g ∈ stabilizer G x, MDifferentiableAt I I (fun y : M ↦ g • y) x :=
    fun g _ ↦ (ContMDiffSMul.contMDiff_const_smul (I := IG) (n := n) g).mdifferentiableAt hn0
  obtain ⟨e, hxe, hex, -, -, -, -, hfixed⟩ :=
    exists_contMDiff_chart_fixedPoints (I := I) IG hn hx hd
  have hv' : v ∈ (tangentRepresentation hd).toRepresentation.invariants :=
    (mem_invariants_tangentRepresentation_iff_of_mem_fixedPoints hd hx).2 hfix
  have h0 : (0 : E) ∈ e.target := hex ▸ e.map_source hxe
  have hcont : Tendsto (fun ε : ℝ ↦ (ε • v : E)) (𝓝 0) (𝓝 0) :=
    Continuous.tendsto' (f := fun ε : ℝ ↦ (ε • v : E)) (by fun_prop) 0 0 (zero_smul ℝ _)
  have htarget : ∀ᶠ ε : ℝ in 𝓝 0, (ε • v : E) ∈ e.target :=
    hcont (e.open_target.mem_nhds h0)
  have hsmul : Tendsto (fun ε : ℝ ↦ (ε • v : E)) (𝓝[≠] 0) (𝓝[≠] (e x)) :=
    hex ▸ tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hcont.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun ε hε ↦ smul_ne_zero hε hv)
  have hc : Tendsto (fun ε : ℝ ↦ e.symm (ε • v)) (𝓝[≠] 0) (𝓝[≠] x) :=
    (e.tendsto_symm_nhdsNE hxe).comp hsmul
  have hmem : ∀ᶠ ε : ℝ in 𝓝[≠] 0, e.symm (ε • v) ∈ fixedPoints G M := by
    filter_upwards [nhdsWithin_le_nhds htarget] with ε hε
    refine (hfixed _ (e.map_target hε)).2 ?_
    rw [e.right_inv hε]
    exact Submodule.smul_mem _ ε hv'
  exact hc.frequently hmem.frequently

variable (IG) in
/-- **A fixed tangent vector at a fixed point gives nearby fixed points.** Let a compact group
`G`, a manifold without boundary, act on a manifold `M` without boundary by a jointly `C^n` map,
`1 ≤ n`, and let `x` be a fixed point. If the derivatives at `x` of all the maps `g • ·` fix a
nonzero tangent vector `v`, then every neighbourhood of `x` contains fixed points other than
`x`. -/
theorem frequently_mem_fixedPoints_of_mfderiv_smul_eq_self [BoundarylessManifold I M]
    [ContMDiffSMul IG I n G M]
    (hn : 1 ≤ n) {x : M} (hx : x ∈ fixedPoints G M) {v : TangentSpace I x} (hv : v ≠ 0)
    (hfix : ∀ g : G, mfderiv I I (fun y : M ↦ g • y) x v = v) :
    ∃ᶠ y in 𝓝[≠] x, y ∈ fixedPoints G M := by
  have : IsManifold I 1 M := IsManifold.of_le (n := n) (by exact_mod_cast hn)
  let Φ := BoundarylessModel.interiorDiffeomorph I (M := M) n
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hn).ne'
  have hΦd (y : M) : MDifferentiableAt I 𝓘(ℝ, E) Φ y := Φ.mdifferentiable hn0 y
  have hx' : Φ x ∈ fixedPoints G (BoundarylessModel I M) := fun g ↦ by
    rw [← BoundarylessModel.interiorDiffeomorph_smul, hx g]
  have hv' : mfderiv I 𝓘(ℝ, E) Φ x v ≠ 0 := fun h ↦
    hv ((Φ.mfderivToContinuousLinearEquiv hn0 x).map_eq_zero_iff.1
      (by rwa [← ContinuousLinearEquiv.coe_coe, Diffeomorph.mfderivToContinuousLinearEquiv_coe]))
  have hfix' (g : G) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y : BoundarylessModel I M ↦ g • y) (Φ x)
      (mfderiv I 𝓘(ℝ, E) Φ x v) = mfderiv I 𝓘(ℝ, E) Φ x v := by
    -- Differentiate `(g • ·) ∘ Φ = Φ ∘ (g • ·)` at the fixed point `x`.
    have h := congrArg (fun f ↦ mfderiv I 𝓘(ℝ, E) f x v)
      (funext fun y ↦ (BoundarylessModel.interiorDiffeomorph_smul I n g y).symm :
        (fun y : BoundarylessModel I M ↦ g • y) ∘ Φ = Φ ∘ fun y : M ↦ g • y)
    rw [mfderiv_comp x ((ContMDiffSMul.contMDiff_const_smul (I := IG) (n := n) g).mdifferentiableAt
        hn0) (hΦd x), mfderiv_comp x (hΦd _)
        ((ContMDiffSMul.contMDiff_const_smul (I := IG) (n := n) g).mdifferentiableAt hn0)] at h
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hfix g] at h
    exact h.trans (congrArg (fun y : M ↦ (mfderiv I 𝓘(ℝ, E) Φ y v : E)) (hx g))
  have h := frequently_mem_fixedPoints_of_mfderiv_smul_eq_self_of_boundaryless IG hn hx' hv' hfix'
  rw [← Φ.coe_toHomeomorph, ← Φ.toHomeomorph.map_punctured_nhds_eq, frequently_map] at h
  exact h.mono fun y hy g ↦
    Φ.injective ((BoundarylessModel.interiorDiffeomorph_smul I n g y).trans (hy g))

end NearbyFixedPoints

section FixedComponents

variable {E H M EG HG G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [IsManifold IG ∞ G] [MulAction G M]
  [ContMDiffSMul IG I ∞ G M]

variable (IG) in
include IG in
/-- **The fixed components of a subgroup of a compact Lie group are embedded submanifolds.** Let a
compact Lie group `G` act smoothly on a σ-compact Hausdorff manifold `M` without boundary, modelled
on a finite-dimensional space, let `K` be a subgroup of `G`, and let `x` be a fixed point of `K`.
For a subspace `L` of the model whose dimension is that of the fixed tangent subspace of `K` at
`x`, the connected component of the fixed set of `K` through `x` is a smooth manifold modelled on
`L`, whose inclusion into `M` is a smooth embedding with tangent image the fixed tangent subspace
of `K` at every point. -/
theorem exists_isSmoothEmbedding_connectedComponentIn_fixedPoints_of_compactSpace
    (K : Subgroup G) {x : M} (hx : x ∈ fixedPoints K M) {L : Submodule ℝ E}
    (hL : Module.finrank ℝ L = Module.finrank ℝ (fixedTangentSubspace I K x)) :
    ∃ C : ChartedSpace L (connectedComponentIn (fixedPoints K M) x), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (connectedComponentIn (fixedPoints K M) x) ∧
      IsSmoothEmbedding 𝓘(ℝ, L) I ∞
        (Subtype.val : connectedComponentIn (fixedPoints K M) x → M) ∧
      ∀ y : connectedComponentIn (fixedPoints K M) x,
        LinearMap.range (mfderiv 𝓘(ℝ, L) I Subtype.val y).toLinearMap =
          fixedTangentSubspace I K (y : M) := by
  have : ContMDiffConstSMul I ∞ G M := ContMDiffSMul.contMDiffConstSMul IG
  refine of_forall_riemannianBundle_inner_mfderiv (I := I) (M := M) IG G fun hG ↦ ?_
  exact exists_isSmoothEmbedding_connectedComponentIn_fixedPoints (K := K) (fun k ↦ hG k) hx hL

end FixedComponents

end SymplecticGeometry

end
