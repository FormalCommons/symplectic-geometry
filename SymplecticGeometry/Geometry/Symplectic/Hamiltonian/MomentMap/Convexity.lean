/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalConvexity
public import SymplecticGeometry.Geometry.Symplectic.Manifold.FixedComponent
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ConvexHull
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.FixedPoints
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.ContMDiff

/-!
# Convexity of the image of a torus moment map, and connectedness of its fibres

Let a compact commutative Lie group `G` act smoothly on a compact connected symplectic manifold
`(M, σ)` without boundary, preserving `σ`, with moment map `μ : M → 𝔤*`. Every point of `M` lies
in a convexity chart of `μ` (`TauCeti.SmoothTwoForm.IsMomentMap.exists_isConvexChart`), and `μ`
is proper since `M` is compact, so the local-to-global theorem of Bjorndahl and Karshon, in the
form of Tau Ceti's `IsProperMap.convex_range_of_isConvexChart` and
`IsProperMap.isPreconnected_preimage_singleton_of_isConvexChart`, shows that the image of `μ` is
convex and its fibres are connected. The dual `𝔤*` carries no norm, so both are applied to `μ`
read in coordinates, through the linear equivalence of a basis of `𝔤*`.

The proofs adapt those of Tau Ceti's
`TauCeti.SmoothTwoForm.IsMomentMap.convex_range_of_forall_mem_fixedPoints_or_isotropy_eq_bot`,
`isPreconnected_preimage_singleton_of_forall_mem_fixedPoints_or_isotropy_eq_bot` and
`range_eq_convexHull_image_fixedPoints_of_forall_mem_fixedPoints_or_isotropy_eq_bot`, which have
convexity charts only at the points that are fixed or have trivial isotropy algebra, and so assume
that every point is one of these.

When `G` is moreover connected, so a torus, Tau Ceti's
`TauCeti.SmoothTwoForm.IsMomentMap.range_subset_convexHull_image_fixedPoints` then gives that the
image is the convex hull of the image of the fixed set. The theorem of Atiyah and
Guillemin–Sternberg collects these with the structure of the fixed set `M^G`:

* it has finitely many connected components, by Tau Ceti's
  `TauCeti.finite_connectedComponents_fixedPoints_of_compactSpace`;
* each of them is a symplectic submanifold, by the theorem
  `exists_isSymplecticSubmanifoldEmbedding_connectedComponentIn_fixedPoints_of_compactSpace` of
  `Geometry/Symplectic/Manifold/FixedComponent.lean`;
* `μ` is constant on each of them, by Tau Ceti's
  `TauCeti.SmoothTwoForm.IsMomentMap.apply_eq_of_isPreconnected`;
* `μ` takes finitely many values on `M^G`, by Tau Ceti's
  `TauCeti.SmoothTwoForm.IsMomentMap.finite_image_fixedPoints`, so the image is a polytope.

The results in Tau Ceti's namespace are stated in Tau Ceti's sign for moment maps; the theorem
`SymplecticGeometry.atiyah_guillemin_sternberg` is stated in the opposite sign, that of the plan,
for which `fun x ↦ -μ x` is a moment map in Tau Ceti's sense. Convexity, the convex hull and the
fibres are unchanged by the sign, up to negation.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.convex_range`: the image of `μ` is convex.
* `TauCeti.SmoothTwoForm.IsMomentMap.isConnected_preimage_singleton`: every nonempty fibre of `μ`
  is connected, over critical values included.
* `TauCeti.SmoothTwoForm.IsMomentMap.range_eq_convexHull_image_fixedPoints`: for a torus, the
  image of `μ` is the convex hull of the image of the fixed set.
* `SymplecticGeometry.atiyah_guillemin_sternberg`: the convexity theorem of Atiyah and
  Guillemin–Sternberg, with connected fibres.

## References

* [M. F. Atiyah, *Convexity and commuting Hamiltonians*][Atiyah1982], Theorem 1.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 5.5.1.
* [A. Cannas da Silva, *Symplectic Toric Manifolds*][CannasdaSilva2001], Theorem 1.5.1.
* [C. Bjorndahl and Y. Karshon, *Revisiting Tietze–Nakajima: local and global convexity for
  maps*][BjorndahlKarshon2010], Theorems 10 and 30.
-/

public section

open Set
open scoped ContDiff Manifold Pointwise

namespace TauCeti.SmoothTwoForm.IsMomentMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [IsMulCommutative G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [CompactSpace M] [PreconnectedSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **The image of a moment map is convex.** Let a compact commutative Lie group `G` act smoothly
on a compact connected symplectic manifold `(M, σ)` without boundary, preserving `σ`, with moment
map `μ`. Then the image of `μ` is a convex subset of `𝔤*`. -/
theorem convex_range
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    Convex ℝ (range μ) := by
  -- `𝔤*` carries no norm, so `μ` is read in the coordinates `e` of a basis.
  set e := (Module.finBasis ℝ (Module.Dual ℝ (GroupLieAlgebra I G))).equivFun
  have hp : IsProperMap (e ∘ μ) := (h.continuous_linearMap_comp e).isProperMap
  have hloc := h.exists_isConvexChart hσ hG e
  have hc := (hp.convex_range_of_isConvexChart hloc).linear_image e.symm.toLinearMap
  rw [range_comp, image_image] at hc
  simpa using hc

/-- **The fibres of a moment map are connected.** Let a compact commutative Lie group `G` act
smoothly on a compact connected symplectic manifold `(M, σ)` without boundary, preserving `σ`,
with moment map `μ`. Then every fibre `μ⁻¹(η)` over a point `η` of the image of `μ` is connected,
whether `η` is a regular value or not. -/
theorem isConnected_preimage_singleton
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {η : Module.Dual ℝ (GroupLieAlgebra I G)} (hη : η ∈ range μ) :
    IsConnected (μ ⁻¹' {η}) := by
  -- `𝔤*` carries no norm, so `μ` is read in the coordinates `e` of a basis.
  set e := (Module.finBasis ℝ (Module.Dual ℝ (GroupLieAlgebra I G))).equivFun
  have hp : IsProperMap (e ∘ μ) := (h.continuous_linearMap_comp e).isProperMap
  have hloc := h.exists_isConvexChart hσ hG e
  obtain ⟨x, rfl⟩ := hη
  refine ⟨⟨x, rfl⟩, ?_⟩
  convert hp.isPreconnected_preimage_singleton_of_isConvexChart hloc (e (μ x)) using 1
  ext y
  simp

/-- **The image of a torus moment map is the convex hull of the image of the fixed set.** Let a
torus `G` act smoothly on a compact connected symplectic manifold `(M, σ)` without boundary,
preserving `σ`, with moment map `μ`. Then the image of `μ` is the convex hull of the image under
`μ` of the fixed set `M^G`. -/
theorem range_eq_convexHull_image_fixedPoints [PreconnectedSpace G]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    range μ = convexHull ℝ (μ '' MulAction.fixedPoints G M) :=
  (h.range_subset_convexHull_image_fixedPoints hσ.isNondegenerate).antisymm <|
    convexHull_min (image_subset_range _ _) (h.convex_range hσ hG)

end TauCeti.SmoothTwoForm.IsMomentMap

namespace SymplecticGeometry

open MulAction TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [IsMulCommutative G] [CompactSpace G] [PreconnectedSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E' M] [IsManifold 𝓘(ℝ, E') ∞ M] [T2Space M]
  [CompactSpace M] [PreconnectedSpace M] [MulAction G M] [ContMDiffSMul I 𝓘(ℝ, E') ∞ G M]
  {σ : SmoothTwoForm 𝓘(ℝ, E') M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The convexity theorem of Atiyah and Guillemin–Sternberg.** Let a torus `G` act smoothly on a
compact connected symplectic manifold `(M, σ)` without boundary, preserving `σ`, with moment map
`μ`, in the sign for which `-μ` is a moment map in Tau Ceti's sense. Then:

* the fixed set `M^G` has finitely many connected components;
* each of them is a symplectic submanifold of `M`, modelled on a subspace `L` of the model space;
* `μ` is constant on each of them;
* `μ` takes finitely many values on `M^G`;
* the image of `μ` is the convex hull of these values, so a convex polytope;
* every fibre `μ⁻¹(η)` over a point of the image is connected, over critical values included.

Milestone: *Convexity and connectedness of moment-map fibers*. -/
theorem atiyah_guillemin_sternberg
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) (fun x ↦ -μ x))
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    Finite (ConnectedComponents (fixedPoints G M)) ∧
    (∀ x ∈ fixedPoints G M, ∃ (L : Submodule ℝ E')
        (_ : ChartedSpace L (connectedComponentIn (fixedPoints G M) x)),
        IsManifold 𝓘(ℝ, L) ∞ (connectedComponentIn (fixedPoints G M) x) ∧
        hσ.isNondegenerate.IsSymplecticSubmanifoldEmbedding 𝓘(ℝ, L)
          (Subtype.val : connectedComponentIn (fixedPoints G M) x → M)) ∧
    (∀ x ∈ fixedPoints G M, ∀ y ∈ connectedComponentIn (fixedPoints G M) x, μ y = μ x) ∧
    (μ '' fixedPoints G M).Finite ∧
    range μ = convexHull ℝ (μ '' fixedPoints G M) ∧
    ∀ η ∈ range μ, IsConnected (μ ⁻¹' {η}) := by
  -- `μ` is the negation of the moment map `ν = -μ` in Tau Ceti's sign.
  set ν : M → Module.Dual ℝ (GroupLieAlgebra I G) := fun x ↦ -μ x
  have hμν : μ = Neg.neg ∘ ν := funext fun x ↦ (neg_neg (μ x)).symm
  have himage (s : Set M) : μ '' s = -(ν '' s) := by
    rw [hμν, image_comp, image_neg_eq_neg]
  refine ⟨finite_connectedComponents_fixedPoints_of_compactSpace 𝓘(ℝ, E') I G, fun x hx ↦ ?_,
    fun x hx y hy ↦ ?_, ?_, ?_, fun η hη ↦ ?_⟩
  · -- The fixed tangent subspace at `x` is itself a subspace of the model `E'`.
    obtain ⟨C, hC, hemb, -⟩ :=
      open SmoothTwoForm.IsNondegenerate in
      exists_isSymplecticSubmanifoldEmbedding_connectedComponentIn_fixedPoints_of_compactSpace
        (IG := I) hσ.isNondegenerate hG hx (L := fixedTangentSubspace 𝓘(ℝ, E') G x) rfl
    exact ⟨_, C, hC, hemb⟩
  · exact neg_inj.1 <| h.apply_eq_of_isPreconnected isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) hy (mem_connectedComponentIn hx)
  · rw [himage]
    exact (h.finite_image_fixedPoints).neg
  · rw [← image_univ, himage, himage, convexHull_neg, image_univ,
      h.range_eq_convexHull_image_fixedPoints hσ hG]
  · rw [hμν, preimage_comp, neg_preimage, neg_singleton]
    refine h.isConnected_preimage_singleton hσ hG ?_
    rw [hμν, range_comp] at hη
    simpa using hη

end SymplecticGeometry
