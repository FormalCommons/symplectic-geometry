/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Coisotropic.Lagrangian.Basic
public import SymplecticGeometry.Geometry.Manifold.Foliation.LeafSpace.ConstantRank

/-!
# The reduced Lagrangian of an injective clean intersection

Let `f : N → M` be a coisotropic immersion with regular characteristic foliation, and let
`g : P → M` be a Lagrangian immersion meeting `f` cleanly along `c : C → N`. By
`Coisotropic/Lagrangian/Basic.lean`, the map `leafSpaceMk ∘ c` from `C` to the reduced space has
constant rank, so the kernels of its derivative form a foliation of `C`
(`TauCeti.Foliation.ofConstantRank`). This file shows that this foliation is regular, so that its
leaf space is a manifold, and that, when every fibre of `leafSpaceMk ∘ c` is preconnected, the map
that `leafSpaceMk ∘ c` induces from this leaf space to the reduced space is injective. The reduced
Lagrangian is to be built on it. For an embedded coisotropic submanifold, the hypothesis on the
fibres follows from the preconnectedness of the corresponding subsets of `M`.

## Main results

* `SymplecticGeometry.IsCleanIntersection.isRegular_ofConstantRank`: the kernel foliation of
  `leafSpaceMk ∘ c` on a boundaryless `C` is regular. It is the case `leafSpaceMk ∘ c` of
  `TauCeti.Foliation.isRegular_ofConstantRank`, which holds for every smooth map of constant rank.
* `SymplecticGeometry.IsCleanIntersection.injective_leafSpaceLift`: with preconnected fibres, the
  map of leaf spaces induced by `leafSpaceMk ∘ c` is injective. It is the case `leafSpaceMk ∘ c` of
  `TauCeti.Foliation.LeafSpace.injective_lift_ofConstantRank`.
* `SymplecticGeometry.IsCleanIntersection.isPreconnected_preimage_leafSpaceMk_comp`: when `f` is
  also a topological embedding, a fibre of `leafSpaceMk ∘ c` is preconnected as soon as the
  corresponding set `range g ∩ f '' (leafSpaceMk ⁻¹' {b})` of `M` is. It is the case of a fibre
  of `leafSpaceMk` of `IsCleanIntersection.isPreconnected_preimage`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.4,
  Proposition 5.4.7
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem) and Chapter 19.
-/

public section

open Manifold Module TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry.IsCleanIntersection

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N]
  {G H'' P : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ G H''} [TopologicalSpace P] [ChartedSpace H'' P]
  {E₀ H₀ C : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  [TopologicalSpace H₀] {L : ModelWithCorners ℝ E₀ H₀} [L.Boundaryless] [TopologicalSpace C]
  [ChartedSpace H₀ C]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : N → M}
  {h : hσ.IsCoisotropicMap J f} {hi : IsImmersion J I ∞ f} {hf : ContMDiff J I ∞ f}
  {hσc : σ.IsClosed} {hn : (1 : ℕ∞ω) ≤ ∞} {g : P → M} {c : C → N}

/-- **The kernel foliation of `leafSpaceMk ∘ c` on a clean intersection is regular.** Let `f`
be a coisotropic immersion with regular characteristic foliation, `g` a Lagrangian immersion, and
`c` a clean intersection of `f` and `g` from a boundaryless manifold `C`. Then the foliation of
`C` by the kernels of the derivative of `leafSpaceMk ∘ c`, a map of constant rank
`dim P - (dim M - dim N)`, is regular. -/
theorem isRegular_ofConstantRank (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) (hg : hσ.IsLagrangianMap K g)
    (hgi : IsImmersion K I ∞ g) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    haveI := hc.isSmoothEmbedding.isImmersion.isManifold
    (Foliation.ofConstantRank
      ((Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff)
      (hc.mfderivRank_leafSpaceMk_comp_eq hR hg hgi) hn).IsRegular :=
  letI := Foliation.leafSpaceChartedSpace hR
  haveI := Foliation.isManifold_leafSpace hR
  haveI := hc.isSmoothEmbedding.isImmersion.isManifold
  Foliation.isRegular_ofConstantRank
    ((Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff)
    (hc.mfderivRank_leafSpaceMk_comp_eq hR hg hgi)

/-- **The leaf space of a clean intersection maps injectively to the reduced space.** Let `f` be
a coisotropic immersion with regular characteristic foliation, `g` a Lagrangian immersion, and
`c` a clean intersection of `f` and `g` from a boundaryless manifold `C`. If every fibre of
`leafSpaceMk ∘ c` is preconnected, the map induced by `leafSpaceMk ∘ c` from the leaf space of the
kernel foliation of `leafSpaceMk ∘ c` on `C` to the leaf space of the characteristic foliation of
`f` is injective. -/
theorem injective_leafSpaceLift (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) (hg : hσ.IsLagrangianMap K g)
    (hgi : IsImmersion K I ∞ g)
    (hpc : ∀ b,
      IsPreconnected ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c ⁻¹' {b})) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    haveI := hc.isSmoothEmbedding.isImmersion.isManifold
    Function.Injective (Foliation.LeafSpace.lift
      ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) fun _ _ ↦
        Foliation.SameLeaf.apply_eq_of_ofConstantRank
          (hf := (Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff)
          (hr := hc.mfderivRank_leafSpaceMk_comp_eq hR hg hgi) (hn := hn)) :=
  letI := Foliation.leafSpaceChartedSpace hR
  haveI := Foliation.isManifold_leafSpace hR
  haveI := hc.isSmoothEmbedding.isImmersion.isManifold
  Foliation.LeafSpace.injective_lift_ofConstantRank _ _ hn hpc

omit [J.Boundaryless] [FiniteDimensional ℝ E₀] [L.Boundaryless] in
/-- **Preconnected fibres from preconnected subsets of `M`.** Let `f` be a coisotropic immersion
that is a topological embedding, as for an embedded coisotropic submanifold
(`IsCoisotropicEmbedding.isEmbedding`), and let `f` and `g` intersect cleanly along `c`. If, for a
leaf `b` of the characteristic foliation of `f`, the set `range g ∩ f '' (leafSpaceMk ⁻¹' {b})` is
preconnected in `M`, then the fibre `(leafSpaceMk ∘ c) ⁻¹' {b}` is preconnected in `C`. -/
theorem isPreconnected_preimage_leafSpaceMk_comp (hc : IsCleanIntersection I J K L f g c)
    (hfe : Topology.IsEmbedding f) (b : (h.characteristicFoliation hi hf hσc hn).LeafSpace)
    (hb : IsPreconnected
      (Set.range g ∩ f '' ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ⁻¹' {b}))) :
    IsPreconnected ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c ⁻¹' {b}) :=
  hc.isPreconnected_preimage hfe hb

end SymplecticGeometry.IsCleanIntersection

end
