/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Coisotropic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Isotropic
public import SymplecticGeometry.Geometry.Symplectic.Lagrangian.ImmersionRange
public import SymplecticGeometry.Geometry.Manifold.Distribution.ConstantRank
import SymplecticGeometry.Geometry.Manifold.Foliation.LeafSpace.ConstantRank
import SymplecticGeometry.Geometry.Symplectic.Coisotropic.Lagrangian.Immersion
import TauCeti.Geometry.Symplectic.Lagrangian.Submersion

/-!
# The reduced Lagrangian of an injective clean intersection

Let `f : N → M` be a coisotropic immersion with regular characteristic foliation, and let
`g : P → M` be a Lagrangian immersion meeting `f` cleanly along `c : C → N`. By
`Coisotropic/Lagrangian/Basic.lean`, the map `leafSpaceMk ∘ c` from `C` to the reduced space has
constant rank, so the kernels of its derivative form a foliation of `C`
(`TauCeti.Foliation.ofConstantRank`). This file shows that this foliation is regular, so that its
leaf space is a manifold, and that, when every fibre of `leafSpaceMk ∘ c` is preconnected, the map
that `leafSpaceMk ∘ c` induces from this leaf space to the reduced space is injective. For an
embedded coisotropic submanifold, the hypothesis on the fibres follows from the preconnectedness of
the corresponding subsets of `M`.

The induced map is then an injective Lagrangian immersion: it is an immersion by
`TauCeti.Foliation.LeafSpace.isImmersion_lift_ofConstantRank`, and Lagrangian by Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianMap_comp_submersion_iff`, applied to the
projection of `C` onto its leaf space, a surjective submersion. When the reduced space is
Hausdorff, so is the leaf space of `C`, since it maps injectively and continuously into it.
Together with the general case of `Immersion.lean` and the transverse case of `Basic.lean`, this
gives the reduction of a Lagrangian submanifold by a coisotropic one.

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
* `SymplecticGeometry.IsCleanIntersection.isLagrangianImmersion_leafSpaceLift`,
  `SymplecticGeometry.IsCleanIntersection.range_leafSpaceLift` and
  `SymplecticGeometry.IsCleanIntersection.t2Space_leafSpace_ofConstantRank`: the induced map is a
  Lagrangian immersion with range `leafSpaceMk '' range c`, and, for a Hausdorff reduced space and
  preconnected fibres, its source is Hausdorff.
* `SymplecticGeometry.IsCleanIntersection.isInjectiveLagrangianImmersionRange_leafSpaceMk_image`:
  for a Hausdorff reduced space and preconnected fibres, the set `leafSpaceMk '' range c`
  satisfies `IsInjectiveLagrangianImmersionRange` in dimension `dim P - (dim M - dim N)`: it is
  the range of an injective Lagrangian immersion whose source is a second countable Hausdorff
  manifold.
* `IsCleanIntersection.isLagrangianImmersionRange_leafSpaceMk_image_and_transverse_and_injective`:
  the general, transverse and injective cases together.
* `IsCleanIntersection.isInjectiveLagrangianImmersionRange_of_isCoisotropicEmbedding`:
  the injective case for a coisotropic embedding `f` and a Lagrangian immersion `g`, with the
  hypothesis on the fibres stated in `M`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.4,
  Proposition 5.4.7
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem) and Chapter 19.
-/

public section

universe u

open Manifold Module TauCeti TauCeti.SmoothTwoForm.IsNondegenerate
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
  {E₀ H₀ : Type*} {C : Type u} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
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
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular)
    (hg : hσ.IsLagrangianImmersion K g) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    haveI := hc.isSmoothEmbedding.isImmersion.isManifold
    (Foliation.ofConstantRank
      ((Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff)
      (hc.mfderivRank_leafSpaceMk_comp_eq hR hg) hn).IsRegular :=
  letI := Foliation.leafSpaceChartedSpace hR
  haveI := Foliation.isManifold_leafSpace hR
  haveI := hc.isSmoothEmbedding.isImmersion.isManifold
  Foliation.isRegular_ofConstantRank
    ((Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff)
    (hc.mfderivRank_leafSpaceMk_comp_eq hR hg)

/-- **The leaf space of a clean intersection maps injectively to the reduced space.** Let `f` be
a coisotropic immersion with regular characteristic foliation, `g` a Lagrangian immersion, and
`c` a clean intersection of `f` and `g` from a boundaryless manifold `C`. If every fibre of
`leafSpaceMk ∘ c` is preconnected, the map induced by `leafSpaceMk ∘ c` from the leaf space of the
kernel foliation of `leafSpaceMk ∘ c` on `C` to the leaf space of the characteristic foliation of
`f` is injective. -/
theorem injective_leafSpaceLift (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular)
    (hg : hσ.IsLagrangianImmersion K g)
    (hpc : ∀ b,
      IsPreconnected ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c ⁻¹' {b})) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    haveI := hc.isSmoothEmbedding.isImmersion.isManifold
    Function.Injective (Foliation.LeafSpace.lift
      ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) fun _ _ ↦
        Foliation.SameLeaf.apply_eq_of_ofConstantRank
          (hf := (Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff)
          (hr := hc.mfderivRank_leafSpaceMk_comp_eq hR hg) (hn := hn)) :=
  letI := Foliation.leafSpaceChartedSpace hR
  haveI := Foliation.isManifold_leafSpace hR
  haveI := hc.isSmoothEmbedding.isImmersion.isManifold
  Foliation.LeafSpace.injective_lift_ofConstantRank _ _ hn hpc

/-- **The leaf space of a clean intersection is Hausdorff.** Let `f` be a coisotropic immersion
whose characteristic foliation is regular with Hausdorff leaf space, `g` a Lagrangian immersion,
and `c` a clean intersection of `f` and `g` from a boundaryless manifold `C`. If every fibre of
`leafSpaceMk ∘ c` is preconnected, the leaf space of the kernel foliation of `leafSpaceMk ∘ c` on
`C` is Hausdorff. -/
theorem t2Space_leafSpace_ofConstantRank
    [T2Space (h.characteristicFoliation hi hf hσc hn).LeafSpace]
    (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular)
    (hg : hσ.IsLagrangianImmersion K g)
    (hpc : ∀ b,
      IsPreconnected ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c ⁻¹' {b})) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    haveI := hc.isSmoothEmbedding.isImmersion.isManifold
    T2Space (Foliation.ofConstantRank
      ((Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff)
      (hc.mfderivRank_leafSpaceMk_comp_eq hR hg) hn).LeafSpace :=
  letI := Foliation.leafSpaceChartedSpace hR
  haveI := Foliation.isManifold_leafSpace hR
  haveI := hc.isSmoothEmbedding.isImmersion.isManifold
  Foliation.LeafSpace.t2Space_ofConstantRank _ _ hn hpc

/-- The range of the map induced by `leafSpaceMk ∘ c` on the leaf space of the kernel foliation of
`leafSpaceMk ∘ c` on `C` is the image of `range c` in the leaf space of the characteristic
foliation of `f`. -/
theorem range_leafSpaceLift (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular)
    (hg : hσ.IsLagrangianImmersion K g) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    haveI := hc.isSmoothEmbedding.isImmersion.isManifold
    Set.range (Foliation.LeafSpace.lift
      ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) fun _ _ ↦
        Foliation.SameLeaf.apply_eq_of_ofConstantRank
          (hf := (Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff)
          (hr := hc.mfderivRank_leafSpaceMk_comp_eq hR hg) (hn := hn)) =
      (h.characteristicFoliation hi hf hσc hn).leafSpaceMk '' Set.range c := by
  let := Foliation.leafSpaceChartedSpace hR
  have := Foliation.isManifold_leafSpace hR
  have := hc.isSmoothEmbedding.isImmersion.isManifold
  rw [Foliation.LeafSpace.range_lift, Set.range_comp]

/-- **The map induced on the leaf space of a clean intersection is a Lagrangian immersion.**
Let `f` be a coisotropic immersion with regular characteristic foliation, `g` a Lagrangian
immersion, and `c` a clean intersection of `f` and `g` from a nonempty boundaryless manifold `C`.
Let `τ` be a nondegenerate two-form on the leaf space of `f` whose pullback to `N` is `f^* σ`.
Then the map induced by `leafSpaceMk ∘ c` from the leaf space of the kernel foliation of
`leafSpaceMk ∘ c` on `C`, with the charts `leafSpaceChartedSpace` of `isRegular_ofConstantRank`,
is a Lagrangian immersion for `τ`. -/
theorem isLagrangianImmersion_leafSpaceLift [Nonempty C] (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular)
    (hg : hσ.IsLagrangianImmersion K g) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    haveI := hc.isSmoothEmbedding.isImmersion.isManifold
    letI := Foliation.leafSpaceChartedSpace (hc.isRegular_ofConstantRank hR hg)
    ∀ {τ : SmoothTwoForm
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        (h.characteristicFoliation hi hf hσc hn).LeafSpace} (hτ : τ.IsNondegenerate),
      SmoothForm.mpullback (h.characteristicFoliation hi hf hσc hn).leafSpaceMk
          (Foliation.contMDiff_leafSpaceMk hR) τ = SmoothForm.mpullback f hf σ →
      hτ.IsLagrangianImmersion 𝓘(ℝ, EuclideanSpace ℝ
          (Fin (finrank ℝ E₀ - (finrank ℝ E₀ - (finrank ℝ G - (finrank ℝ E - finrank ℝ F))))))
        (Foliation.LeafSpace.lift
          ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c) fun _ _ ↦
            Foliation.SameLeaf.apply_eq_of_ofConstantRank
              (hf := (Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff)
              (hr := hc.mfderivRank_leafSpaceMk_comp_eq hR hg) (hn := hn)) := by
  let := Foliation.leafSpaceChartedSpace hR
  have := Foliation.isManifold_leafSpace hR
  have := hc.isSmoothEmbedding.isImmersion.isManifold
  have hR' := hc.isRegular_ofConstantRank hR hg
  let := Foliation.leafSpaceChartedSpace hR'
  have := Foliation.isManifold_leafSpace hR'
  intro τ hτ hτσ
  have hfc := (Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff
  have : Nonempty (Foliation.ofConstantRank hfc
      (hc.mfderivRank_leafSpaceMk_comp_eq hR hg) hn).LeafSpace :=
    ⟨Foliation.leafSpaceMk _ (Classical.arbitrary C)⟩
  refine isLagrangianImmersion_iff.2 ⟨Foliation.LeafSpace.isImmersion_lift_ofConstantRank hfc
    (hc.mfderivRank_leafSpaceMk_comp_eq hR hg), (hτ.isLagrangianMap_comp_submersion_iff
      (Foliation.isSubmersion_leafSpaceMk hR') Foliation.leafSpaceMk_surjective ?_).1 ?_⟩ <;>
    rw [Foliation.LeafSpace.lift_comp_leafSpaceMk]
  · exact hfc
  · exact hc.isLagrangianMap_leafSpaceMk_comp hR hg.isLagrangianMap hτ hτσ

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

omit [FiniteDimensional ℝ E₀] in
/-- **The injective case of the reduced Lagrangian.** Let `f` be a coisotropic immersion of a
nonempty, second countable manifold `N` whose characteristic foliation is regular with Hausdorff
leaf space, `g` a Lagrangian immersion, and `c` a clean intersection
of `f` and `g` from a boundaryless manifold `C`, such that every fibre of `leafSpaceMk ∘ c` is
preconnected. Let `τ` be a nondegenerate two-form on the leaf space whose pullback to `N` is
`f^* σ`. Then the image of `range c` in the leaf space is the range of an injective Lagrangian
immersion for `τ` from a Hausdorff, second countable manifold in the universe of `C`, modelled on
`EuclideanSpace ℝ (Fin (dim P - (dim M - dim N)))` (`IsInjectiveLagrangianImmersionRange`). -/
theorem isInjectiveLagrangianImmersionRange_leafSpaceMk_image [Nonempty N]
    [SecondCountableTopology N] [T2Space (h.characteristicFoliation hi hf hσc hn).LeafSpace]
    (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular)
    (hg : hσ.IsLagrangianImmersion K g)
    (hpc : ∀ b,
      IsPreconnected ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c ⁻¹' {b})) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    ∀ {τ : SmoothTwoForm
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        (h.characteristicFoliation hi hf hσc hn).LeafSpace} (hτ : τ.IsNondegenerate),
      SmoothForm.mpullback (h.characteristicFoliation hi hf hσc hn).leafSpaceMk
          (Foliation.contMDiff_leafSpaceMk hR) τ = SmoothForm.mpullback f hf σ →
      hτ.IsInjectiveLagrangianImmersionRange.{u} (finrank ℝ G - (finrank ℝ E - finrank ℝ F))
        ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk '' Set.range c) := by
  let := Foliation.leafSpaceChartedSpace hR
  have := Foliation.isManifold_leafSpace hR
  intro τ hτ hτσ
  have := hc.isSmoothEmbedding.isImmersion.isManifold
  -- For an empty `C`, the source of the general case is empty, so its map is injective.
  rcases isEmpty_or_nonempty C with hC | hC
  · obtain ⟨S, _, _, hS, hT2, hSC, ι, hι, hrange⟩ := isLagrangianImmersionRange_def.1
      (hc.isLagrangianImmersionRange_leafSpaceMk_image hR hg hτ hτσ)
    have : IsEmpty S := by
      rw [← Set.range_eq_empty_iff, hrange, Set.range_eq_empty, Set.image_empty]
    rw [← hrange]
    exact isInjectiveLagrangianImmersionRange_range hι (Function.injective_of_subsingleton ι)
  have : SecondCountableTopology C := hc.isSmoothEmbedding.isEmbedding.secondCountableTopology
  have x₀ : C := Classical.arbitrary C
  have : FiniteDimensional ℝ E₀ := FiniteDimensional.of_injective _
    (hc.isSmoothEmbedding.isImmersion.mfderiv_injective (by simp) x₀)
  -- The leaf space of `C` is modelled on `EuclideanSpace ℝ (Fin (dim C - (dim C - r)))`, where the
  -- rank `r` is at most `dim C`.
  have hle := (hc.mfderivRank_leafSpaceMk_comp_eq hR hg x₀).symm.trans_le
    mfderivRank_le_finrank_source
  rw [← Nat.sub_sub_self hle, ← hc.range_leafSpaceLift hR hg]
  have hR' := hc.isRegular_ofConstantRank hR hg
  let := Foliation.leafSpaceChartedSpace hR'
  have := Foliation.isManifold_leafSpace hR'
  have := hc.t2Space_leafSpace_ofConstantRank hR hg hpc
  exact isInjectiveLagrangianImmersionRange_range
    (hc.isLagrangianImmersion_leafSpaceLift hR hg hτ hτσ) (hc.injective_leafSpaceLift hR hg hpc)

omit [FiniteDimensional ℝ E₀] in
/-- **Clean reduction of a Lagrangian immersion by a coisotropic one.** Let `f` be a coisotropic
immersion of a nonempty, second countable manifold `N` with regular characteristic foliation,
`g` a Lagrangian immersion, and `c` a clean intersection of `f` and
`g` from a boundaryless manifold `C`. Let `τ` be a nondegenerate two-form on the leaf space whose
pullback to `N` is `f^* σ`, and write `r = dim P - (dim M - dim N)`. Then:

* the image `leafSpaceMk '' range c` is the range of a Lagrangian immersion for `τ` from a
  Hausdorff, second countable manifold, in the universe of `C`, modelled on
  `EuclideanSpace ℝ (Fin r)` (`isLagrangianImmersionRange_leafSpaceMk_image`);
* if `C` is nonempty and the tangent spaces of `f` and `g` span the tangent space of `M` at
  every point over the intersection, `leafSpaceMk ∘ c` itself is a Lagrangian immersion for `τ`
  (`isLagrangianImmersion_leafSpaceMk_comp_of_transverse`); an empty `C` may be modelled on a
  space of any dimension, so this clause needs `C` nonempty;
* if the leaf space is Hausdorff and every fibre of `leafSpaceMk ∘ c` is preconnected, the
  image is moreover the range of such an immersion that is injective
  (`isInjectiveLagrangianImmersionRange_leafSpaceMk_image`). For an embedded `f`, the hypothesis
  on the fibres follows from the preconnectedness of each `range g ∩ f '' (leafSpaceMk ⁻¹' {b})`
  (`isInjectiveLagrangianImmersionRange_of_isCoisotropicEmbedding`).

Milestone: *Clean reduction of Lagrangian submanifolds*. -/
theorem isLagrangianImmersionRange_leafSpaceMk_image_and_transverse_and_injective [Nonempty N]
    [SecondCountableTopology N] (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular)
    (hg : hσ.IsLagrangianImmersion K g) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    ∀ {τ : SmoothTwoForm
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        (h.characteristicFoliation hi hf hσc hn).LeafSpace} (hτ : τ.IsNondegenerate),
      SmoothForm.mpullback (h.characteristicFoliation hi hf hσc hn).leafSpaceMk
          (Foliation.contMDiff_leafSpaceMk hR) τ = SmoothForm.mpullback f hf σ →
      hτ.IsLagrangianImmersionRange.{u} (finrank ℝ G - (finrank ℝ E - finrank ℝ F))
        ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk '' Set.range c) ∧
      (Nonempty C → (∀ (x : C) (y : P), g y = f (c x) →
        LinearMap.range (mfderiv J I f (c x)).toLinearMap ⊔
          LinearMap.range (mfderiv K I g y).toLinearMap = ⊤) →
        hτ.IsLagrangianImmersion L ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c)) ∧
      (T2Space (h.characteristicFoliation hi hf hσc hn).LeafSpace →
        (∀ b, IsPreconnected ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c ⁻¹' {b})) →
        hτ.IsInjectiveLagrangianImmersionRange.{u} (finrank ℝ G - (finrank ℝ E - finrank ℝ F))
          ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk '' Set.range c)) :=
  fun hτ hτσ ↦ ⟨hc.isLagrangianImmersionRange_leafSpaceMk_image hR hg hτ hτσ,
    fun _ htr ↦ hc.isLagrangianImmersion_leafSpaceMk_comp_of_transverse hR hg.isLagrangianMap htr
      hτ hτσ,
    fun _ hpc ↦ hc.isInjectiveLagrangianImmersionRange_leafSpaceMk_image hR hg hpc hτ hτσ⟩

omit [FiniteDimensional ℝ E₀] in
/-- **The injective case for an embedded coisotropic submanifold.** Let `f` be a coisotropic
embedding of a nonempty, second countable manifold `N` whose characteristic foliation is regular
with Hausdorff leaf space, `g` a Lagrangian immersion, and `c` a
clean intersection of `f` and `g` from a boundaryless manifold `C`. Suppose that for every leaf
`b` the set `range g ∩ f '' (leafSpaceMk ⁻¹' {b})`, the part of the image of `g` on the image of
that leaf, is preconnected in `M`. Let `τ` be a nondegenerate two-form on the leaf space whose
pullback to `N` is `f^* σ`. Then the image of `range c` in the leaf space is the range of an
injective Lagrangian immersion for `τ` from a Hausdorff, second countable manifold in the universe
of `C`, modelled on `EuclideanSpace ℝ (Fin (dim P - (dim M - dim N)))`
(`IsInjectiveLagrangianImmersionRange`). -/
theorem isInjectiveLagrangianImmersionRange_of_isCoisotropicEmbedding [Nonempty N]
    [SecondCountableTopology N] (hQ : hσ.IsCoisotropicEmbedding J f)
    [T2Space (hQ.isCoisotropicMap.characteristicFoliation hQ.isImmersion hQ.isImmersion.contMDiff
      hσc hn).LeafSpace]
    (hc : IsCleanIntersection I J K L f g c)
    (hR : (hQ.isCoisotropicMap.characteristicFoliation hQ.isImmersion hQ.isImmersion.contMDiff
      hσc hn).IsRegular)
    (hg : hσ.IsLagrangianImmersion K g)
    (hpc : ∀ b, IsPreconnected (Set.range g ∩ f ''
      ((hQ.isCoisotropicMap.characteristicFoliation hQ.isImmersion hQ.isImmersion.contMDiff
        hσc hn).leafSpaceMk ⁻¹' {b}))) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    ∀ {τ : SmoothTwoForm
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        (hQ.isCoisotropicMap.characteristicFoliation hQ.isImmersion hQ.isImmersion.contMDiff
          hσc hn).LeafSpace} (hτ : τ.IsNondegenerate),
      SmoothForm.mpullback
          (hQ.isCoisotropicMap.characteristicFoliation hQ.isImmersion hQ.isImmersion.contMDiff
            hσc hn).leafSpaceMk
          (Foliation.contMDiff_leafSpaceMk hR) τ =
        SmoothForm.mpullback f hQ.isImmersion.contMDiff σ →
      hτ.IsInjectiveLagrangianImmersionRange.{u} (finrank ℝ G - (finrank ℝ E - finrank ℝ F))
        ((hQ.isCoisotropicMap.characteristicFoliation hQ.isImmersion hQ.isImmersion.contMDiff
          hσc hn).leafSpaceMk '' Set.range c) :=
  fun hτ hτσ ↦ hc.isInjectiveLagrangianImmersionRange_leafSpaceMk_image hR hg
    (fun b ↦ hc.isPreconnected_preimage_leafSpaceMk_comp hQ.isEmbedding b (hpc b))
    hτ hτσ

end SymplecticGeometry.IsCleanIntersection

end
