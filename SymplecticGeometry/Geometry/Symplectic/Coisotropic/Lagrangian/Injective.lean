/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Coisotropic.Lagrangian.Basic
public import SymplecticGeometry.Geometry.Manifold.Foliation.LeafSpace.ConstantRank
public import SymplecticGeometry.Geometry.Symplectic.Coisotropic.Lagrangian.Immersion
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Isotropic
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

The induced map is then an injective Lagrangian immersion: the projection of `C` onto its leaf
space is a surjective submersion whose differential has the same kernel as that of
`leafSpaceMk ∘ c`, so Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.isLagrangianImmersion_of_comp_submersion`
applies. When the reduced space is Hausdorff, so is the leaf space of `C`, since it maps
injectively and continuously into it. Together with the general case of `Immersion.lean` and the
transverse case of `Basic.lean`, this gives the reduction of a Lagrangian submanifold by a
coisotropic one.

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
* `SymplecticGeometry.IsCleanIntersection.exists_injective_isLagrangianImmersion_range_eq_image`:
  for a Hausdorff reduced space and preconnected fibres, some injective Lagrangian immersion has
  range `leafSpaceMk '' range c`; its source has dimension `dim P - (dim M - dim N)` and is
  Hausdorff and second countable.
* `IsCleanIntersection.exists_isLagrangianImmersion_range_eq_image_and_transverse_and_injective`:
  the general, transverse and injective cases together.
* `IsCleanIntersection.exists_injective_isLagrangianImmersion_of_isCoisotropicEmbedding`:
  the injective case for a coisotropic embedding `f` and a Lagrangian embedding `g`, with the
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

omit [FiniteDimensional ℝ E₀] in
/-- **The injective case of the reduced Lagrangian.** Let `f` be a coisotropic immersion of a
second countable manifold `N` whose characteristic foliation is regular with Hausdorff leaf space,
`g` a Lagrangian immersion, and `c` a clean intersection of `f` and `g` from a nonempty
boundaryless manifold `C`, such that every fibre of `leafSpaceMk ∘ c` is preconnected. Let `τ` be
a nondegenerate two-form on the leaf space whose pullback to `N` is `f^* σ`. Then there is a
Hausdorff, second countable manifold `S`, modelled on
`EuclideanSpace ℝ (Fin (dim P - (dim M - dim N)))`, with an injective Lagrangian immersion
`S → LeafSpace` for `τ` whose range is the image of `range c` in the leaf space. -/
theorem exists_injective_isLagrangianImmersion_range_eq_image [Nonempty C]
    [SecondCountableTopology N] [T2Space (h.characteristicFoliation hi hf hσc hn).LeafSpace]
    (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) (hg : hσ.IsLagrangianMap K g)
    (hgi : IsImmersion K I ∞ g)
    (hpc : ∀ b,
      IsPreconnected ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c ⁻¹' {b})) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    ∀ {τ : SmoothTwoForm
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        (h.characteristicFoliation hi hf hσc hn).LeafSpace} (hτ : τ.IsNondegenerate),
      SmoothForm.mpullback (h.characteristicFoliation hi hf hσc hn).leafSpaceMk
          (Foliation.contMDiff_leafSpaceMk hR) τ = SmoothForm.mpullback f hf σ →
      ∃ (S : Type u) (_ : TopologicalSpace S)
        (_ : ChartedSpace (EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) S),
        IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) ∞ S ∧
        T2Space S ∧ SecondCountableTopology S ∧
        ∃ ι : S → (h.characteristicFoliation hi hf hσc hn).LeafSpace,
          hτ.IsLagrangianImmersion
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) ι ∧
          Function.Injective ι ∧
          Set.range ι = (h.characteristicFoliation hi hf hσc hn).leafSpaceMk '' Set.range c := by
  let := Foliation.leafSpaceChartedSpace hR
  have := Foliation.isManifold_leafSpace hR
  intro τ hτ hτσ
  have := hc.isSmoothEmbedding.isImmersion.isManifold
  have : SecondCountableTopology C := hc.isSmoothEmbedding.isEmbedding.secondCountableTopology
  have hpc' := (Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff
  have hr := hc.mfderivRank_leafSpaceMk_comp_eq hR hg hgi
  obtain ⟨x₀⟩ := ‹Nonempty C›
  have : FiniteDimensional ℝ E₀ := FiniteDimensional.of_injective _
    (hc.isSmoothEmbedding.isImmersion.mfderiv_injective (by simp) x₀)
  -- The leaf space of `C` is modelled on `EuclideanSpace ℝ (Fin (dim C - (dim C - r)))`, where the
  -- rank `r` is at most `dim C`.
  have hle := (hr x₀).symm.trans_le mfderivRank_le_finrank_source
  rw [← Nat.sub_sub_self hle]
  have hR' := hc.isRegular_ofConstantRank hR hg hgi
  let := Foliation.leafSpaceChartedSpace hR'
  have hS := Foliation.isManifold_leafSpace hR'
  have hinj := hc.injective_leafSpaceLift hR hg hgi hpc
  have hcomp := Foliation.LeafSpace.lift_comp_leafSpaceMk _
    fun _ _ ↦ Foliation.SameLeaf.apply_eq_of_ofConstantRank (hf := hpc') (hr := hr) (hn := hn)
  have : Nonempty (Foliation.ofConstantRank hpc' hr hn).LeafSpace :=
    ⟨Foliation.leafSpaceMk _ x₀⟩
  refine ⟨_, _, _, hS, T2Space.of_injective_continuous hinj
    (Foliation.LeafSpace.continuous_lift hpc'.continuous), inferInstance, _, ?_, hinj, ?_⟩
  · refine IsLagrangianMap.isLagrangianImmersion_of_comp_submersion (q := Foliation.leafSpaceMk _)
      ?_ (Foliation.isSubmersion_leafSpaceMk hR') Foliation.leafSpaceMk_surjective ?_ fun x ↦ ?_
    · rw [hcomp]
      exact hc.isLagrangianMap_leafSpaceMk_comp hR hg hτ hτσ
    · rwa [hcomp]
    · rw [hcomp]
      exact ((Foliation.ker_mfderiv_leafSpaceMk hR' x).trans
        (Foliation.ofConstantRank_distribution _ _ _ x)).symm
  · rw [← Foliation.leafSpaceMk_surjective.range_comp, hcomp, Set.range_comp]

omit [FiniteDimensional ℝ E₀] in
/-- **Clean reduction of a Lagrangian immersion by a coisotropic one.** Let `f` be a coisotropic
immersion of a second countable manifold `N` with regular characteristic foliation, `g` a
Lagrangian immersion, and `c` a clean intersection of `f` and `g` from a nonempty boundaryless
manifold `C`. Let `τ` be a nondegenerate two-form on the leaf space whose pullback to `N` is
`f^* σ`, and write `r = dim P - (dim M - dim N)`. Then:

* the image `leafSpaceMk '' range c` is the range of a Lagrangian immersion for `τ` from a
  Hausdorff, second countable manifold modelled on `EuclideanSpace ℝ (Fin r)`
  (`exists_isLagrangianImmersion_range_eq_image`);
* if the tangent spaces of `f` and `g` span the tangent space of `M` at every point over the
  intersection, `leafSpaceMk ∘ c` itself is a Lagrangian immersion for `τ`
  (`isLagrangianImmersion_leafSpaceMk_comp_of_transverse`);
* if the leaf space is Hausdorff and every fibre of `leafSpaceMk ∘ c` is preconnected, the
  image is moreover the range of such an immersion that is injective
  (`exists_injective_isLagrangianImmersion_range_eq_image`). For an embedded `f`, the hypothesis
  on the fibres follows from the preconnectedness of each `range g ∩ f '' (leafSpaceMk ⁻¹' {b})`
  (`exists_injective_isLagrangianImmersion_of_isCoisotropicEmbedding`).

Milestone: *Clean reduction of Lagrangian submanifolds*. -/
theorem exists_isLagrangianImmersion_range_eq_image_and_transverse_and_injective [Nonempty C]
    [SecondCountableTopology N] (hc : IsCleanIntersection I J K L f g c)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) (hg : hσ.IsLagrangianMap K g)
    (hgi : IsImmersion K I ∞ g) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    ∀ {τ : SmoothTwoForm
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        (h.characteristicFoliation hi hf hσc hn).LeafSpace} (hτ : τ.IsNondegenerate),
      SmoothForm.mpullback (h.characteristicFoliation hi hf hσc hn).leafSpaceMk
          (Foliation.contMDiff_leafSpaceMk hR) τ = SmoothForm.mpullback f hf σ →
      (∃ (S : Type) (_ : TopologicalSpace S)
        (_ : ChartedSpace (EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) S),
        IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) ∞ S ∧
        T2Space S ∧ SecondCountableTopology S ∧
        ∃ ι : S → (h.characteristicFoliation hi hf hσc hn).LeafSpace,
          hτ.IsLagrangianImmersion
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) ι ∧
          Set.range ι = (h.characteristicFoliation hi hf hσc hn).leafSpaceMk '' Set.range c) ∧
      ((∀ (x : C) (y : P), g y = f (c x) →
        LinearMap.range (mfderiv J I f (c x)).toLinearMap ⊔
          LinearMap.range (mfderiv K I g y).toLinearMap = ⊤) →
        hτ.IsLagrangianImmersion L ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c)) ∧
      (T2Space (h.characteristicFoliation hi hf hσc hn).LeafSpace →
        (∀ b, IsPreconnected ((h.characteristicFoliation hi hf hσc hn).leafSpaceMk ∘ c ⁻¹' {b})) →
        ∃ (S : Type u) (_ : TopologicalSpace S)
          (_ : ChartedSpace (EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) S),
          IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) ∞ S ∧
          T2Space S ∧ SecondCountableTopology S ∧
          ∃ ι : S → (h.characteristicFoliation hi hf hσc hn).LeafSpace,
            hτ.IsLagrangianImmersion
              𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) ι ∧
            Function.Injective ι ∧
            Set.range ι = (h.characteristicFoliation hi hf hσc hn).leafSpaceMk '' Set.range c) :=
  fun hτ hτσ ↦ ⟨hc.exists_isLagrangianImmersion_range_eq_image hR hg hgi hτ hτσ,
    fun htr ↦ hc.isLagrangianImmersion_leafSpaceMk_comp_of_transverse hR hg htr hτ hτσ,
    fun _ hpc ↦ hc.exists_injective_isLagrangianImmersion_range_eq_image hR hg hgi hpc hτ hτσ⟩

omit [FiniteDimensional ℝ E₀] in
/-- **The injective case for an embedded coisotropic submanifold.** Let `f` be a coisotropic
embedding of a second countable manifold `N` whose characteristic foliation is regular with
Hausdorff leaf space, `g` a Lagrangian embedding, and `c` a clean intersection of `f` and `g`
from a nonempty boundaryless manifold `C`. Suppose that for every leaf `b` the set
`range g ∩ f '' (leafSpaceMk ⁻¹' {b})`, the part of the image of `g` on the image of that leaf,
is preconnected in `M`. Let `τ` be a nondegenerate two-form on the leaf space whose pullback to
`N` is `f^* σ`. Then there is a Hausdorff, second countable manifold `S`, modelled on
`EuclideanSpace ℝ (Fin (dim P - (dim M - dim N)))`, with an injective Lagrangian immersion
`S → LeafSpace` for `τ` whose range is the image of `range c` in the leaf space. -/
theorem exists_injective_isLagrangianImmersion_of_isCoisotropicEmbedding [Nonempty C]
    [SecondCountableTopology N] (hQ : hσ.IsCoisotropicEmbedding J f)
    [T2Space (hQ.isCoisotropicMap.characteristicFoliation hQ.isImmersion hQ.isImmersion.contMDiff
      hσc hn).LeafSpace]
    (hc : IsCleanIntersection I J K L f g c)
    (hR : (hQ.isCoisotropicMap.characteristicFoliation hQ.isImmersion hQ.isImmersion.contMDiff
      hσc hn).IsRegular)
    (hg : hσ.IsLagrangianEmbedding K g)
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
      ∃ (S : Type u) (_ : TopologicalSpace S)
        (_ : ChartedSpace (EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) S),
        IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) ∞ S ∧
        T2Space S ∧ SecondCountableTopology S ∧
        ∃ ι : S → (hQ.isCoisotropicMap.characteristicFoliation hQ.isImmersion
            hQ.isImmersion.contMDiff hσc hn).LeafSpace,
          hτ.IsLagrangianImmersion
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) ι ∧
          Function.Injective ι ∧
          Set.range ι = (hQ.isCoisotropicMap.characteristicFoliation hQ.isImmersion
            hQ.isImmersion.contMDiff hσc hn).leafSpaceMk '' Set.range c :=
  fun hτ hτσ ↦ hc.exists_injective_isLagrangianImmersion_range_eq_image hR hg.isLagrangianMap
    hg.isImmersion (fun b ↦ hc.isPreconnected_preimage_leafSpaceMk_comp hQ.isEmbedding b (hpc b))
    hτ hτσ

end SymplecticGeometry.IsCleanIntersection

end
