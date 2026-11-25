/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Coisotropic.Lagrangian.Basic
public import TauCeti.Geometry.Manifold.Instances.Sigma
import SymplecticGeometry.Geometry.Manifold.ConstantRank.Factorization
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Sigma
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The reduced Lagrangian as a Lagrangian immersion

Let `f : N → M` be a coisotropic immersion with regular characteristic foliation, and let
`g : P → M` be a Lagrangian immersion meeting `f` cleanly along `c : C → N`. By
`Coisotropic/Lagrangian/Basic.lean`, the map `leafSpaceMk ∘ c` into the reduced space has constant
rank `dim P - (dim M - dim N)` and Lagrangian tangent images. This file turns it into a Lagrangian
immersion with the same image, without building a leaf space of `C`: near each point of `C`,
`leafSpaceMk ∘ c` factors as a submersion onto an open set of
`EuclideanSpace ℝ (Fin (dim P - (dim M - dim N)))` followed by a map with injective derivatives
(`ContMDiff.exists_comp_eq_of_mfderivRank_eq`, from the rank theorem), and the second map is
Lagrangian since the submersion does not change the tangent images. When `C` is second countable,
countably many of these open sets cover the image; their disjoint union `Σ i : ℕ, U i`, with the
charted space `ChartedSpace.sigma`, is a Hausdorff, second countable manifold, and the maps on the
pieces give the Lagrangian immersion.

## Main results

* `SymplecticGeometry.IsCleanIntersection.exists_isLagrangianImmersion_range_eq_image`: for a
  second countable `N` and a nonempty boundaryless `C`, a Hausdorff, second countable manifold of
  dimension `dim P - (dim M - dim N)` and a Lagrangian immersion from it into the reduced space,
  for any nondegenerate `τ` there whose pullback is `f^* σ`, with image
  `leafSpaceMk '' range c`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.4,
  Proposition 5.4.7
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem).
-/

public section

open Set Function Manifold Module TauCeti TauCeti.Manifold TauCeti.SmoothTwoForm.IsNondegenerate
  TopologicalSpace
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry.IsCleanIntersection

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [IsManifold J (∞ + 1) N]
  {G H'' P : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ G H''} [TopologicalSpace P] [ChartedSpace H'' P]
  {E₀ H₀ C : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀]
  {L : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace C] [ChartedSpace H₀ C]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : N → M}
  {h : hσ.IsCoisotropicMap J f} {hi : IsImmersion J I ∞ f} {hf : ContMDiff J I ∞ f}
  {hσc : σ.IsClosed} {hn : (1 : ℕ∞ω) ≤ ∞} {g : P → M} {c : C → N}

/-- **The reduced Lagrangian immersion.** Let `f` be a coisotropic immersion of a second countable
manifold `N` with regular characteristic foliation, `g` a Lagrangian immersion, and `c` a clean
intersection of `f` and `g` from a nonempty boundaryless manifold `C`. Let `τ` be a nondegenerate
two-form on the leaf space whose pullback to `N` is `f^* σ`. Then there is a Hausdorff, second
countable manifold `S`, modelled on `EuclideanSpace ℝ (Fin (dim P - (dim M - dim N)))`, with a
Lagrangian immersion `S → LeafSpace` for `τ` whose range is the image of `range c` in the leaf
space. -/
theorem exists_isLagrangianImmersion_range_eq_image [L.Boundaryless] [Nonempty C]
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
      ∃ (S : Type) (_ : TopologicalSpace S)
        (_ : ChartedSpace (EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) S),
        IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) ∞ S ∧
        T2Space S ∧ SecondCountableTopology S ∧
        ∃ ι : S → (h.characteristicFoliation hi hf hσc hn).LeafSpace,
          hτ.IsLagrangianImmersion
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) ι ∧
          range ι = (h.characteristicFoliation hi hf hσc hn).leafSpaceMk '' range c := by
  let := Foliation.leafSpaceChartedSpace hR
  have := Foliation.isManifold_leafSpace hR
  intro τ hτ hτσ
  have := hc.isSmoothEmbedding.isImmersion.isManifold
  obtain ⟨x₀⟩ := ‹Nonempty C›
  have : FiniteDimensional ℝ E₀ := FiniteDimensional.of_injective _
    (hc.isSmoothEmbedding.isImmersion.mfderiv_injective (by simp) x₀)
  have : SecondCountableTopology C := hc.isSmoothEmbedding.isEmbedding.secondCountableTopology
  set p := (h.characteristicFoliation hi hf hσc hn).leafSpaceMk
  have hpc : ContMDiff L _ ∞ (p ∘ c) :=
    (Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff
  -- Near each point, `p ∘ c` is `ι x ∘ q x` on `V x`, with `q x` a submersion onto `U x`.
  choose V U q ι hV hxV hU hqV hιq hq hqs hι hιi using fun x ↦
    hpc.exists_comp_eq_of_mfderivRank_eq (by simp) (hc.mfderivRank_leafSpaceMk_comp_eq hR hg hgi) x
  -- Countably many of the `V x` cover `C`.
  obtain ⟨s, hs, hcover⟩ := TopologicalSpace.countable_cover_nhds fun x ↦ (hV x).mem_nhds (hxV x)
  have hsne : s.Nonempty := by
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.1 (hcover ▸ mem_univ x₀ : x₀ ∈ ⋃ x ∈ s, V x)
    exact ⟨y, hy⟩
  obtain ⟨e, rfl⟩ := hs.exists_eq_range hsne
  have hcover' : ⋃ i, V (e i) = univ := by rwa [biUnion_range] at hcover
  -- The pieces of the source and the map on their disjoint union.
  let W (i : ℕ) : Opens (EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) :=
    ⟨U (e i), hU (e i)⟩
  let ιS : (Σ i, W i) → (h.characteristicFoliation hi hf hσc hn).LeafSpace :=
    fun z ↦ ι (e z.1) z.2
  have hιS (i : ℕ) : ιS ∘ Sigma.mk i = ι (e i) ∘ Subtype.val := rfl
  have hne : Nonempty (Σ i, W i) :=
    ⟨⟨0, q (e 0) (e 0), (hqV (e 0)).subset (mem_image_of_mem _ (hxV (e 0)))⟩⟩
  have hιd (x : C) {u} (hu : u ∈ U x) := ((hι x).mdifferentiableOn (by simp)).mdifferentiableAt
    ((hU x).mem_nhds hu)
  have hdι (i : ℕ) (u : W i) :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F))))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F)))) ιS ⟨i, u⟩ =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F))))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F)))) (ι (e i)) u ∘L
        (tangentSpaceOpenEquiv u).toContinuousLinearMap := by
    rw [mfderiv_sigma, hιS, mfderiv_comp u (hιd (e i) u.property)
      ((contMDiff_subtypeVal (n := 1)).mdifferentiableAt one_ne_zero), mfderiv_subtype_val]
  refine ⟨Σ i, W i, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ιS, ?_, ?_⟩
  · rw [isLagrangianImmersion_iff]
    refine ⟨ContMDiff.isImmersion_of_injective_mfderiv
      (fun ⟨i, u⟩ ↦ contMDiffAt_sigma_iff.2 ?_) (by simp) fun ⟨i, u⟩ ↦ ?_, ?_⟩
    · rw [hιS]
      exact ((hι (e i)).contMDiffAt ((hU (e i)).mem_nhds u.property)).comp u
        contMDiff_subtypeVal.contMDiffAt
    · rw [hdι]
      exact (hιi (e i) u u.property).comp (tangentSpaceOpenEquiv u).injective
    · rw [isLagrangianMap_iff_forall]
      rintro ⟨i, u, hu⟩
      obtain ⟨y, hy, rfl⟩ := (hqV (e i)).symm.subset hu
      have hlag := isLagrangianMap_iff_forall.1
        (hc.isLagrangianMap_leafSpaceMk_comp hR hg hτ hτσ) y
      have heq : p ∘ c =ᶠ[𝓝 y] ι (e i) ∘ q (e i) :=
        Filter.eventuallyEq_of_mem ((hV _).mem_nhds hy) fun z hz ↦ (hιq _ z hz).symm
      -- The derivatives of `ιS` at the point and of `p ∘ c` at `y` have the same range.
      have hd (v : TangentSpace L y) :
          mfderiv L 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
            (p ∘ c) y v =
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F))))
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
            (ι (e i)) (q (e i) y)
            (mfderiv L 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F))))
              (q (e i)) y v) := by
        rw [heq.mfderiv_eq, mfderiv_comp y (hιd (e i) hu)
          (((hq (e i)).mdifferentiableOn (by simp)).mdifferentiableAt ((hV _).mem_nhds hy)),
          ]
        rfl
      have hd' (v : TangentSpace
          𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F))))
          (⟨i, q (e i) y, hu⟩ : Σ i, W i)) :
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F))))
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
            ιS ⟨i, q (e i) y, hu⟩ v =
          mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F))))
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
            (ι (e i)) (q (e i) y) (tangentSpaceOpenEquiv ⟨q (e i) y, hu⟩ v) := by
        rw [hdι]
        rfl
      have hrange : Set.range (mfderiv
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F))))
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
            ιS ⟨i, q (e i) y, hu⟩) =
          Set.range (mfderiv L
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
            (p ∘ c) y) := by
        ext w
        constructor
        · rintro ⟨v, rfl⟩
          obtain ⟨v', hv'⟩ := hqs _ y hy (tangentSpaceOpenEquiv ⟨q (e i) y, hu⟩ v)
          exact ⟨v', by rw [hd, hd', hv']⟩
        · rintro ⟨v, rfl⟩
          obtain ⟨v', hv'⟩ := (tangentSpaceOpenEquiv ⟨q (e i) y, hu⟩).surjective
            (mfderiv L 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F))))
              (q (e i)) y v)
          exact ⟨v', by rw [hd]; exact (hd' v').trans (by rw [hv'])⟩
      -- Move the base point from `ιS` of the point to `p (c y)`.
      have key : ∀ (X : (h.characteristicFoliation hi hf hσc hn).LeafSpace)
          (W : Submodule ℝ
            (TangentSpace
              𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F)))) X)),
          X = (p ∘ c) y → (W : Set (TangentSpace
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F)))) X)) =
            Set.range (mfderiv L
              𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
              (p ∘ c) y) →
          (hτ.symplecticFormAt X).IsLagrangian W := by
        rintro X W rfl hW
        have : W = LinearMap.range (mfderiv L
            𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
            (p ∘ c) y).toLinearMap :=
          SetLike.coe_injective (hW.trans (LinearMap.coe_range _).symm)
        rw [this]
        exact hlag
      exact key _ _ (hιq _ y hy) ((LinearMap.coe_range _).trans hrange)
  · ext z
    constructor
    · rintro ⟨⟨i, u⟩, rfl⟩
      obtain ⟨y, hy, hyu⟩ := (hqV (e i)).symm.subset u.property
      exact ⟨c y, mem_range_self y, (hιq _ y hy).symm.trans (congrArg (ι (e i)) hyu)⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hcover' ▸ mem_univ y : y ∈ ⋃ i, V (e i))
      exact ⟨⟨i, q (e i) y, (hqV (e i)).subset (mem_image_of_mem _ hi)⟩, hιq _ y hi⟩

end SymplecticGeometry.IsCleanIntersection

end
