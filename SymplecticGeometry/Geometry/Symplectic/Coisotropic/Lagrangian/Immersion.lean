/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Coisotropic.Lagrangian.Basic
import SymplecticGeometry.Geometry.Manifold.ConstantRank.Immersion
import SymplecticGeometry.Geometry.Symplectic.Lagrangian.Manifold

/-!
# The reduced Lagrangian as a Lagrangian immersion

Let `f : N → M` be a coisotropic immersion with regular characteristic foliation, and let
`g : P → M` be a Lagrangian immersion meeting `f` cleanly along `c : C → N`. By
`Coisotropic/Lagrangian/Basic.lean`, the map `leafSpaceMk ∘ c` into the reduced space has constant
rank `dim P - (dim M - dim N)` and Lagrangian tangent images. This file turns it into a Lagrangian
immersion with the same image, without building a leaf space of `C`. When `C` is second countable,
`ContMDiff.exists_isImmersion_range_eq_of_mfderivRank_eq` gives an immersion from a Hausdorff,
second countable manifold modelled on `EuclideanSpace ℝ (Fin (dim P - (dim M - dim N)))`, a
disjoint union of countably many open sets of that space, with the same range as
`leafSpaceMk ∘ c` and the same tangent images, so that it is Lagrangian too.

## Main results

* `SymplecticGeometry.IsCleanIntersection.exists_isLagrangianImmersion_range_eq_image`: for a
  second countable, nonempty `N` and a boundaryless `C`, a Hausdorff, second
  countable manifold, in the universe of `C`, of dimension `dim P - (dim M - dim N)` and a
  Lagrangian immersion from it into the reduced space, for any nondegenerate `τ` there whose
  pullback is `f^* σ`, with image `leafSpaceMk '' range c`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.4,
  Proposition 5.4.7
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.12 (the rank theorem).
-/

public section

universe u

open Set Manifold Module TauCeti TauCeti.SmoothTwoForm.IsNondegenerate
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
  {E₀ H₀ : Type*} {C : Type u} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀]
  {L : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace C] [ChartedSpace H₀ C]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : N → M}
  {h : hσ.IsCoisotropicMap J f} {hi : IsImmersion J I ∞ f} {hf : ContMDiff J I ∞ f}
  {hσc : σ.IsClosed} {hn : (1 : ℕ∞ω) ≤ ∞} {g : P → M} {c : C → N}

/-- **The reduced Lagrangian immersion.** Let `f` be a coisotropic immersion of a second countable
manifold `N` with regular characteristic foliation, `g` a Lagrangian immersion, and `c` a clean
intersection of `f` and `g` from a boundaryless manifold `C` in the universe `u`, with `N`
nonempty. Let `τ` be a nondegenerate two-form on the leaf space whose pullback to `N` is `f^* σ`.
Then there is a Hausdorff, second countable manifold `S` in the universe `u`, modelled on
`EuclideanSpace ℝ (Fin (dim P - (dim M - dim N)))`, with a Lagrangian immersion `S → LeafSpace`
for `τ` whose range is the image of `range c` in the leaf space. The empty `C` is allowed; the
nonempty `N` gives `dim N ≤ dim M ≤ 2 dim N`, which an empty `N` leaves free. -/
theorem exists_isLagrangianImmersion_range_eq_image [L.Boundaryless] [Nonempty N]
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
      ∃ (S : Type u) (_ : TopologicalSpace S)
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
  -- For an empty `C`, the source is empty, of the right dimension since `g` is a Lagrangian
  -- immersion and `N` is nonempty.
  rcases isEmpty_or_nonempty C with hC | ⟨⟨x₀⟩⟩
  · obtain ⟨x⟩ := ‹Nonempty N›
    have hG := hg.two_mul_finrank
    have hF := h.finrank_ker_bilinFormAt_mpullback_add hf (hi.mfderiv_injective (by simp) x)
    have hk := h.finrank_le_two_mul_finrank x
    let := ChartedSpace.empty
      (EuclideanSpace ℝ (Fin (finrank ℝ G - (finrank ℝ E - finrank ℝ F)))) PEmpty.{u + 1}
    refine ⟨PEmpty, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      isEmptyElim, isLagrangianImmersion_iff_of_isEmpty.2 ?_, ?_⟩
    · simp only [finrank_euclideanSpace_fin]
      omega
    · rw [range_eq_empty, range_eq_empty, image_empty]
  have : FiniteDimensional ℝ E₀ := FiniteDimensional.of_injective _
    (hc.isSmoothEmbedding.isImmersion.mfderiv_injective (by simp) x₀)
  have : SecondCountableTopology C := hc.isSmoothEmbedding.isEmbedding.secondCountableTopology
  set p := (h.characteristicFoliation hi hf hσc hn).leafSpaceMk
  have hpc : ContMDiff L _ ∞ (p ∘ c) :=
    (Foliation.contMDiff_leafSpaceMk hR).comp hc.isSmoothEmbedding.contMDiff
  obtain ⟨S, _, _, hS, hT2, hSC, ι, hι, hrange, hιf⟩ :=
    hpc.exists_isImmersion_range_eq_of_mfderivRank_eq (by simp)
      (hc.mfderivRank_leafSpaceMk_comp_eq hR hg.isLagrangianMap hg.isImmersion)
  have : Nonempty S := by
    rw [← range_nonempty_iff_nonempty, hrange]
    exact ⟨_, mem_range_self x₀⟩
  refine ⟨S, _, _, hS, hT2, hSC, ι, isLagrangianImmersion_iff.2 ⟨hι, ?_⟩, by
    rw [hrange, range_comp]⟩
  exact isLagrangianMap_iff_forall.2 <| hιf (fun X W ↦ (hτ.symplecticFormAt X).IsLagrangian W) <|
    isLagrangianMap_iff_forall.1 (hc.isLagrangianMap_leafSpaceMk_comp hR hg.isLagrangianMap hτ hτσ)

end SymplecticGeometry.IsCleanIntersection

end
