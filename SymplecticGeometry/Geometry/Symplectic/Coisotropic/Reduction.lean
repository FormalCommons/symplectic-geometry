/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Foliation.LeafSpace.Smooth
public import SymplecticGeometry.Geometry.Symplectic.Manifold.CharacteristicFoliation
import TauCeti.Geometry.Manifold.Submersion.Diffeomorph

/-!
# Regular coisotropic reduction

Let `f : N → M` be a coisotropic immersion of a boundaryless manifold `N` into a manifold `M`
with a closed nondegenerate two-form `σ`, and let `𝓕` be its characteristic foliation, the
foliation of `N` by the kernels of the presymplectic form `f^* σ`
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsCoisotropicMap.characteristicFoliation`). If `𝓕` is
regular (`TauCeti.Foliation.IsRegular`), its leaf space carries the smooth structure of
`TauCeti.Foliation.leafSpaceChartedSpace`, and the reduced space is this leaf space.

The projection onto the leaf space is a characteristic submersion of `f^* σ`
(`TauCeti.SmoothForm.IsCharacteristicSubmersion`): its fibres are leaves, which are path-connected,
and the kernels of its differential are the tangent spaces of `𝓕`, which are the kernels of
`f^* σ`. So `f^* σ` descends to a unique symplectic form on the leaf space
(`TauCeti.SmoothForm.IsCharacteristicSubmersion.existsUnique_isSymplectic_mpullback_eq`).

The theorem for regular coisotropic reduction collects these facts with the involutivity of the
kernels of `f^* σ`, the uniqueness of the smooth structure on the leaf space for which the
projection is a submersion, and the dimension of the leaf space. Unlike McDuff–Salamon, it does
not assume that the leaf space is Hausdorff: neither the smooth structure nor the reduced form
uses it. It is stated for coisotropic immersions, which include the embedded coisotropic
submanifolds of Tau Ceti's `IsCoisotropicEmbedding`.

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `IsCoisotropicMap.isCharacteristicSubmersion_leafSpaceMk`: the projection onto the leaf space
  of a regular characteristic foliation is a characteristic submersion of the presymplectic form.
* `IsCoisotropicMap.existsUnique_isSymplectic_mpullback_eq`: the presymplectic form is the
  pullback of a unique symplectic form on the leaf space.
* `IsCoisotropicMap.isSubmersion_leafSpaceMk_and_existsUnique_isSymplectic_mpullback_eq`:
  regular coisotropic reduction.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.4,
  Lemma 5.4.1 and Proposition 5.4.5
-/

public section

noncomputable section

open Function Manifold Module TauCeti.Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

universe u v

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [IsManifold J (∞ + 1) N]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : N → M}
  {h : hσ.IsCoisotropicMap J f} {hi : IsImmersion J I ∞ f} {hf : ContMDiff J I ∞ f}
  {hσc : σ.IsClosed} {hn : (1 : ℕ∞ω) ≤ ∞}

/-- **The projection onto the reduced space is a characteristic submersion.** For a coisotropic
immersion `f` whose characteristic foliation is regular, the projection of `N` onto the leaf space
of the characteristic foliation is a characteristic submersion of the presymplectic form
`f^* σ`. -/
theorem IsCoisotropicMap.isCharacteristicSubmersion_leafSpaceMk
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) :
    letI := Foliation.leafSpaceChartedSpace hR
    SmoothForm.IsCharacteristicSubmersion
      𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
      (SmoothForm.mpullback f hf σ) (h.characteristicFoliation hi hf hσc hn).leafSpaceMk := by
  let := Foliation.leafSpaceChartedSpace hR
  refine ⟨Foliation.isSubmersion_leafSpaceMk hR, Foliation.leafSpaceMk_surjective, fun b ↦ ?_,
    fun x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := Foliation.leafSpaceMk_surjective b
    rw [Foliation.preimage_leafSpaceMk_singleton]
    exact (Foliation.isPathConnected_leaf _ x).isConnected.isPreconnected
  · exact (Foliation.ker_mfderiv_leafSpaceMk hR x).trans
      (h.characteristicFoliation_distribution hi hf hσc hn x)

/-- **The reduced form.** For a coisotropic immersion `f` whose characteristic foliation is
regular, the presymplectic form `f^* σ` is the pullback, along the projection onto the leaf space
of the characteristic foliation, of a unique symplectic form on the leaf space. -/
theorem IsCoisotropicMap.existsUnique_isSymplectic_mpullback_eq
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) :
    letI := Foliation.leafSpaceChartedSpace hR
    haveI := Foliation.isManifold_leafSpace hR
    ∃! τ : SmoothTwoForm 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
        (h.characteristicFoliation hi hf hσc hn).LeafSpace,
      τ.IsSymplectic ∧ SmoothForm.mpullback (h.characteristicFoliation hi hf hσc hn).leafSpaceMk
        (Foliation.contMDiff_leafSpaceMk hR) τ = SmoothForm.mpullback f hf σ := by
  let := Foliation.leafSpaceChartedSpace hR
  have := Foliation.isManifold_leafSpace hR
  exact (h.isCharacteristicSubmersion_leafSpaceMk hR).existsUnique_isSymplectic_mpullback_eq
    (hσc.mpullback f hf)

/-- **Regular coisotropic reduction.** Let `f : N → M` be a coisotropic immersion of codimension
`k` of a boundaryless manifold into a `2n`-dimensional manifold with a closed nondegenerate
two-form `σ`. Then the kernels of the presymplectic form `f^* σ` form an involutive distribution.
If its foliation, the characteristic foliation of `f`, is regular, then:

* the leaf space is a smooth manifold for `TauCeti.Foliation.leafSpaceChartedSpace`, and the
  projection onto it is a submersion;
* any other topology and charted space on the leaf space for which the projection is a submersion
  give a smooth structure diffeomorphic to this one by the identity;
* its model space has dimension `2n - 2k`;
* there is a unique symplectic form `τ` on the leaf space whose pullback along the projection is
  `f^* σ`.

Milestone: *Regular coisotropic reduction*. -/
theorem IsCoisotropicMap.isSubmersion_leafSpaceMk_and_existsUnique_isSymplectic_mpullback_eq
    {n k : ℕ}
    (hE : finrank ℝ E = 2 * n) (hk : finrank ℝ F + k = finrank ℝ E)
    (hR : (h.characteristicFoliation hi hf hσc hn).IsRegular) :
    IsInvolutiveDistribution J
        (fun x ↦ LinearMap.ker ((SmoothForm.mpullback f hf σ).bilinFormAt x)) ∧
      letI := Foliation.leafSpaceChartedSpace hR
      (IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F)))) ∞
          (h.characteristicFoliation hi hf hσc hn).LeafSpace ∧
        IsSubmersion J 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F)))) ∞
          (h.characteristicFoliation hi hf hσc hn).leafSpaceMk) ∧
      (∀ {G : Type u} {H'' : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
          [TopologicalSpace H'']
          (K : ModelWithCorners ℝ G H'')
          (t : TopologicalSpace (h.characteristicFoliation hi hf hσc hn).LeafSpace)
          (b : @ChartedSpace H'' _ (h.characteristicFoliation hi hf hσc hn).LeafSpace t),
          (letI := t; letI := b;
            IsSubmersion J K ∞ (h.characteristicFoliation hi hf hσc hn).leafSpaceMk) →
          ∃ e : @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
              𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F)))) K
              (h.characteristicFoliation hi hf hσc hn).LeafSpace
              (h.characteristicFoliation hi hf hσc hn).instTopologicalSpaceLeafSpace
              (Foliation.leafSpaceChartedSpace hR)
              (h.characteristicFoliation hi hf hσc hn).LeafSpace t b ∞,
            ∀ q, e q = q) ∧
      finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F)))) =
        2 * n - 2 * k ∧
      haveI := Foliation.isManifold_leafSpace hR
      ∃! τ : SmoothTwoForm
          𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F - (finrank ℝ E - finrank ℝ F))))
          (h.characteristicFoliation hi hf hσc hn).LeafSpace,
        τ.IsSymplectic ∧ SmoothForm.mpullback (h.characteristicFoliation hi hf hσc hn).leafSpaceMk
          (Foliation.contMDiff_leafSpaceMk hR) τ = SmoothForm.mpullback f hf σ := by
  let := Foliation.leafSpaceChartedSpace hR
  refine ⟨SmoothForm.isInvolutiveDistribution_ker_bilinFormAt _ (hσc.mpullback f hf),
    ⟨Foliation.isManifold_leafSpace hR, Foliation.isSubmersion_leafSpaceMk hR⟩,
    fun K t b hb ↦ ChartedSpace.exists_diffeomorph_apply_eq_self_of_isSubmersion _ b
      Foliation.leafSpaceMk_surjective (Foliation.isSubmersion_leafSpaceMk hR) hb, ?_,
    h.existsUnique_isSymplectic_mpullback_eq hR⟩
  rw [finrank_euclideanSpace_fin]
  omega

end TauCeti.SmoothTwoForm.IsNondegenerate

end
