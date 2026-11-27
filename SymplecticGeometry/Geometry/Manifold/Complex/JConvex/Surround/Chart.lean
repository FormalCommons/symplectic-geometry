/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Shape

import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.Gluing
import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Section

/-!
# The first-order chart along a disc

Cieliebak and Eliashberg place their model handle along an attached disc `ι : ℝᵏ → M` through a
map `Φ` from a neighbourhood of the core `ℝᵏ × 0` of the model space `ℂᵏ × ℂᵐ` into `M`, with
`Φ ∘ ι₀ = ι` for the model disc `ι₀ = SymplecticGeometry.modelDisc k m`. This file builds the
first step of that map: given a frame `A x : ℂᵏ × ℂᵐ → T_(ι x) M` along the disc, such as the
complex frame of `SymplecticGeometry.exists_complexFrame_mfderiv`, there is a partial
diffeomorphism `Φ₀` from `ℂᵏ × ℂᵐ` to `M`, defined near the core and with image in a given open
neighbourhood of the disc, such that `Φ₀ ∘ ι₀ = ι` and the differential of `Φ₀` at `ι₀ x` is
`A x`. When `A` is complex linear, `Φ₀` is thus holomorphic to first order along the core.

The partial diffeomorphism is Tau Ceti's extension with a prescribed differential,
`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq`, for the embedding `ι₀` and the
map `ι`, in the form `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq'`, which does
not ask `M` to be second countable.

The statement holds for any real manifold `M` modelled on a finite-dimensional space `E`, and the
frame needs no complex linearity; the complex manifolds of the surrounding are the case of a
complex `E`, through the real manifold structure of Tau Ceti.

The chart of higher order replaces `Φ₀` by `Φ₀ ∘ G` for a map `G` of the model space that fixes
the core pointwise and has the identity as differential there. The second part of the file shows
that such a `G` is a partial diffeomorphism near the core, by the inverse function theorem
`TauCeti.isLocalDiffeomorphAt_of_fderiv_eq` at each core point and Tau Ceti's assembly
`TauCeti.exists_partialDiffeomorph_near_section_of_isLocalDiffeomorphAt` along the section
`ι₀`, whose continuous left inverse is the projection `SymplecticGeometry.modelDiscProj`; and
that composing with it changes neither the values nor the differential of `Φ₀` along the core.

## Main results

* `SymplecticGeometry.exists_partialDiffeomorph_modelDisc`: a partial diffeomorphism from the
  model space to `M`, defined near the core, that restricts to `ι` on the model disc and has the
  prescribed differential `A x` at each point `ι₀ x`.
* `SymplecticGeometry.exists_partialDiffeomorph_of_fderiv_modelDisc_eq_id`: a map of the model
  space fixing the core with identity differential there is a partial diffeomorphism near it.
* `SymplecticGeometry.exists_partialDiffeomorph_trans_modelDisc`: precomposing a partial
  diffeomorphism defined near the core with such a map keeps its source, target, values and
  differential along the core.
* `SymplecticGeometry.exists_contDiff_glue_modelDisc`: local maps of the model space that fix
  the core to first order and agree with each other to order `N + 1` near its compact subsets
  glue to one such map on the whole space, agreeing with each to the same order. This is the
  gluing along the core, which is not compact, of the proof of Proposition 5.55; it is the case
  of the core of `SymplecticGeometry.exists_contDiff_glue_of_norm_iteratedFDeriv_sub_le`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 5.55 and its proof (a chart along a totally real disc).
-/

public section

open Filter Manifold Set Topology
open scoped ContDiff

namespace SymplecticGeometry

variable {k m : ℕ}

section FirstOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- **The first-order chart along a disc.** Let `ι : ℝᵏ → M` be a smooth map that induces the
topology of `ℝᵏ`, and let `A x : ℂᵏ × ℂᵐ → T_(ι x) M` be linear isomorphisms, smooth in tangent
coordinates along the model disc `ι₀ = modelDisc k m`, with `A x ∘ dι₀ x = dι x`. Then, inside any
open neighbourhood `O` of the image of `ι`, there is a smooth partial diffeomorphism `Φ₀` from
`ℂᵏ × ℂᵐ` to `M` whose source contains the core `ι₀ (ℝᵏ)`, with `Φ₀ (ι₀ x) = ι x` and
`dΦ₀ (ι₀ x) = A x` for all `x`. -/
theorem exists_partialDiffeomorph_modelDisc {ι : EuclideanSpace ℝ (Fin k) → M}
    (hι : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ∞ ι)
    (hιi : Topology.IsInducing ι)
    {A : ∀ x, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ]
      TangentSpace 𝓘(ℝ, E) (ι x)}
    (hA : ∀ x₀, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
      𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ] E) ∞
      (inTangentCoordinates 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        𝓘(ℝ, E) (modelDisc k m) ι A x₀) x₀)
    (hAinv : ∀ x, (A x).IsInvertible)
    (hAι : ∀ x, (A x).comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
        𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelDisc k m) x) =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x)
    {O : Set M} (hO : IsOpen O) (hιO : range ι ⊆ O) :
    ∃ Φ₀ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        𝓘(ℝ, E) (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞,
      range (modelDisc k m) ⊆ Φ₀.source ∧ Φ₀.target ⊆ O ∧
        (∀ x, Φ₀ (modelDisc k m x) = ι x) ∧
        ∀ x, mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) Φ₀
          (modelDisc k m x) = A x := by
  let i₀ := TauCeti.SmoothEmbedding.ofIsSmoothEmbedding (modelDisc k m)
    (isSmoothEmbedding_modelDisc (k := k) (m := m) ∞)
  have hi₀ : ⇑i₀ = modelDisc k m := TauCeti.SmoothEmbedding.coe_ofIsSmoothEmbedding _ _
  obtain ⟨Φ₀, hsrc, -, htgt, hval, hd⟩ := i₀.exists_partialDiffeomorph_mfderiv_eq' hι hιi
    (A := A) (hi₀ ▸ hA) hAinv (hi₀ ▸ hAι) isOpen_univ (subset_univ _) hO hιO
  exact ⟨Φ₀, hi₀ ▸ hsrc, htgt, hi₀ ▸ hval, hi₀ ▸ hd⟩

end FirstOrder

section Correction

/-! ### Correcting the first-order chart near the core -/


/-- **A map that fixes the core to first order is a diffeomorphism near it.** Let
`G : ℂᵏ × ℂᵐ → ℂᵏ × ℂᵐ` be smooth on an open neighbourhood `W` of the core `ι₀ (ℝᵏ)`, where
`ι₀ = modelDisc k m`, with `G (ι₀ x) = ι₀ x` and `dG (ι₀ x) = id` for all `x`. Then, for every
open neighbourhood `O'` of the core, there is a smooth partial diffeomorphism `Ψ` with forward map
`G` whose source contains the core and lies in `W`, and whose target lies in `O'`. -/
theorem exists_partialDiffeomorph_of_fderiv_modelDisc_eq_id
    {G : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    {W : Set (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))} (hW : IsOpen W)
    (hcore : range (modelDisc k m) ⊆ W) (hG : ContDiffOn ℝ ∞ G W)
    (hfix : ∀ x, G (modelDisc k m x) = modelDisc k m x)
    (hd : ∀ x, fderiv ℝ G (modelDisc k m x) = ContinuousLinearMap.id ℝ _)
    {O' : Set (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))} (hO' : IsOpen O')
    (hcoreO' : range (modelDisc k m) ⊆ O') :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) ∞,
      ⇑Ψ = G ∧ range (modelDisc k m) ⊆ Ψ.source ∧ Ψ.source ⊆ W ∧ Ψ.target ⊆ O' := by
  have hsect := leftInverse_modelDiscProj (k := k) (m := m)
  have hπ := (modelDiscProj k m).continuous
  have hGs : G ∘ modelDisc k m = modelDisc k m := funext hfix
  obtain ⟨Ψ, hsrc, hsrcW, htgt, -, hΨ⟩ :=
    TauCeti.exists_partialDiffeomorph_near_section_of_isLocalDiffeomorphAt
      (fun x ↦ TauCeti.isLocalDiffeomorphAt_of_fderiv_eq hG hW (hcore (mem_range_self x))
        (by simp) (e := ContinuousLinearEquiv.refl ℝ _) (hd x).symm)
      hW hcore hO' (by rwa [hGs]) (modelDisc k m).continuous _ hπ hsect
      (by rw [hGs]; exact (hsect.isEmbedding hπ (modelDisc k m).continuous).isInducing)
  exact ⟨Ψ, hΨ, hsrc, hsrcW, htgt⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The corrected chart keeps the first-order data along the core.** Let `Φ₀` be a smooth
partial diffeomorphism from `ℂᵏ × ℂᵐ` to `M` whose source contains the core `ι₀ (ℝᵏ)`, where
`ι₀ = modelDisc k m`, such as the chart of `exists_partialDiffeomorph_modelDisc`, and let `G` be
as in `exists_partialDiffeomorph_of_fderiv_modelDisc_eq_id`. Then there is a smooth partial
diffeomorphism `Ψ` with forward map `G`, source in `W` and target in the source of `Φ₀`, such
that the composite `Φ₀ ∘ Ψ` has source containing the core and target in that of `Φ₀`, and
agrees with `Φ₀` at each `ι₀ x` in value and in differential. -/
theorem exists_partialDiffeomorph_trans_modelDisc
    (Φ₀ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) I
      (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞)
    (hΦ₀ : range (modelDisc k m) ⊆ Φ₀.source)
    {G : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    {W : Set (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))} (hW : IsOpen W)
    (hcore : range (modelDisc k m) ⊆ W) (hG : ContDiffOn ℝ ∞ G W)
    (hfix : ∀ x, G (modelDisc k m x) = modelDisc k m x)
    (hd : ∀ x, fderiv ℝ G (modelDisc k m x) = ContinuousLinearMap.id ℝ _) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) ∞,
      ⇑Ψ = G ∧ Ψ.source ⊆ W ∧ Ψ.target ⊆ Φ₀.source ∧
        range (modelDisc k m) ⊆ (Ψ.trans Φ₀).source ∧ (Ψ.trans Φ₀).target ⊆ Φ₀.target ∧
        (∀ x, Ψ.trans Φ₀ (modelDisc k m x) = Φ₀ (modelDisc k m x)) ∧
        ∀ x, mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) I (Ψ.trans Φ₀)
          (modelDisc k m x) =
          mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) I Φ₀
            (modelDisc k m x) := by
  obtain ⟨Ψ, hΨ, hsrc, hsrcW, htgt⟩ := exists_partialDiffeomorph_of_fderiv_modelDisc_eq_id
    hW hcore hG hfix hd Φ₀.open_source hΦ₀
  have hsrc' : range (modelDisc k m) ⊆ (Ψ.trans Φ₀).source := by
    rw [PartialDiffeomorph.trans_source]
    exact fun p hp ↦ ⟨hsrc hp, htgt (Ψ.map_source (hsrc hp))⟩
  have hval : ∀ x, Ψ.trans Φ₀ (modelDisc k m x) = Φ₀ (modelDisc k m x) := fun x ↦ by
    rw [PartialDiffeomorph.coe_trans, Function.comp_apply, hΨ, hfix]
  refine ⟨Ψ, hΨ, hsrcW, htgt, hsrc', ?_, hval, fun x ↦ ?_⟩
  · rw [PartialDiffeomorph.trans_target]
    exact inter_subset_left
  · rw [PartialDiffeomorph.mfderiv_trans Ψ Φ₀ (by simp) (hsrc' (mem_range_self x)),
      mfderiv_eq_fderiv, hΨ, hd, hfix]
    exact ContinuousLinearMap.comp_id _

/-- **Gluing local corrections along the core.** Let the open sets `U i` of `ℂᵏ × ℂᵐ` cover the
core `ι₀ (ℝᵏ)`, where `ι₀ = modelDisc k m`, and let `G i` be smooth on `U i`, fixing the points
of the core in `U i` with the identity as differential there. Let `w ≥ 0` be a continuous weight
vanishing on the core, and suppose that near every compact subset of the core inside `U i ∩ U j`
the derivatives of order `l ≤ r` of `G i - G j` are bounded by a constant times
`w ^ (N + 1 - l)`. Then there is a smooth `G` fixing the core with the identity as differential
there, such that near every compact subset of the core inside `U i` the derivatives of order
`l ≤ r` of `G - G i` have bounds of the same form. Such a `G` is what
`exists_partialDiffeomorph_trans_modelDisc` takes, with `W = univ`. -/
theorem exists_contDiff_glue_modelDisc {ι : Type*}
    {U : ι → Set (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))} (hU : ∀ i, IsOpen (U i))
    (hcore : range (modelDisc k m) ⊆ ⋃ i, U i)
    {G : ι → EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hG : ∀ i, ContDiffOn ℝ ∞ (G i) (U i))
    (hfix : ∀ i x, modelDisc k m x ∈ U i → G i (modelDisc k m x) = modelDisc k m x)
    (hd : ∀ i x, modelDisc k m x ∈ U i →
      fderiv ℝ (G i) (modelDisc k m x) = ContinuousLinearMap.id ℝ _)
    {w : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) → ℝ} (hw : Continuous w)
    (hw₀ : ∀ y, 0 ≤ w y) (hwcore : ∀ x, w (modelDisc k m x) = 0) {N r : ℕ}
    (hpair : ∀ i j K, IsCompact K → K ⊆ range (modelDisc k m) ∩ U i ∩ U j →
      ∃ C, ∀ᶠ y in 𝓝ˢ K, ∀ l ≤ r,
        ‖iteratedFDeriv ℝ l (G i - G j) y‖ ≤ C * w y ^ (N + 1 - l)) :
    ∃ G' : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →
        EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m),
      ContDiff ℝ ∞ G' ∧ (∀ x, G' (modelDisc k m x) = modelDisc k m x) ∧
        (∀ x, fderiv ℝ G' (modelDisc k m x) = ContinuousLinearMap.id ℝ _) ∧
        ∀ i K, IsCompact K → K ⊆ range (modelDisc k m) ∩ U i → ∃ C, ∀ᶠ y in 𝓝ˢ K, ∀ l ≤ r,
          ‖iteratedFDeriv ℝ l (G' - G i) y‖ ≤ C * w y ^ (N + 1 - l) := by
  obtain ⟨G', hG', hval, hbound⟩ := exists_contDiff_glue_of_norm_iteratedFDeriv_sub_le
    (leftInverse_modelDiscProj.isClosed_range (modelDiscProj k m).continuous
      (modelDisc k m).continuous) hU hcore hG
    (fun i j z ⟨⟨⟨x, hx⟩, hzi⟩, hzj⟩ ↦ by
      subst hx
      exact (hd i x hzi).trans (hd j x hzj).symm)
    hw hw₀ (by rintro _ ⟨x, rfl⟩; exact hwcore x) hpair
  have hcore' : ∀ x, ∃ i, modelDisc k m x ∈ U i := fun x ↦ mem_iUnion.1 (hcore (mem_range_self x))
  refine ⟨G', hG', fun x ↦ ?_, fun x ↦ ?_, hbound⟩
  · obtain ⟨i, hi⟩ := hcore' x
    exact ((hval i _ ⟨mem_range_self x, hi⟩).1).trans (hfix i x hi)
  · obtain ⟨i, hi⟩ := hcore' x
    exact ((hval i _ ⟨mem_range_self x, hi⟩).2).trans (hd i x hi)

end Correction

end SymplecticGeometry

end
