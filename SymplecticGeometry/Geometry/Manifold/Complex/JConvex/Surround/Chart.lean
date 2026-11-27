/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Shape

import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.Gluing
import SymplecticGeometry.Analysis.InnerProductSpace.Euclidean.ComplexExtension
import SymplecticGeometry.Analysis.InnerProductSpace.PiL2
import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.AlmostHolomorphic
import SymplecticGeometry.Geometry.Manifold.Complex.TangentCoordinates
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Section
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Chart
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import SymplecticGeometry.Analysis.Calculus.Jet.LocalInverse
import SymplecticGeometry.Analysis.Complex.Wirtinger.Basic
import SymplecticGeometry.Analysis.Complex.Wirtinger.Comp
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Chart

/-!
# The chart along a disc

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

The third part of the file reads the model space in the coordinates of one complex Euclidean
space, those of `Surround/AlmostHolomorphic.lean`. Since `ℂᵏ × ℂᵐ` carries the sup norm of the
product, it is not isometric to `EuclideanSpace ℂ (Fin k ⊕ Fin m)`; Mathlib's continuous complex
linear equivalence `EuclideanSpace.sumEquivProd` identifies the two. Imaginary parts are taken
with Tau Ceti's `TauCeti.complexEuclideanEquivRealProd`, and the real points through the inverse
of `sumEquivProd` are described by
`TauCeti.complexEuclideanEquivRealProd_sumEquivProd_symm_snd_eq_zero_iff` from
`SymplecticGeometry/Analysis/InnerProductSpace/Euclidean/ComplexExtension.lean`. Here the core is
shown to be real, and the imaginary part to have norm at most `√(t p)` for the shape coordinate
`t p = (SymplecticGeometry.shape p).2`.

The final part builds, near one point `p₀` of the core, the local map of the correction of order
`N`. When `M` is a complex manifold and the differential of `Φ₀` is complex linear along the
core, the reading `h = κ ∘ Φ₀ ∘ L⁻¹` of `Φ₀` in the chart `κ` of `M` at `Φ₀ p₀` and through
`L = EuclideanSpace.sumEquivProd.symm` has a complex-linear derivative at the core points, by
`SymplecticGeometry.fderiv_extChartAt_comp_comp_I_smul`. The Euclidean construction
`SymplecticGeometry.exists_localInverse_comp_taylorExtension` of
`Surround/AlmostHolomorphic.lean` then gives a map `G'` of `ℂ^(k ⊕ m)`, and `G = L⁻¹ ∘ G' ∘ L`
is the local map.

Two such local maps `G₁` and `G₂`, built in the charts `κ₁` and `κ₂`, agree to order `N + 1`
near every compact set of real points where both are defined, which is the pairwise hypothesis of
`SymplecticGeometry.exists_contDiff_glue_modelDisc`. Near a real point, both are read in `κ₁`:
the change of charts `κ₁ ∘ κ₂⁻¹` is holomorphic, so by
`TauCeti.eventually_norm_conjWirtingerDeriv_comp_le` the reading of `G₂` in `κ₁` still has `∂̄`
of order `N`. The difference of the two readings vanishes at the real points, so its jets of
order `N` vanish there
(`SymplecticGeometry.iteratedFDeriv_eq_zero_of_norm_conjWirtingerDeriv_le`). Since `κ₁ ∘ Φ₀` has
invertible derivative, `TauCeti.SameJetAt.of_comp_left` carries this to `G₁ - G₂`, and
`SymplecticGeometry.exists_norm_iteratedFDeriv_le_of_iteratedFDeriv_eq_zero` gives the bound.

The last part assembles these steps into the chart of order `N`. The local maps of order `N + 1`
at all points of the core glue to one map `G`, which `exists_partialDiffeomorph_trans_modelDisc`
makes a diffeomorphism near the core, and `Φ = Φ₀ ∘ G`. Near a point of the core, `G` agrees with
the local map there to order `N + 2`, so their composites with `Φ₀` read in a chart agree to the
same order (`TauCeti.SameJetAt.comp`), and
`SymplecticGeometry.exists_norm_conjWirtingerDeriv_le_of_norm_iteratedFDeriv_sub_le` carries the
bounds on `∂̄` from one to the other. The bounds are then read on the model space through
`EuclideanSpace.sumEquivProd`, and `‖y‖ ≤ √(t p)` turns them into bounds in the shape coordinate.

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
* `SymplecticGeometry.complexEuclideanEquivRealProd_sumEquivProd_symm_modelDisc_snd`: in the
  coordinates of `EuclideanSpace ℂ (Fin k ⊕ Fin m)`, the core is real.
* `SymplecticGeometry.norm_complexEuclideanEquivRealProd_sumEquivProd_symm_snd_le`: in those
  coordinates, the imaginary part of `p` has norm at most `√(t p)`.
* `SymplecticGeometry.exists_almostHolomorphic_modelDisc`: near a point of the core, a map `G`
  of the model space, fixing the real points and with differential the identity on the core,
  such that `Φ₀ ∘ G`, read in a chart of `M`, has `∂̄` of order `N` in the imaginary part.
* `SymplecticGeometry.exists_norm_iteratedFDeriv_sub_le_of_norm_conjWirtingerDeriv_le`: two such
  maps, built in two charts of `M`, agree to order `N + 1` near every compact set of real points
  in both domains.
* `SymplecticGeometry.exists_modelChart`: the chart of order `N` along the disc, a partial
  diffeomorphism with the first-order data of `exists_partialDiffeomorph_modelDisc` whose reading
  in a chart of `M` near each point of the core has `∂̄` of order `N` in `√(t p)`, and the
  derivative of `∂̄` of order `N - 1`.

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

section EuclideanCoordinates

/-! ### The core and the shape in Euclidean coordinates -/

open TauCeti

/-- In the coordinates of `EuclideanSpace ℂ (Fin k ⊕ Fin m)`, the core is real: the point that
corresponds to `ι₀ x = modelDisc k m x` has imaginary part `0`. -/
theorem complexEuclideanEquivRealProd_sumEquivProd_symm_modelDisc_snd
    (x : EuclideanSpace ℝ (Fin k)) :
    (complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm (modelDisc k m x))).2 =
      0 :=
  complexEuclideanEquivRealProd_sumEquivProd_symm_snd_eq_zero_iff.2
    ⟨fun i ↦ by simp, fun j ↦ by simp⟩

/-- In the coordinates of `EuclideanSpace ℂ (Fin k ⊕ Fin m)`, the imaginary part of the point
that corresponds to `p` has norm at most `√(t p)`, where `t p = (shape p).2`. -/
theorem norm_complexEuclideanEquivRealProd_sumEquivProd_symm_snd_le
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    ‖(complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm p)).2‖ ≤
      √(shape p).2 := by
  refine Real.le_sqrt_of_sq_le ?_
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, shape_snd, EuclideanSpace.norm_sq_eq]
  simp only [complexEuclideanEquivRealProd_apply_snd, EuclideanSpace.sumEquivProd_symm_apply_inl,
    EuclideanSpace.sumEquivProd_symm_apply_inr, Real.norm_eq_abs, sq_abs]
  refine add_le_add le_rfl (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [sq, ← Complex.normSq_eq_norm_sq]
  exact Complex.im_sq_le_normSq _

end EuclideanCoordinates

section LocalMap

/-! ### The local almost holomorphic map at a point of the core -/

open TauCeti

/-- The identification `L = EuclideanSpace.sumEquivProd.symm` of the model space with
`ℂ^(k ⊕ m)`, as a real continuous linear equivalence. -/
private theorem exists_sumEquivProd_symm_restrictScalars :
    ∃ Lr : (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℂ (Fin k ⊕ Fin m), ⇑Lr = ⇑(EuclideanSpace.sumEquivProd (𝕜 := ℂ)).symm ∧
        ⇑Lr.symm = ⇑(EuclideanSpace.sumEquivProd (𝕜 := ℂ)) :=
  ⟨(EuclideanSpace.sumEquivProd (𝕜 := ℂ)).symm.restrictScalars' ℝ,
    ContinuousLinearEquiv.coe_restrictScalars' _ _,
    (ContinuousLinearEquiv.coe_restrictScalars'_symm _ _).trans (by simp)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- At a point of the core where the differential of `Φ₀` commutes with `i`, so does the
derivative of `Φ₀` read in a chart of `M` and in the coordinates of `ℂ^(k ⊕ m)`. -/
private theorem fderiv_extChartAt_comp_sumEquivProd_I_smul
    (Φ₀ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E)
      (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞)
    (hΦ₀I : ∀ x, modelDisc k m x ∈ Φ₀.source →
      ∀ v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m),
        mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) Φ₀
        (modelDisc k m x) (Complex.I • v) =
        Complex.I • (show E from mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
          𝓘(ℝ, E) Φ₀ (modelDisc k m x) v))
    {x : EuclideanSpace ℝ (Fin k)} (hx : modelDisc k m x ∈ Φ₀.source) {x₀ : M}
    (hx₀ : Φ₀ (modelDisc k m x) ∈ (chartAt E x₀).source) (v : EuclideanSpace ℂ (Fin k ⊕ Fin m)) :
    fderiv ℝ (extChartAt 𝓘(ℝ, E) x₀ ∘ Φ₀ ∘ EuclideanSpace.sumEquivProd)
        (EuclideanSpace.sumEquivProd.symm (modelDisc k m x)) (Complex.I • v) =
      Complex.I • fderiv ℝ (extChartAt 𝓘(ℝ, E) x₀ ∘ Φ₀ ∘ EuclideanSpace.sumEquivProd)
        (EuclideanSpace.sumEquivProd.symm (modelDisc k m x)) v := by
  let Lc : EuclideanSpace ℂ (Fin k ⊕ Fin m) →L[ℂ]
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) :=
    (EuclideanSpace.sumEquivProd (𝕜 := ℂ)).toContinuousLinearMap
  have hLc : ⇑Lc = ⇑(EuclideanSpace.sumEquivProd (𝕜 := ℂ)) := ContinuousLinearEquiv.coe_coe _
  have hq : Lc (EuclideanSpace.sumEquivProd.symm (modelDisc k m x)) = modelDisc k m x := by
    rw [hLc, ContinuousLinearEquiv.apply_symm_apply]
  rw [← hLc]
  exact fderiv_extChartAt_comp_comp_I_smul Lc
    (by rw [hq]; exact Φ₀.mdifferentiableAt (by simp) hx) (by rw [hq]; exact hΦ₀I x hx)
    (by rw [hq]; exact hx₀) v

/-- **The local almost holomorphic map at a point of the core.** Let `M` be a complex manifold,
`Φ₀` a smooth partial diffeomorphism from the model space `V = ℂᵏ × ℂᵐ` to `M` whose differential
commutes with multiplication by `i` at each point of the core `ι₀ (ℝᵏ)` in its source, `p₀` a
point of the core in the source of `Φ₀`, and `1 ≤ N`. Write `L : V → ℂ^(k ⊕ m)` for the inverse
of `EuclideanSpace.sumEquivProd`. Then there are an open neighbourhood `U` of `p₀`, inside the
source of `Φ₀`, on which `Φ₀` lands in the source of the chart `κ` of `M` at `Φ₀ p₀`, a map
`G : V → V` and a constant `C` such that, with `x + i y` for the point `L z`:
* `G` is smooth on `U` and maps `U` into the source of `Φ₀` and the preimage of the source of
  `κ`;
* `G` fixes the points of `U` that are real in the coordinates of `L`;
* `G` has derivative the identity at the points of the core in `U`;
* at `L z` for `z ∈ U`, the map `e = κ ∘ Φ₀ ∘ G ∘ L⁻¹` has conjugate Wirtinger derivative of norm
  at most `C * ‖y‖ ^ N`, and the derivative of `w ↦ complexAntilinearPartL (fderiv ℝ e w)` has
  norm at most `C * ‖y‖ ^ (N - 1)`. -/
theorem exists_almostHolomorphic_modelDisc {N : ℕ} (hN : 1 ≤ N)
    (Φ₀ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E)
      (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞)
    (hΦ₀I : ∀ x, modelDisc k m x ∈ Φ₀.source →
      ∀ v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m),
        mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) Φ₀
        (modelDisc k m x) (Complex.I • v) =
        Complex.I • (show E from mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
          𝓘(ℝ, E) Φ₀ (modelDisc k m x) v))
    {p₀ : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hp₀ : p₀ ∈ range (modelDisc k m)) (hp₀Φ : p₀ ∈ Φ₀.source) :
    ∃ U, IsOpen U ∧ p₀ ∈ U ∧ U ⊆ Φ₀.source ∩ Φ₀ ⁻¹' (chartAt E (Φ₀ p₀)).source ∧
    ∃ (G : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (C : ℝ),
      ContDiffOn ℝ ∞ G U ∧ G '' U ⊆ Φ₀.source ∩ Φ₀ ⁻¹' (chartAt E (Φ₀ p₀)).source ∧
      (∀ z ∈ U, (complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2 = 0 →
        G z = z) ∧
      (∀ z ∈ U, z ∈ range (modelDisc k m) → fderiv ℝ G z = ContinuousLinearMap.id ℝ _) ∧
      (∀ z ∈ U, ‖conjWirtingerDeriv
          (fun w ↦ extChartAt 𝓘(ℝ, E) (Φ₀ p₀) (Φ₀ (G (EuclideanSpace.sumEquivProd w))))
          (EuclideanSpace.sumEquivProd.symm z)‖ ≤
        C * ‖(complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2‖ ^ N) ∧
      ∀ z ∈ U, ‖fderiv ℝ (fun w ↦ ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ
          (fun w ↦ extChartAt 𝓘(ℝ, E) (Φ₀ p₀) (Φ₀ (G (EuclideanSpace.sumEquivProd w)))) w))
          (EuclideanSpace.sumEquivProd.symm z)‖ ≤
        C * ‖(complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2‖ ^
          (N - 1) := by
  -- `Lr`: the identification `L` of the model space with `ℂ^(k ⊕ m)`, as a real equivalence.
  obtain ⟨Lr, hLr, hLrs⟩ := exists_sumEquivProd_symm_restrictScalars (k := k) (m := m)
  simp only [← hLr, ← hLrs]
  set κ := extChartAt 𝓘(ℝ, E) (Φ₀ p₀)
  set S₀ := Φ₀.source ∩ Φ₀ ⁻¹' (chartAt E (Φ₀ p₀)).source
  have hS₀ : IsOpen S₀ :=
    Φ₀.toOpenPartialHomeomorph.isOpen_inter_preimage (chartAt E (Φ₀ p₀)).open_source
  -- `h`: `Φ₀` read in the chart `κ` and in the coordinates of `L`.
  set h : EuclideanSpace ℂ (Fin k ⊕ Fin m) → E := κ ∘ Φ₀ ∘ Lr.symm
  have hh : ContDiffOn ℝ ∞ h (Lr.symm ⁻¹' S₀) :=
    (Φ₀.contMDiffOn.contDiffOn_extChartAt_comp _).comp Lr.symm.contDiff.contDiffOn fun _ hx ↦ hx
  obtain ⟨x₀, rfl⟩ := hp₀
  have hp₀S : Lr (modelDisc k m x₀) ∈ Lr.symm ⁻¹' S₀ := by
    rw [mem_preimage, Lr.symm_apply_apply]
    exact ⟨hp₀Φ, mem_chart_source E (Φ₀ (modelDisc k m x₀))⟩
  have hreal : ∀ x, (complexEuclideanEquivRealProd _ (Lr (modelDisc k m x))).2 = 0 := fun x ↦ by
    rw [hLr]
    exact complexEuclideanEquivRealProd_sumEquivProd_symm_modelDisc_snd x
  have hinv : (fderiv ℝ h (Lr (modelDisc k m x₀))).IsInvertible := by
    simpa only [Lr.symm_symm] using Φ₀.isInvertible_fderiv_extChartAt_comp_comp (by simp) Lr.symm
      hp₀Φ (mem_chart_source E _)
  obtain ⟨U', hU', hpU', hU'S, G', -, C, hG'c, hG'S, hG'fix, hG'id, hC₁, hC₂, -⟩ :=
    exists_localInverse_comp_taylorExtension hN (hS₀.preimage Lr.symm.continuous) hh hp₀S
      (hreal x₀) hinv
  -- The local map `G` is `G'` read back on the model space.
  have he : (fun w ↦ κ (Φ₀ (Lr.symm (G' (Lr (Lr.symm w)))))) = h ∘ G' :=
    funext fun w ↦ by rw [Lr.apply_symm_apply]; rfl
  refine ⟨Lr ⁻¹' U', hU'.preimage Lr.continuous, hpU', fun p hp ↦ by
      simpa using hU'S hp, fun p ↦ Lr.symm (G' (Lr p)), C, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Lr.symm.contDiff.comp_contDiffOn (hG'c.comp Lr.contDiff.contDiffOn fun _ hp ↦ hp)
  · rintro _ ⟨p, hp, rfl⟩
    exact hG'S ⟨_, hp, rfl⟩
  · intro p hp hp0
    dsimp only
    rw [hG'fix _ hp hp0, Lr.symm_apply_apply]
  · rintro p hp ⟨x, rfl⟩
    -- At a core point, the derivative of `h` commutes with `i`, since that of `Φ₀` does.
    have hx := hU'S hp
    rw [mem_preimage, Lr.symm_apply_apply] at hx
    have hhI : ∀ v, fderiv ℝ h (Lr (modelDisc k m x)) (Complex.I • v) =
        Complex.I • fderiv ℝ h (Lr (modelDisc k m x)) v := by
      simp only [h, hLr, hLrs]
      exact fderiv_extChartAt_comp_sumEquivProd_I_smul Φ₀ hΦ₀I hx.1 hx.2
    have hG' := hG'id _ hp (hreal x) hhI
    -- `G` is written as a lambda; the chain rules for `Lr` ask for a composite.
    change fderiv ℝ (Lr.symm ∘ (G' ∘ Lr)) _ = _
    rw [Lr.symm.comp_fderiv, Lr.comp_right_fderiv, hG']
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp
  · intro p hp
    dsimp only
    rw [he]
    exact hC₁ _ hp
  · intro p hp
    dsimp only
    rw [he]
    exact hC₂ _ hp

end LocalMap

section Agreement

/-! ### Two local maps agree to order `N + 1` along the real points -/

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Let `Lr` be a real continuous linear equivalence of the model space with `ℂ^(k ⊕ m)`, and let
`z₀ ∈ U` be a point where `Φ₀ ∘ G` lands in the source of the chart at `x₁`. A bound
`C * ‖y‖ ^ N` on `∂̄` of `G ∘ Lr⁻¹` read through `Φ₀` in the chart at `x₂`, at the points of
`Lr U`, gives a bound of the same order in the chart at `x₁` near `Lr z₀`: the change of charts is
holomorphic. -/
private theorem exists_eventually_norm_conjWirtingerDeriv_extChartAt_le {N : ℕ}
    (Φ₀ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E)
      (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞) {x₁ x₂ : M}
    (Lr : (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℂ (Fin k ⊕ Fin m))
    {U : Set (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))} (hU : IsOpen U)
    {G : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hG : ContDiffOn ℝ 1 G U)
    (hGS : G '' U ⊆ Φ₀.source ∩ Φ₀ ⁻¹' (chartAt E x₂).source) {C : ℝ}
    (hC : ∀ z ∈ U,
      ‖conjWirtingerDeriv (fun v ↦ extChartAt 𝓘(ℝ, E) x₂ (Φ₀ (G (Lr.symm v)))) (Lr z)‖ ≤
        C * ‖(complexEuclideanEquivRealProd _ (Lr z)).2‖ ^ N)
    {z₀ : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hz₀ : z₀ ∈ U)
    (hz₀₁ : Φ₀ (G z₀) ∈ (chartAt E x₁).source) :
    ∃ C', ∀ᶠ w in 𝓝 (Lr z₀),
      ‖conjWirtingerDeriv (fun v ↦ extChartAt 𝓘(ℝ, E) x₁ (Φ₀ (G (Lr.symm v)))) w‖ ≤
        C' * ‖(complexEuclideanEquivRealProd _ w).2‖ ^ N := by
  set κ₁ := extChartAt 𝓘(ℝ, E) x₁
  set κ₂ := extChartAt 𝓘(ℝ, E) x₂
  -- `τ`: the change of charts, holomorphic on the open set `T`.
  set τ := κ₁ ∘ κ₂.symm
  set T := κ₂.target ∩ κ₂.symm ⁻¹' κ₁.source
  have hκ (x : M) : extChartAt 𝓘(ℝ, E) x = extChartAt 𝓘(ℂ, E) x := by
    rw [← modelWithCornersSelf_restrictScalars (𝕜 := ℝ) (𝕜' := ℂ),
      ModelWithCorners.extChartAt_restrictScalars]
  have hT : IsOpen T := (continuousOn_extChartAt_symm x₂).isOpen_inter_preimage
    (isOpen_extChartAt_target x₂) (isOpen_extChartAt_source x₁)
  have hτ : ContDiffOn ℂ 1 τ T := by
    have h := contDiffOn_ext_coord_change (I := 𝓘(ℂ, E)) (n := 1) x₁ x₂
    simp only [PartialEquiv.trans_source, PartialEquiv.symm_source] at h
    simpa only [τ, T, κ₁, κ₂, hκ] using h
  -- `Y`: the map `G ∘ Lr⁻¹` read through `Φ₀` in the chart at `x₂`, `C¹` on `U' = Lr U`.
  set Y := fun v ↦ κ₂ (Φ₀ (G (Lr.symm v)))
  set U' := Lr.symm ⁻¹' U
  have hU' : IsOpen U' := hU.preimage Lr.symm.continuous
  have hz₀' : Lr z₀ ∈ U' := by rwa [mem_preimage, Lr.symm_apply_apply]
  have hY : ContDiffOn ℝ 1 Y U' :=
    ((Φ₀.contMDiffOn.contDiffOn_extChartAt_comp x₂).of_le (by simp)).comp
      (hG.comp Lr.symm.contDiff.contDiffOn fun _ hv ↦ hv) fun _ hv ↦ hGS ⟨_, hv, rfl⟩
  have hGz₀ := hGS ⟨z₀, hz₀, rfl⟩
  have hYT : Y (Lr z₀) ∈ T := by
    simp only [Y, Lr.symm_apply_apply]
    refine ⟨κ₂.map_source (by rw [extChartAt_source]; exact hGz₀.2), ?_⟩
    rw [mem_preimage, κ₂.left_inv (by rw [extChartAt_source]; exact hGz₀.2), extChartAt_source]
    exact hz₀₁
  -- On `U'`, the reading in the chart at `x₁` is `τ ∘ Y`.
  have hev (w : EuclideanSpace ℂ (Fin k ⊕ Fin m)) (hw : w ∈ U') :
      (fun v ↦ κ₁ (Φ₀ (G (Lr.symm v)))) =ᶠ[𝓝 w] τ ∘ Y := by
    filter_upwards [hU'.mem_nhds hw] with v hv
    simp only [Function.comp_apply, τ, Y]
    rw [κ₂.left_inv (by rw [extChartAt_source]; exact (hGS ⟨_, hv, rfl⟩).2)]
  have hb : ∀ᶠ w in 𝓝 (Lr z₀), ‖conjWirtingerDeriv Y w‖ ≤
      C * ‖(complexEuclideanEquivRealProd _ w).2‖ ^ N := by
    filter_upwards [hU'.mem_nhds hz₀'] with w hw
    simpa only [Lr.apply_symm_apply] using hC _ hw
  refine ⟨(‖fderiv ℂ τ (Y (Lr z₀))‖ + 1) * C, ?_⟩
  filter_upwards [eventually_norm_conjWirtingerDeriv_comp_le (hτ.contDiffAt (hT.mem_nhds hYT))
      ((hU'.eventually_mem hz₀').mono fun w hw ↦
        (hY.contDiffAt (hU'.mem_nhds hw)).differentiableAt one_ne_zero) hb,
    hU'.mem_nhds hz₀'] with w hw hwU
  rw [(hev w hwU).conjWirtingerDeriv_eq, mul_assoc]
  exact hw

/-- **Two local maps agree to order `N + 1` along the real points.** Let `Φ₀` be a smooth partial
diffeomorphism from `V = ℂᵏ × ℂᵐ` to the complex manifold `M`, and write `L : V → ℂ^(k ⊕ m)` for
the inverse of `EuclideanSpace.sumEquivProd` and `x + i y` for the point `L z`. For `i = 1, 2`, let
`G i` be `C^(N + 1)` on an open set `U i`, map `U i` into the source of `Φ₀` and, through `Φ₀`,
into the source of the chart `κ i` of `M` at a point `x i`, fix the points of `U i` that are real
in the coordinates of `L`, and be such that `κ i ∘ Φ₀ ∘ G i ∘ L⁻¹` has conjugate Wirtinger
derivative of norm at most `C i * ‖y‖ ^ N` at `L z` for `z ∈ U i`; for instance two local maps of
`exists_almostHolomorphic_modelDisc`. Then for every compact set `K ⊆ U 1 ∩ U 2` of real points,
such as a compact subset of the core, there is a constant `C` such that near `K` the derivatives
of order `j ≤ N + 1` of `G 1 - G 2` have norm at most `C * ‖y‖ ^ (N + 1 - j)`. -/
theorem exists_norm_iteratedFDeriv_sub_le_of_norm_conjWirtingerDeriv_le {N : ℕ}
    (Φ₀ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E)
      (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞) {x₁ x₂ : M}
    {U₁ U₂ : Set (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))} (hU₁ : IsOpen U₁)
    (hU₂ : IsOpen U₂)
    {G₁ G₂ : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hG₁ : ContDiffOn ℝ (N + 1) G₁ U₁) (hG₂ : ContDiffOn ℝ (N + 1) G₂ U₂)
    (hG₁S : G₁ '' U₁ ⊆ Φ₀.source ∩ Φ₀ ⁻¹' (chartAt E x₁).source)
    (hG₂S : G₂ '' U₂ ⊆ Φ₀.source ∩ Φ₀ ⁻¹' (chartAt E x₂).source)
    (hG₁fix : ∀ z ∈ U₁,
      (complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2 = 0 → G₁ z = z)
    (hG₂fix : ∀ z ∈ U₂,
      (complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2 = 0 → G₂ z = z)
    {C₁ C₂ : ℝ}
    (hC₁ : ∀ z ∈ U₁, ‖conjWirtingerDeriv
        (fun w ↦ extChartAt 𝓘(ℝ, E) x₁ (Φ₀ (G₁ (EuclideanSpace.sumEquivProd w))))
        (EuclideanSpace.sumEquivProd.symm z)‖ ≤
      C₁ * ‖(complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2‖ ^ N)
    (hC₂ : ∀ z ∈ U₂, ‖conjWirtingerDeriv
        (fun w ↦ extChartAt 𝓘(ℝ, E) x₂ (Φ₀ (G₂ (EuclideanSpace.sumEquivProd w))))
        (EuclideanSpace.sumEquivProd.symm z)‖ ≤
      C₂ * ‖(complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2‖ ^ N)
    {K : Set (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))} (hK : IsCompact K)
    (hKU : K ⊆ U₁ ∩ U₂)
    (hKre : ∀ z ∈ K, (complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2 = 0) :
    ∃ C, ∀ᶠ z in 𝓝ˢ K, ∀ j ≤ N + 1, ‖iteratedFDeriv ℝ j (G₁ - G₂) z‖ ≤
      C * ‖(complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2‖ ^
        (N + 1 - j) := by
  obtain ⟨Lr, hLr, hLrs⟩ := exists_sumEquivProd_symm_restrictScalars (k := k) (m := m)
  simp only [← hLr, ← hLrs] at hG₁fix hG₂fix hC₁ hC₂ hKre ⊢
  set e := complexEuclideanEquivRealProd (Fin k ⊕ Fin m)
  set S₁ := Φ₀.source ∩ Φ₀ ⁻¹' (chartAt E x₁).source
  have hS₁ : IsOpen S₁ :=
    Φ₀.toOpenPartialHomeomorph.isOpen_inter_preimage (chartAt E x₁).open_source
  -- `h₁`: `Φ₀` read in the chart at `x₁`.
  set h₁ := extChartAt 𝓘(ℝ, E) x₁ ∘ Φ₀
  have hh₁ : ContDiffOn ℝ ∞ h₁ S₁ := Φ₀.contMDiffOn.contDiffOn_extChartAt_comp x₁
  -- `O`: the open set near `K` where both maps land in `S₁`.
  set O := U₁ ∩ (U₂ ∩ G₂ ⁻¹' S₁)
  have hO : IsOpen O := hU₁.inter (hG₂.continuousOn.isOpen_inter_preimage hU₂ hS₁)
  have hKO : K ⊆ O := fun z hz ↦ ⟨(hKU hz).1, (hKU hz).2, by
    rw [mem_preimage, hG₂fix z (hKU hz).2 (hKre z hz), ← hG₁fix z (hKU hz).1 (hKre z hz)]
    exact hG₁S ⟨z, (hKU hz).1, rfl⟩⟩
  -- `g i`: the map `G i` read in the coordinates of `ℂ^(k ⊕ m)` on the source.
  set g₁ := G₁ ∘ Lr.symm
  set g₂ := G₂ ∘ Lr.symm
  have hg₁ : ContDiffOn ℝ (N + 1) g₁ (Lr.symm ⁻¹' U₁) :=
    hG₁.comp Lr.symm.contDiff.contDiffOn fun _ hw ↦ hw
  have hg₂ : ContDiffOn ℝ (N + 1) g₂ (Lr.symm ⁻¹' U₂) :=
    hG₂.comp Lr.symm.contDiff.contDiffOn fun _ hw ↦ hw
  have hOw : IsOpen (Lr.symm ⁻¹' O) := hO.preimage Lr.symm.continuous
  have hOU₁ : Lr.symm ⁻¹' O ⊆ Lr.symm ⁻¹' U₁ := fun _ h ↦ h.1
  have hOU₂ : Lr.symm ⁻¹' O ⊆ Lr.symm ⁻¹' U₂ := fun _ h ↦ h.2.1
  have hNle : (N : WithTop ℕ∞) ≤ N + 1 := by exact_mod_cast N.le_succ
  -- The jets of order `N` of `g₁ - g₂` vanish at the real points of `L O`.
  have hjet : ∀ w ∈ Lr.symm ⁻¹' O, (e w).2 = 0 → ∀ j ≤ N, iteratedFDeriv ℝ j (g₁ - g₂) w = 0 := by
    intro w hw hw0 j hj
    set z := Lr.symm w
    have hz₁ : g₁ w = z := hG₁fix z hw.1 (by rwa [Lr.apply_symm_apply])
    have hz₂ : g₂ w = z := hG₂fix z hw.2.1 (by rwa [Lr.apply_symm_apply])
    have hzS : z ∈ S₁ := hz₁ ▸ hG₁S ⟨z, hw.1, rfl⟩
    -- Near `w`, the reading of `g₂` in the chart at `x₁` also has `∂̄` of order `N`.
    obtain ⟨C', hC'⟩ := exists_eventually_norm_conjWirtingerDeriv_extChartAt_le Φ₀ Lr hU₂
      (hG₂.of_le (by exact_mod_cast Nat.le_add_left 1 N)) hG₂S hC₂ hw.2.1 hw.2.2.2
    rw [Lr.apply_symm_apply] at hC'
    obtain ⟨Bw, hBwsub, hBw, hwBw⟩ := mem_nhds_iff.1 (inter_mem hC' (hOw.mem_nhds hw))
    have hBwO : Bw ⊆ Lr.symm ⁻¹' O := fun _ hv ↦ (hBwsub hv).2
    -- The readings of `g₁` and `g₂` in the chart at `x₁`, and their difference `D`.
    have hd₁ : ContDiffOn ℝ (N + 1) (h₁ ∘ g₁) Bw :=
      (hh₁.of_le (by exact_mod_cast le_top)).comp (hg₁.mono fun _ hv ↦ (hBwO hv).1)
        fun _ hv ↦ hG₁S ⟨_, (hBwO hv).1, rfl⟩
    have hd₂ : ContDiffOn ℝ (N + 1) (h₁ ∘ g₂) Bw :=
      (hh₁.of_le (by exact_mod_cast le_top)).comp (hg₂.mono fun _ hv ↦ (hBwO hv).2.1)
        fun _ hv ↦ (hBwO hv).2.2
    have hD0 : ∀ j ≤ N, iteratedFDeriv ℝ j (h₁ ∘ g₁ - h₁ ∘ g₂) w = 0 := by
      refine fun j hj ↦ iteratedFDeriv_eq_zero_of_norm_conjWirtingerDeriv_le (C := C₁ + C')
        (D := h₁ ∘ g₁ - h₁ ∘ g₂) hBw ((hd₁.sub hd₂).of_le hNle) (fun v hv hv0 ↦ ?_)
        (fun v hv ↦ ?_) hwBw hw0 hj
      · have h₁' := hG₁fix _ (hBwO hv).1 (by rwa [Lr.apply_symm_apply])
        have h₂' := hG₂fix _ (hBwO hv).2.1 (by rwa [Lr.apply_symm_apply])
        simp [g₁, g₂, h₁', h₂']
      · rw [conjWirtingerDeriv_sub
          ((hd₁.contDiffAt (hBw.mem_nhds hv)).differentiableAt (by simp))
          ((hd₂.contDiffAt (hBw.mem_nhds hv)).differentiableAt (by simp)), add_mul]
        have h1 := hC₁ _ (hBwO hv).1
        rw [Lr.apply_symm_apply] at h1
        exact (norm_sub_le _ _).trans (add_le_add h1 (hBwsub hv).1)
    have hc₁ := hd₁.contDiffAt (hBw.mem_nhds hwBw)
    have hc₂ := hd₂.contDiffAt (hBw.mem_nhds hwBw)
    have hjet' : SameJetAt ℝ N w (h₁ ∘ g₁) (h₁ ∘ g₂) := sameJetAt_iff.2 fun i hi ↦ by
      have hi' : (i : WithTop ℕ∞) ≤ N + 1 := by exact_mod_cast hi.trans N.le_succ
      rw [← sub_eq_zero, ← iteratedFDeriv_sub_apply (hc₁.of_le hi') (hc₂.of_le hi')]
      exact hD0 i hi
    -- `h₁` has invertible derivative at `z`, so it cancels from the jets.
    have hinv : (fderiv ℝ h₁ z).IsInvertible :=
      Φ₀.isInvertible_fderiv_extChartAt_comp_comp (by simp) (ContinuousLinearEquiv.refl ℝ _)
        hzS.1 hzS.2
    have hgc₁ : ContDiffAt ℝ (N + 1) g₁ w :=
      hg₁.contDiffAt (mem_of_superset (hOw.mem_nhds hw) hOU₁)
    have hgc₂ : ContDiffAt ℝ (N + 1) g₂ w :=
      hg₂.contDiffAt (mem_of_superset (hOw.mem_nhds hw) hOU₂)
    have hsame : SameJetAt ℝ N w g₁ g₂ := by
      refine hjet'.of_comp_left ?_ ?_ (hgc₁.of_le hNle) (hgc₂.of_le hNle) (hz₁.trans hz₂.symm)
      · rw [hz₁]
        exact (hh₁.contDiffAt (hS₁.mem_nhds hzS)).of_le (by exact_mod_cast le_top)
      · rwa [hz₁]
    have hj' : (j : WithTop ℕ∞) ≤ N + 1 := by exact_mod_cast hj.trans N.le_succ
    rw [iteratedFDeriv_sub_apply (hgc₁.of_le hj') (hgc₂.of_le hj'), hsame.iteratedFDeriv_eq hj,
      sub_self]
  -- The bound in `ℂ^(k ⊕ m)`, and back on the model space.
  have hK' : IsCompact (Lr.symm ⁻¹' K) := Lr.symm.toHomeomorph.isCompact_preimage.2 hK
  obtain ⟨U', hU', C, hC⟩ := exists_norm_iteratedFDeriv_le_of_iteratedFDeriv_eq_zero hOw
    ((hg₁.mono hOU₁).sub (hg₂.mono hOU₂)) hK' (fun w hw ↦ hKO hw)
    (fun w hw ↦ by simpa using hKre _ hw) hjet
  have hmaps : MapsTo Lr K (Lr.symm ⁻¹' K) := fun z hz ↦ by simpa using hz
  have hGg : G₁ - G₂ = (g₁ - g₂) ∘ Lr := funext fun z ↦ by simp [g₁, g₂]
  refine ⟨max ‖(Lr : (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) →L[ℝ]
    EuclideanSpace ℂ (Fin k ⊕ Fin m))‖ 1 ^ (N + 1) * max C 0, ?_⟩
  filter_upwards [(Lr.continuous.tendsto_nhdsSet hmaps).eventually hU'] with z hz j hj
  rw [hGg, mul_assoc]
  refine (Lr.norm_iteratedFDeriv_comp_right_le _ z j).trans ?_
  gcongr
  · exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ 1) j).trans
      (pow_le_pow_right₀ (le_max_right _ _) hj)
  · exact (hC _ hz j hj).trans (by gcongr; exact le_max_left _ _)

end Agreement

section ModelChart

/-! ### The chart of order `N` along the disc -/

open TauCeti

/-- Let `G₁` and `G₂` have the same jets of order `N` at the points of an open set `B` that are
real in the coordinates of `Lr`, and let `h` be smooth on an open set containing their images.
Then near a real point `p₀ ∈ B` the derivatives of order `j ≤ N + 1` of
`h ∘ G₁ ∘ Lr⁻¹ - h ∘ G₂ ∘ Lr⁻¹` at `x + i y` have norm at most a constant times
`‖y‖ ^ (N + 1 - j)`. -/
private theorem exists_norm_iteratedFDeriv_comp_sub_comp_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {N : ℕ}
    (Lr : (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℂ (Fin k ⊕ Fin m))
    {h : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) → F}
    {S B : Set (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))} (hS : IsOpen S)
    (hh : ContDiffOn ℝ ∞ h S) (hB : IsOpen B)
    {G₁ G₂ : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hG₁ : ContDiffOn ℝ ∞ G₁ B) (hG₂ : ContDiffOn ℝ ∞ G₂ B) (hG₁S : MapsTo G₁ B S)
    (hG₂S : MapsTo G₂ B S)
    (hjet : ∀ z ∈ B, (complexEuclideanEquivRealProd _ (Lr z)).2 = 0 →
      ∀ l ≤ N, iteratedFDeriv ℝ l (G₁ - G₂) z = 0)
    {p₀ : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hp₀ : p₀ ∈ B)
    (hp₀re : (complexEuclideanEquivRealProd _ (Lr p₀)).2 = 0) :
    ∃ U ∈ 𝓝 (Lr p₀), ∃ C, ∀ w ∈ U, ∀ j ≤ N + 1,
      ‖iteratedFDeriv ℝ j (h ∘ G₁ ∘ Lr.symm - h ∘ G₂ ∘ Lr.symm) w‖ ≤
        C * ‖(complexEuclideanEquivRealProd _ w).2‖ ^ (N + 1 - j) := by
  have hc₁ : ∀ z ∈ B, ContDiffAt ℝ ∞ G₁ z := fun z hz ↦ hG₁.contDiffAt (hB.mem_nhds hz)
  have hc₂ : ∀ z ∈ B, ContDiffAt ℝ ∞ G₂ z := fun z hz ↦ hG₂.contDiffAt (hB.mem_nhds hz)
  have hch : ∀ z ∈ S, ContDiffAt ℝ ∞ h z := fun z hz ↦ hh.contDiffAt (hS.mem_nhds hz)
  have hD : h ∘ G₁ ∘ Lr.symm - h ∘ G₂ ∘ Lr.symm = (h ∘ G₁ - h ∘ G₂) ∘ Lr.symm := rfl
  have hB' : IsOpen (Lr.symm ⁻¹' B) := hB.preimage Lr.symm.continuous
  have hDc : ContDiffOn ℝ (N + 1) ((h ∘ G₁ - h ∘ G₂) ∘ Lr.symm) (Lr.symm ⁻¹' B) :=
    (((hh.comp hG₁ hG₁S).sub (hh.comp hG₂ hG₂S)).comp Lr.symm.contDiff.contDiffOn
      fun _ hw ↦ hw).of_le (by exact_mod_cast le_top)
  have h0 : ∀ w ∈ Lr.symm ⁻¹' B, (complexEuclideanEquivRealProd _ w).2 = 0 →
      ∀ j ≤ N, iteratedFDeriv ℝ j ((h ∘ G₁ - h ∘ G₂) ∘ Lr.symm) w = 0 := by
    intro w hw hw0 j hj
    set z := Lr.symm w
    have hz0 : (complexEuclideanEquivRealProd _ (Lr z)).2 = 0 := by simpa [z] using hw0
    have hsame : SameJetAt ℝ N z G₁ G₂ := sameJetAt_iff.2 fun l hl ↦ by
      have hl' : (l : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
      rw [← sub_eq_zero, ← iteratedFDeriv_sub_apply ((hc₁ z hw).of_le hl') ((hc₂ z hw).of_le hl')]
      exact hjet z hw hz0 l hl
    have hN : (N : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have hS₁ := hch _ (hG₁S hw)
    have hS₂ := hch _ (hG₂S hw)
    have hcomp : SameJetAt ℝ N z (h ∘ G₁) (h ∘ G₂) :=
      hsame.comp (SameJetAt.refl h (G₁ z)) ((hc₁ z hw).of_le hN) ((hc₂ z hw).of_le hN)
        (hS₁.of_le hN) (by rw [← hsame.apply_eq]; exact hS₁.of_le hN)
    have hj' : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    rw [ContinuousLinearEquiv.iteratedFDeriv_comp_right,
      iteratedFDeriv_sub_apply ((hS₁.comp z (hc₁ z hw)).of_le hj')
        ((hS₂.comp z (hc₂ z hw)).of_le hj'),
      hcomp.iteratedFDeriv_eq hj, sub_self]
    ext v
    simp
  obtain ⟨U, hU, C, hC⟩ := exists_norm_iteratedFDeriv_le_of_iteratedFDeriv_eq_zero hB' hDc
    (isCompact_singleton (x := Lr p₀)) (by simpa using hp₀) (by simpa using hp₀re) h0
  rw [nhdsSet_singleton] at hU
  exact ⟨U, hU, C, by rw [hD]; exact hC⟩

/-- Let `G₁` and `G₂` have the same jets of order `N + 1` at the real points of an open set `B`,
and let `h` be smooth on an open set containing their images. If the reading of `h ∘ G₁` through
`EuclideanSpace.sumEquivProd` has `∂̄` of order `N + 1` and the derivative of `∂̄` of order `N`
in the imaginary part on `B`, then so has that of `h ∘ G₂` near a real point `p₀ ∈ B`, with
another constant. -/
private theorem exists_norm_conjWirtingerDeriv_comp_le_of_iteratedFDeriv_sub_eq_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {N : ℕ} {C₁ : ℝ}
    {h : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) → F}
    {S B : Set (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))} (hS : IsOpen S)
    (hh : ContDiffOn ℝ ∞ h S) (hB : IsOpen B)
    {G₁ G₂ : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)}
    (hG₁ : ContDiffOn ℝ ∞ G₁ B) (hG₂ : ContDiffOn ℝ ∞ G₂ B) (hG₁S : MapsTo G₁ B S)
    (hG₂S : MapsTo G₂ B S)
    (hjet : ∀ z ∈ B, (complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2 = 0 →
      ∀ l ≤ N + 1, iteratedFDeriv ℝ l (G₁ - G₂) z = 0)
    {p₀ : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hp₀ : p₀ ∈ B)
    (hp₀re : (complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm p₀)).2 = 0)
    (hC₁ : ∀ z ∈ B, ‖conjWirtingerDeriv (fun w ↦ h (G₁ (EuclideanSpace.sumEquivProd w)))
          (EuclideanSpace.sumEquivProd.symm z)‖ ≤
        C₁ * ‖(complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2‖ ^ (N + 1))
    (hC₁' : ∀ z ∈ B, ‖fderiv ℝ (fun w ↦ ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ
          (fun w ↦ h (G₁ (EuclideanSpace.sumEquivProd w))) w))
          (EuclideanSpace.sumEquivProd.symm z)‖ ≤
        C₁ * ‖(complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2‖ ^ N) :
    ∃ U ∈ 𝓝 (EuclideanSpace.sumEquivProd.symm p₀), ∃ C₂, ∀ v ∈ U,
      ‖conjWirtingerDeriv (fun w ↦ h (G₂ (EuclideanSpace.sumEquivProd w))) v‖ ≤
          C₂ * ‖(complexEuclideanEquivRealProd _ v).2‖ ^ (N + 1) ∧
        ‖fderiv ℝ (fun w ↦ ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ
          (fun w ↦ h (G₂ (EuclideanSpace.sumEquivProd w))) w)) v‖ ≤
          C₂ * ‖(complexEuclideanEquivRealProd _ v).2‖ ^ N := by
  obtain ⟨Lr, hLr, hLrs⟩ := exists_sumEquivProd_symm_restrictScalars (k := k) (m := m)
  simp only [← hLr, ← hLrs] at hjet hp₀re hC₁ hC₁' ⊢
  obtain ⟨Ub, hUb, Cb, hCb⟩ :=
    exists_norm_iteratedFDeriv_comp_sub_comp_le Lr hS hh hB hG₁ hG₂ hG₁S hG₂S hjet hp₀ hp₀re
  set UE := interior Ub ∩ Lr.symm ⁻¹' B
  have hUE : IsOpen UE := isOpen_interior.inter (hB.preimage Lr.symm.continuous)
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by simp
  have he₁ : ContDiffOn ℝ 2 (fun w ↦ h (G₁ (Lr.symm w))) UE :=
    ((hh.comp hG₁ hG₁S).comp Lr.symm.contDiff.contDiffOn fun _ (hv : _ ∈ UE) ↦ hv.2).of_le h2
  have he₂ : ContDiffOn ℝ 2 (fun w ↦ h (G₂ (Lr.symm w))) UE :=
    ((hh.comp hG₂ hG₂S).comp Lr.symm.contDiff.contDiffOn fun _ (hv : _ ∈ UE) ↦ hv.2).of_le h2
  obtain ⟨C₂, hC₂⟩ := exists_norm_conjWirtingerDeriv_le_of_norm_iteratedFDeriv_sub_le
    (N := N + 1) hUE he₁ he₂
    (fun v hv j hj ↦ hCb v (interior_subset hv.1) j (by simp at hj; omega))
    (fun v hv ↦ by simpa only [Lr.apply_symm_apply] using hC₁ _ hv.2)
    (fun v hv ↦ by simpa only [Lr.apply_symm_apply, Nat.add_sub_cancel] using hC₁' _ hv.2)
  refine ⟨UE, hUE.mem_nhds ⟨mem_interior_iff_mem_nhds.2 hUb, by simpa using hp₀⟩, C₂,
    fun v hv ↦ ?_⟩
  simpa only [Nat.add_sub_cancel] using hC₂ v hv

/-- Let `L = EuclideanSpace.sumEquivProd.symm`, and let `a` be the norm of the imaginary part of
`L p`. Bounds `C * a ^ (N + 1)` on `∂̄ F` and `C * a ^ N` on its derivative at `L p`, where
`a ≤ 1`, give bounds of order `N` and `N - 1` in `√(t p)` on `∂̄ (F ∘ L)` and on its derivative
at `p`, with a constant that does not depend on `F` or `p`. -/
private theorem exists_norm_conjWirtingerDeriv_comp_sumEquivProd_symm_le {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] (N : ℕ) (C : ℝ) :
    ∃ C', ∀ (F : EuclideanSpace ℂ (Fin k ⊕ Fin m) → W)
      (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)),
      ‖(complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm p)).2‖ ≤ 1 →
      ‖conjWirtingerDeriv F (EuclideanSpace.sumEquivProd.symm p)‖ ≤
        C * ‖(complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm p)).2‖ ^ (N + 1) →
      ‖fderiv ℝ (fun w ↦ ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ F w))
          (EuclideanSpace.sumEquivProd.symm p)‖ ≤
        C * ‖(complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm p)).2‖ ^ N →
      ‖conjWirtingerDeriv (F ∘ EuclideanSpace.sumEquivProd.symm) p‖ ≤ C' * √(shape p).2 ^ N ∧
        ‖fderiv ℝ (conjWirtingerDeriv (F ∘ EuclideanSpace.sumEquivProd.symm)) p‖ ≤
          C' * √(shape p).2 ^ (N - 1) := by
  set L := (EuclideanSpace.sumEquivProd (𝕜 := ℂ) (ι := Fin k) (κ := Fin m)).symm
  set nL := ‖(L : (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) →L[ℂ]
    EuclideanSpace ℂ (Fin k ⊕ Fin m))‖
  refine ⟨max C 0 * (nL + nL ^ 2), fun F p ha1 h₁ h₂ ↦ ?_⟩
  set a := ‖(complexEuclideanEquivRealProd _ (L p)).2‖
  have ha0 : 0 ≤ a := norm_nonneg _
  have hat : a ≤ √(shape p).2 := norm_complexEuclideanEquivRealProd_sumEquivProd_symm_snd_le p
  have hLn : 0 ≤ nL := norm_nonneg _
  have hC : C ≤ max C 0 := le_max_left _ _
  constructor
  · rw [conjWirtingerDeriv_comp_continuousLinearEquiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc _ ≤ max C 0 * a ^ (N + 1) * nL := by
          gcongr
          exact h₁.trans (by gcongr)
      _ ≤ max C 0 * √(shape p).2 ^ N * (nL + nL ^ 2) := by
          gcongr
          · exact (pow_le_pow_of_le_one ha0 ha1 (Nat.le_succ N)).trans (by gcongr)
          · exact le_add_of_nonneg_right (by positivity)
      _ = _ := by ring
  · rw [← norm_fderiv_complexAntilinearPartL_fderiv]
    refine (norm_fderiv_complexAntilinearPartL_fderiv_comp_continuousLinearEquiv_le L _ p).trans ?_
    calc _ ≤ nL ^ 2 * (max C 0 * a ^ N) := by
          gcongr
          exact h₂.trans (by gcongr)
      _ ≤ (nL + nL ^ 2) * (max C 0 * √(shape p).2 ^ (N - 1)) := by
          gcongr
          · exact le_add_of_nonneg_left hLn
          · exact (pow_le_pow_of_le_one ha0 ha1 (Nat.sub_le N 1)).trans (by gcongr)
      _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- **The chart of order `N` along a disc.** Let `M` be a complex manifold, `ι : ℝᵏ → M` a smooth
map that induces the topology of `ℝᵏ`, and `A x : ℂᵏ × ℂᵐ → T_(ι x) M` complex-linear
isomorphisms, smooth in tangent coordinates along the model disc `ι₀ = modelDisc k m`, with
`A x ∘ dι₀ x = dι x`. Then for every open neighbourhood `O` of the image of `ι` and every `N`
there is a smooth partial diffeomorphism `Φ` from `ℂᵏ × ℂᵐ` to `M` whose source contains the core
`ι₀ (ℝᵏ)`, with target in `O`, `Φ (ι₀ x) = ι x` and `dΦ (ι₀ x) = A x` for all `x`, which is
holomorphic to order `N` along the core: every point `p₀` of the core has a neighbourhood `U` in
the source of `Φ`, mapped by `Φ` into the source of the chart of `M` at `Φ p₀`, and a constant `C`
such that the reading `e` of `Φ` in that chart satisfies, at every `p ∈ U`,
`‖∂̄ e p‖ ≤ C * √(t p) ^ N`, and the derivative of `∂̄ e` at `p` has norm at most
`C * √(t p) ^ (N - 1)`, where `t p = (shape p).2`. -/
theorem exists_modelChart {ι : EuclideanSpace ℝ (Fin k) → M}
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
    (hAI : ∀ x v, A x (Complex.I • v) = Complex.I • (show E from A x v))
    {O : Set M} (hO : IsOpen O) (hιO : range ι ⊆ O) (N : ℕ) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
        𝓘(ℝ, E) (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) M ∞,
      range (modelDisc k m) ⊆ Φ.source ∧ Φ.target ⊆ O ∧
        (∀ x, Φ (modelDisc k m x) = ι x) ∧
        (∀ x, mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) Φ
          (modelDisc k m x) = A x) ∧
        ∀ p₀ ∈ range (modelDisc k m), ∃ U ∈ 𝓝 p₀,
          U ⊆ Φ.source ∧ U ⊆ Φ ⁻¹' (chartAt E (Φ p₀)).source ∧ ∃ C, ∀ p ∈ U,
            ‖conjWirtingerDeriv (writtenInExtChartAt
              𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) p₀ Φ) p‖ ≤
              C * √(shape p).2 ^ N ∧
            ‖fderiv ℝ (conjWirtingerDeriv (writtenInExtChartAt
              𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) p₀ Φ)) p‖ ≤
              C * √(shape p).2 ^ (N - 1) := by
  -- Step 1: the first-order chart `Φ₀`.
  obtain ⟨Φ₀, hsrc, htgt, hval, hd⟩ :=
    exists_partialDiffeomorph_modelDisc hι hιi hA hAinv hAι hO hιO
  have hΦ₀I : ∀ x, modelDisc k m x ∈ Φ₀.source →
      ∀ v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m),
        mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) 𝓘(ℝ, E) Φ₀
        (modelDisc k m x) (Complex.I • v) =
        Complex.I • (show E from mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
          𝓘(ℝ, E) Φ₀ (modelDisc k m x) v) := fun x _ v ↦ by
    rw [hd x]
    exact hAI x v
  -- Step 2: the local maps at the points of the core, of order `N + 1`.
  choose U hUo hpU hUS G C hGc hGS hGfix hGid hC₁ hC₂ using
    fun x : EuclideanSpace ℝ (Fin k) ↦ exists_almostHolomorphic_modelDisc (N := N + 1)
      (by omega) Φ₀ hΦ₀I (mem_range_self x) (hsrc (mem_range_self x))
  set w : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) → ℝ := fun y ↦
    ‖(complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm y)).2‖
  have hw : Continuous w := (continuous_snd.comp ((complexEuclideanEquivRealProd _).continuous.comp
    EuclideanSpace.sumEquivProd.symm.continuous)).norm
  have hreal := complexEuclideanEquivRealProd_sumEquivProd_symm_modelDisc_snd (k := k) (m := m)
  -- Steps 3 and 4: the local maps agree to order `N + 2`, and glue to `G'`.
  obtain ⟨G', hG', hG'fix, hG'd, hG'b⟩ := exists_contDiff_glue_modelDisc (U := U) hUo
    (fun _ ⟨x, hx⟩ ↦ mem_iUnion.2 ⟨x, hx ▸ hpU x⟩) hGc
    (fun i x hx ↦ hGfix i _ hx (hreal x)) (fun i x hx ↦ hGid i _ hx (mem_range_self x))
    hw (fun _ ↦ norm_nonneg _) (fun x ↦ by simp only [w, hreal x, norm_zero]) (N := N + 1)
    (r := N + 1 + 1)
    (fun i j K hK hKU ↦ exists_norm_iteratedFDeriv_sub_le_of_norm_conjWirtingerDeriv_le Φ₀
      (hUo i) (hUo j) ((hGc i).of_le (by exact_mod_cast le_top))
      ((hGc j).of_le (by exact_mod_cast le_top)) (hGS i) (hGS j) (hGfix i) (hGfix j) (hC₁ i)
      (hC₁ j) hK (fun z hz ↦ ⟨(hKU hz).1.2, (hKU hz).2⟩)
      (fun z hz ↦ by obtain ⟨x, rfl⟩ := (hKU hz).1.1; exact hreal x))
  -- Step 5: `G'` is a diffeomorphism near the core, and `Φ = Φ₀ ∘ G'`.
  obtain ⟨Ψ, hΨ, -, -, hsrc', htgt', hval', hd'⟩ := exists_partialDiffeomorph_trans_modelDisc Φ₀
    hsrc isOpen_univ (subset_univ _) hG'.contDiffOn hG'fix hG'd
  refine ⟨Ψ.trans Φ₀, hsrc', htgt'.trans htgt, fun x ↦ (hval' x).trans (hval x),
    fun x ↦ (hd' x).trans (hd x), ?_⟩
  -- Step 6: the bounds near `p₀ = ι₀ x₀`.
  rintro _ ⟨x₀, rfl⟩
  set p₀ := modelDisc k m x₀
  set Φ := Ψ.trans Φ₀
  have hΦ : ⇑Φ = Φ₀ ∘ G' := by rw [PartialDiffeomorph.coe_trans, hΨ]
  have hΦp₀ : Φ p₀ = Φ₀ p₀ := hval' x₀
  set κ := extChartAt 𝓘(ℝ, E) (Φ₀ p₀)
  set S₀ := Φ₀.source ∩ Φ₀ ⁻¹' (chartAt E (Φ₀ p₀)).source
  have hS₀ : IsOpen S₀ :=
    Φ₀.toOpenPartialHomeomorph.isOpen_inter_preimage (chartAt E (Φ₀ p₀)).open_source
  have hh : ContDiffOn ℝ ∞ (fun y ↦ κ (Φ₀ y)) S₀ := Φ₀.contMDiffOn.contDiffOn_extChartAt_comp _
  -- Near `p₀`, `G'` agrees with the local map `G x₀` to order `N + 2`.
  obtain ⟨Cg, hCg⟩ := hG'b x₀ {p₀} isCompact_singleton
    (singleton_subset_iff.2 ⟨mem_range_self _, hpU x₀⟩)
  rw [nhdsSet_singleton] at hCg
  obtain ⟨B₀, hB₀sub, hB₀o, hpB₀⟩ := mem_nhds_iff.1 hCg
  set B := B₀ ∩ U x₀ ∩ G' ⁻¹' S₀
  have hB : IsOpen B := (hB₀o.inter (hUo x₀)).inter (hS₀.preimage hG'.continuous)
  have hp₀B : p₀ ∈ B := ⟨⟨hpB₀, hpU x₀⟩, by rw [mem_preimage, hG'fix]; exact hUS x₀ (hpU x₀)⟩
  have hjet : ∀ z ∈ B,
      (complexEuclideanEquivRealProd _ (EuclideanSpace.sumEquivProd.symm z)).2 = 0 →
      ∀ l ≤ N + 1, iteratedFDeriv ℝ l (G x₀ - G') z = 0 := by
    intro z hz hz0 l hl
    have hb := hB₀sub hz.1.1 l (by omega)
    simp only [w, hz0, norm_zero, zero_pow (show N + 1 + 1 - l ≠ 0 by omega), mul_zero,
      norm_le_zero_iff] at hb
    rw [← neg_sub, iteratedFDeriv_neg, Pi.neg_apply, hb, neg_zero]
  -- The bounds on `∂̄` of the reading of `Φ₀ ∘ G'` in the coordinates of `ℂ^(k ⊕ m)`.
  obtain ⟨UE, hUE, C₂, hC₂'⟩ :=
    exists_norm_conjWirtingerDeriv_comp_le_of_iteratedFDeriv_sub_eq_zero hS₀ hh hB
      ((hGc x₀).mono fun _ hz ↦ hz.1.2) hG'.contDiffOn (fun z hz ↦ hGS x₀ ⟨z, hz.1.2, rfl⟩)
      (fun _ hz ↦ hz.2) hjet hp₀B (hreal x₀) (fun z hz ↦ hC₁ x₀ z hz.1.2)
      (fun z hz ↦ by simpa only [Nat.add_sub_cancel] using hC₂ x₀ z hz.1.2)
  -- Back on the model space, through the complex-linear `sumEquivProd.symm`.
  obtain ⟨C, hC⟩ := exists_norm_conjWirtingerDeriv_comp_sumEquivProd_symm_le (W := E) N C₂
  have he : writtenInExtChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      𝓘(ℝ, E) p₀ Φ = (fun v ↦ κ (Φ₀ (G' (EuclideanSpace.sumEquivProd v)))) ∘
        EuclideanSpace.sumEquivProd.symm := by
    rw [writtenInExtChartAt_model_space_left, hΦp₀, hΦ]
    funext p
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply, κ]
  refine ⟨EuclideanSpace.sumEquivProd.symm ⁻¹' interior UE ∩ {y | w y < 1} ∩
      (Φ.source ∩ Φ ⁻¹' (chartAt E (Φ p₀)).source), ?_, fun _ hp ↦ hp.2.1, fun _ hp ↦ hp.2.2, C,
    fun p hp ↦ ?_⟩
  · refine (((isOpen_interior.preimage EuclideanSpace.sumEquivProd.symm.continuous).inter
      (isOpen_lt hw continuous_const)).inter
      (Φ.toOpenPartialHomeomorph.isOpen_inter_preimage (chartAt E _).open_source)).mem_nhds
      ⟨⟨mem_interior_iff_mem_nhds.2 hUE, ?_⟩, hsrc' (mem_range_self x₀), mem_chart_source E _⟩
    simp only [mem_ofPred_eq, w]
    exact (norm_eq_zero.2 (hreal x₀)).trans_lt zero_lt_one
  have hp1 : w p < 1 := hp.1.2
  have hb := hC₂' _ (interior_subset hp.1.1)
  rw [he]
  exact hC _ p hp1.le hb.1 hb.2

end ModelChart

end SymplecticGeometry

end
