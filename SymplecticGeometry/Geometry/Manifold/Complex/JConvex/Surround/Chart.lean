/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Shape

import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.MFDeriv

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

## Main results

* `SymplecticGeometry.exists_partialDiffeomorph_modelDisc`: a partial diffeomorphism from the
  model space to `M`, defined near the core, that restricts to `ι` on the model disc and has the
  prescribed differential `A x` at each point `ι₀ x`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 5.55 and its proof (a chart along a totally real disc).
-/

public section

open Manifold Set
open scoped ContDiff

namespace SymplecticGeometry

variable {k m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
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

end SymplecticGeometry

end
