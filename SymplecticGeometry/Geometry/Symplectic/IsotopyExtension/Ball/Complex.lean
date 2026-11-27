/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# Symplectic balls read in complex coordinates

Let `M` be a manifold modelled on `Fin m → ℂ` and `ψ : StdSpace (Fin m) → M` a symplectic
embedding of the closed ball of radius `r`. Precomposing the partial diffeomorphism
`IsSymplecticBallEmbedding.toPartialDiffeomorph` with Tau Ceti's linear isometry
`complexToRealEuclidean (Fin m) : (Fin m → ℂ) ≃L[ℝ] StdSpace (Fin m)` reads `ψ` on `Fin m → ℂ`.

## Main definitions

* `SymplecticGeometry.IsSymplecticBallEmbedding.complexPartialDiffeomorph hψ`: the map
  `ψ ∘ complexToRealEuclidean (Fin m)` as a partial diffeomorphism from the preimage in
  `Fin m → ℂ` of the open ball of radius `r` onto the image under `ψ` of that ball.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1.
-/

public section

noncomputable section

open Set Metric
open scoped ContDiff Manifold

namespace SymplecticGeometry

namespace IsSymplecticBallEmbedding

open TauCeti

variable {m : ℕ} {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin m → ℂ) H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
  {ψ : StdSpace (Fin m) → M} {r : ℝ}

/-- A symplectic embedding `ψ` of `B(r)` read on `Fin m → ℂ` through `complexToRealEuclidean`:
the map `ψ ∘ complexToRealEuclidean (Fin m)` as a smooth partial diffeomorphism from the preimage
of the open ball of radius `r` onto the image under `ψ` of that ball. -/
def complexPartialDiffeomorph (hψ : IsSymplecticBallEmbedding σ r ψ) :
    PartialDiffeomorph 𝓘(ℝ, Fin m → ℂ) I (Fin m → ℂ) M ∞ :=
  (complexToRealEuclidean (Fin m)).toPartialDiffeomorph.trans
    (hψ.toPartialDiffeomorph (complexToRealEuclidean (Fin m)).toLinearEquiv.finrank_eq.symm)

theorem complexPartialDiffeomorph_def (hψ : IsSymplecticBallEmbedding σ r ψ) :
    hψ.complexPartialDiffeomorph = (complexToRealEuclidean (Fin m)).toPartialDiffeomorph.trans
      (hψ.toPartialDiffeomorph (complexToRealEuclidean (Fin m)).toLinearEquiv.finrank_eq.symm) :=
  (rfl)

@[simp]
theorem coe_complexPartialDiffeomorph (hψ : IsSymplecticBallEmbedding σ r ψ) :
    ⇑hψ.complexPartialDiffeomorph = ψ ∘ complexToRealEuclidean (Fin m) := by
  simp [complexPartialDiffeomorph]

/-- The source of `hψ.complexPartialDiffeomorph` is the preimage of the open ball of radius `r`. -/
@[simp]
theorem complexPartialDiffeomorph_source (hψ : IsSymplecticBallEmbedding σ r ψ) :
    hψ.complexPartialDiffeomorph.source = complexToRealEuclidean (Fin m) ⁻¹' ball 0 r := by
  simp [complexPartialDiffeomorph]

theorem mem_complexPartialDiffeomorph_source_iff (hψ : IsSymplecticBallEmbedding σ r ψ)
    {w : Fin m → ℂ} :
    w ∈ hψ.complexPartialDiffeomorph.source ↔ ‖complexToRealEuclidean (Fin m) w‖ < r := by
  simp

/-- The target of `hψ.complexPartialDiffeomorph` is the image under `ψ` of the open ball of
radius `r`. -/
@[simp]
theorem complexPartialDiffeomorph_target (hψ : IsSymplecticBallEmbedding σ r ψ) :
    hψ.complexPartialDiffeomorph.target = ψ '' ball 0 r := by
  simp [complexPartialDiffeomorph]

end IsSymplecticBallEmbedding

end SymplecticGeometry

end
