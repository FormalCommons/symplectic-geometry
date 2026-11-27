/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Ball.Basic
public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
import TauCeti.Geometry.Symplectic.Manifold.NeighborhoodGerm

/-!
# Symplectic balls read in complex coordinates

Let `M` be a manifold modelled on `Fin m → ℂ` and `ψ : StdSpace (Fin m) → M` a symplectic
embedding of the closed ball of radius `r`. Precomposing the partial diffeomorphism
`IsSymplecticBallEmbedding.toPartialDiffeomorph` with Tau Ceti's real continuous linear
equivalence `complexToRealEuclidean (Fin m) : (Fin m → ℂ) ≃L[ℝ] StdSpace (Fin m)` reads `ψ` on
`Fin m → ℂ`. This equivalence is not an isometry for the sup norm of `Fin m → ℂ` when `m ≥ 2`,
so the source of the chart is the preimage of a Euclidean ball, not a sup-norm ball.

## Main definitions

* `SymplecticGeometry.IsSymplecticBallEmbedding.complexPartialDiffeomorph hψ`: the map
  `ψ ∘ complexToRealEuclidean (Fin m)` as a partial diffeomorphism from the preimage in
  `Fin m → ℂ` of the open ball of radius `r` onto the image under `ψ` of that ball.

## Main results

* `SymplecticGeometry.isPseudoholomorphic_complexToRealEuclidean`: `complexToRealEuclidean ι` is
  pseudoholomorphic from the complex structure of `ι → ℂ` to the constant structure `J₀`.
* `SymplecticGeometry.IsSymplecticBallEmbedding.isSymplecticMapOn_complexPartialDiffeomorph`:
  on its source, `hψ.complexPartialDiffeomorph` is a symplectic map from the constant form of
  `stdComplexPiSymplecticForm (Fin m)` to `σ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1.
-/

public section

noncomputable section

open Set Metric
open scoped ContDiff Manifold

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothAlmostComplexStructure in
/-- `complexToRealEuclidean ι : (ι → ℂ) → StdSpace ι` is pseudoholomorphic from the complex
structure of `ι → ℂ` (multiplication by `I`) to the constant structure `J₀` of `StdSpace ι`. -/
theorem isPseudoholomorphic_complexToRealEuclidean (ι : Type*) [Fintype ι] :
    IsPseudoholomorphic (ofComplexManifold (ι → ℂ) (ι → ℂ))
      (stdComplexStructure ι).constSmooth (complexToRealEuclidean ι) :=
  isPseudoholomorphic_iff.2 fun _ ↦
    isPseudoholomorphicAt_of_hasMFDerivAt (complexToRealEuclidean ι).hasMFDerivAt fun v ↦
      (congrArg (complexToRealEuclidean ι) (ofComplexManifold_apply (E := ι → ℂ) _ v)).trans
        ((stdComplexStructure_complexToRealEuclidean v).symm.trans
          (AlmostComplexStructure.constSmooth_apply _ _ _).symm)

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

/-- On its source, `hψ.complexPartialDiffeomorph` is a symplectic map from the constant form of
`stdComplexPiSymplecticForm (Fin m)` on `Fin m → ℂ` to `σ`. -/
theorem isSymplecticMapOn_complexPartialDiffeomorph (hψ : IsSymplecticBallEmbedding σ r ψ) :
    (stdComplexPiSymplecticForm (Fin m)).constSmooth.IsSymplecticMapOn σ
      hψ.complexPartialDiffeomorph hψ.complexPartialDiffeomorph.source := by
  rw [complexPartialDiffeomorph_def]
  refine PartialDiffeomorph.isSymplecticMapOn_trans (σ := (stdForm (Fin m)).constSmooth)
    _ _ ?_ ?_ (by simp)
  · simpa using (SymplecticForm.isSymplectomorphism_constSmooth_toDiffeomorph_iff.2
      (isSymplectomorphism_complexToRealEuclidean (Fin m))).isSymplecticMap
  · rw [hψ.coe_toPartialDiffeomorph, hψ.toPartialDiffeomorph_source]
    exact hψ.isSymplecticMapOn

end IsSymplecticBallEmbedding

end SymplecticGeometry

end
