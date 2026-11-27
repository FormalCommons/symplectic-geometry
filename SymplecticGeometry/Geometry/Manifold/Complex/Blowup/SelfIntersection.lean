/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.AlmostComplex
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Tautological
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.SelfIntersection
import SymplecticGeometry.Geometry.Manifold.Projectivization.HyperplaneClass
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace
import SymplecticGeometry.Topology.VectorBundle.Complex.Structure
import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# The self-intersection number of the exceptional divisor

The exceptional divisor of the model blowup `BlowupModel 1` of `ℂ²` at the origin is the zero
section `zeroSectionRealEmbedding 1` of the tautological line over `ℙ ℂ (Fin 2 → ℂ) = ℂℙ¹`. This
file shows that its self-intersection number, for the almost complex structure of the complex
surface `BlowupModel 1` and the complex orientation of `ℂℙ¹`, is `-1`. It then transfers this
to the exceptional divisor of the almost complex blowup `Blowup c` of an almost complex
four-manifold at a point, and so to the blowup of a complex surface.

## Main results

* `SymplecticGeometry.BlowupModel.selfIntersectionNumber_zeroSection`: the self-intersection
  number `TauCeti.SmoothEmbedding.selfIntersectionNumber` of the zero section of `BlowupModel 1`,
  re-modelled on `𝓡 2` along any diffeomorphism `Φ` of models (`SymplecticGeometry.Remodel`), is
  `-1`.
* `SymplecticGeometry.Blowup.selfIntersectionNumber_exceptionalDivisor_almostComplexStructure`:
  the same for the exceptional divisor `divisorRealEmbedding c` of the blowup of an almost complex
  four-manifold `(M, J)`, for the almost complex blowup `Blowup.almostComplexStructure c J hJ`.
* `SymplecticGeometry.Blowup.selfIntersectionNumber_exceptionalDivisor`: the same for the
  blowup of a complex surface, for the complex structure of `Blowup c`.

## Proof

By `TauCeti.SmoothEmbedding.selfIntersectionNumber_remodel_complexCurveOrientation` the number is
the Euler class of the complex normal bundle of the zero section, evaluated on the fundamental
class of `ℂℙ¹` for its complex orientation. The isomorphisms
`BlowupModel.normalSpaceZeroSectionRealEquiv` carry the complex structure of the normal bundle to
multiplication by `Complex.I`, so they are complex-linear isomorphisms onto the tautological line
(`TauCeti.Bundle.ContinuousComplexStructure.fiberEquivOfCommuteI`), continuous on total spaces;
by Tau Ceti's `TauCeti.complexEulerClass_eq_of_fiberwise` the two Euler
classes agree. The Euler class of the tautological line is minus the hyperplane class
(`Projectivization.hyperplaneClass_def`), which takes the value `1` on `[ℂℙ¹]`
(`Projectivization.complexManifoldEvalFundamentalClass_hyperplaneClass`).

For the almost complex blowup, the map `Blowup.lift c` is pseudoholomorphic along the exceptional
divisor (`Blowup.isPseudoholomorphicAt_lift_divisorRealEmbedding`), with invertible differential
there (`Blowup.isInvertible_mfderiv_lift_divisorRealEmbedding`), and sends the divisor onto the
zero section of the model (`Blowup.lift_comp_divisorRealEmbedding`). So
`TauCeti.SmoothEmbedding.selfIntersectionNumber_eq_of_comp` gives the same number as for the model.
For a complex surface, the almost complex blowup is the complex structure of `Blowup c`
(`Blowup.almostComplexStructure_eq_ofComplexManifold`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  Lemma 7.1.1.
-/

public section

open Bundle Module TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization TauCeti.ComplexManifold

namespace SymplecticGeometry

namespace BlowupModel

attribute [local instance] Complex.finrank_real_complex_eq_two_mul_finrank_fact

/-- **The exceptional divisor of the blowup of `ℂ²` at the origin has self-intersection `-1`.**
Let `Φ` be any diffeomorphism from the model `𝓘(ℝ, Fin 1 → ℂ)` of `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` to `𝓡 2`.
Re-model `ℂℙ¹` on `𝓡 2` along `Φ`, give it its complex orientation (`complexCurveOrientation`)
carried along, and embed it in `BlowupModel 1` as the zero section, the exceptional divisor
`Z`. For the almost complex structure of the complex surface `BlowupModel 1`, which preserves the
tangent planes of `Z`, the self-intersection number of `Z` is `-1`.

Milestone: *Tautological line bundle and the exceptional divisor*. -/
theorem selfIntersectionNumber_zeroSection
    (Φ : (Fin 1 → ℂ) ≃ₘ^∞⟮𝓘(ℝ, Fin 1 → ℂ), 𝓡 2⟯ EuclideanSpace ℝ (Fin 2)) :
    ((zeroSectionRealEmbedding 1).compDiffeomorphOfBoundaryless
        (remodelDiffeomorph Φ (ℙ ℂ (Fin 2 → ℂ))).symm (by simp)).selfIntersectionNumber
        (by simp [Module.finrank_pi_fintype])
        (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (BlowupModel 1))
        ((zeroSectionRealEmbedding 1).mapsTo_tangentRange_compDiffeomorphOfBoundaryless _
          (by simp) (by simp) (A := (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ)
            (BlowupModel 1) ·))
          mapsTo_ofComplexManifold_tangentRange_zeroSectionRealEmbedding)
        ((complexCurveOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) (finrank_fin_fun ℂ)).map
          (remodelDiffeomorph Φ (ℙ ℂ (Fin 2 → ℂ))) (by simp)
          (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])) = -1 := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hdim := Complex.finrank_real_eq_finrank_sub_of_finrank_eq_four_of_finrank_eq_two
    (by simp [Module.finrank_pi_fintype] : finrank ℝ (Fin 2 → ℂ) = 4)
    (finrank_real_of_finrank_complex_eq_add_one (finrank_fin_fun ℂ (n := 1)))
  let := (zeroSectionRealEmbedding 1).normalSpaceFiberBundle hn hdim
  let := (zeroSectionRealEmbedding 1).normalSpaceVectorBundle hn hdim
  set J := (zeroSectionRealEmbedding 1).normalComplexStructure hn
    (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (BlowupModel 1)) hdim
    mapsTo_ofComplexManifold_tangentRange_zeroSectionRealEmbedding with hJdef
  -- The normal isomorphisms carry the complex structure `J` of the normal bundle to `I`.
  have he (ℓ : ℙ ℂ (Fin 2 → ℂ)) (w) :
      normalSpaceZeroSectionRealEquiv 1 hn ℓ (J ℓ w) =
        Complex.I • normalSpaceZeroSectionRealEquiv 1 hn ℓ w := by
    have h := normalSpaceZeroSectionRealEquiv_contMDiffNormalComplexStructure hdim ℓ w
    rw [SmoothEmbedding.contMDiffNormalComplexStructure_apply] at h
    rw [hJdef, SmoothEmbedding.normalComplexStructure_apply, h]
  rw [SmoothEmbedding.selfIntersectionNumber_remodel_complexCurveOrientation (finrank_fin_fun ℂ)
      (hJ := mapsTo_ofComplexManifold_tangentRange_zeroSectionRealEmbedding),
    complexEulerClass_eq_of_fiberwise (finrank_self ℂ) (finrank_self ℂ)
      (J.continuous_fiberEquivOfCommuteI _ he ℂ (continuous_normalSpaceZeroSectionRealEquiv hn)),
    ← neg_neg (((TopCat.of _).uliftIntegralCohomologyIso _).hom _),
    ← Projectivization.hyperplaneClass_def, map_neg,
    Projectivization.complexManifoldEvalFundamentalClass_hyperplaneClass]

end BlowupModel

namespace Blowup

section AlmostComplex

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin 2 → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin 2 → ℂ) ∞ M] {p₀ : M} (c : BlowupChart (n := 1) M p₀)
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin 2 → ℂ) ∞ M)]
  (J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin 2 → ℂ) M)
  (hJ : IsPseudoholomorphicOn J
    (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (Fin 2 → ℂ)) c c.source)

/-- **The exceptional divisor of the almost complex blowup has self-intersection `-1`.**
Let `M` be a real four-manifold modelled on `ℂ²` with a smooth almost complex structure `J`, `c`
a chart of its smooth atlas centred at `p₀` that is pseudoholomorphic on its source from `J` to
the standard structure of `ℂ²`, and `Φ` any diffeomorphism from the model `𝓘(ℝ, Fin 1 → ℂ)` of
`ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` to `𝓡 2`. Re-model `ℂℙ¹` on `𝓡 2` along `Φ`, give it its complex
orientation carried along, and embed it in the blowup `Blowup c` as the exceptional divisor
(`divisorRealEmbedding c`). For the almost complex blowup `almostComplexStructure c J hJ`, the
self-intersection number of the exceptional divisor is `-1`. -/
theorem selfIntersectionNumber_exceptionalDivisor_almostComplexStructure
    (Φ : (Fin 1 → ℂ) ≃ₘ^∞⟮𝓘(ℝ, Fin 1 → ℂ), 𝓡 2⟯ EuclideanSpace ℝ (Fin 2)) :
    ((divisorRealEmbedding c).compDiffeomorphOfBoundaryless
        (remodelDiffeomorph Φ (ℙ ℂ (Fin 2 → ℂ))).symm (by simp)).selfIntersectionNumber
        (by simp [Module.finrank_pi_fintype]) (almostComplexStructure c J hJ)
        ((divisorRealEmbedding c).mapsTo_tangentRange_compDiffeomorphOfBoundaryless _
          (by simp) (by simp) (A := (almostComplexStructure c J hJ ·))
          (mapsTo_almostComplexStructure_tangentRange_divisorRealEmbedding c J hJ))
        ((complexCurveOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) (finrank_fin_fun ℂ)).map
          (remodelDiffeomorph Φ (ℙ ℂ (Fin 2 → ℂ))) (by simp)
          (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])) = -1 := by
  rw [← BlowupModel.selfIntersectionNumber_zeroSection Φ]
  -- Near the exceptional divisor, `lift c` is a pseudoholomorphic local diffeomorphism onto a
  -- neighbourhood of the model's zero section, which it sends the divisor to.
  refine SmoothEmbedding.selfIntersectionNumber_eq_of_comp _ _ _ _ _ _ _ _ (φ := lift c) ?_
    (fun x ↦ ?_) (fun x ↦ ?_) (fun x ↦ ?_) _
  · rw [SmoothEmbedding.coe_compDiffeomorphOfBoundaryless,
      SmoothEmbedding.coe_compDiffeomorphOfBoundaryless, ← Function.comp_assoc,
      lift_comp_divisorRealEmbedding, BlowupModel.coe_zeroSectionRealEmbedding]
  · rw [SmoothEmbedding.compDiffeomorphOfBoundaryless_apply]
    exact (isLocalDiffeomorphAt_lift_divisorRealEmbedding c _).contMDiffAt.of_le
      ENat.LEInfty.out
  · rw [SmoothEmbedding.compDiffeomorphOfBoundaryless_apply]
    exact isPseudoholomorphicAt_lift_divisorRealEmbedding c J hJ _
  · rw [SmoothEmbedding.compDiffeomorphOfBoundaryless_apply]
    exact isInvertible_mfderiv_lift_divisorRealEmbedding c _

end AlmostComplex

section Complex

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin 2 → ℂ) M]
  [IsManifold 𝓘(ℂ, Fin 2 → ℂ) ω M] {p₀ : M} (c : BlowupChart (n := 1) M p₀)
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin 2 → ℂ) ω M)]

/-- **The exceptional divisor of the blowup of a complex surface has self-intersection `-1`.**
Let `M` be a complex surface, `c` a holomorphic chart of `M` centred at `p₀`, and `Φ` any
diffeomorphism from the model `𝓘(ℝ, Fin 1 → ℂ)` of `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` to `𝓡 2`.
Re-model `ℂℙ¹` on `𝓡 2` along `Φ`, give it its complex orientation carried along, and embed it
in the blowup `Blowup c` of `M` at `p₀` as the exceptional divisor
(`divisorRealEmbedding c`). For the almost complex structure of the complex surface `Blowup c`,
the self-intersection number of the exceptional divisor is `-1`. -/
theorem selfIntersectionNumber_exceptionalDivisor
    (Φ : (Fin 1 → ℂ) ≃ₘ^∞⟮𝓘(ℝ, Fin 1 → ℂ), 𝓡 2⟯ EuclideanSpace ℝ (Fin 2)) :
    ((divisorRealEmbedding c).compDiffeomorphOfBoundaryless
        (remodelDiffeomorph Φ (ℙ ℂ (Fin 2 → ℂ))).symm (by simp)).selfIntersectionNumber
        (by simp [Module.finrank_pi_fintype])
        (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (Blowup c))
        ((divisorRealEmbedding c).mapsTo_tangentRange_compDiffeomorphOfBoundaryless _
          (by simp) (by simp) (A := (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ)
            (Blowup c) ·))
          (mapsTo_ofComplexManifold_tangentRange_divisorRealEmbedding c))
        ((complexCurveOrientation (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) (finrank_fin_fun ℂ)).map
          (remodelDiffeomorph Φ (ℙ ℂ (Fin 2 → ℂ))) (by simp)
          (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])) = -1 := by
  -- The almost complex blowup of the structure of `M` is the structure of `Blowup c`.
  have h := selfIntersectionNumber_exceptionalDivisor_almostComplexStructure c _
    (isPseudoholomorphicOn_ofComplexManifold_of_mem_maximalAtlas (n := ω) Fact.out (by simp)) Φ
  simpa only [almostComplexStructure_eq_ofComplexManifold] using h

end Complex

end Blowup

end SymplecticGeometry

end
