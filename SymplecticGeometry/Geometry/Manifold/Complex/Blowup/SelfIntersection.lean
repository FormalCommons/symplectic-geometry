/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Tautological
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.SelfIntersection
import SymplecticGeometry.Geometry.Manifold.Projectivization.HyperplaneClass
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace
import TauCeti.Topology.Algebra.Module.ComplexSmulI
import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# The self-intersection number of the exceptional divisor

The exceptional divisor of the model blowup `BlowupModel 1` of `ℂ²` at the origin is the zero
section `zeroSectionRealEmbedding 1` of the tautological line over `ℙ ℂ (Fin 2 → ℂ) = ℂℙ¹`. This
file shows that its self-intersection number, for the almost complex structure of the complex
surface `BlowupModel 1` and the complex orientation of `ℂℙ¹`, is `-1`.

## Main results

* `SymplecticGeometry.BlowupModel.selfIntersectionNumber_zeroSection`: the self-intersection
  number `TauCeti.SmoothEmbedding.selfIntersectionNumber` of the zero section of `BlowupModel 1`,
  re-modelled on `𝓡 2` along any diffeomorphism `Φ` of models (`SymplecticGeometry.Remodel`), is
  `-1`.

## Proof

By `TauCeti.SmoothEmbedding.selfIntersectionNumber_remodel_complexCurveOrientation` the number is
the Euler class of the complex normal bundle of the zero section, evaluated on the fundamental
class of `ℂℙ¹` for its complex orientation. The isomorphisms
`BlowupModel.normalSpaceZeroSectionRealEquiv` carry the complex structure of the normal bundle to
multiplication by `Complex.I`, so they are complex-linear isomorphisms onto the tautological line,
continuous on total spaces; by Tau Ceti's `TauCeti.complexEulerClass_eq_of_fiberwise` the two Euler
classes agree. The Euler class of the tautological line is minus the hyperplane class
(`Projectivization.hyperplaneClass_def`), which takes the value `1` on `[ℂℙ¹]`
(`Projectivization.complexManifoldEvalFundamentalClass_hyperplaneClass`).

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
  have hdim := finrank_real_complex_eq_sub_of_finrank_eq_four_of_finrank_eq_two
    (by simp [Module.finrank_pi_fintype] : finrank ℝ (Fin 2 → ℂ) = 4)
    (finrank_real_of_finrank_complex_eq_add_one (finrank_fin_fun ℂ (n := 1)))
  let := (zeroSectionRealEmbedding 1).normalSpaceFiberBundle hn hdim
  let := (zeroSectionRealEmbedding 1).normalSpaceVectorBundle hn hdim
  set J := (zeroSectionRealEmbedding 1).normalComplexStructure hn
    (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (BlowupModel 1)) hdim
    mapsTo_ofComplexManifold_tangentRange_zeroSectionRealEmbedding with hJdef
  -- The normal isomorphisms, complex-linear for the complex structure `J` of the normal bundle.
  let φ (ℓ : ℙ ℂ (Fin 2 → ℂ)) : J.Fiber ℓ ≃L[ℂ] Projectivization.Tautological ℂ (Fin 2 → ℂ) ℓ :=
    ((J.fiberEquiv ℓ).trans (normalSpaceZeroSectionRealEquiv 1 hn ℓ)).complexOfMapISmul fun v ↦ by
      have h := normalSpaceZeroSectionRealEquiv_contMDiffNormalComplexStructure hdim ℓ
        (J.fiberEquiv ℓ v)
      rw [SmoothEmbedding.contMDiffNormalComplexStructure_apply] at h
      rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
        J.fiberEquiv_I_smul, hJdef, SmoothEmbedding.normalComplexStructure_apply, h]
  have hφ : Continuous fun p : TotalSpace ℂ J.Fiber ↦
      TotalSpace.mk' ℂ (E := Projectivization.Tautological ℂ (Fin 2 → ℂ)) p.proj
        (φ p.proj p.snd) :=
    ((continuous_normalSpaceZeroSectionRealEquiv hn).comp
      (J.totalSpaceHomeomorph ℂ).continuous).congr fun p ↦ by
        rw [Function.comp_apply, Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply]
        simp only [φ, ContinuousLinearEquiv.complexOfMapISmul_apply,
          ContinuousLinearEquiv.trans_apply]
  rw [SmoothEmbedding.selfIntersectionNumber_remodel_complexCurveOrientation (finrank_fin_fun ℂ)
      (hJ := mapsTo_ofComplexManifold_tangentRange_zeroSectionRealEmbedding),
    complexEulerClass_eq_of_fiberwise (finrank_self ℂ) (finrank_self ℂ) hφ,
    ← neg_neg (((TopCat.of _).uliftIntegralCohomologyIso _).hom _),
    ← Projectivization.hyperplaneClass_def, map_neg,
    Projectivization.complexManifoldEvalFundamentalClass_hyperplaneClass]

end BlowupModel

end SymplecticGeometry

end
