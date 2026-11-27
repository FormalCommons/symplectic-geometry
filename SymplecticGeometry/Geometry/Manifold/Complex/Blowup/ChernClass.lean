/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.AlmostComplex
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.ExceptionalClass
public import SymplecticGeometry.Geometry.Manifold.Projectivization.HyperplaneClass
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ComplexStructure
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.FirstChernClass
import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
import SymplecticGeometry.Topology.VectorBundle.Complex.Structure
import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# The first Chern class of the blowup

Let `M` be a smooth manifold modelled on `E = ℂⁿ⁺¹` with a smooth almost complex structure `J`,
`c` a chart of `M` at `p₀` that is `J`-holomorphic on its source, and `J̃` the almost complex
structure of the blowup `Blowup c` (`SymplecticGeometry.Blowup.almostComplexStructure`). The
first Chern classes below are Tau Ceti's `TauCeti.firstChernClass`: of the complex tangent bundles
`(T Blowup c, J̃)` and `(TM, J)`, with any complex model `G`, and of the normal bundle of the
exceptional divisor with the complex structure induced by `J̃`, with complex model `ℂ`.

## Main results

* `SymplecticGeometry.Blowup.firstChernClass_restrict_compl`: on the complement of the
  exceptional divisor, `c₁(T Blowup c, J̃)` and the pull-back of `c₁(TM, J)` by the blowdown `π`
  restrict to the same class. There `dπ` is invertible
  (`SymplecticGeometry.Blowup.isLocalDiffeomorphAt_blowdown_real`) and complex linear
  (`SymplecticGeometry.Blowup.mfderiv_blowdown_almostComplexStructure_apply`), so it is a complex
  isomorphism of the tangent bundle of the complement with the pull-back of `(TM, J)`, and the
  naturality of the first Chern class
  (`TauCeti.firstChernClass_eq_singularCohomologyMap_of_fiberwise`) applies.
* `SymplecticGeometry.Blowup.divisorNormalEquiv_normalComplexStructureAt`: the isomorphism
  `SymplecticGeometry.Blowup.divisorNormalEquiv` from the normal spaces of the exceptional divisor
  onto the tautological line takes the normal complex structure induced by `J̃` to
  multiplication by `Complex.I`. Near the divisor `lift c` is pseudoholomorphic
  (`SymplecticGeometry.Blowup.isPseudoholomorphicAt_lift_divisorRealEmbedding`), so its
  differential is complex linear on normal spaces
  (`TauCeti.SmoothEmbedding.normalSpaceEquivOfComp_normalComplexStructureAt`), and on the model
  the normal structure is `Complex.I`
  (`BlowupModel.normalSpaceZeroSectionRealEquiv_contMDiffNormalComplexStructure`).
* `SymplecticGeometry.Blowup.firstChernClass_normalComplexStructure_divisorRealEmbedding`: so the
  normal bundle of the exceptional divisor, with the complex structure induced by `J̃`, is
  isomorphic to the tautological line, and its first Chern class is `-h`, with `h` the
  hyperplane class (`Projectivization.firstChernClass_tautological`). The complex isomorphism
  is built as in the proof of `SymplecticGeometry.BlowupModel.selfIntersectionNumber_zeroSection`.

The first result is step 1, and the last two are part of step 3, of the proof of the formula
`c₁(T Blowup c) = π^* c₁(TM) - n e`, where `e` is `SymplecticGeometry.Blowup.exceptionalClass`
and Lean's `n` is the complex dimension of `M` minus one; McDuff–Salamon use this formula,
(7.1.31), without proving it.

The private steps of the proof adapt Tau Ceti's `mfderivFiberEquiv` and
`continuous_mfderivFiberRealEquiv` (`TauCeti/Geometry/Symplectic/Manifold/AlmostComplex/Chern.lean`)
from a diffeomorphism to the blowdown, a local diffeomorphism off the divisor, and from the
tangent bundle of the target to its pull-back.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1, (7.1.31), p. 311, and Example 4.4.3.
-/

public section

open Bundle Module Set TauCeti TauCeti.SmoothAlmostComplexStructure
open scoped Manifold ContDiff LinearAlgebra.Projectivization TauCeti.ComplexManifold

noncomputable section

namespace SymplecticGeometry

namespace Blowup

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M] {p₀ : M} (c : BlowupChart (n := n) M p₀)
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)]
  (J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M)
  (hJ : IsPseudoholomorphicOn J (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)) c
    c.source)

/-- Off the exceptional divisor, the differential of the blowdown, as a complex-linear
isomorphism of the fibres of the complex tangent bundles `(T Blowup c, J̃)` and `(TM, J)`. -/
private def mfderivBlowdownEquiv (z : ↥(exceptionalDivisor c)ᶜ) :
    ((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure.Fiber
        (z : Blowup c) ≃L[ℂ]
      (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber (blowdown c z) :=
  Bundle.ContinuousComplexStructure.fiberEquivOfCommuteAt _ _
    ((isLocalDiffeomorphAt_blowdown_real c z.property).mfderivToContinuousLinearEquiv (by simp))
    fun v ↦ by
      simp only [toContMDiff_apply,
        ContMDiffAlmostComplexStructure.toContinuousComplexStructure_apply]
      rw [← ContinuousLinearEquiv.coe_coe, IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe]
      -- `J̃ z` and `J (blowdown c z)` are applied through `toEndomorphism`, their coercion.
      exact mfderiv_blowdown_almostComplexStructure_apply c J hJ z _

/-- `mfderivBlowdownEquiv` is the differential of the blowdown on the underlying real vectors. -/
private theorem fiberEquiv_mfderivBlowdownEquiv (z : ↥(exceptionalDivisor c)ᶜ)
    (v : ((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure.Fiber
      (z : Blowup c)) :
    (J.toContMDiff ⊤).toContinuousComplexStructure.fiberEquiv (blowdown c z)
        (mfderivBlowdownEquiv c J hJ z v) =
      mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (blowdown c) z
        (((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure.fiberEquiv
          z v) := by
  rw [mfderivBlowdownEquiv, Bundle.ContinuousComplexStructure.fiberEquiv_fiberEquivOfCommuteAt,
    ← ContinuousLinearEquiv.coe_coe, IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe]

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ (Fin (n + 1) → ℂ) = 2 * finrank ℂ G)]

/-- The isomorphisms `mfderivBlowdownEquiv` are continuous on total spaces, from the pull-back
of `(T Blowup c, J̃)` to the complement of the exceptional divisor to `(TM, J)`. -/
private theorem continuous_mfderivBlowdownEquiv :
    Continuous fun v : TotalSpace G (⇑(ContinuousMap.subtypeVal (exceptionalDivisor c)ᶜ) *ᵖ
        ((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure.Fiber) ↦
      TotalSpace.mk' G (E := (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber)
        (blowdown c v.proj) (mfderivBlowdownEquiv c J hJ v.proj v.snd) := by
  -- The map is `tangentMap (blowdown c)`, read through the complex tangent bundles.
  refine (((J.toContMDiff ⊤).toContinuousComplexStructure.totalSpaceHomeomorph
      G).symm.continuous.comp (((contMDiff_blowdown_real c).continuous_tangentMap (by simp)).comp
    ((((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure
      |>.totalSpaceHomeomorph G).continuous.comp (Pullback.continuous_lift G _ _)))).congr
    fun v ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Homeomorph.symm_apply_eq,
    Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply,
    Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply]
  -- `tangentMap` and `Pullback.lift` are read at `v` by unfolding: the fibres of the pull-back
  -- are aliases of those of the bundle, at which their rewriting lemmas cannot be stated.
  exact congrArg (TotalSpace.mk' _ (blowdown c v.proj))
    (fiberEquiv_mfderivBlowdownEquiv c J hJ v.proj v.snd).symm

/-- **The first Chern class of the blowup off the exceptional divisor.** On the complement of
the exceptional divisor, the first Chern class of the complex tangent bundle of the blowup, with
the almost complex structure `J̃ = almostComplexStructure c J hJ`, and the pull-back by the
blowdown of the first Chern class of `(TM, J)` restrict to the same class; both are computed with
the complex model `G`. -/
theorem firstChernClass_restrict_compl :
    TopCat.singularCohomologyMap
        (TopPair.ofSubset (X := TopCat.of (Blowup c)) (exceptionalDivisor c)ᶜ).map 2
        (firstChernClass G
          ((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure.Fiber) =
      TopCat.singularCohomologyMap
        (TopPair.ofSubset (X := TopCat.of (Blowup c)) (exceptionalDivisor c)ᶜ).map 2
        (TopCat.singularCohomologyMap (TopCat.ofHom (blowdown c)) 2
          (firstChernClass G (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber)) := by
  have h := firstChernClass_eq_singularCohomologyMap_of_fiberwise
    (g := (blowdown c).comp (ContinuousMap.subtypeVal _))
    (continuous_mfderivBlowdownEquiv c J hJ G)
  rw [firstChernClass_pullback, TopCat.ofHom_comp, TopCat.singularCohomologyMap_comp,
    CategoryTheory.ConcreteCategory.comp_apply] at h
  rw [TopPair.ofSubset_map]
  exact h


/-! ### The normal bundle of the exceptional divisor -/

/-- **`divisorNormalEquiv` is complex linear.** On the normal space of the exceptional divisor at
`ℓ`, the isomorphism `divisorNormalEquiv c ℓ` onto the line `ℓ` carries the complex structure that
the almost complex blowup `J̃ = almostComplexStructure c J hJ` induces on normal spaces to
multiplication by `Complex.I`. -/
theorem divisorNormalEquiv_normalComplexStructureAt {hn : (∞ : ℕ∞ω) ≠ 0}
    (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) (w : (divisorRealEmbedding c).isImmersion.NormalSpace ℓ hn) :
    divisorNormalEquiv c ℓ ((divisorRealEmbedding c).normalComplexStructureAt hn
        (almostComplexStructure c J hJ) ℓ
        (mapsTo_almostComplexStructure_tangentRange_divisorRealEmbedding c J hJ ℓ) w) =
      Complex.I • divisorNormalEquiv c ℓ w := by
  -- `lift c` is pseudoholomorphic along the divisor, and the model's normal structure is `I`.
  have h := BlowupModel.normalSpaceZeroSectionRealEquiv_contMDiffNormalComplexStructure (hn := hn)
    (P := ℂ) (Complex.finrank_real_eq_finrank_pi_succ_sub n) ℓ
  simp only [SmoothEmbedding.contMDiffNormalComplexStructure_apply] at h
  rw [divisorNormalEquiv_def, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
    SmoothEmbedding.normalSpaceEquivOfComp_normalComplexStructureAt _ _ _ _ _ _ ℓ _
      (BlowupModel.mapsTo_ofComplexManifold_tangentRange_zeroSectionRealEmbedding ℓ)
      (isPseudoholomorphicAt_lift_divisorRealEmbedding c J hJ ℓ), h]

/-- **The normal bundle of the exceptional divisor has first Chern class `-h`.** The normal
bundle of the exceptional divisor `divisorRealEmbedding c`, with model fibre `P` of dimension
`hdim` and the complex structure that the almost complex blowup
`J̃ = almostComplexStructure c J hJ` induces on it, has first Chern class, with complex model
`ℂ` and read in integral cohomology, minus the hyperplane class of `ℙ ℂ (Fin (n + 1) → ℂ)`. -/
theorem firstChernClass_normalComplexStructure_divisorRealEmbedding {hn : (∞ : ℕ∞ω) ≠ 0}
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [Fact (finrank ℝ P = 2 * finrank ℂ ℂ)]
    (hdim : finrank ℝ P = finrank ℝ (Fin (n + 1) → ℂ) - finrank ℝ (Fin n → ℂ)) :
    letI := (divisorRealEmbedding c).normalSpaceFiberBundle hn hdim
    letI := (divisorRealEmbedding c).normalSpaceVectorBundle hn hdim
    ((TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))).uliftIntegralCohomologyIso 2).hom
        (firstChernClass ℂ ((divisorRealEmbedding c).normalComplexStructure hn
          (almostComplexStructure c J hJ) hdim
          (mapsTo_almostComplexStructure_tangentRange_divisorRealEmbedding c J hJ)).Fiber) =
      -Projectivization.hyperplaneClass (Fin (n + 1) → ℂ) := by
  let := (divisorRealEmbedding c).normalSpaceFiberBundle hn hdim
  let := (divisorRealEmbedding c).normalSpaceVectorBundle hn hdim
  set ν := (divisorRealEmbedding c).normalComplexStructure hn (almostComplexStructure c J hJ) hdim
    (mapsTo_almostComplexStructure_tangentRange_divisorRealEmbedding c J hJ) with hν
  -- The isomorphisms `divisorNormalEquiv c`, complex linear for `ν`.
  let φ (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) :
      ν.Fiber ℓ ≃L[ℂ] Projectivization.Tautological ℂ (Fin (n + 1) → ℂ) ℓ :=
    ((ν.fiberEquiv ℓ).trans (divisorNormalEquiv c ℓ)).complexOfMapISmul fun v ↦ by
      rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
        ν.fiberEquiv_I_smul, hν, SmoothEmbedding.normalComplexStructure_apply,
        divisorNormalEquiv_normalComplexStructureAt]
  have hφ : Continuous fun p : TotalSpace ℂ ν.Fiber ↦
      TotalSpace.mk' ℂ (E := Projectivization.Tautological ℂ (Fin (n + 1) → ℂ)) p.proj
        (φ p.proj p.snd) :=
    ((continuous_divisorNormalEquiv c).comp (ν.totalSpaceHomeomorph ℂ).continuous).congr
      fun p ↦ by
        rw [Function.comp_apply, Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply]
        simp only [φ, ContinuousLinearEquiv.complexOfMapISmul_apply,
          ContinuousLinearEquiv.trans_apply]
  rw [SymplecticGeometry.Bundle.firstChernClass_congr φ hφ,
    Projectivization.firstChernClass_tautological]

end Blowup

end SymplecticGeometry
