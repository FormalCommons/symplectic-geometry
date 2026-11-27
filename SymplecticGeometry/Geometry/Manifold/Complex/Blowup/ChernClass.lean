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
import SymplecticGeometry.Geometry.Manifold.Projectivization.ChernClass
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ComplexStructure
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.FirstChernClass
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.FirstChernClass
import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
import SymplecticGeometry.Topology.VectorBundle.Complex.Structure
import TauCeti.AlgebraicTopology.Cohomology.Point

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
* `SymplecticGeometry.Blowup.singularCohomologyMap_divisorRealEmbedding_blowdown`: on the
  exceptional divisor, the pull-back by the blowdown of a class of `M` of positive degree, such as
  `c₁(TM, J)`, restricts to zero, since the blowdown maps the divisor to the point `p₀`
  (`TopCat.singularCohomologyMap_eq_zero_of_nullhomotopic`).
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
  hyperplane class (`Projectivization.firstChernClass_tautological`). The complex isomorphisms
  are `TauCeti.Bundle.ContinuousComplexStructure.fiberEquivOfCommuteI`.
* `SymplecticGeometry.Blowup.firstChernClass_restrict_divisor`: on the exceptional divisor,
  `c₁(T Blowup c, J̃)` restricts to `n • h`. The divisor is a pseudoholomorphic embedding of
  `ℙ ℂ (Fin (n + 1) → ℂ)`, so the restriction is `c₁(Tℙ) + c₁(ν)`
  (`TauCeti.SmoothEmbedding.firstChernClass_pullback_eq_add`), with `c₁(Tℙ) = (n + 1) h`
  (`Projectivization.firstChernClass_ofComplexManifold`) and `c₁(ν) = -h` by the result above.

The first result is step 1, and the other four are part of step 3, of the proof of the formula
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

/-- `dπ` intertwines `J̃` with `J` off the exceptional divisor, read on the differential of the
blowdown as a real-linear isomorphism. -/
private theorem mfderivToContinuousLinearEquiv_blowdown_apply (z : ↥(exceptionalDivisor c)ᶜ)
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℂ) (z : Blowup c)) :
    (isLocalDiffeomorphAt_blowdown_real c z.property).mfderivToContinuousLinearEquiv (by simp)
        (((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure z v) =
      (J.toContMDiff ⊤).toContinuousComplexStructure (blowdown c z)
        ((isLocalDiffeomorphAt_blowdown_real c z.property).mfderivToContinuousLinearEquiv
          (by simp) v) := by
  simp only [toContMDiff_apply, ContMDiffAlmostComplexStructure.toContinuousComplexStructure_apply]
  rw [← ContinuousLinearEquiv.coe_coe, IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe]
  -- `J̃ z` and `J (blowdown c z)` are applied through `toEndomorphism`, their coercion.
  exact mfderiv_blowdown_almostComplexStructure_apply c J hJ z _

/-- Off the exceptional divisor, the differential of the blowdown, as a complex-linear
isomorphism of the fibres of the complex tangent bundles `(T Blowup c, J̃)` and `(TM, J)`. -/
private def mfderivBlowdownEquiv (z : ↥(exceptionalDivisor c)ᶜ) :
    ((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure.Fiber
        (z : Blowup c) ≃L[ℂ]
      (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber (blowdown c z) :=
  Bundle.ContinuousComplexStructure.fiberEquivOfCommuteAt _ _
    ((isLocalDiffeomorphAt_blowdown_real c z.property).mfderivToContinuousLinearEquiv (by simp))
    (mfderivToContinuousLinearEquiv_blowdown_apply c J hJ z)

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ (Fin (n + 1) → ℂ) = 2 * finrank ℂ G)]

/-- The isomorphisms `mfderivBlowdownEquiv` are continuous on total spaces, from the pull-back
of `(T Blowup c, J̃)` to the complement of the exceptional divisor to `(TM, J)`. -/
private theorem continuous_mfderivBlowdownEquiv :
    Continuous fun v : TotalSpace G (⇑(ContinuousMap.subtypeVal (exceptionalDivisor c)ᶜ) *ᵖ
        ((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure.Fiber) ↦
      TotalSpace.mk' G (E := (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber)
        (blowdown c v.proj) (mfderivBlowdownEquiv c J hJ v.proj v.snd) := by
  simp only [mfderivBlowdownEquiv]
  refine Bundle.ContinuousComplexStructure.continuous_fiberEquivOfCommuteAt_pullback _ _
    (X := ↥(exceptionalDivisor c)ᶜ) (ContinuousMap.subtypeVal _) (fun z ↦ blowdown c z) _
    (mfderivToContinuousLinearEquiv_blowdown_apply c J hJ)
    ((((contMDiff_blowdown_real c).continuous_tangentMap (by simp)).comp
      (Pullback.continuous_lift _ _ _)).congr fun v ↦ ?_)
  rw [Function.comp_apply]
  -- The map is `tangentMap (blowdown c)` after `Pullback.lift`. Neither has a lemma that reads it
  -- at `v`, and `IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe` cannot be rewritten at
  -- the fibre of the pull-back that `v.snd` lies in, so all three are unfolded.
  rfl

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

/-- On the exceptional divisor, the pull-back by the blowdown of a cohomology class of `M` of
positive degree vanishes, since the blowdown is constant, equal to `p₀`, on the divisor. For
instance the pull-back of `c₁(TM, J)` restricts to zero on the divisor. -/
theorem singularCohomologyMap_divisorRealEmbedding_blowdown {C : Type*}
    [CategoryTheory.Category C] [CategoryTheory.Limits.HasCoproducts.{0} C]
    [CategoryTheory.Abelian C] {R : C} {k : Type*} [Ring k] [CategoryTheory.Linear k C] {N : C}
    {m : ℕ} (hm : m ≠ 0) (x : (TopCat.of M).singularCohomology R k N m) :
    TopCat.singularCohomologyMap
        (TopCat.ofHom ⟨divisorRealEmbedding c, (divisorRealEmbedding c).isEmbedding.continuous⟩) m
        (TopCat.singularCohomologyMap (TopCat.ofHom (blowdown c)) m x) = 0 := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    ← TopCat.ofHom_comp, TopCat.singularCohomologyMap_eq_zero_of_nullhomotopic _ hm]
  · simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
  have h : (blowdown c).comp
      ⟨divisorRealEmbedding c, (divisorRealEmbedding c).isEmbedding.continuous⟩ =
      ContinuousMap.const _ p₀ := by
    ext ℓ
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, coe_divisorRealEmbedding,
      blowdown_ofDirection, ContinuousMap.const_apply]
  rw [TopCat.hom_ofHom, h]
  exact ContinuousMap.nullhomotopic_of_constant p₀

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
  -- `divisorNormalEquiv c` carries `ν` to multiplication by `I`.
  have he (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) (w) :
      divisorNormalEquiv c ℓ (ν ℓ w) = Complex.I • divisorNormalEquiv c ℓ w := by
    rw [hν, SmoothEmbedding.normalComplexStructure_apply,
      divisorNormalEquiv_normalComplexStructureAt]
  rw [SymplecticGeometry.Bundle.firstChernClass_congr _
      (ν.continuous_fiberEquivOfCommuteI _ he ℂ (continuous_divisorNormalEquiv c)),
    Projectivization.firstChernClass_tautological]

/-! ### The tangent bundle of the blowup along the exceptional divisor -/

/-- **The first Chern class of the blowup on the exceptional divisor.** The pull-back along the
exceptional divisor `divisorRealEmbedding c` of the first Chern class of the complex tangent
bundle of the blowup, with the almost complex structure `J̃ = almostComplexStructure c J hJ` and
the complex model `G`, is `n • h` in integral cohomology, with `h` the hyperplane class of
`ℙ ℂ (Fin (n + 1) → ℂ)`. -/
theorem firstChernClass_restrict_divisor :
    ((TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))).uliftIntegralCohomologyIso 2).hom
        (TopCat.singularCohomologyMap
          (TopCat.ofHom ⟨divisorRealEmbedding c, (divisorRealEmbedding c).isEmbedding.continuous⟩)
          2 (firstChernClass G
            ((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure.Fiber)) =
      (n : ℤ) • Projectivization.hyperplaneClass (Fin (n + 1) → ℂ) := by
  have : Fact (finrank ℝ (Fin n → ℂ) = 2 * finrank ℂ (Fin n → ℂ)) :=
    ⟨finrank_real_of_complex _⟩
  have := Complex.finrank_real_complex_eq_two_mul_finrank_fact
  -- `ι^* c₁(T Blowup c) = c₁(Tℙ) + c₁(ν) = (n + 1) h - h`.
  rw [(divisorRealEmbedding c).firstChernClass_pullback_eq_add (hn := by simp)
      (Complex.finrank_real_eq_finrank_pi_succ_sub n)
      (isPseudoholomorphic_divisorRealEmbedding c J hJ) G (Fin n → ℂ) ℂ,
    map_add, Projectivization.firstChernClass_ofComplexManifold,
    firstChernClass_normalComplexStructure_divisorRealEmbedding, Nat.cast_succ, add_zsmul,
    one_zsmul, add_neg_cancel_right]

end Blowup

end SymplecticGeometry
