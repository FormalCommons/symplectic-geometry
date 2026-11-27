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
import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.DimensionOne
import SymplecticGeometry.Geometry.Manifold.Projectivization.ChernClass
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Multiple
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ComplexStructure
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.FirstChernClass
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.FirstChernClass
import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace
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
  restrict to the same class. There the blowdown is a local diffeomorphism
  (`SymplecticGeometry.Blowup.isLocalDiffeomorphAt_blowdown_real`) and pseudoholomorphic
  (`SymplecticGeometry.Blowup.isPseudoholomorphicAt_blowdown`), so the naturality of the first
  Chern class along such maps
  (`TauCeti.IsPseudoholomorphicAt.singularCohomologyMap_firstChernClass_eq`) applies.
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
* `SymplecticGeometry.Blowup.firstChernClass_tangent`: the formula
  `c₁(T Blowup c, J̃) = π^* c₁(TM, J) - n e`, where `e` is
  `SymplecticGeometry.Blowup.exceptionalClass` and Lean's `n` is the complex dimension of `M`
  minus one. For `1 ≤ n`, the class `x = c₁(T Blowup c, J̃) + n e - π^* c₁(TM, J)` vanishes off
  the divisor, by `firstChernClass_restrict_compl` and `exceptionalClass_restrict_compl`, so it
  is `m e` for an integer `m`
  (`TauCeti.SmoothEmbedding.exists_eq_zsmul_dualClass_of_restrict_compl`). On the divisor `x`
  restricts to `n h - n h - 0 = 0`, by `firstChernClass_restrict_divisor`,
  `exceptionalClass_restrict_divisor` and `singularCohomologyMap_divisorRealEmbedding_blowdown`,
  and `m e` to `-m h`; since `m ↦ m • h` is injective
  (`Projectivization.bijective_zsmul_hyperplaneClass`), `m = 0`. For `n = 0` the blowdown is a
  local diffeomorphism everywhere (`SymplecticGeometry.Blowup.isLocalDiffeomorph_blowdown_real`),
  so the naturality above, for `ι` the identity, gives `c₁(T Blowup c, J̃) = π^* c₁(TM, J)`.
  McDuff–Salamon use this formula, (7.1.31), without proving it.
* `SymplecticGeometry.Blowup.firstChernClass_tangent_ofComplexManifold`: the same formula for a
  complex manifold `M`, a chart `c` of its complex atlas, and the tangent bundles of the complex
  manifolds `Blowup c` and `M`.

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
  {p₀ : M} (c : BlowupChart (n := n) M p₀)

section Smooth

variable [IsManifold 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M]
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ M)]
  (J : SmoothAlmostComplexStructure 𝓘(ℝ, Fin (n + 1) → ℂ) M)
  (hJ : IsPseudoholomorphicOn J (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)) c
    c.source)

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ (Fin (n + 1) → ℂ) = 2 * finrank ℂ G)]

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
  rw [TopPair.ofSubset_map]
  exact IsPseudoholomorphicAt.singularCohomologyMap_firstChernClass_eq G
    (ContinuousMap.subtypeVal _)
    ((contMDiff_blowdown_real c).of_le (by simp))
    (fun _ ↦ isPseudoholomorphicAt_blowdown c J hJ _)
    (fun z ↦ isLocalDiffeomorphAt_blowdown_real c z.property) (by simp)

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


/-! ### The first Chern class of the blowup -/

section Tangent

variable [T2Space M] [SecondCountableTopology M]

/-- The case `1 ≤ n` of `firstChernClass_tangent`: the difference
`c₁(T Blowup c) + n e - π^* c₁(TM)` vanishes off the exceptional divisor, so it is `m e`; on the
divisor it restricts to `0 = -m h`, so `m = 0`. -/
private theorem firstChernClass_tangent_of_pos (hn0 : 0 < n) :
    firstChernClass G
        ((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure.Fiber =
      TopCat.singularCohomologyMap (TopCat.ofHom (blowdown c)) 2
          (firstChernClass G (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber) -
        n • exceptionalClass c := by
  rw [eq_sub_iff_add_eq, ← sub_eq_zero]
  set a := firstChernClass G
        ((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure.Fiber +
      n • exceptionalClass c - TopCat.singularCohomologyMap (TopCat.ofHom (blowdown c)) 2
          (firstChernClass G (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber) with ha_def
  -- Step 2: `a` vanishes off the divisor (step 1), so it is a multiple of the dual class `e`.
  have hcompl : TopCat.singularCohomologyMap
      (TopCat.ofHom (ContinuousMap.subtypeVal (exceptionalDivisor c)ᶜ)) 2 a = 0 := by
    have h₁ := IsPseudoholomorphicAt.singularCohomologyMap_firstChernClass_eq G
      (ContinuousMap.subtypeVal (exceptionalDivisor c)ᶜ)
      ((contMDiff_blowdown_real c).of_le (by simp))
      (fun _ ↦ isPseudoholomorphicAt_blowdown c J hJ _)
      (fun z ↦ isLocalDiffeomorphAt_blowdown_real c z.property) (by simp)
    have h₂ : TopCat.singularCohomologyMap
        (TopCat.ofHom (ContinuousMap.subtypeVal (exceptionalDivisor c)ᶜ)) 2 (exceptionalClass c) =
          0 := by
      have h := exceptionalClass_restrict_compl c
      -- After the rewrite, `h` reads the domain as `TopCat.of (Blowup c)` coerced to a type, which
      -- is `Blowup c` by definition; `rwa` closes the goal up to that unfolding.
      rwa [TopPair.ofSubset_map] at h
    rw [ha_def, map_sub, map_add, map_nsmul, h₁, h₂, nsmul_zero, add_zero, sub_self]
  obtain ⟨m, hm⟩ := (divisorRealEmbedding c).exists_eq_zsmul_dualClass_of_restrict_compl
    (Iff.mpr WithTop.coe_ne_zero ENat.top_ne_zero) (Complex.finrank_real_eq_finrank_pi_succ_sub n)
    (by rw [range_divisorRealEmbedding]; exact isClosed_exceptionalDivisor c)
    (divisorNormalOrientation c) Complex.finrank_real_complex (a := a)
    -- As for `h₂`, `exact` accepts the coerced ambient space of the pair.
    (by rw [range_divisorRealEmbedding, TopPair.ofSubset_map]; exact hcompl)
  rw [← exceptionalClass_def] at hm
  -- Step 3: on the divisor, `a` restricts to `n h - n h - 0 = 0` and `m e` to `-m h`.
  have h := congrArg (fun x ↦ ((TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))).uliftIntegralCohomologyIso 2).hom
    (TopCat.singularCohomologyMap
      (TopCat.ofHom ⟨divisorRealEmbedding c, (divisorRealEmbedding c).isEmbedding.continuous⟩) 2
      x)) hm
  simp only [ha_def, map_sub, map_add, map_zsmul, firstChernClass_restrict_divisor,
    exceptionalClass_restrict_divisor, singularCohomologyMap_divisorRealEmbedding_blowdown _
      two_ne_zero, sub_zero, ← natCast_zsmul] at h
  rw [zsmul_neg, zsmul_neg, add_neg_cancel, eq_comm, neg_eq_zero] at h
  obtain rfl : m = 0 := (Projectivization.bijective_zsmul_hyperplaneClass
    (V := Fin (n + 1) → ℂ) (by simp) hn0).injective
    (by simp only [h, zero_smul])
  rw [hm, zero_smul]

/-- **The first Chern class of the blowup.** For the almost complex blowup
`J̃ = almostComplexStructure c J hJ` of `M` at `p₀`, with `M` of complex dimension `n + 1`,
`c₁(T Blowup c, J̃) = π^* c₁(TM, J) - n e`, where `π` is the blowdown and `e` the exceptional
class `exceptionalClass c`; both first Chern classes are computed with the complex model `G`.
For a complex manifold `M` and a holomorphic chart `c`, its holomorphic counterpart is the
isomorphism `canonicalBundleEquiv` of canonical bundles, `K ≅ π^* K_M ⊗ 𝒪(n E)`.

Milestone: *First Chern class of a blowup at a point*. -/
theorem firstChernClass_tangent :
    firstChernClass G
        ((almostComplexStructure c J hJ).toContMDiff ⊤).toContinuousComplexStructure.Fiber =
      TopCat.singularCohomologyMap (TopCat.ofHom (blowdown c)) 2
          (firstChernClass G (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber) -
        n • exceptionalClass c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- For `n = 0` the blowdown is a local diffeomorphism everywhere, so naturality applies.
    have h := IsPseudoholomorphicAt.singularCohomologyMap_firstChernClass_eq G
      (ContinuousMap.id _)
      ((contMDiff_blowdown_real c).of_le (by simp))
      (fun _ ↦ isPseudoholomorphicAt_blowdown c J hJ _)
      (fun z ↦ isLocalDiffeomorph_blowdown_real c z) (by simp)
    rw [TopCat.ofHom_id, TopCat.singularCohomologyMap_id] at h
    rw [zero_smul, sub_zero]
    exact h
  · exact firstChernClass_tangent_of_pos c J hJ G hn0

end Tangent

end Smooth

/-! ### The complex case -/

section Complex

variable [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
  [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]
  [T2Space M] [SecondCountableTopology M]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ (Fin (n + 1) → ℂ) = 2 * finrank ℂ G)]

/-- **The first Chern class of the blowup of a complex manifold.** For a complex manifold `M` of
complex dimension `n + 1` and a chart `c` of its complex atlas, the first Chern classes of the
tangent bundles of the complex manifolds `Blowup c` and `M`, computed with the complex model
`G`, satisfy `c₁(T Blowup c) = π^* c₁(TM) - n e`, where `π` is the blowdown and `e` the
exceptional class `exceptionalClass c`. It is `firstChernClass_tangent` for the structure of
`M`, whose almost complex blowup is the structure of `Blowup c`
(`almostComplexStructure_eq_ofComplexManifold`). -/
theorem firstChernClass_tangent_ofComplexManifold :
    firstChernClass G (ofComplexManifold (Fin (n + 1) → ℂ) (Blowup c) |>.toContMDiff ⊤
        |>.toContinuousComplexStructure.Fiber) =
      TopCat.singularCohomologyMap (TopCat.ofHom (blowdown c)) 2
          (firstChernClass G (ofComplexManifold (Fin (n + 1) → ℂ) M |>.toContMDiff ⊤
            |>.toContinuousComplexStructure.Fiber)) -
        n • exceptionalClass c := by
  rw [← almostComplexStructure_eq_ofComplexManifold]
  exact firstChernClass_tangent c _ _ G

end Complex

end Blowup

end SymplecticGeometry
