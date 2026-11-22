/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import SymplecticGeometry.Algebra.BigOperators.Homogenization
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cup.OpenCover
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Naturality

/-!
# The Whitney sum formula for Chern classes

For complex vector bundles `E₁` and `E₂` over a compact base, of ranks `n₁` and `n₂`,
`c(E₁ ⊕ E₂) = c(E₁) c(E₂)`, that is `c_k(E₁ ⊕ E₂) = ∑_{i ≤ k} cᵢ(E₁) ⌣ c_{k-i}(E₂)`.

The proof is Hatcher's, which needs no splitting principle. Let `P = P(E₁ ⊕ E₂)`, with
projection `π` and tautological class `x`, and let `rₗ = ∑_{i ≤ nₗ} π^* cᵢ(Eₗ) x^{nₗ-i}` on `P`.
The embedding `inl : P(E₁) → P` pulls `x` back to the tautological class of `E₁`, so it pulls
`r₁` back to the left side of the defining relation of the Chern classes of `E₁`, which is zero.
The complement `U₁` of the range of `inr` deformation retracts onto the range of `inl`
(`ProjectiveBundle.homotopic_inlCompl_comp_inlRetraction`), so `r₁` restricts to zero on `U₁`.
In the same way `r₂` restricts to zero on the complement `U₂` of the range of `inl`, through the
exchange of the summands `ProjectiveBundle.prodComm`. The ranges of `inl` and `inr` are disjoint
closed sets, so `U₁` and `U₂` are open and cover `P`, and `r₁ r₂ = 0`
(`TopCat.evenIntegralCohomology_mul_eq_zero_of_union_eq_univ`). Expanding the product,
`r₁ r₂ = ∑_{k ≤ n₁ + n₂} π^* aₖ x^{n₁+n₂-k}` with `aₖ = ∑_{i ≤ k} cᵢ(E₁) ⌣ c_{k-i}(E₂)`
(`Finset.sum_mul_pow_sub_mul_sum_mul_pow_sub`), and `a₀ = 1`. By the uniqueness of the
coefficients of the relation (`chernClass_eq_of_sum_mul_pow_eq_zero`) the `aₖ` are the Chern
classes of `E₁ ⊕ E₂`.

The pull-back of such a relation along a map of projective bundles over the identity of `B` that
preserves the tautological class adapts a step of the proof of
`chernClass_eq_singularCohomologyMap_of_projectiveBundle` to bundles of different ranks.

## Main results

* `singularCohomologyMap_inl_projectiveBundleClass`,
  `singularCohomologyMap_inr_projectiveBundleClass`: `inl` and `inr` pull the tautological class
  of `E₁ ⊕ E₂` back to those of `E₁` and `E₂`.
* `ProjectiveBundle.evenIntegralCohomologyMap_subtypeVal_compl_range_inr_eq_zero` and
  `ProjectiveBundle.evenIntegralCohomologyMap_subtypeVal_compl_range_inl_eq_zero`: a class of
  `P(E₁ ⊕ E₂)` whose pull-back along `inl` (along `inr`) vanishes restricts to zero on the
  complement of the range of `inr` (of `inl`).
* `chernClass_prod`: `c_k(E₁ ⊕ E₂) = ∑_{i ≤ k} cᵢ(E₁) ⌣ c_{k-i}(E₂)`.
* `totalChernClass_prod`: the **Whitney sum formula** `c(E₁ ⊕ E₂) = c(E₁) c(E₂)`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §3.1 (the proof of the Whitney sum formula in
  Theorem 3.2, by the product of the two relations on the projective bundle of the sum).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the Whitney
  product formula).
-/

public section

noncomputable section

open Bundle Module TauCeti CategoryTheory Set

namespace SymplecticGeometry.Bundle

variable {B : Type} [TopologicalSpace B]
  {G₁ : Type} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
  {E₁ : B → Type} [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℂ (E₁ b)] [∀ b, Module ℝ (E₁ b)]
  [∀ b, IsScalarTower ℝ ℂ (E₁ b)] [∀ b, TopologicalSpace (E₁ b)]
  [TopologicalSpace (TotalSpace G₁ E₁)] [FiberBundle G₁ E₁] [VectorBundle ℂ G₁ E₁]
  {G₂ : Type} [NormedAddCommGroup G₂] [NormedSpace ℂ G₂]
  {E₂ : B → Type} [∀ b, AddCommGroup (E₂ b)] [∀ b, Module ℂ (E₂ b)] [∀ b, Module ℝ (E₂ b)]
  [∀ b, IsScalarTower ℝ ℂ (E₂ b)] [∀ b, TopologicalSpace (E₂ b)]
  [TopologicalSpace (TotalSpace G₂ E₂)] [FiberBundle G₂ E₂] [VectorBundle ℂ G₂ E₂]

/-! ### The tautological class on the summands -/

/-- The embedding `inl : P(E₁) → P(E₁ ⊕ E₂)` pulls the tautological class of `E₁ ⊕ E₂` back to
that of `E₁`. -/
theorem singularCohomologyMap_inl_projectiveBundleClass :
    TopCat.singularCohomologyMap
        (TopCat.ofHom (ProjectiveBundle.inl G₂ E₂ : C(ProjectiveBundle ℂ G₁ E₁, _))) 2
        (projectiveBundleClass (G₁ × G₂) (E₁ ×ᵇ E₂)) = projectiveBundleClass G₁ E₁ :=
  singularCohomologyMap_projectiveBundleClass_of_fiberwise
    (φ := ProjectiveBundle.tautologicalInlEquiv G₂ E₂)
    ((Pullback.continuous_lift _ _ _).comp ProjectiveBundle.continuous_tautologicalInlEquiv)

/-- The embedding `inr : P(E₂) → P(E₁ ⊕ E₂)` pulls the tautological class of `E₁ ⊕ E₂` back to
that of `E₂`. -/
theorem singularCohomologyMap_inr_projectiveBundleClass :
    TopCat.singularCohomologyMap
        (TopCat.ofHom (ProjectiveBundle.inr G₁ E₁ : C(ProjectiveBundle ℂ G₂ E₂, _))) 2
        (projectiveBundleClass (G₁ × G₂) (E₁ ×ᵇ E₂)) = projectiveBundleClass G₂ E₂ :=
  singularCohomologyMap_projectiveBundleClass_of_fiberwise
    (φ := ProjectiveBundle.tautologicalInrEquiv G₁ E₁)
    ((Pullback.continuous_lift _ _ _).comp ProjectiveBundle.continuous_tautologicalInrEquiv)

/-! ### Classes vanishing on the summands -/

namespace ProjectiveBundle

omit [∀ b, Module ℝ (E₁ b)] [∀ b, Module ℝ (E₂ b)] [∀ b, IsScalarTower ℝ ℂ (E₁ b)]
  [∀ b, IsScalarTower ℝ ℂ (E₂ b)]

/-- A class of `P(E₁ ⊕ E₂)` whose pull-back along `inl` vanishes restricts to zero on the
complement of the range of `inr`, which deformation retracts onto the range of `inl`. -/
theorem evenIntegralCohomologyMap_subtypeVal_compl_range_inr_eq_zero
    {y : (TopCat.of (ProjectiveBundle ℂ (G₁ × G₂) (E₁ ×ᵇ E₂))).EvenIntegralCohomology}
    (hy : TopCat.evenIntegralCohomologyMap
      (TopCat.ofHom (inl G₂ E₂ : C(ProjectiveBundle ℂ G₁ E₁, _))) y = 0) :
    TopCat.evenIntegralCohomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal
      (range (inr G₁ E₁ : C(ProjectiveBundle ℂ G₂ E₂, _)))ᶜ)) y = 0 := by
  have hH := (ContinuousMap.Homotopic.refl (ContinuousMap.subtypeVal
    (range (inr G₁ E₁ : C(ProjectiveBundle ℂ G₂ E₂, _)))ᶜ)).comp
    (homotopic_inlCompl_comp_inlRetraction (𝕜 := ℂ) (E₁ := E₁) (E₂ := E₂))
  rw [ContinuousMap.comp_id] at hH
  obtain ⟨H⟩ := hH
  have hH' : TopCat.ofHom ((ContinuousMap.subtypeVal _).comp ((inlCompl G₂ E₂).comp
        inlRetraction)) =
      TopCat.ofHom (inlRetraction (G₁ := G₁) (E₁ := E₁) (G₂ := G₂) (E₂ := E₂) (𝕜 := ℂ)) ≫
        TopCat.ofHom (inl G₂ E₂ : C(ProjectiveBundle ℂ G₁ E₁, _)) :=
    TopCat.ext fun p ↦ coe_inlCompl_apply (inlRetraction p)
  refine DFinsupp.ext fun k ↦ ?_
  have hk := congrArg (· k) hy
  simp only [TopCat.evenIntegralCohomologyMap_apply, DirectSum.zero_apply] at hk ⊢
  rw [← TopCat.Homotopy.congr_singularCohomologyMap (f := TopCat.ofHom _)
      (g := TopCat.ofHom (ContinuousMap.subtypeVal _)) H, hH',
    TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply, hk, map_zero]

/-- A class of `P(E₁ ⊕ E₂)` whose pull-back along `inr` vanishes restricts to zero on the
complement of the range of `inl`: exchanging the summands reduces this to
`evenIntegralCohomologyMap_subtypeVal_compl_range_inr_eq_zero`. -/
theorem evenIntegralCohomologyMap_subtypeVal_compl_range_inl_eq_zero
    {y : (TopCat.of (ProjectiveBundle ℂ (G₁ × G₂) (E₁ ×ᵇ E₂))).EvenIntegralCohomology}
    (hy : TopCat.evenIntegralCohomologyMap
      (TopCat.ofHom (inr G₁ E₁ : C(ProjectiveBundle ℂ G₂ E₂, _))) y = 0) :
    TopCat.evenIntegralCohomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal
      (range (inl G₂ E₂ : C(ProjectiveBundle ℂ G₁ E₁, _)))ᶜ)) y = 0 := by
  -- The class `y` read on `P(E₂ ⊕ E₁)`.
  let σ : C(ProjectiveBundle ℂ (G₂ × G₁) (E₂ ×ᵇ E₁), ProjectiveBundle ℂ (G₁ × G₂) (E₁ ×ᵇ E₂)) :=
    ⟨prodComm, prodComm.continuous⟩
  set y' := TopCat.evenIntegralCohomologyMap (TopCat.ofHom σ) y
  have hσ : TopCat.ofHom (inl G₁ E₁ : C(ProjectiveBundle ℂ G₂ E₂, _)) ≫ TopCat.ofHom σ =
      TopCat.ofHom (inr G₁ E₁) :=
    TopCat.ext fun p ↦ prodComm_inl p
  have hy' : TopCat.evenIntegralCohomologyMap
      (TopCat.ofHom (inl G₁ E₁ : C(ProjectiveBundle ℂ G₂ E₂, _))) y' = 0 := by
    rw [← RingHom.comp_apply, ← TopCat.evenIntegralCohomologyMap_comp, hσ, hy]
  have h := evenIntegralCohomologyMap_subtypeVal_compl_range_inr_eq_zero hy'
  -- `prodComm` carries the complement of the range of `inl` into that of the range of `inr`.
  have hmaps : MapsTo (prodComm : ProjectiveBundle ℂ (G₁ × G₂) (E₁ ×ᵇ E₂) ≃ₜ _)
      (range (inl G₂ E₂ : C(ProjectiveBundle ℂ G₁ E₁, _)))ᶜ
      (range (inr G₂ E₂ : C(ProjectiveBundle ℂ G₁ E₁, _)))ᶜ := by
    rintro p hp ⟨q, hq⟩
    exact hp ⟨q, prodComm.injective ((prodComm_inl q).trans hq)⟩
  let ρ : C(((range (inl G₂ E₂ : C(ProjectiveBundle ℂ G₁ E₁, _)))ᶜ : Set _),
      ((range (inr G₂ E₂ : C(ProjectiveBundle ℂ G₁ E₁, _)))ᶜ : Set _)) :=
    ⟨hmaps.restrict, (prodComm.continuous.comp continuous_subtypeVal).subtype_mk _⟩
  have hρ : TopCat.ofHom ρ ≫ TopCat.ofHom (ContinuousMap.subtypeVal _) ≫ TopCat.ofHom σ =
      TopCat.ofHom (ContinuousMap.subtypeVal _) :=
    TopCat.ext fun p ↦ (congrArg (fun e ↦ e (prodComm p.val)) prodComm_symm).symm.trans
      (prodComm.symm_apply_apply p.val)
  rw [← hρ, TopCat.evenIntegralCohomologyMap_comp, TopCat.evenIntegralCohomologyMap_comp,
    RingHom.comp_apply, RingHom.comp_apply, h, map_zero]

end ProjectiveBundle

/-! ### The Whitney sum formula -/

/-- The ring map of `g : P' → P` sends the left side of a relation of the form of the defining
relation of the Chern classes on `P` to the same on `P'`, when `g` lies over the identity of the
base and pulls the tautological class back to the tautological class. -/
private theorem evenIntegralCohomologyMap_sum_mul_pow
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {E : B → Type} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, Module ℝ (E b)]
    [∀ b, IsScalarTower ℝ ℂ (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace G E)] [FiberBundle G E] [VectorBundle ℂ G E]
    {G' : Type} [NormedAddCommGroup G'] [NormedSpace ℂ G']
    {E' : B → Type} [∀ b, AddCommGroup (E' b)] [∀ b, Module ℂ (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, IsScalarTower ℝ ℂ (E' b)] [∀ b, TopologicalSpace (E' b)]
    [TopologicalSpace (TotalSpace G' E')] [FiberBundle G' E'] [VectorBundle ℂ G' E']
    (g : C(ProjectiveBundle ℂ G' E', ProjectiveBundle ℂ G E))
    (hπ : (ProjectiveBundle.projection ℂ G E).comp g = ProjectiveBundle.projection ℂ G' E')
    (hx : TopCat.singularCohomologyMap (TopCat.ofHom g) 2 (projectiveBundleClass G E) =
      projectiveBundleClass G' E')
    (a : ∀ k : ℕ, (TopCat.of B).integralCohomology (2 * k)) (n : ℕ) :
    TopCat.evenIntegralCohomologyMap (TopCat.ofHom g)
        (∑ i ∈ Finset.range (n + 1),
          TopCat.evenIntegralCohomologyMap (TopCat.ofHom (ProjectiveBundle.projection ℂ G E))
            ((TopCat.of B).evenIntegralCohomologyOf i (a i)) *
          (TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
            (projectiveBundleClass G E) ^ (n - i)) =
      ∑ i ∈ Finset.range (n + 1),
        TopCat.evenIntegralCohomologyMap (TopCat.ofHom (ProjectiveBundle.projection ℂ G' E'))
          ((TopCat.of B).evenIntegralCohomologyOf i (a i)) *
        (TopCat.of (ProjectiveBundle ℂ G' E')).evenIntegralCohomologyOf 1
          (projectiveBundleClass G' E') ^ (n - i) := by
  have hx' : TopCat.evenIntegralCohomologyMap (TopCat.ofHom g)
      ((TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
        (projectiveBundleClass G E)) =
      (TopCat.of (ProjectiveBundle ℂ G' E')).evenIntegralCohomologyOf 1
        (projectiveBundleClass G' E') := by
    rw [TopCat.evenIntegralCohomologyMap_of]
    -- `evenIntegralCohomologyMap_of` pulls back in degree `2 * 1`, which `hx` writes `2`.
    exact congrArg _ hx
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow, hx', ← RingHom.comp_apply, ← TopCat.evenIntegralCohomologyMap_comp,
    ← TopCat.ofHom_comp, hπ]

variable (G₁ E₁ G₂ E₂) in
/-- The Cauchy product `k ↦ ∑_{i ≤ k} cᵢ(E₁) ⌣ c_{k-i}(E₂)` of the Chern classes of `E₁` and
`E₂`, in degree `2k`. -/
private abbrev chernClassCauchy (k : ℕ) : (TopCat.of B).integralCohomology (2 * k) :=
  ∑ i : Fin (k + 1), (TopCat.of B).integralCup (2 * i) (2 * (k - i)) (2 * k) (by omega)
    (chernClass G₁ E₁ i) (chernClass G₂ E₂ (k - i))

/-- In the even integral cohomology ring, the Cauchy product of the Chern classes is the sum of
the products `cᵢ(E₁) c_{k-i}(E₂)`. -/
private theorem evenIntegralCohomologyOf_chernClassCauchy (k : ℕ) :
    (TopCat.of B).evenIntegralCohomologyOf k (chernClassCauchy G₁ E₁ G₂ E₂ k) =
      ∑ i ∈ Finset.range (k + 1),
        (TopCat.of B).evenIntegralCohomologyOf i (chernClass G₁ E₁ i) *
          (TopCat.of B).evenIntegralCohomologyOf (k - i) (chernClass G₂ E₂ (k - i)) := by
  rw [map_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [TopCat.evenIntegralCohomologyOf_mul]
  exact DirectSum.of_eq_of_gradedMonoid_eq
    (Sigma.ext (Nat.add_sub_cancel' (Nat.le_of_lt_succ i.isLt)).symm
      (TopCat.integralCup_heq _ _ _ _ _))

/-- The product of the classes `∑_{i ≤ nₗ} cᵢ(Eₗ) x^{nₗ-i}`, `l = 1, 2`, in a ring map from the
even integral cohomology ring of `B`, is `∑_{k ≤ n₁+n₂} aₖ x^{n₁+n₂-k}`, where `aₖ` is the Cauchy
product of the Chern classes. -/
private theorem sum_mul_pow_mul_sum_mul_pow {R : Type*} [CommRing R]
    (φ : (TopCat.of B).EvenIntegralCohomology →+* R) (x : R) :
    (∑ i ∈ Finset.range (finrank ℂ G₁ + 1),
        φ ((TopCat.of B).evenIntegralCohomologyOf i (chernClass G₁ E₁ i)) *
          x ^ (finrank ℂ G₁ - i)) *
      (∑ j ∈ Finset.range (finrank ℂ G₂ + 1),
        φ ((TopCat.of B).evenIntegralCohomologyOf j (chernClass G₂ E₂ j)) *
          x ^ (finrank ℂ G₂ - j)) =
      ∑ k ∈ Finset.range (finrank ℂ G₁ + finrank ℂ G₂ + 1),
        φ ((TopCat.of B).evenIntegralCohomologyOf k (chernClassCauchy G₁ E₁ G₂ E₂ k)) *
          x ^ (finrank ℂ G₁ + finrank ℂ G₂ - k) := by
  rw [Finset.sum_mul_pow_sub_mul_sum_mul_pow_sub x
    (fun i hi ↦ by rw [chernClass_eq_zero_of_finrank_lt G₁ E₁ hi, map_zero, map_zero])
    (fun j hj ↦ by rw [chernClass_eq_zero_of_finrank_lt G₂ E₂ hj, map_zero, map_zero])]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [evenIntegralCohomologyOf_chernClassCauchy, map_sum]
  simp only [map_mul]

variable [FiniteDimensional ℂ G₁] [FiniteDimensional ℂ G₂] [CompactSpace B]

/-- The Cauchy product of the Chern classes satisfies the defining relation of the Chern classes
of `E₁ ⊕ E₂`. -/
private theorem sum_chernClassCauchy_mul_pow_eq_zero :
    ∑ i ∈ Finset.range (finrank ℂ (G₁ × G₂) + 1),
        TopCat.evenIntegralCohomologyMap
            (TopCat.ofHom (ProjectiveBundle.projection ℂ (G₁ × G₂) (E₁ ×ᵇ E₂)))
          ((TopCat.of B).evenIntegralCohomologyOf i (chernClassCauchy G₁ E₁ G₂ E₂ i)) *
        (TopCat.of (ProjectiveBundle ℂ (G₁ × G₂) (E₁ ×ᵇ E₂))).evenIntegralCohomologyOf 1
          (projectiveBundleClass (G₁ × G₂) (E₁ ×ᵇ E₂)) ^ (finrank ℂ (G₁ × G₂) - i) = 0 := by
  set P := TopCat.of (ProjectiveBundle ℂ (G₁ × G₂) (E₁ ×ᵇ E₂))
  set φ := TopCat.evenIntegralCohomologyMap
    (TopCat.ofHom (ProjectiveBundle.projection ℂ (G₁ × G₂) (E₁ ×ᵇ E₂)))
  set x := P.evenIntegralCohomologyOf 1 (projectiveBundleClass (G₁ × G₂) (E₁ ×ᵇ E₂))
  rw [Module.finrank_prod, ← sum_mul_pow_mul_sum_mul_pow φ x]
  refine TopCat.evenIntegralCohomology_mul_eq_zero_of_union_eq_univ
    (ProjectiveBundle.isClosedEmbedding_inr.isClosed_range.isOpen_compl)
    (ProjectiveBundle.isClosedEmbedding_inl.isClosed_range.isOpen_compl) ?_
    (ProjectiveBundle.evenIntegralCohomologyMap_subtypeVal_compl_range_inr_eq_zero ?_)
    (ProjectiveBundle.evenIntegralCohomologyMap_subtypeVal_compl_range_inl_eq_zero ?_)
  · rw [← compl_inter, (ProjectiveBundle.disjoint_range_inl_inr).symm.inter_eq, compl_empty]
  · rw [evenIntegralCohomologyMap_sum_mul_pow _ (ContinuousMap.ext fun _ ↦ rfl)
      singularCohomologyMap_inl_projectiveBundleClass]
    exact sum_chernClass_mul_projectiveBundleClass_pow G₁ E₁
  · rw [evenIntegralCohomologyMap_sum_mul_pow _ (ContinuousMap.ext fun _ ↦ rfl)
      singularCohomologyMap_inr_projectiveBundleClass]
    exact sum_chernClass_mul_projectiveBundleClass_pow G₂ E₂

/-- **The Whitney sum formula in degree `2k`.** Over a compact base,
`c_k(E₁ ⊕ E₂) = ∑_{i ≤ k} cᵢ(E₁) ⌣ c_{k-i}(E₂)`. -/
theorem chernClass_prod (k : ℕ) :
    chernClass (G₁ × G₂) (E₁ ×ᵇ E₂) k =
      ∑ i : Fin (k + 1), (TopCat.of B).integralCup (2 * i) (2 * (k - i)) (2 * k) (by omega)
        (chernClass G₁ E₁ i) (chernClass G₂ E₂ (k - i)) := by
  -- The right side is `chernClassCauchy` written out.
  change _ = chernClassCauchy G₁ E₁ G₂ E₂ k
  rcases le_or_gt k (finrank ℂ (G₁ × G₂)) with hk | hk
  · refine (chernClass_eq_of_sum_mul_pow_eq_zero _ _ _ ?_
      sum_chernClassCauchy_mul_pow_eq_zero hk).symm
    rw [chernClassCauchy, Fin.sum_univ_one]
    simp only [Fin.val_zero, Nat.sub_zero, chernClass_zero]
    exact TopCat.integralCup_integralCohomologyOne _ _ _
  · rw [chernClass_eq_zero_of_finrank_lt _ _ hk]
    rw [Module.finrank_prod] at hk
    refine (Finset.sum_eq_zero fun i _ ↦ ?_).symm
    rcases le_or_gt (i : ℕ) (finrank ℂ G₁) with hi | hi
    · rw [chernClass_eq_zero_of_finrank_lt G₂ E₂ (by omega), map_zero]
    · rw [chernClass_eq_zero_of_finrank_lt G₁ E₁ hi, map_zero, LinearMap.zero_apply]

/-- **The Whitney sum formula.** Over a compact base, the total Chern class of a direct sum is the
product of the total Chern classes: `c(E₁ ⊕ E₂) = c(E₁) c(E₂)`. -/
theorem totalChernClass_prod :
    totalChernClass (G₁ × G₂) (E₁ ×ᵇ E₂) = totalChernClass G₁ E₁ * totalChernClass G₂ E₂ := by
  have h := sum_mul_pow_mul_sum_mul_pow (G₁ := G₁) (E₁ := E₁) (G₂ := G₂) (E₂ := E₂)
    (RingHom.id _) 1
  simp only [one_pow, mul_one, RingHom.id_apply] at h
  rw [totalChernClass_def, totalChernClass_def, totalChernClass_def, h, Module.finrank_prod]
  exact Finset.sum_congr rfl fun k _ ↦ congrArg _ (chernClass_prod k)

end SymplecticGeometry.Bundle

end
