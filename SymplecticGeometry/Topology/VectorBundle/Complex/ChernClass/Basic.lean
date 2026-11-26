/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.Empty
public import SymplecticGeometry.AlgebraicTopology.Cohomology.LerayHirsch.Bundle
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace

/-!
# Chern classes

For a complex vector bundle `E` over `B` with model `G`, of rank `n = finrank ℂ G`, let
`π : P(E) → B` be its projective bundle and `x ∈ H²(P(E); ℤ)` the tautological class, minus the
Euler class of the tautological line (`SymplecticGeometry.Bundle.projectiveBundleClass`). On the
fibre over each point it restricts to the hyperplane class of `ℙ ℂ G`, so by the Leray–Hirsch
theorem every class of `P(E)` is uniquely `∑_{i < n} π^* aᵢ ⌣ xⁱ` when `B` is compact. The Chern
classes `c_k(E) ∈ H^{2k}(B; ℤ)` are the coefficients for which `c₀(E) = 1` and
`∑_{i ≤ n} π^* cᵢ(E) ⌣ x^{n-i} = 0`, and `c_k(E) = 0` for `k > n`. This is Grothendieck's
definition, in the normalization of Bott–Tu, §20: for a line bundle `c₁` is the Euler class.

## Main definitions

* `SymplecticGeometry.Bundle.projectiveBundleClass G E`: the tautological class `x`.
* `SymplecticGeometry.Bundle.projectiveBundleClassPow G E`: the powers `xⁱ`, `i < n`, indexed
  by degree, the classes of the Leray–Hirsch theorem.
* `SymplecticGeometry.Bundle.chernClass G E k`: the Chern class `c_k(E)`, with `chernClass_def`.
* `SymplecticGeometry.Bundle.totalChernClass G E`: the total Chern class `∑_{k ≤ n} c_k(E)` in the
  even integral cohomology ring, with `totalChernClass_def` and `totalChernClass_apply`; it is `1`
  in rank zero and `1 + c₁(E)` in rank one (`totalChernClass_eq_one_of_finrank_eq_zero`,
  `totalChernClass_eq_one_add_of_finrank_eq_one`). When it is `1`, the Chern classes of positive
  degree vanish (`chernClass_eq_zero_of_totalChernClass_eq_one`).

## Main results

* `singularCohomologyMap_fiberInclusionMap_projectiveBundleClass`: `x` restricts on each fibre,
  read through the trivialization there, to `Projectivization.hyperplaneClass G`.
* `bijective_integralLerayHirsch_projectiveBundle`: the Leray–Hirsch theorem for `P(E)` over a
  compact base, for `E` of finite rank.
* `sum_mul_projectiveBundleClass_pow_eq_zero_iff`: over a compact base, classes `aₖ` with
  `a₀ = 1` satisfy the relation `∑_{i ≤ n} π^* aᵢ ⌣ x^{n-i} = 0` exactly when they are the
  Chern classes; hence `sum_chernClass_mul_projectiveBundleClass_pow`, the defining relation,
  and `chernClass_eq_of_sum_mul_pow_eq_zero`, the uniqueness.
* `injective_projectiveBundle_proj`: `π^*` is injective in every degree, over a compact base
  and for `E` of positive rank.
* `chernClass_zero`, `chernClass_eq_zero_of_finrank_lt`, and
  `chernClass_one_eq_complexEulerClass`: `c₀(E) = 1`, `c_k(E) = 0` for `k > n`, and `c₁` of a
  line bundle over a compact base is its Euler class `TauCeti.complexEulerClass`, read in
  integral cohomology through `TopCat.uliftIntegralCohomologyIso`.
* `Projectivization.chernClass_one_tautological`: on a finite-dimensional complex projective
  space, `c₁(𝒪(-1)) = -h`, with `h` the hyperplane class.

## Implementation notes

The classes take values in Tau Ceti's `TopCat.integralCohomology`, and the relation is written in
the even integral cohomology ring `TopCat.EvenIntegralCohomology`, where `x` has index `1`. The
definition of `chernClass` needs no hypothesis on `B`: where the Leray–Hirsch map in degree `2n`
is not bijective, the classes of positive degree are `0`. The restriction of `x` to a fibre is
computed by the naturality of the Euler class
(`TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise`), as in
`Projectivization.hyperplaneClass_map`: the fibre inclusion acts on lines by Tau Ceti's
`ContinuousLinearEquiv.mapProjectivization` of the trivialization, and the fibrewise isomorphisms
of tautological lines are its restrictions `ContinuousLinearEquiv.ofSubmodules`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the
  tautological class of the projective bundle, the Leray–Hirsch theorem and the definition of the
  Chern classes by the relation of the tautological class).
* A. Hatcher, *Vector Bundles and K-Theory*, §3.1 (the proof of Theorem 3.2: the construction
  of the Chern classes by the projective bundle and the Leray–Hirsch theorem).
-/

public section

noncomputable section

open Bundle Module TauCeti CategoryTheory Limits MonoidalCategory
open scoped LinearAlgebra.Projectivization DirectSum

namespace SymplecticGeometry.Bundle

variable {B : Type} [TopologicalSpace B]
  (G : Type) [NormedAddCommGroup G] [NormedSpace ℂ G]
  (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsScalarTower ℝ ℂ (E b)] [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle ℂ G E]

/-- The **tautological class** `x ∈ H²(P(E); ℤ)` of the projective bundle of a complex vector
bundle `E`: minus the Euler class of the tautological line, read in integral cohomology. It is the
first Chern class of the dual of the tautological line, in the normalization of Bott–Tu, §20. -/
def projectiveBundleClass : (TopCat.of (ProjectiveBundle ℂ G E)).integralCohomology 2 :=
  -((TopCat.of (ProjectiveBundle ℂ G E)).uliftIntegralCohomologyIso 2).hom
    (complexEulerClass (r := 0) ℂ (ProjectiveBundle.Tautological ℂ G E) (finrank_self ℂ))

theorem projectiveBundleClass_def :
    projectiveBundleClass G E =
      -((TopCat.of (ProjectiveBundle ℂ G E)).uliftIntegralCohomologyIso 2).hom
        (complexEulerClass (r := 0) ℂ (ProjectiveBundle.Tautological ℂ G E) (finrank_self ℂ)) :=
  (rfl)

/-- The inclusion of the fibre over `b` of the projective bundle, read through the trivialization
at `b`, pulls the tautological class back to the hyperplane class of `ℙ ℂ G`. -/
theorem singularCohomologyMap_fiberInclusionMap_projectiveBundleClass (b : B) :
    TopCat.singularCohomologyMap
        (TopCat.ofHom ((trivializationAt (ℙ ℂ G) (fun b ↦ ℙ ℂ (E b)) b).fiberInclusionMap
          (mem_baseSet_trivializationAt _ _ b)))
        2 (projectiveBundleClass G E) = Projectivization.hyperplaneClass G := by
  set e := trivializationAt G E b
  have hb : b ∈ e.baseSet := mem_baseSet_trivializationAt G E b
  set L := (e.continuousLinearEquivAt ℂ b hb).symm
  let := VectorBundle.isTopologicalAddGroup ℂ G E b
  let := VectorBundle.continuousSMul ℂ G E b
  let := FiberBundle.t2Space G E b
  have hcont : Continuous fun ℓ : ℙ ℂ G ↦
      (⟨b, L.mapProjectivization ℓ⟩ : ProjectiveBundle ℂ G E) := by
    refine ((trivializationAt (ℙ ℂ G) (fun b ↦ ℙ ℂ (E b)) b).fiberInclusionMap
      (mem_baseSet_trivializationAt _ _ b)).continuous.congr fun ℓ ↦ ?_
    rw [Trivialization.fiberInclusionMap_apply, ProjectiveBundle.trivializationAt_symm_apply hb]
  let g : C(ℙ ℂ G, ProjectiveBundle ℂ G E) := ⟨_, hcont⟩
  have hg : TopCat.ofHom ((trivializationAt (ℙ ℂ G) (fun b ↦ ℙ ℂ (E b)) b).fiberInclusionMap
      (mem_baseSet_trivializationAt _ _ b)) = TopCat.ofHom g := by
    refine TopCat.ext fun ℓ ↦ ?_
    rw [ConcreteCategory.hom_ofHom, ConcreteCategory.hom_ofHom,
      Trivialization.fiberInclusionMap_apply, ProjectiveBundle.trivializationAt_symm_apply hb,
      ContinuousMap.coe_mk]
  have h := complexEulerClass_eq_singularCohomologyMap_of_fiberwise (r := 0) (finrank_self ℂ)
    (finrank_self ℂ) (g := g) (E := ProjectiveBundle.Tautological ℂ G E)
    (E' := Projectivization.Tautological ℂ G)
    (φ := fun ℓ ↦ L.ofSubmodules ℓ.submodule (L.mapProjectivization ℓ).submodule
      (by rw [ContinuousLinearEquiv.coe_mapProjectivization, Projectivization.submodule_map]))
    ?_
  · rw [hg, projectiveBundleClass_def, Projectivization.hyperplaneClass_def, map_neg, h]
    exact congrArg _ (TopCat.uliftIntegralCohomologyIso_naturality_apply _ 2 _).symm
  · refine ProjectiveBundle.continuous_totalSpace_tautological_iff.2
      ⟨hcont.comp (Projectivization.continuous_proj_tautological ℂ G), ?_⟩
    have hs := e.continuousOn_symm.comp_continuous
      (continuous_const.prodMk (Projectivization.continuous_snd_tautological ℂ G))
      (fun v ↦ Set.mk_mem_prod hb (Set.mem_univ _))
    refine hs.congr fun v ↦ ?_
    have hL (w : G) : L w = e.symm b w := congrFun (e.continuousLinearEquivAt_symm_apply ℂ b hb) w
    exact congrArg (TotalSpace.mk' G b) ((hL _).symm.trans
      (L.ofSubmodules_apply _ v.snd).symm)

/-! ### The Leray–Hirsch classes -/

/-- The powers `xⁱ ∈ H^{2i}(P(E); ℤ)` of the tautological class, for `i < finrank ℂ G`, indexed
by degree as the Leray–Hirsch theorem takes them: in degree `d`, by the `i` with `2 * i = d`. -/
def projectiveBundleClassPow :
    ∀ d : ℕ, {i : Fin (finrank ℂ G) // 2 * (i : ℕ) = d} →
      (TopCat.of (ProjectiveBundle ℂ G E)).integralCohomology d
  | _, ⟨i, rfl⟩ => ((TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
      (projectiveBundleClass G E) ^ (i : ℕ)) i

theorem projectiveBundleClassPow_mk (i : Fin (finrank ℂ G)) :
    projectiveBundleClassPow G E (2 * i) ⟨i, rfl⟩ =
      ((TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
        (projectiveBundleClass G E) ^ (i : ℕ)) i :=
  (rfl)

/-- On the fibre over each point, read through the trivialization there, the powers of the
tautological class form a basis of the integral cohomology of `ℙ ℂ G` in every degree. -/
private theorem basis_fiberInclusionMap_projectiveBundleClassPow {m : ℕ}
    (hm : finrank ℂ G = m + 1) (b : B) (d : ℕ) :
    LinearIndependent ℤ (fun i ↦ TopCat.singularCohomologyMap
        (TopCat.ofHom ((trivializationAt (ℙ ℂ G) (fun b ↦ ℙ ℂ (E b)) b).fiberInclusionMap
          (mem_baseSet_trivializationAt _ _ b))) d (projectiveBundleClassPow G E d i)) ∧
      ⊤ ≤ Submodule.span ℤ (Set.range fun i ↦ TopCat.singularCohomologyMap
        (TopCat.ofHom ((trivializationAt (ℙ ℂ G) (fun b ↦ ℙ ℂ (E b)) b).fiberInclusionMap
          (mem_baseSet_trivializationAt _ _ b))) d (projectiveBundleClassPow G E d i)) := by
  by_cases hd : ∃ i : Fin (finrank ℂ G), 2 * (i : ℕ) = d
  · obtain ⟨i, rfl⟩ := hd
    let : Unique {j : Fin (finrank ℂ G) // 2 * (j : ℕ) = 2 * i} :=
      { default := ⟨i, rfl⟩
        uniq := fun j ↦ Subtype.ext (Fin.ext (Nat.eq_of_mul_eq_mul_left two_pos j.property)) }
    set v := ((TopCat.of (ℙ ℂ G)).evenIntegralCohomologyOf 1
      (Projectivization.hyperplaneClass G) ^ (i : ℕ)) i
    have hv (j) : TopCat.singularCohomologyMap
        (TopCat.ofHom ((trivializationAt (ℙ ℂ G) (fun b ↦ ℙ ℂ (E b)) b).fiberInclusionMap
          (mem_baseSet_trivializationAt _ _ b))) (2 * i) (projectiveBundleClassPow G E _ j) =
        v := by
      rw [Unique.eq_default j]
      -- `default` is `⟨i, rfl⟩` by the definition of the `Unique` instance.
      change TopCat.singularCohomologyMap _ (2 * i) (projectiveBundleClassPow G E _ ⟨i, rfl⟩) = v
      rw [projectiveBundleClassPow_mk, ← TopCat.evenIntegralCohomologyMap_apply, map_pow,
        TopCat.evenIntegralCohomologyMap_of,
        singularCohomologyMap_fiberInclusionMap_projectiveBundleClass]
    have hbij := Projectivization.bijective_zsmul_hyperplaneClass_pow hm (k := i) (by omega)
    have hbij' : Function.Bijective (LinearMap.toSpanSingleton ℤ _ v) := by
      convert hbij using 1
      funext m
      rw [LinearMap.toSpanSingleton_apply]
      exact int_smul_eq_zsmul _ m v
    let e := LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ _ v) hbij'
    let c := (Module.Basis.singleton {j : Fin (finrank ℂ G) // 2 * (j : ℕ) = 2 * i} ℤ).map e
    have hc : ⇑c = fun j ↦ TopCat.singularCohomologyMap
        (TopCat.ofHom ((trivializationAt (ℙ ℂ G) (fun b ↦ ℙ ℂ (E b)) b).fiberInclusionMap
          (mem_baseSet_trivializationAt _ _ b))) (2 * i) (projectiveBundleClassPow G E _ j) := by
      funext j
      rw [hv, Module.Basis.map_apply, Module.Basis.singleton_apply, LinearEquiv.ofBijective_apply,
        LinearMap.toSpanSingleton_apply]
      exact (int_smul_eq_zsmul _ 1 v).trans (one_zsmul v)
    rw [← hc]
    exact ⟨c.linearIndependent, c.span_eq.ge⟩
  · have hz : IsZero ((TopCat.of (ℙ ℂ G)).integralCohomology d) := by
      rcases Nat.even_or_odd d with ⟨j, rfl⟩ | hodd
      · refine Projectivization.isZero_integralCohomology_of_lt hm ?_
        by_contra hj
        exact hd ⟨⟨j, by omega⟩, by simp only; omega⟩
      · exact Projectivization.isZero_integralCohomology_of_odd hm hodd
    have : IsEmpty {i : Fin (finrank ℂ G) // 2 * (i : ℕ) = d} := ⟨fun i ↦ hd ⟨i.val, i.property⟩⟩
    have := ModuleCat.subsingleton_of_isZero hz
    exact ⟨linearIndependent_empty_type, fun x _ ↦ Subsingleton.elim x 0 ▸ Submodule.zero_mem _⟩

/-- **The Leray–Hirsch theorem for the projective bundle.** Over a compact base, for `E` of
finite rank, the integral Leray–Hirsch map of the projection `P(E) → B` and the powers
`xⁱ`, `i < finrank ℂ G`, of the tautological class is bijective in every degree: every class of
`P(E)` is uniquely `∑ π^* aᵢ ⌣ xⁱ`. In rank zero both sides are zero, since `P(E)` is empty. -/
theorem bijective_integralLerayHirsch_projectiveBundle [CompactSpace B] [FiniteDimensional ℂ G]
    (n : ℕ) :
    Function.Bijective (TopCat.integralLerayHirsch
      (TopCat.ofHom (ProjectiveBundle.projection ℂ G E)) n (projectiveBundleClassPow G E)) := by
  rcases Nat.eq_zero_or_pos (finrank ℂ G) with hG | hG
  · -- In rank zero there are no powers `xⁱ`, and `P(E)` is empty.
    have := ProjectiveBundle.isEmpty_of_finrank_eq_zero (E := E) hG
    have : IsEmpty (Fin (finrank ℂ G)) := ⟨fun i ↦ by have := i.isLt; omega⟩
    exact ⟨fun x y _ ↦ DFinsupp.ext fun j ↦ isEmptyElim j.2.val,
      fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, finrank ℂ G = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hG).symm⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun b ↦ (trivializationAt (ℙ ℂ G) (fun b ↦ ℙ ℂ (E b)) b).baseSet)
    (fun b ↦ (trivializationAt (ℙ ℂ G) (fun b ↦ ℙ ℂ (E b)) b).open_baseSet)
    (fun b _ ↦ Set.mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt _ _ b⟩)
  have := Projectivization.projective_singularHomology (V := G) (𝟙_ (ModuleCat.{0} ℤ)) hm
  exact TopCat.integralLerayHirsch_bijective s (Set.univ_subset_iff.1 hs) n _
    (fun d _ ↦ TauCeti.finite_singularHomology_of_finiteCWType (ℙ ℂ G) _ d)
    fun y d _ ↦ basis_fiberInclusionMap_projectiveBundleClassPow G E hm y d

/-! ### The Chern classes -/

open Classical in
/-- The **Chern classes** `c_k(E) ∈ H^{2k}(B; ℤ)` of a complex vector bundle `E` with model `G`,
of rank `n = finrank ℂ G`, defined by the relation `∑_{i ≤ n} π^* cᵢ(E) ⌣ x^{n-i} = 0` on the
projective bundle (Bott–Tu, §20). For `1 ≤ k ≤ n`, when the Leray–Hirsch map of the powers
`xⁱ`, `i < n`, is bijective in degree `2n`, `c_k(E)` is the coefficient of `x^{n-k}` in the
decomposition of `-xⁿ`. Otherwise it is the component of degree `2k` of the unit: `c₀(E) = 1`,
and `c_k(E) = 0` for `k > n` and wherever the Leray–Hirsch map is not bijective. -/
def chernClass (k : ℕ) : (TopCat.of B).integralCohomology (2 * k) :=
  if h : 1 ≤ k ∧ k ≤ finrank ℂ G ∧ Function.Bijective (TopCat.integralLerayHirsch
      (TopCat.ofHom (ProjectiveBundle.projection ℂ G E)) (2 * finrank ℂ G)
      (projectiveBundleClassPow G E)) then
    (AddEquiv.ofBijective _ h.2.2).symm
      (-(((TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
        (projectiveBundleClass G E) ^ finrank ℂ G) (finrank ℂ G)))
      ⟨⟨(2 * (finrank ℂ G - k), 2 * k), by omega⟩, ⟨⟨finrank ℂ G - k, by omega⟩, rfl⟩⟩
  else (1 : (TopCat.of B).EvenIntegralCohomology) k

open Classical in
theorem chernClass_def (k : ℕ) :
    chernClass G E k =
      if h : 1 ≤ k ∧ k ≤ finrank ℂ G ∧ Function.Bijective (TopCat.integralLerayHirsch
          (TopCat.ofHom (ProjectiveBundle.projection ℂ G E)) (2 * finrank ℂ G)
          (projectiveBundleClassPow G E)) then
        (AddEquiv.ofBijective _ h.2.2).symm
          (-(((TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
            (projectiveBundleClass G E) ^ finrank ℂ G) (finrank ℂ G)))
          ⟨⟨(2 * (finrank ℂ G - k), 2 * k), by omega⟩, ⟨⟨finrank ℂ G - k, by omega⟩, rfl⟩⟩
      else (1 : (TopCat.of B).EvenIntegralCohomology) k :=
  (rfl)

/-- The **total Chern class** `c(E) = ∑_{k ≤ n} c_k(E)` of a complex vector bundle of rank `n`,
in the even integral cohomology ring of the base. -/
def totalChernClass : (TopCat.of B).EvenIntegralCohomology :=
  ∑ k ∈ Finset.range (finrank ℂ G + 1), (TopCat.of B).evenIntegralCohomologyOf k (chernClass G E k)

theorem totalChernClass_def :
    totalChernClass G E =
      ∑ k ∈ Finset.range (finrank ℂ G + 1),
        (TopCat.of B).evenIntegralCohomologyOf k (chernClass G E k) :=
  (rfl)

/-- The Chern class of degree zero is the unit class. -/
@[simp]
theorem chernClass_zero : chernClass G E 0 = (TopCat.of B).integralCohomologyOne := by
  rw [chernClass_def, dite_eq_right (by omega), ← TopCat.evenIntegralCohomologyOf_one,
    DirectSum.of_eq_same]

/-- The Chern classes above the rank vanish. -/
theorem chernClass_eq_zero_of_finrank_lt {k : ℕ} (hk : finrank ℂ G < k) :
    chernClass G E k = 0 := by
  rw [chernClass_def, dite_eq_right (by omega), ← TopCat.evenIntegralCohomologyOf_one]
  exact DirectSum.of_eq_of_ne _ _ _ (by omega)

/-- The component of degree `2k` of the total Chern class is `c_k(E)`, for every `k`: the
classes above the rank vanish. -/
@[simp]
theorem totalChernClass_apply (k : ℕ) : totalChernClass G E k = chernClass G E k := by
  rw [totalChernClass_def, DirectSum.sum_apply]
  rcases le_or_gt k (finrank ℂ G) with hk | hk
  · rw [Finset.sum_eq_single k (fun i _ hi ↦ DirectSum.of_eq_of_ne i k _ hi.symm)
      (fun h ↦ (h (Finset.mem_range.2 (by omega))).elim)]
    exact DirectSum.of_eq_same _ _
  · rw [chernClass_eq_zero_of_finrank_lt G E hk]
    exact Finset.sum_eq_zero fun i hi ↦
      DirectSum.of_eq_of_ne _ _ _ (by rw [Finset.mem_range] at hi; omega)

/-- The total Chern class of a bundle of rank zero is `1`. -/
theorem totalChernClass_eq_one_of_finrank_eq_zero (hG : finrank ℂ G = 0) :
    totalChernClass G E = 1 := by
  rw [totalChernClass_def, hG, Finset.sum_range_one, chernClass_zero,
    TopCat.evenIntegralCohomologyOf_one]

/-- If the total Chern class of a bundle is `1`, then its Chern classes of positive degree
vanish. -/
theorem chernClass_eq_zero_of_totalChernClass_eq_one (h : totalChernClass G E = 1) {k : ℕ}
    (hk : k ≠ 0) : chernClass G E k = 0 := by
  rw [← totalChernClass_apply, h, ← TopCat.evenIntegralCohomologyOf_one]
  exact DirectSum.of_eq_of_ne _ _ _ hk

/-- The total Chern class of a bundle of rank one is `1 + c₁(E)`. -/
theorem totalChernClass_eq_one_add_of_finrank_eq_one (hG : finrank ℂ G = 1) :
    totalChernClass G E = 1 + (TopCat.of B).evenIntegralCohomologyOf 1 (chernClass G E 1) := by
  rw [totalChernClass_def, hG, Finset.sum_range_succ, Finset.sum_range_one, chernClass_zero,
    TopCat.evenIntegralCohomologyOf_one]

/-! ### The defining relation -/

/-- The index set of the summands of the source of the Leray–Hirsch map in degree `2n`. -/
private abbrev LerayHirschIndex :=
  Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = 2 * finrank ℂ G},
    {i : Fin (finrank ℂ G) // 2 * (i : ℕ) = pq.val.1}

/-- The source of the Leray–Hirsch map in degree `2n`. -/
private abbrev LerayHirschSource :=
  ⨁ j : LerayHirschIndex G, (TopCat.of B).integralCohomology j.1.val.2

/-- The summand of the Leray–Hirsch decomposition of `H^{2n}(P(E); ℤ)` that pairs a class of
degree `2k` of the base with `x^{n-k}`, for `1 ≤ k ≤ n`. -/
private def lerayHirschIndex (k : ℕ) (h₁ : 1 ≤ k) (h₂ : k ≤ finrank ℂ G) :
    LerayHirschIndex G :=
  ⟨⟨(2 * (finrank ℂ G - k), 2 * k), by omega⟩, ⟨⟨finrank ℂ G - k, by omega⟩, rfl⟩⟩

/-- The element of the source of the Leray–Hirsch map with coefficients `a k`, `1 ≤ k ≤ n`. -/
private def lerayHirschElem (a : ∀ k : ℕ, (TopCat.of B).integralCohomology (2 * k)) :
    LerayHirschSource (B := B) G :=
  ∑ k : Fin (finrank ℂ G), DirectSum.of (fun j : LerayHirschIndex G ↦
      (TopCat.of B).integralCohomology j.1.val.2)
    (lerayHirschIndex G (k + 1) (by omega) k.isLt) (a (k + 1))

private theorem lerayHirschElem_apply (a : ∀ k : ℕ, (TopCat.of B).integralCohomology (2 * k))
    (k : Fin (finrank ℂ G)) :
    lerayHirschElem G a (lerayHirschIndex G (k + 1) (by omega) k.isLt) = a (k + 1) := by
  rw [lerayHirschElem, DirectSum.sum_apply, Finset.sum_eq_single k]
  · exact DirectSum.of_eq_same _ _
  · intro k' _ hk'
    refine DirectSum.of_eq_of_ne _ _ _ fun h ↦ hk' (Fin.ext ?_)
    have := congrArg (fun j ↦ j.1.val.2) h
    simp only [lerayHirschIndex] at this
    omega
  · simp

/-- Every element of the source of the Leray–Hirsch map in degree `2n` is determined by its
coefficients of degrees `2k`, `1 ≤ k ≤ n`. -/
private theorem eq_lerayHirschElem
    (y : LerayHirschSource (B := B) G)
    (a : ∀ k : ℕ, (TopCat.of B).integralCohomology (2 * k))
    (ha : ∀ k : Fin (finrank ℂ G),
      y (lerayHirschIndex G (k + 1) (by omega) k.isLt) = a (k + 1)) :
    y = lerayHirschElem G a := by
  refine DFinsupp.ext fun j ↦ ?_
  obtain ⟨⟨⟨d, q⟩, hdq⟩, ⟨i, hi⟩⟩ := j
  obtain rfl : d = 2 * i := hi.symm
  have key : ∀ (i' : Fin (finrank ℂ G)) (q' : ℕ) (h' : 2 * (i' : ℕ) + q' = 2 * finrank ℂ G),
      i' = i → q' = q →
      (⟨⟨(2 * (i' : ℕ), q'), h'⟩, ⟨i', rfl⟩⟩ : LerayHirschIndex G) =
        ⟨⟨(2 * (i : ℕ), q), hdq⟩, ⟨i, rfl⟩⟩ := by
    rintro i' q' h' rfl rfl
    rfl
  have hk : finrank ℂ G - 1 - i < finrank ℂ G := by omega
  rw [← key ⟨finrank ℂ G - (finrank ℂ G - 1 - i + 1), by omega⟩ (2 * (finrank ℂ G - 1 - i + 1))
    (by simp only; omega) (Fin.ext (by simp only; omega)) (by simp only at hdq ⊢; omega)]
  exact (ha ⟨_, hk⟩).trans (lerayHirschElem_apply G a ⟨_, hk⟩).symm

/-- The left side of the defining relation, for classes `a k` with `a 0 = 1`, is `xⁿ` plus the
image of `lerayHirschElem a` under the Leray–Hirsch map. -/
private theorem sum_mul_pow_eq (a : ∀ k : ℕ, (TopCat.of B).integralCohomology (2 * k))
    (ha : a 0 = (TopCat.of B).integralCohomologyOne) :
    ∑ i ∈ Finset.range (finrank ℂ G + 1),
        TopCat.evenIntegralCohomologyMap (TopCat.ofHom (ProjectiveBundle.projection ℂ G E))
          ((TopCat.of B).evenIntegralCohomologyOf i (a i)) *
        (TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
          (projectiveBundleClass G E) ^ (finrank ℂ G - i) =
      (TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
          (projectiveBundleClass G E) ^ finrank ℂ G +
        (TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf (finrank ℂ G)
          (TopCat.integralLerayHirsch (TopCat.ofHom (ProjectiveBundle.projection ℂ G E))
            (2 * finrank ℂ G) (projectiveBundleClassPow G E) (lerayHirschElem G a)) := by
  rw [Finset.sum_range_succ', add_comm, ha, TopCat.evenIntegralCohomologyMap_of,
    TopCat.singularCohomologyMap_integralCohomologyOne, TopCat.evenIntegralCohomologyOf_one,
    one_mul, Nat.sub_zero, lerayHirschElem, map_sum, map_sum, ← Fin.sum_univ_eq_sum_range]
  refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
  refine Eq.trans ?_ (congrArg _ (TopCat.integralLerayHirsch_of
    (TopCat.ofHom (ProjectiveBundle.projection ℂ G E)) (2 * finrank ℂ G)
    (projectiveBundleClassPow G E) (2 * (finrank ℂ G - (k + 1)))
    (2 * (k + 1)) (by omega) ⟨⟨finrank ℂ G - (k + 1), by omega⟩, rfl⟩ (a (k + 1)))).symm
  rw [TopCat.evenIntegralCohomologyMap_of,
    TopCat.evenIntegralCohomologyOf_pow_eq_of _ _ (finrank ℂ G - (k + 1)),
    TopCat.evenIntegralCohomologyOf_mul_of_add_eq _ (Nat.add_sub_cancel' (by omega)),
    projectiveBundleClassPow_mk G E ⟨finrank ℂ G - (k + 1), by omega⟩]

variable [FiniteDimensional ℂ G] [CompactSpace B]

/-- **The Chern classes are characterized by the relation of the tautological class.** Over a
compact base, for `E` of rank `n` and classes `a k ∈ H^{2k}(B; ℤ)` with `a 0 = 1`, the relation
`∑_{i ≤ n} π^* aᵢ ⌣ x^{n-i} = 0` holds on the projective bundle exactly when `a k` is the Chern
class `c_k(E)` for every `k ≤ n`. -/
theorem sum_mul_projectiveBundleClass_pow_eq_zero_iff
    (a : ∀ k : ℕ, (TopCat.of B).integralCohomology (2 * k))
    (ha : a 0 = (TopCat.of B).integralCohomologyOne) :
    ∑ i ∈ Finset.range (finrank ℂ G + 1),
        TopCat.evenIntegralCohomologyMap (TopCat.ofHom (ProjectiveBundle.projection ℂ G E))
          ((TopCat.of B).evenIntegralCohomologyOf i (a i)) *
        (TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
          (projectiveBundleClass G E) ^ (finrank ℂ G - i) = 0 ↔
      ∀ k ≤ finrank ℂ G, a k = chernClass G E k := by
  rcases Nat.eq_zero_or_pos (finrank ℂ G) with hN | _
  · -- For `E` of rank zero the projective bundle is empty, and so is its cohomology.
    have := ProjectiveBundle.isEmpty_of_finrank_eq_zero (E := E) hN
    refine ⟨fun _ k hk ↦ ?_, fun _ ↦ DFinsupp.ext fun k ↦ ?_⟩
    · obtain rfl : k = 0 := by omega
      rw [ha, chernClass_zero]
    · exact Subsingleton.elim _ _
  have hbij := bijective_integralLerayHirsch_projectiveBundle G E (2 * finrank ℂ G)
  -- The Chern classes are the coefficients of the decomposition of `-xⁿ`.
  have hc (k : Fin (finrank ℂ G)) : (AddEquiv.ofBijective _ hbij).symm
      (-(((TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
        (projectiveBundleClass G E) ^ finrank ℂ G) (finrank ℂ G)))
      (lerayHirschIndex G (k + 1) (by omega) k.isLt) = chernClass G E (k + 1) := by
    rw [chernClass_def, dite_eq_left ⟨by omega, by omega, hbij⟩]
    -- `lerayHirschIndex G (k + 1)` is the summand that `chernClass_def` writes out.
    rfl
  rw [sum_mul_pow_eq G E a ha]
  refine ⟨fun h k hk ↦ ?_, fun h ↦ ?_⟩
  · rcases k with _ | k
    · rw [ha, chernClass_zero]
    have h' : TopCat.integralLerayHirsch (TopCat.ofHom (ProjectiveBundle.projection ℂ G E))
        (2 * finrank ℂ G) (projectiveBundleClassPow G E) (lerayHirschElem G a) =
        -(((TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
          (projectiveBundleClass G E) ^ finrank ℂ G) (finrank ℂ G)) := by
      refine DirectSum.of_injective (β := fun k : ℕ ↦
        ↥((TopCat.of (ProjectiveBundle ℂ G E)).integralCohomology (2 * k))) (finrank ℂ G) ?_
      rw [map_neg, ← TopCat.evenIntegralCohomologyOf_pow_eq_of]
      exact eq_neg_of_add_eq_zero_right h
    rw [← hc ⟨k, by omega⟩, ← (AddEquiv.ofBijective _ hbij).eq_symm_apply.2 h']
    exact (lerayHirschElem_apply G a ⟨k, by omega⟩).symm
  · rw [← eq_lerayHirschElem G _ a fun k ↦ (hc k).trans (h _ (by omega)).symm,
      ← AddEquiv.ofBijective_apply _ hbij, AddEquiv.apply_symm_apply, map_neg,
      ← TopCat.evenIntegralCohomologyOf_pow_eq_of, add_neg_cancel]

/-- **The defining relation of the Chern classes.** Over a compact base, for `E` of rank `n`,
`∑_{i ≤ n} π^* cᵢ(E) ⌣ x^{n-i} = 0` in the even integral cohomology ring of the projective
bundle, where `x` is the tautological class. -/
theorem sum_chernClass_mul_projectiveBundleClass_pow :
    ∑ i ∈ Finset.range (finrank ℂ G + 1),
        TopCat.evenIntegralCohomologyMap (TopCat.ofHom (ProjectiveBundle.projection ℂ G E))
          ((TopCat.of B).evenIntegralCohomologyOf i (chernClass G E i)) *
        (TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
          (projectiveBundleClass G E) ^ (finrank ℂ G - i) = 0 :=
  (sum_mul_projectiveBundleClass_pow_eq_zero_iff G E _ (chernClass_zero G E)).2 fun _ _ ↦ rfl

/-- **Uniqueness of the Chern classes.** Over a compact base, classes `a k ∈ H^{2k}(B; ℤ)` with
`a 0 = 1` that satisfy the relation `∑_{i ≤ n} π^* aᵢ ⌣ x^{n-i} = 0` on the projective bundle
are the Chern classes of `E` in degrees `k ≤ n`. -/
theorem chernClass_eq_of_sum_mul_pow_eq_zero
    (a : ∀ k : ℕ, (TopCat.of B).integralCohomology (2 * k))
    (ha : a 0 = (TopCat.of B).integralCohomologyOne)
    (h : ∑ i ∈ Finset.range (finrank ℂ G + 1),
        TopCat.evenIntegralCohomologyMap (TopCat.ofHom (ProjectiveBundle.projection ℂ G E))
          ((TopCat.of B).evenIntegralCohomologyOf i (a i)) *
        (TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
          (projectiveBundleClass G E) ^ (finrank ℂ G - i) = 0)
    {k : ℕ} (hk : k ≤ finrank ℂ G) : a k = chernClass G E k :=
  (sum_mul_projectiveBundleClass_pow_eq_zero_iff G E a ha).1 h k hk

omit [FiniteDimensional ℂ G] in
/-- **The pull-back to the projective bundle is injective.** Over a compact base, for `E` of
positive rank, `π^* : Hⁿ(B; ℤ) → Hⁿ(P(E); ℤ)` is injective in every degree. -/
theorem injective_projectiveBundle_proj (hG : 0 < finrank ℂ G) (n : ℕ) :
    Function.Injective (TopCat.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ)
      (M := ModuleCat.of ℤ ℤ) (TopCat.ofHom (ProjectiveBundle.projection ℂ G E)) n) :=
  have := Module.finite_of_finrank_pos hG
  TopCat.singularCohomologyMap_injective_of_integralLerayHirsch_injective _ n _
    (bijective_integralLerayHirsch_projectiveBundle G E n).1 ⟨⟨0, hG⟩, rfl⟩
    ((projectiveBundleClassPow_mk G E ⟨0, hG⟩).trans
      ((congrArg (fun y : (TopCat.of (ProjectiveBundle ℂ G E)).EvenIntegralCohomology ↦ y 0)
        (pow_zero _)).trans
        (by rw [← TopCat.evenIntegralCohomologyOf_one, DirectSum.of_eq_same])))

/-- **The first Chern class of a line bundle is its Euler class.** Over a compact base, for `E` of
rank one, `c₁(E)` is the Euler class of `E`, read in integral cohomology. -/
theorem chernClass_one_eq_complexEulerClass (hG : finrank ℂ G = 1) :
    chernClass G E 1 =
      ((TopCat.of B).uliftIntegralCohomologyIso 2).hom (complexEulerClass (r := 0) G E hG) := by
  -- Every line of a fibre of rank one is the whole fibre.
  have htop (p : ProjectiveBundle ℂ G E) : p.snd.submodule = ⊤ := by
    have e := (VectorBundle.continuousLinearEquivAt ℂ G E p.proj).toLinearEquiv
    have := e.symm.finiteDimensional
    exact Submodule.eq_top_of_finrank_eq
      ((Projectivization.finrank_submodule _).trans (e.finrank_eq.trans hG).symm)
  let φ (p : ProjectiveBundle ℂ G E) : ProjectiveBundle.Tautological ℂ G E p ≃L[ℂ] E p.proj :=
    { LinearEquiv.ofTop _ (htop p) with
      continuous_toFun := continuous_subtypeVal
      continuous_invFun := continuous_id.subtype_mk _ }
  have hS := complexEulerClass_eq_singularCohomologyMap_of_fiberwise (r := 0) hG (finrank_self ℂ)
    (g := ProjectiveBundle.projection ℂ G E) (E' := ProjectiveBundle.Tautological ℂ G E)
    (φ := φ) (ProjectiveBundle.continuous_totalSpace_tautological_iff.1 continuous_id).2
  have hrel := sum_chernClass_mul_projectiveBundleClass_pow G E
  rw [hG, Finset.sum_range_succ, Finset.sum_range_one, chernClass_zero,
    TopCat.evenIntegralCohomologyMap_of, TopCat.evenIntegralCohomologyMap_of,
    TopCat.singularCohomologyMap_integralCohomologyOne, TopCat.evenIntegralCohomologyOf_one,
    one_mul, Nat.sub_zero, pow_one, Nat.sub_self, pow_zero] at hrel
  simp only [mul_one] at hrel
  have h1 := eq_neg_of_add_eq_zero_right hrel
  rw [← map_neg] at h1
  apply injective_projectiveBundle_proj G E (by omega) 2
  rw [DirectSum.of_injective 1 h1, projectiveBundleClass_def, neg_neg, hS]
  exact TopCat.uliftIntegralCohomologyIso_naturality_apply _ 2 _

end SymplecticGeometry.Bundle

namespace Projectivization

/-- The first Chern class of the tautological line `𝒪(-1)` of a finite-dimensional complex
projective space `ℙ ℂ V` is minus the hyperplane class: `c₁(𝒪(-1)) = -h`. -/
theorem chernClass_one_tautological (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] :
    SymplecticGeometry.Bundle.chernClass ℂ (Tautological ℂ V) 1 = -hyperplaneClass V := by
  rw [SymplecticGeometry.Bundle.chernClass_one_eq_complexEulerClass _ _ (Module.finrank_self ℂ),
    hyperplaneClass_def, neg_neg]

end Projectivization

end
