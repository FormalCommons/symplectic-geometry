/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
public import SymplecticGeometry.AlgebraicTopology.Cohomology.LerayHirsch.MayerVietoris
public import SymplecticGeometry.Topology.FiberBundle.Basic
public import TauCeti.AlgebraicTopology.Cohomology.LerayHirsch.FiberwiseBasis

/-!
# The Leray–Hirsch theorem for bundles with a finite trivializing cover

Let `k` be a commutative ring and `Z` a fibre bundle over `Y` with fibre `F`, given as Mathlib's
`[FiberBundle F Z]`, such that finitely many of the trivializations `trivializationAt F Z y`
cover `Y`. Suppose that the homology `H_d(F; k)` is projective in every degree and finitely
generated in degrees `d ≤ n`, and that classes `c d i ∈ Hᵈ(Z; k)`, finitely many in each degree
`d ≤ n`, restrict on the fibre over every point `y`, read through the trivialization at `y`
(`Bundle.Trivialization.fiberInclusion`), to a basis of `Hᵈ(F; k)`. Then the Leray–Hirsch map

`⨁_{d + q = n} ⨁_{i : ι d} H^q(Y; k) ⟶ Hⁿ(Z; k)`, `(a_{d,i}) ↦ ∑ π^* a_{d,i} ⌣ c d i`,

is bijective (`TopCat.lerayHirsch_bijective`, and `TopCat.lerayHirschEquiv` for the linear
equivalence). The same holds for any map `p : E ⟶ B` with finitely many trivializations whose base
sets cover `B`, if the classes restrict to bases through each of them
(`TopCat.lerayHirsch_bijective_of_biUnion_baseSet_eq_univ`), and over any finite union of open
sets, each inside the base set of such a trivialization, for the restriction of `p` there
(`TopCat.lerayHirschRestrict_biUnion_bijective`). When one of the classes of degree
zero is the unit, the pull-back `p^*` is injective
(`TopCat.singularCohomologyMap_injective_of_lerayHirsch_injective`).

The integral form, for `TopCat.integralCohomology` and the integral cup product
`TopCat.integralCup`, is `TopCat.integralLerayHirsch_bijective`, with
`TopCat.integralLerayHirschEquiv` and
`TopCat.singularCohomologyMap_injective_of_integralLerayHirsch_injective`. Its Leray–Hirsch map
`TopCat.integralLerayHirsch` is an additive map, which over `ℤ` is the same as a linear one.

## Proof

Over a subset `S` of the base set of one trivialization `t`, the trivialization identifies
`p⁻¹ S` with `S × F` over `S`, and the Leray–Hirsch map with Tau Ceti's
`TopCat.lerayHirschProdOfClasses`, which is bijective by `TopCat.lerayHirschProdOfClasses_bijective`
(`TopCat.lerayHirschRestrict_bijective_of_subset_baseSet`). The finite cover is handled by
induction on the number of open sets, with the Mayer–Vietoris step
`TopCat.lerayHirschRestrict_union_bijective`; the intersection of a new set with the union of the
others is again a union of fewer sets, each inside a trivializing set. This induction adapts the
proof of Tau Ceti's `TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion` (the Thom
isomorphism over a finite union of trivializing sets) to the Leray–Hirsch map. For a fibre bundle,
the restrictions of the classes through two trivializations differ by the coordinate change, a
homeomorphism of `F`, so the hypothesis at the trivialization of each point gives it through every
trivialization of the atlas.

The integral form follows from the case `k = ℤ`, through the linear equivalence
`TopCat.integralCohomologyLinearEquiv` of cohomology with coefficients `ℤ` with integral
cohomology, which commutes with pull-backs and carries the cup product to the integral cup product
(`TopCat.integralLerayHirsch_integralCohomologyLinearEquiv`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4D.1 (Leray–Hirsch) and its proof.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Bundle Set
open scoped DirectSum

universe w

namespace TopCat

variable {k : Type w} [CommRing k]

/-- For the projection `X × F ⟶ X` of a product, the Leray–Hirsch map is
`TopCat.lerayHirschProdOfClasses`. -/
lemma lerayHirsch_fst (X F : TopCat.{w}) (n : ℕ) {ι : ℕ → Type w} [∀ d, DecidableEq (ι d)]
    (c : ∀ d, ι d → (X ⊗ F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d) :
    lerayHirsch (fst X F) n c = lerayHirschProdOfClasses X F n c := by
  refine DirectSum.linearMap_ext k fun ⟨⟨⟨d, q⟩, h⟩, i⟩ ↦ LinearMap.ext fun a ↦ ?_
  simp only [LinearMap.comp_apply]
  rw [lerayHirsch_lof, lerayHirschProdOfClasses_lof]

section Local

variable {E B F : TopCat.{w}} (p : E ⟶ B) {ι : ℕ → Type w} [∀ d, DecidableEq (ι d)]
  [∀ d, Projective (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
    (𝟙_ (ModuleCat.{w} k))).obj F)]

/-- **The Leray–Hirsch theorem over a trivializing set.** Let `t` be a trivialization of
`p : E ⟶ B` with fibre `F`, and `S` a subset of its base set. Suppose that the homology
`H_d(F; k)` is projective in every degree and finitely generated in degrees `d ≤ n`, that `ι d`
is finite for `d ≤ n`, and that over every point `x` of `S` the classes `c d i ∈ Hᵈ(E; k)`,
restricted to the fibre over `x` through `t`, form a basis of `Hᵈ(F; k)`. Then the
Leray–Hirsch map of the restriction `p⁻¹ S ⟶ S` of `p`, with the restricted classes, is
bijective in degree `n`. -/
theorem lerayHirschRestrict_bijective_of_subset_baseSet (t : Trivialization F p) {S : Set B}
    (hS : S ⊆ t.baseSet) (n : ℕ)
    (c : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)
    (hι : ∀ d ≤ n, Finite (ι d))
    (hF : ∀ d ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
      (𝟙_ (ModuleCat.{w} k))).obj F))
    (hc : ∀ x (hx : x ∈ S) (d : ℕ),
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap (ofHom (t.fiberInclusion (hS hx))) d
        (c d i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦
        TopCat.singularCohomologyMap (ofHom (t.fiberInclusion (hS hx))) d (c d i))) :
    Function.Bijective (lerayHirschRestrict p c S n) := by
  let f : of S ⊗ F ⟶ of (p ⁻¹' S) := (isoOfHomeo (t.preimageHomeomorph hS).symm).hom
  have hf : f ≫ ofHom (p.hom.restrictPreimage S) = fst (of S) F ≫ 𝟙 _ := by
    ext ⟨x, y⟩
    -- The map of `isoOfHomeo` is the homeomorphism, which sends `(x, y)` to `t⁻¹ (x, y)`.
    exact t.proj_symm_apply' (hS x.property)
  rw [← lerayHirsch_bijective_iff_of_isIso f (𝟙 _) hf (fun _ _ _ ↦ rfl), lerayHirsch_fst]
  refine lerayHirschProdOfClasses_bijective (F := F) _ n _ hι hF fun x d ↦ ?_
  have hx : prodFiberInclusion (of S) F x ≫ f ≫ ofHom (ContinuousMap.subtypeVal (p ⁻¹' S)) =
      ofHom (t.fiberInclusion (hS x.property)) := by
    ext y
    rw [ConcreteCategory.comp_apply, prodFiberInclusion_apply, ConcreteCategory.hom_ofHom,
      Trivialization.fiberInclusion_apply]
    -- The map of `isoOfHomeo` is the homeomorphism, which sends `(x, y)` to `t⁻¹ (x, y)`.
    exact congrArg Subtype.val (t.preimageHomeomorph_symm_apply hS (x, y))
  simp only [← ConcreteCategory.comp_apply, ← singularCohomologyMap_comp, hx]
  exact hc x x.property d

end Local

section Cover

variable {E B F : TopCat.{w}} (p : E ⟶ B) {ι : ℕ → Type w} [∀ d, DecidableEq (ι d)]
  [∀ d, Projective (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
    (𝟙_ (ModuleCat.{w} k))).obj F)]

/-- The Leray–Hirsch map over a finite union of trivializing sets is bijective in every degree
`m ≤ n`; the induction on the finite set behind `TopCat.lerayHirschRestrict_biUnion_bijective`. -/
private theorem lerayHirschRestrict_biUnion_bijective_of_le {κ : Type*} (s : Finset κ)
    {W : κ → Set B} (hWo : ∀ j ∈ s, IsOpen (W j)) (n : ℕ)
    (c : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)
    (hι : ∀ d ≤ n, Finite (ι d))
    (hF : ∀ d ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
      (𝟙_ (ModuleCat.{w} k))).obj F))
    (hWe : ∀ j ∈ s, ∃ (t : Trivialization F p) (hW : W j ⊆ t.baseSet), ∀ x (hx : x ∈ W j) (d : ℕ),
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap (ofHom (t.fiberInclusion (hW hx)))
        d (c d i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦
        TopCat.singularCohomologyMap (ofHom (t.fiberInclusion (hW hx))) d (c d i))) :
    ∀ m ≤ n, Function.Bijective (lerayHirschRestrict p c (⋃ j ∈ s, W j) m) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    intro m _
    rw [(by simp : (⋃ j ∈ (∅ : Finset κ), W j) = ∅)]
    exact lerayHirschRestrict_empty_bijective p c m
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have ha : a ∈ insert a s := Finset.mem_insert_self a s
    have hs (j : κ) (hj : j ∈ s) : j ∈ insert a s := Finset.mem_insert_of_mem hj
    obtain ⟨t, ht, hct⟩ := hWe a ha
    refine lerayHirschRestrict_union_bijective p c
      ((hWo a ha).preimage continuous_subtypeVal)
      ((isOpen_biUnion fun j hj ↦ hWo j (hs j hj)).preimage continuous_subtypeVal) n
      (fun m hm ↦ lerayHirschRestrict_bijective_of_subset_baseSet p t ht m c
        (fun d hd ↦ hι d (hd.trans hm)) (fun d hd ↦ hF d (hd.trans hm)) hct)
      (ih (fun j hj ↦ hWo j (hs j hj)) fun j hj ↦ hWe j (hs j hj)) ?_
    rw [inter_iUnion₂]
    exact ih (W := fun j ↦ W a ∩ W j) (fun j hj ↦ (hWo a ha).inter (hWo j (hs j hj)))
      fun j hj ↦ let ⟨t', ht', hc'⟩ := hWe j (hs j hj)
        ⟨t', inter_subset_right.trans ht', fun x hx ↦ hc' x hx.2⟩

/-- **The Leray–Hirsch theorem over a finite union of trivializing sets.** Let `W j`, for `j` in
a finite set `s`, be open sets of the base of `p : E ⟶ B`, each contained in the base set of a
trivialization of `p` with fibre `F` through which, over every point of `W j`, the classes
`c d i ∈ Hᵈ(E; k)` restrict to a basis of `Hᵈ(F; k)`. Suppose that the homology `H_d(F; k)` is
projective in every degree and finitely generated in degrees `d ≤ n`, and that `ι d` is finite for
`d ≤ n`. Then the Leray–Hirsch map of the restriction of `p` over `⋃ j ∈ s, W j`, with the
restricted classes, is bijective in degree `n`. -/
theorem lerayHirschRestrict_biUnion_bijective {κ : Type*} (s : Finset κ)
    {W : κ → Set B} (hWo : ∀ j ∈ s, IsOpen (W j)) (n : ℕ)
    (c : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)
    (hι : ∀ d ≤ n, Finite (ι d))
    (hF : ∀ d ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
      (𝟙_ (ModuleCat.{w} k))).obj F))
    (hWe : ∀ j ∈ s, ∃ (t : Trivialization F p) (hW : W j ⊆ t.baseSet), ∀ x (hx : x ∈ W j) (d : ℕ),
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap (ofHom (t.fiberInclusion (hW hx)))
        d (c d i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦
        TopCat.singularCohomologyMap (ofHom (t.fiberInclusion (hW hx))) d (c d i))) :
    Function.Bijective (lerayHirschRestrict p c (⋃ j ∈ s, W j) n) :=
  lerayHirschRestrict_biUnion_bijective_of_le p s hWo n c hι hF hWe n le_rfl

/-- **The Leray–Hirsch theorem for a finite trivializing cover.** Let `p : E ⟶ B` have
trivializations `t j` with fibre `F`, for `j` in a finite set `s`, whose base sets cover `B`.
Suppose that the homology `H_d(F; k)` is projective in every degree and finitely generated in
degrees `d ≤ n`, that `ι d` is finite for `d ≤ n`, and that over every point `x` of the base set
of each `t j` the classes `c d i ∈ Hᵈ(E; k)`, restricted to the fibre over `x` through `t j`,
form a basis of `Hᵈ(F; k)`. Then the Leray–Hirsch map
`⨁_{d + q = n} ⨁_{i : ι d} H^q(B; k) ⟶ Hⁿ(E; k)` of `p` and `c` is bijective. -/
theorem lerayHirsch_bijective_of_biUnion_baseSet_eq_univ {κ : Type*} (s : Finset κ)
    (t : κ → Trivialization F p) (hs : ⋃ j ∈ s, (t j).baseSet = univ) (n : ℕ)
    (c : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)
    (hι : ∀ d ≤ n, Finite (ι d))
    (hF : ∀ d ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
      (𝟙_ (ModuleCat.{w} k))).obj F))
    (hc : ∀ j ∈ s, ∀ x (hx : x ∈ (t j).baseSet) (d : ℕ),
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap (ofHom ((t j).fiberInclusion hx))
        d (c d i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦
        TopCat.singularCohomologyMap (ofHom ((t j).fiberInclusion hx)) d (c d i))) :
    Function.Bijective (lerayHirsch p n c) := by
  refine (lerayHirschRestrict_univ_bijective_iff p c n).1 ?_
  rw [← hs]
  exact lerayHirschRestrict_biUnion_bijective p s (fun j _ ↦ (t j).open_baseSet) n c hι hF
    (fun j hj ↦ ⟨t j, subset_rfl, hc j hj⟩)

end Cover

section FiberBundle

variable {Y F : Type w} [TopologicalSpace Y] [TopologicalSpace F] {Z : Y → Type w}
  [TopologicalSpace (TotalSpace F Z)] [∀ y, TopologicalSpace (Z y)] [FiberBundle F Z]
  {ι : ℕ → Type w}

/-- If the classes `c` restrict to bases of the fibre through the trivialization at every point,
they do so through every trivialization of the atlas: the two restrictions differ by the
homeomorphism of `F` given by the coordinate change. -/
private theorem fiberInclusion_basis_of_trivializationAt
    (c : ∀ d, ι d → (of (TotalSpace F Z)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) d)
    (hc : ∀ (y : Y) (d : ℕ),
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)))
    (t : Trivialization F (π F Z)) {x : Y} (hx : x ∈ t.baseSet) (d : ℕ) :
    LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap (ofHom (t.fiberInclusion hx))
      d (c d i)) ∧
    ⊤ ≤ Submodule.span k (Set.range fun i ↦
      TopCat.singularCohomologyMap (ofHom (t.fiberInclusion hx)) d (c d i)) := by
  set t' := trivializationAt F Z x
  have hx' : x ∈ t'.baseSet := mem_baseSet_trivializationAt F Z x
  let φ := t.coordChangeHomeomorph t' hx hx'
  have hφ : ofHom (t.fiberInclusion hx) =
      (isoOfHomeo (X := of F) (Y := of F) φ).hom ≫ ofHom (t'.fiberInclusion hx') := by
    refine TopCat.ext fun f ↦ ?_
    exact (t.fiberInclusion_coordChange t' hx hx' f).symm
  let L := LinearEquiv.ofBijective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k))
    (k := k) (M := 𝟙_ (ModuleCat.{w} k)) (isoOfHomeo (X := of F) (Y := of F) φ).hom d).hom
    ((TauCeti.singularCohomologyFunctor _ k _ d).mapIso
      (isoOfHomeo (X := of F) (Y := of F) φ).op).toLinearEquiv.bijective
  let b := Module.Basis.mk (hc x d).1 (hc x d).2
  have hb : ⇑(b.map L) = fun i ↦ TopCat.singularCohomologyMap (ofHom (t.fiberInclusion hx))
      d (c d i) := by
    ext i
    simp only [L, b, Module.Basis.map_apply, Module.Basis.mk_apply]
    rw [hφ, singularCohomologyMap_comp, ConcreteCategory.comp_apply]
    exact LinearEquiv.ofBijective_apply _ _
  rw [← hb]
  exact ⟨(b.map L).linearIndependent, (b.map L).span_eq.ge⟩

variable [∀ d, DecidableEq (ι d)]
  [∀ d, Projective (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
    (𝟙_ (ModuleCat.{w} k))).obj (of F))]

/-- **The Leray–Hirsch theorem for a fibre bundle with a finite trivializing cover.** Let
`Z` be a fibre bundle over `Y` with fibre `F`, and `s` a finite set of points whose
trivializations cover `Y`. Suppose that the homology `H_d(F; k)` is projective in every degree
and finitely generated in degrees `d ≤ n`, that `ι d` is finite for `d ≤ n`, and that for every
point `y` the classes `c d i ∈ Hᵈ(Z; k)`, restricted to the fibre over `y` through the
trivialization at `y`, form a basis of `Hᵈ(F; k)`. Then the Leray–Hirsch map
`⨁_{d + q = n} ⨁_{i : ι d} H^q(Y; k) ⟶ Hⁿ(Z; k)`, `(a_{d,i}) ↦ ∑ π^* a_{d,i} ⌣ c d i`, is
bijective. -/
theorem lerayHirsch_bijective (s : Finset Y)
    (hs : ⋃ y ∈ s, (trivializationAt F Z y).baseSet = univ) (n : ℕ)
    (c : ∀ d, ι d → (of (TotalSpace F Z)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) d)
    (hι : ∀ d ≤ n, Finite (ι d))
    (hF : ∀ d ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
      (𝟙_ (ModuleCat.{w} k))).obj (of F)))
    (hc : ∀ (y : Y) (d : ℕ),
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i))) :
    Function.Bijective (lerayHirsch (ofHom ⟨π F Z, FiberBundle.continuous_proj F Z⟩) n c) :=
  lerayHirsch_bijective_of_biUnion_baseSet_eq_univ (F := of F) _ s (trivializationAt F Z) hs n c
    hι hF fun _ _ _ hx d ↦ fiberInclusion_basis_of_trivializationAt c hc _ hx d

/-- **The Leray–Hirsch isomorphism** of a fibre bundle with a finite trivializing cover,
`⨁_{d + q = n} ⨁_{i : ι d} H^q(Y; k) ≃ Hⁿ(Z; k)`, the linear equivalence given by the
Leray–Hirsch map under the hypotheses of `TopCat.lerayHirsch_bijective`. -/
def lerayHirschEquiv (s : Finset Y)
    (hs : ⋃ y ∈ s, (trivializationAt F Z y).baseSet = univ) (n : ℕ)
    (c : ∀ d, ι d → (of (TotalSpace F Z)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) d)
    (hι : ∀ d ≤ n, Finite (ι d))
    (hF : ∀ d ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
      (𝟙_ (ModuleCat.{w} k))).obj (of F)))
    (hc : ∀ (y : Y) (d : ℕ),
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i))) :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1,
        (of Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2) ≃ₗ[k]
      (of (TotalSpace F Z)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n :=
  LinearEquiv.ofBijective _ (lerayHirsch_bijective s hs n c hι hF hc)

@[simp]
lemma lerayHirschEquiv_apply (s : Finset Y)
    (hs : ⋃ y ∈ s, (trivializationAt F Z y).baseSet = univ) (n : ℕ)
    (c : ∀ d, ι d → (of (TotalSpace F Z)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) d)
    (hι : ∀ d ≤ n, Finite (ι d))
    (hF : ∀ d ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
      (𝟙_ (ModuleCat.{w} k))).obj (of F)))
    (hc : ∀ (y : Y) (d : ℕ),
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)))
    (a : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1,
        (of Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2) :
    lerayHirschEquiv s hs n c hι hF hc a =
      lerayHirsch (ofHom ⟨π F Z, FiberBundle.continuous_proj F Z⟩) n c a :=
  (rfl)

/-- The Leray–Hirsch isomorphism sends `a` in the summand indexed by `d + q = n` and `i : ι d` to
`π^* a ⌣ c d i`. -/
lemma lerayHirschEquiv_lof (s : Finset Y)
    (hs : ⋃ y ∈ s, (trivializationAt F Z y).baseSet = univ) (n : ℕ)
    (c : ∀ d, ι d → (of (TotalSpace F Z)).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) d)
    (hι : ∀ d ≤ n, Finite (ι d))
    (hF : ∀ d ≤ n, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) d).obj
      (𝟙_ (ModuleCat.{w} k))).obj (of F)))
    (hc : ∀ (y : Y) (d : ℕ),
      LinearIndependent k (fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)) ∧
      ⊤ ≤ Submodule.span k (Set.range fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)))
    (d q : ℕ) (h : d + q = n) (i : ι d)
    (a : (of Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lerayHirschEquiv s hs n c hι hF hc (DirectSum.lof k _
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1 ↦
          (of Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2)
        ⟨⟨(d, q), h⟩, i⟩ a) =
      (of (TotalSpace F Z)).singularCup k (λ_ _).inv (λ_ _).hom q d n (by omega)
        (TopCat.singularCohomologyMap (ofHom ⟨π F Z, FiberBundle.continuous_proj F Z⟩) q a)
        (c d i) := by
  rw [lerayHirschEquiv_apply, lerayHirsch_lof]

end FiberBundle

section Injective

variable {E B : TopCat.{w}} (p : E ⟶ B) (n : ℕ) {ι : ℕ → Type*} [∀ d, DecidableEq (ι d)]

/-- If the Leray–Hirsch map of `p` is injective in degree `n` and one of the classes of degree
zero is the unit, then `p^* : Hⁿ(B; k) ⟶ Hⁿ(E; k)` is injective: it is the Leray–Hirsch map on
the summand of the unit class. -/
theorem singularCohomologyMap_injective_of_lerayHirsch_injective
    (c : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)
    (h : Function.Injective (lerayHirsch p n c)) (i₀ : ι 0)
    (hi₀ : c 0 i₀ = singularCohomologyZeroOne E) :
    Function.Injective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
      (M := 𝟙_ (ModuleCat.{w} k)) p n) := by
  intro a b hab
  refine DirectSum.of_injective (β := fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
    ι pq.val.1 ↦ B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.val.2)
    ⟨⟨(0, n), zero_add n⟩, i₀⟩ (h ?_)
  rw [← DirectSum.lof_eq_of k, ← DirectSum.lof_eq_of k, lerayHirsch_lof, lerayHirsch_lof, hi₀,
    singularCup_singularCohomologyZeroOne_right, singularCup_singularCohomologyZeroOne_right, hab]

end Injective

/-! ### Integral coefficients -/

section Integral

open TauCeti

variable {E B : TopCat.{0}} (p : E ⟶ B) (n : ℕ) {ι : ℕ → Type*} [∀ d, DecidableEq (ι d)]

/-- **The integral Leray–Hirsch map** of `p : E ⟶ B` and classes `c d : ι d → Hᵈ(E; ℤ)` in
degree `n`, `⨁_{d + q = n} ⨁_{i : ι d} H^q(B; ℤ) ⟶ Hⁿ(E; ℤ)`, sending `a` in the summand indexed
by `d + q = n` and `i : ι d` to the integral cup product `p^* a ⌣ c d i`. It is stated as an
additive map, which over `ℤ` is the same as a linear one; this avoids comparing the `ℤ`-module
structure of the cohomology groups with the one every abelian group has. -/
def integralLerayHirsch (c : ∀ d, ι d → E.integralCohomology d) :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1,
        B.integralCohomology j.1.val.2) →+ E.integralCohomology n :=
  DirectSum.toAddMonoid fun j ↦ AddMonoidHom.mk' (fun a ↦
    E.integralCup j.1.val.2 j.1.val.1 n (by rw [add_comm]; exact j.1.property)
      (TopCat.singularCohomologyMap p j.1.val.2 a) (c j.1.val.1 j.2))
    fun a b ↦ by rw [map_add, map_add, LinearMap.add_apply]

/-- The integral Leray–Hirsch map sends `a` in the summand indexed by `d + q = n` and `i : ι d`
to `p^* a ⌣ c d i`. -/
@[simp]
lemma integralLerayHirsch_of (c : ∀ d, ι d → E.integralCohomology d) (d q : ℕ) (h : d + q = n)
    (i : ι d) (a : B.integralCohomology q) :
    integralLerayHirsch p n c (DirectSum.of
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1 ↦
          B.integralCohomology j.1.val.2) ⟨⟨(d, q), h⟩, i⟩ a) =
      E.integralCup q d n (by omega) (TopCat.singularCohomologyMap p q a) (c d i) := by
  rw [integralLerayHirsch, DirectSum.toAddMonoid_of, AddMonoidHom.mk'_apply]

/-- If the integral Leray–Hirsch map of `p` is injective in degree `n` and one of the classes of
degree zero is the unit, then `p^* : Hⁿ(B; ℤ) ⟶ Hⁿ(E; ℤ)` is injective: it is the Leray–Hirsch
map on the summand of the unit class. -/
theorem singularCohomologyMap_injective_of_integralLerayHirsch_injective
    (c : ∀ d, ι d → E.integralCohomology d) (h : Function.Injective (integralLerayHirsch p n c))
    (i₀ : ι 0) (hi₀ : c 0 i₀ = E.integralCohomologyOne) :
    Function.Injective (TopCat.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ)
      (M := ModuleCat.of ℤ ℤ) p n) := by
  intro a b hab
  refine DirectSum.of_injective (β := fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
    ι pq.val.1 ↦ B.integralCohomology j.1.val.2) ⟨⟨(0, n), zero_add n⟩, i₀⟩ (h ?_)
  rw [integralLerayHirsch_of, integralLerayHirsch_of, hi₀, integralCup_integralCohomologyOne_right,
    integralCup_integralCohomologyOne_right, hab]

section LinearEquiv

/- `TopCat.lerayHirsch` for `k = ℤ` uses the structure `ModuleCat.instLinear`, which instance
search would not find here (`TopCat.integralCohomologyLinearEquiv`). -/
attribute [local instance high] ModuleCat.instLinear

/-- The integral Leray–Hirsch map is the Leray–Hirsch map with coefficients `ℤ`, read through
`TopCat.integralCohomologyLinearEquiv` on the summands, on the classes and on the target. -/
theorem integralLerayHirsch_integralCohomologyLinearEquiv
    (c : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) d)
    (x : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1,
      B.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) j.1.val.2) :
    integralLerayHirsch p n (fun d i ↦ E.integralCohomologyLinearEquiv d (c d i))
        (DirectSum.map (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1 ↦
          (B.integralCohomologyLinearEquiv j.1.val.2).toLinearMap.toAddMonoidHom) x) =
      E.integralCohomologyLinearEquiv n (lerayHirsch p n c x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of j a =>
    obtain ⟨⟨⟨d, q⟩, h⟩, i⟩ := j
    rw [DirectSum.map_of, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
      integralLerayHirsch_of, ← DirectSum.lof_eq_of ℤ, lerayHirsch_lof,
      integralCohomologyLinearEquiv_singularCup, integralCohomologyLinearEquiv_naturality]

end LinearEquiv

end Integral

section IntegralBundle

variable {Y F : Type} [TopologicalSpace Y] [TopologicalSpace F] {Z : Y → Type}
  [TopologicalSpace (TotalSpace F Z)] [∀ y, TopologicalSpace (Z y)] [FiberBundle F Z]
  {ι : ℕ → Type} [∀ d, DecidableEq (ι d)]
  [∀ d, Projective (((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj
    (𝟙_ (ModuleCat.{0} ℤ))).obj (of F))]

/-- **The Leray–Hirsch theorem for a fibre bundle with a finite trivializing cover, with integral
coefficients.** Let `Z` be a fibre bundle over `Y` with fibre `F`, and `s` a finite set of points
whose trivializations cover `Y`. Suppose that the homology `H_d(F; ℤ)` is projective in every
degree and finitely generated in degrees `d ≤ n`, that `ι d` is finite for `d ≤ n`, and that for
every point `y` the classes `c d i ∈ Hᵈ(Z; ℤ)`, restricted to the fibre over `y` through the
trivialization at `y`, form a basis of `Hᵈ(F; ℤ)`. Then the integral Leray–Hirsch map
`⨁_{d + q = n} ⨁_{i : ι d} H^q(Y; ℤ) ⟶ Hⁿ(Z; ℤ)`, `(a_{d,i}) ↦ ∑ π^* a_{d,i} ⌣ c d i`, is
bijective. -/
theorem integralLerayHirsch_bijective (s : Finset Y)
    (hs : ⋃ y ∈ s, (trivializationAt F Z y).baseSet = univ) (n : ℕ)
    (c : ∀ d, ι d → (of (TotalSpace F Z)).integralCohomology d)
    (hι : ∀ d ≤ n, Finite (ι d))
    (hF : ∀ d ≤ n, Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj
      (𝟙_ (ModuleCat.{0} ℤ))).obj (of F)))
    (hc : ∀ (y : Y) (d : ℕ),
      LinearIndependent ℤ (fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)) ∧
      ⊤ ≤ Submodule.span ℤ (Set.range fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i))) :
    Function.Bijective
      (integralLerayHirsch (ofHom ⟨π F Z, FiberBundle.continuous_proj F Z⟩) n c) := by
  -- The classes with coefficients `ℤ` that correspond to `c`.
  let c' (d : ℕ) (i : ι d) := ((of (TotalSpace F Z)).integralCohomologyLinearEquiv d).symm (c d i)
  have hcc' : c = fun d i ↦ (of (TotalSpace F Z)).integralCohomologyLinearEquiv d (c' d i) := by
    funext d i
    rw [LinearEquiv.apply_symm_apply]
  have hc' (y : Y) (d : ℕ) := by
    let b := Module.Basis.mk (hc y d).1 (hc y d).2
    -- The pull-back with coefficients `ℤ`, for the structure `ModuleCat.instLinear` that
    -- `TopCat.lerayHirsch` uses, which instance search would not find here.
    have hb : ⇑(b.map ((of F).integralCohomologyLinearEquiv d).symm) = fun i ↦
        @TopCat.singularCohomologyMap _ _ _ _ (𝟙_ (ModuleCat.{0} ℤ)) ℤ _ ModuleCat.instLinear
          (𝟙_ (ModuleCat.{0} ℤ)) _ _
          (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
          d (c' d i) := by
      ext i
      rw [Module.Basis.map_apply, Module.Basis.mk_apply, LinearEquiv.symm_apply_eq,
        integralCohomologyLinearEquiv_naturality, LinearEquiv.apply_symm_apply]
    exact hb ▸ And.intro (b.map _).linearIndependent (b.map _).span_eq.ge
  have hmap : Function.Bijective (DirectSum.map
      fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1 ↦
        ((of Y).integralCohomologyLinearEquiv j.1.val.2).toLinearMap.toAddMonoidHom) :=
    ⟨(DirectSum.map_injective _).2 fun j ↦ (integralCohomologyLinearEquiv _ _).injective,
      (DirectSum.map_surjective _).2 fun j ↦ (integralCohomologyLinearEquiv _ _).surjective⟩
  rw [← Function.Bijective.of_comp_iff _ hmap]
  have hcomp : ⇑(integralLerayHirsch (ofHom ⟨π F Z, FiberBundle.continuous_proj F Z⟩) n c) ∘
      ⇑(DirectSum.map fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1 ↦
        ((of Y).integralCohomologyLinearEquiv j.1.val.2).toLinearMap.toAddMonoidHom) =
      ⇑((of (TotalSpace F Z)).integralCohomologyLinearEquiv n) ∘
        ⇑(lerayHirsch (ofHom ⟨π F Z, FiberBundle.continuous_proj F Z⟩) n c') := by
    funext x
    rw [Function.comp_apply, Function.comp_apply,
      ← integralLerayHirsch_integralCohomologyLinearEquiv, ← hcc']
  rw [hcomp]
  exact (integralCohomologyLinearEquiv _ n).bijective.comp
    (lerayHirsch_bijective (k := ℤ) s hs n c' hι hF hc')

/-- **The integral Leray–Hirsch isomorphism** of a fibre bundle with a finite trivializing cover,
`⨁_{d + q = n} ⨁_{i : ι d} H^q(Y; ℤ) ≃ Hⁿ(Z; ℤ)`, the additive equivalence given by the integral
Leray–Hirsch map under the hypotheses of `TopCat.integralLerayHirsch_bijective`. -/
def integralLerayHirschEquiv (s : Finset Y)
    (hs : ⋃ y ∈ s, (trivializationAt F Z y).baseSet = univ) (n : ℕ)
    (c : ∀ d, ι d → (of (TotalSpace F Z)).integralCohomology d)
    (hι : ∀ d ≤ n, Finite (ι d))
    (hF : ∀ d ≤ n, Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj
      (𝟙_ (ModuleCat.{0} ℤ))).obj (of F)))
    (hc : ∀ (y : Y) (d : ℕ),
      LinearIndependent ℤ (fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)) ∧
      ⊤ ≤ Submodule.span ℤ (Set.range fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i))) :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1,
        (of Y).integralCohomology j.1.val.2) ≃+ (of (TotalSpace F Z)).integralCohomology n :=
  AddEquiv.ofBijective _ (integralLerayHirsch_bijective s hs n c hι hF hc)

@[simp]
lemma integralLerayHirschEquiv_apply (s : Finset Y)
    (hs : ⋃ y ∈ s, (trivializationAt F Z y).baseSet = univ) (n : ℕ)
    (c : ∀ d, ι d → (of (TotalSpace F Z)).integralCohomology d)
    (hι : ∀ d ≤ n, Finite (ι d))
    (hF : ∀ d ≤ n, Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj
      (𝟙_ (ModuleCat.{0} ℤ))).obj (of F)))
    (hc : ∀ (y : Y) (d : ℕ),
      LinearIndependent ℤ (fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)) ∧
      ⊤ ≤ Submodule.span ℤ (Set.range fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)))
    (a : ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1,
      (of Y).integralCohomology j.1.val.2) :
    integralLerayHirschEquiv s hs n c hι hF hc a =
      integralLerayHirsch (ofHom ⟨π F Z, FiberBundle.continuous_proj F Z⟩) n c a :=
  (rfl)

/-- The integral Leray–Hirsch isomorphism sends `a` in the summand indexed by `d + q = n` and
`i : ι d` to `π^* a ⌣ c d i`. -/
lemma integralLerayHirschEquiv_of (s : Finset Y)
    (hs : ⋃ y ∈ s, (trivializationAt F Z y).baseSet = univ) (n : ℕ)
    (c : ∀ d, ι d → (of (TotalSpace F Z)).integralCohomology d)
    (hι : ∀ d ≤ n, Finite (ι d))
    (hF : ∀ d ≤ n, Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{0} ℤ) d).obj
      (𝟙_ (ModuleCat.{0} ℤ))).obj (of F)))
    (hc : ∀ (y : Y) (d : ℕ),
      LinearIndependent ℤ (fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)) ∧
      ⊤ ≤ Submodule.span ℤ (Set.range fun i ↦ TopCat.singularCohomologyMap
        (ofHom ((trivializationAt F Z y).fiberInclusion (mem_baseSet_trivializationAt F Z y)))
        d (c d i)))
    (d q : ℕ) (h : d + q = n) (i : ι d) (a : (of Y).integralCohomology q) :
    integralLerayHirschEquiv s hs n c hι hF hc (DirectSum.of
        (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.val.1 ↦
          (of Y).integralCohomology j.1.val.2) ⟨⟨(d, q), h⟩, i⟩ a) =
      (of (TotalSpace F Z)).integralCup q d n (by omega)
        (TopCat.singularCohomologyMap (ofHom ⟨π F Z, FiberBundle.continuous_proj F Z⟩) q a)
        (c d i) := by
  rw [integralLerayHirschEquiv_apply, integralLerayHirsch_of]

end IntegralBundle

end TopCat
