/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Suspension
public import SymplecticGeometry.AlgebraicTopology.Singular.MayerVietoris.Connecting
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Prod

/-!
# The local orientation of `F × ℝ` read on the sheets `F × {±1}`

Let `F` be a real normed space of dimension `m + 1`, `z` a local orientation of `F` at `0`, and
`w = TauCeti.LocalOrientation.prod z ι` the local orientation of `F × ℝ` at `0`, `ι` being the one
selected by the standard orientation of `ℝ`. This file computes the image of `w` under the
connecting morphism of `(F × ℝ, (F × ℝ) ∖ {0})`, followed by the map
`Hₘ₊₁((F × ℝ) ∖ {0}) ⟶ Hₘ₊₁((F × ℝ) ∖ {0}, (F ∖ {0}) × ℝ)`. For `t ≠ 0` let
`jₜ : (F, F ∖ {0}) ⟶ ((F × ℝ) ∖ {0}, (F ∖ {0}) × ℝ)` be the sheet `x ↦ (x, t)`
(`TauCeti.prodSheetPairMap`). Then the image of `w` is `j₋₁ z - j₁ z`, that is
`s m • (j₁ z - j₋₁ z)` with `s m = -1` in every dimension
(`TauCeti.LocalOrientation.singularHomologyπ_singularHomologyδ_prod`).

The computation is first made in a real inner product space `E` of dimension `m + 2` with an
orthonormal basis `b`, `p` its last vector and `G = (ℝ ∙ p)ᗮ`, where the sheets are
`x ↦ x + t • p` on `G` (`TauCeti.orthogonalSheetPairMap`)
(`TauCeti.singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_singularHomologyπ`
for the oriented local homology isomorphisms, with any coefficients, and
`TauCeti.singularHomologyπ_singularHomologyδ_localOrientation` for the local orientations).
Cover `E ∖ {0}` by `U = TauCeti.complRay p` and `V = TauCeti.complRay (-p)`, whose intersection is
the complement of the line through `p`. By `TopCat.singularHomologyπ_ofSubset_inter_eq_add`, the
image of a class `c` of `Hₘ₊₁(E ∖ {0})` relative to `U ∩ V` is the sum of the images of its two
excision preimages `a ∈ Hₘ₊₁(U, U ∩ V)` and `a' ∈ Hₘ₊₁(V, V ∩ U)`. Since `U` and `V` are
contractible (`TauCeti.contractibleSpace_complRay`), the connecting morphisms of these pairs are
injective in positive degrees (`TopPair.mono_singularHomologyδ_of_contractibleSpace`). By
`TopCat.mayerVietorisδ_eq_singularHomologyδ_left` and
`TopCat.mayerVietorisδ_eq_neg_singularHomologyδ_right` they send `a` and `-a'` to the
Mayer–Vietoris connecting morphism of `c`, which for the boundary of the local orientation of `E`
is the image of the boundary of that of `G`
(`TauCeti.singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_mayerVietorisδ`).
The sheet at `-1` lies in `U` and the sheet at `1` in `V`; by naturality of the connecting
morphism, and as each sheet is homotopic to the inclusion of `G ∖ {0}` off the line through `p`,
the connecting morphisms send the images of the local orientation of `G` under these sheets to
the same class. Hence `a` and `-a'` are these images.

The case of `F × ℝ` follows by naturality, along a continuous linear equivalence of `F × ℝ` with
the Euclidean space `EuclideanSpace ℝ (Fin (m + 2))` that carries `F × {0}` onto the orthogonal
complement of the last basis vector and `(0, 1)` to it, built from a basis of `F` with the
orientation of `z`.

## Main definitions

* `TauCeti.orthogonalSheetPairMap`: the sheet `x ↦ x + t • p` on `(ℝ ∙ p)ᗮ`, as a map of pairs.
* `TauCeti.prodSheetPairMap`: the sheet `x ↦ (x, t)` of `F × ℝ`, as a map of pairs.

## Main results

* `TauCeti.singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_singularHomologyπ`
  and `TauCeti.singularHomologyπ_singularHomologyδ_localOrientation`: the computation in an inner
  product space.
* `TauCeti.LocalOrientation.singularHomologyπ_singularHomologyδ_prod`: the product local
  orientation of `F × ℝ` read on the sheets `F × {±1}`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2 (the Mayer–Vietoris sequence and the homology of spheres) and Section 3.3 (local
  orientations).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, Section 9.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Metric Module
open scoped ContinuousMap

universe w v u

/-- In an inner product space, a vector `x` of `Kᗮ` with `x + y ∈ K` for some `y ∈ K` is zero. -/
theorem Submodule.eq_zero_of_mem_orthogonal_of_add_mem {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {K : Submodule 𝕜 E} {x y : E} (hx : x ∈ Kᗮ)
    (hy : y ∈ K) (h : x + y ∈ K) : x = 0 :=
  Submodule.disjoint_def.1 K.orthogonal_disjoint x (by simpa using K.sub_mem h hy) hx

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- If the ambient space of a pair is contractible, its connecting morphism
`Hₘ₊₁(X, A) ⟶ Hₘ(A)` is a monomorphism. -/
theorem mono_singularHomologyδ_of_contractibleSpace (P : TopPair.{w}) [ContractibleSpace P.fst]
    (m : ℕ) : Mono (P.singularHomologyδ R (m + 1) m) :=
  (P.singularHomology_exact_relative R (m + 1) m).mono_g
    ((TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace R P.fst
      m.succ_ne_zero).eq_of_src _ _)

end TopPair

namespace TauCeti

section Sheets

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The translate `x + t • p` of a point `x` of `(ℝ ∙ p)ᗮ`, for `t ≠ 0`, as a point of
`E ∖ {0}`. -/
def orthogonalSheet (p : sphere (0 : E) 1) {t : ℝ} (ht : t ≠ 0) :
    C((ℝ ∙ (p : E))ᗮ, ({0}ᶜ : Set E)) where
  toFun x := ⟨x + t • (p : E), fun h ↦ by
    have hx := Submodule.eq_zero_of_mem_orthogonal_of_add_mem x.property
      (Submodule.smul_mem _ t (Submodule.mem_span_singleton_self (p : E)))
      (by rw [h]; exact Submodule.zero_mem _)
    rw [hx, zero_add] at h
    exact ht ((smul_eq_zero.1 h).resolve_right (ne_zero_of_mem_unit_sphere p))⟩
  continuous_toFun := by fun_prop

@[simp]
theorem coe_orthogonalSheet_apply (p : sphere (0 : E) 1) {t : ℝ} (ht : t ≠ 0)
    (x : (ℝ ∙ (p : E))ᗮ) : (orthogonalSheet p ht x : E) = x + t • (p : E) :=
  (rfl)

/-- A translate `x + s • p` of a point `x` of `(ℝ ∙ p)ᗮ` lies on the line through `p` only for
`x = 0`. -/
theorem add_smul_mem_span_singleton_iff (p : E) (x : (ℝ ∙ p)ᗮ) (s : ℝ) :
    (x : E) + s • p ∈ ℝ ∙ p ↔ x = 0 := by
  refine ⟨fun h ↦ Subtype.ext (Submodule.eq_zero_of_mem_orthogonal_of_add_mem x.property
    (Submodule.smul_mem _ s (Submodule.mem_span_singleton_self p)) h), fun h ↦ ?_⟩
  rw [h, Submodule.coe_zero, zero_add]
  exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self p)

/-- Off `0`, the sheet `x ↦ x + t • p` lies off the line through `p`. -/
theorem orthogonalSheet_mem_complRay_inter_complRay_neg (p : sphere (0 : E) 1) {t : ℝ}
    (ht : t ≠ 0) {x : (ℝ ∙ (p : E))ᗮ} (hx : x ≠ 0) :
    orthogonalSheet p ht x ∈ complRay p ∩ complRay (-p) :=
  mem_complRay_inter_complRay_neg_iff.2 fun h ↦
    hx ((add_smul_mem_span_singleton_iff _ x t).1 h)

/-- For `t < 0`, the sheet `x ↦ x + t • p` lies off the open ray through `p`. -/
theorem orthogonalSheet_mem_complRay_of_neg (p : sphere (0 : E) 1) {t : ℝ} (ht : t < 0)
    (x : (ℝ ∙ (p : E))ᗮ) : orthogonalSheet p ht.ne x ∈ complRay p := by
  refine mem_complRay_iff.2 fun s hs h ↦ ?_
  have h' : (x : E) + t • (p : E) = s • (p : E) := h.symm
  rw [(add_smul_mem_span_singleton_iff _ x t).1 (h' ▸ Submodule.smul_mem _ _
    (Submodule.mem_span_singleton_self _)), Submodule.coe_zero, zero_add] at h'
  have := smul_left_injective ℝ (ne_zero_of_mem_unit_sphere p) h'
  linarith

/-- For `t > 0`, the sheet `x ↦ x + t • p` lies off the open ray through `-p`. -/
theorem orthogonalSheet_mem_complRay_neg_of_pos (p : sphere (0 : E) 1) {t : ℝ} (ht : 0 < t)
    (x : (ℝ ∙ (p : E))ᗮ) : orthogonalSheet p ht.ne' x ∈ complRay (-p) := by
  refine mem_complRay_iff.2 fun s hs h ↦ ?_
  have h' : (x : E) + t • (p : E) = (-s) • (p : E) := by
    rw [neg_smul, ← smul_neg]; exact h.symm
  rw [(add_smul_mem_span_singleton_iff _ x t).1 (h' ▸ Submodule.smul_mem _ _
    (Submodule.mem_span_singleton_self _)), Submodule.coe_zero, zero_add] at h'
  have := smul_left_injective ℝ (ne_zero_of_mem_unit_sphere p) h'
  linarith

/-- **The sheets over the orthogonal complement.** For a point `p` of the unit sphere and
`t ≠ 0`, the map of pairs `((ℝ ∙ p)ᗮ, (ℝ ∙ p)ᗮ ∖ {0}) ⟶ (E ∖ {0}, E ∖ ℝ p)`, `x ↦ x + t • p`, the
target pair being `E ∖ {0}` relative to `TauCeti.complRay p ∩ TauCeti.complRay (-p)`. -/
def orthogonalSheetPairMap (p : sphere (0 : E) 1) {t : ℝ} (ht : t ≠ 0) :
    TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (ℝ ∙ (p : E))ᗮ)) ⟶
      TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set E)) (complRay p ∩ complRay (-p)) :=
  TopPair.ofSubsetMap (TopCat.ofHom (orthogonalSheet p ht))
    fun _ hx ↦ orthogonalSheet_mem_complRay_inter_complRay_neg p ht hx

theorem orthogonalSheetPairMap_fst (p : sphere (0 : E) 1) {t : ℝ} (ht : t ≠ 0) :
    TopPair.Hom.fst (orthogonalSheetPairMap p ht) = TopCat.ofHom (orthogonalSheet p ht) :=
  TopPair.ofSubsetMap_fst _ _

end Sheets

section Pieces

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- The sheet `x ↦ x + t • p` as a map of pairs into `(A, A ∩ A')`, for subsets `A` and `A'` of
`E ∖ {0}` such that `A` contains the sheet and `A'` contains its points off `0`. -/
private def orthogonalSheetInterPairMap (p : sphere (0 : E) 1) {t : ℝ} (ht : t ≠ 0)
    (A A' : Set (TopCat.of ({0}ᶜ : Set E))) (hA : ∀ x, orthogonalSheet p ht x ∈ A)
    (hA' : ∀ x, x ≠ 0 → orthogonalSheet p ht x ∈ A') :
    TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (ℝ ∙ (p : E))ᗮ)) ⟶ TopPair.interPair A A' :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨fun x ↦ ⟨orthogonalSheet p ht x, hA x⟩, by fun_prop⟩)
    fun x hx ↦ by exact hA' x hx

/-- On the punctured orthogonal complement, a map into the complement of the line through `p`
that is a sheet `x ↦ x + t • p` induces on homology the map of the inclusion: the straight-line
homotopy `x + (s * t) • p` stays off the line. -/
private theorem homologyMap_eq_complZeroOrthogonalInclusion (p : sphere (0 : E) 1) (t : ℝ)
    (f : TopCat.of ↥({0}ᶜ : Set (ℝ ∙ (p : E))ᗮ) ⟶ TopCat.of ↥(complRay p ∩ complRay (-p)))
    (hf : ∀ x, ((f x : ({0}ᶜ : Set E)) : E) = (x : (ℝ ∙ (p : E))ᗮ) + t • (p : E)) (m : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map f) R m =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (complZeroOrthogonalInclusion p))) R m := by
  have hmem : ∀ (s : ℝ) (x : ({0}ᶜ : Set (ℝ ∙ (p : E))ᗮ)),
      (x : E) + s • (p : E) ≠ 0 ∧ ∀ h : (x : E) + s • (p : E) ≠ 0,
        (⟨_, h⟩ : ({0}ᶜ : Set E)) ∈ complRay p ∩ complRay (-p) := fun s x ↦
    have h' : (x : E) + s • (p : E) ∉ ℝ ∙ (p : E) := fun h ↦
      x.property ((add_smul_mem_span_singleton_iff _ _ s).1 h)
    ⟨fun h ↦ h' (by rw [h]; exact Submodule.zero_mem _),
      fun _ ↦ mem_complRay_inter_complRay_neg_iff.2 h'⟩
  let H : ContinuousMap.Homotopy (complZeroOrthogonalInclusion p) f.hom :=
    { toFun := fun q ↦ ⟨⟨_, (hmem ((q.1 : ℝ) * t) q.2).1⟩, (hmem _ q.2).2 _⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun x ↦ by ext; simp
      map_one_left := fun x ↦ by ext; simp [hf] }
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H.symm R m

/-- A sheet `x ↦ x + t • p` into a pair `(A, A ∩ A')`, followed by the connecting morphism of the
pair and an identification of `A ∩ A'` with the complement of the line through `p` under which
the sheet stays `x ↦ x + t • p`, agrees with the connecting morphism of
`((ℝ ∙ p)ᗮ, (ℝ ∙ p)ᗮ ∖ {0})` followed by the inclusion. -/
private theorem singularHomologyMap_orthogonalSheetInterPairMap_singularHomologyδ
    (p : sphere (0 : E) 1) {t : ℝ} (ht : t ≠ 0) (A A' : Set (TopCat.of ({0}ᶜ : Set E)))
    (hA : ∀ x, orthogonalSheet p ht x ∈ A) (hA' : ∀ x, x ≠ 0 → orthogonalSheet p ht x ∈ A')
    (e : (TopPair.interPair A A').snd ≅ TopCat.of ↥(complRay p ∩ complRay (-p)))
    (he : ∀ x, ((e.hom (TopPair.Hom.snd (orthogonalSheetInterPairMap p ht A A' hA hA') x) :
      ({0}ᶜ : Set E)) : E) = (x.val : E) + t • (p : E)) (m : ℕ) :
    TopPair.singularHomologyMap (orthogonalSheetInterPairMap p ht A A' hA hA') R (m + 1) ≫
        (TopPair.interPair A A').singularHomologyδ R (m + 1) m ≫
          SSet.homologyMap (TopCat.toSSet.map e.hom) R m =
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (ℝ ∙ (p : E))ᗮ))).singularHomologyδ R (m + 1) m ≫
        ((singularHomologyFunctor C m).obj R).map
          (TopCat.ofHom (complZeroOrthogonalInclusion p)) := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker (TopPair.singularHomologyδ_naturality R _ (m + 1) m).symm _).trans ?_
  refine (Category.assoc _ _ _).trans (whisker_eq _ ?_)
  exact (((singularHomologyFunctor C m).obj R).map_comp _ _).symm.trans
    (homologyMap_eq_complZeroOrthogonalInclusion R p t
      (TopPair.Hom.snd (orthogonalSheetInterPairMap p ht A A' hA hA') ≫ e.hom) he m)

/-- If `A` is contractible, the connecting morphism of `(A, A ∩ A')` in positive degree, followed
by the map induced by an isomorphism out of the subspace, is a monomorphism. -/
private theorem mono_singularHomologyδ_interPair_comp {X Y : TopCat.{w}} (A A' : Set X)
    [ContractibleSpace A] (e : (TopPair.interPair A A').snd ≅ Y) (m : ℕ) :
    Mono ((TopPair.interPair A A').singularHomologyδ R (m + 1) m ≫
      SSet.homologyMap (TopCat.toSSet.map e.hom) R m) := by
  have : ContractibleSpace (TopPair.interPair A A').fst := ‹ContractibleSpace A›
  have hδ := TopPair.mono_singularHomologyδ_of_contractibleSpace R (TopPair.interPair A A') m
  have hi : IsIso (SSet.homologyMap (TopCat.toSSet.map e.hom) R m) :=
    inferInstanceAs (IsIso (((singularHomologyFunctor C m).obj R).mapIso e).hom)
  exact @mono_comp _ _ _ _ _ _ hδ _ (@IsIso.mono_of_iso _ _ _ _ _ hi)

/-- The excision preimage in `(complRay p, complRay p ∩ complRay (-p))` of the image of a class
`gE ≫ δ` of `E ∖ {0}` is the image of a class `gG` of `(ℝ ∙ p)ᗮ` under the sheet at `-1`, as soon
as the Mayer–Vietoris connecting morphism sends `gE ≫ δ` to the inclusion of `gG ≫ δ`: both have
the same boundary in the pair, and the boundary is injective there. The steps are `Eq.trans`
rather than `rw`, as the homology of `E ∖ {0}` appears under several names. -/
private theorem singularHomologyδ_singularHomologyπ_inv_excisionMap_left (p : sphere (0 : E) 1)
    {m : ℕ} {D : C}
    (gE : D ⟶ (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomology R (m + 2))
    (gG : D ⟶ (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (ℝ ∙ (p : E))ᗮ))).singularHomology R
      (m + 1))
    (h : gE ≫ (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomologyδ R (m + 2) (m + 1) ≫
        TopCat.mayerVietorisδ R (X := TopCat.of ({0}ᶜ : Set E)) (isOpen_complRay p)
          (isOpen_complRay (-p)) (complRay_union_complRay_neg p) (m + 1) m =
      gG ≫ (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (ℝ ∙ (p : E))ᗮ))).singularHomologyδ R
        (m + 1) m ≫
        ((singularHomologyFunctor C m).obj R).map (TopCat.ofHom (complZeroOrthogonalInclusion p))) :
    gE ≫ (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomologyδ R (m + 2) (m + 1) ≫
      (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set E)) (complRay (-p))).singularHomologyπ R
        (m + 1) ≫
        (haveI := TopPair.isIso_singularHomologyMap_excisionMap R (X := TopCat.of ({0}ᶜ : Set E))
          (complRay p) (complRay (-p)) (by rw [(isOpen_complRay p).interior_eq,
            (isOpen_complRay (-p)).interior_eq, complRay_union_complRay_neg p]) (m + 1)
        inv (TopPair.singularHomologyMap (TopPair.excisionMap (X := TopCat.of ({0}ᶜ : Set E))
          (complRay p) (complRay (-p))) R (m + 1))) =
    gG ≫ TopPair.singularHomologyMap (orthogonalSheetInterPairMap p (neg_ne_zero.2 one_ne_zero) _ _
      (orthogonalSheet_mem_complRay_of_neg p (neg_lt_zero.2 zero_lt_one))
      (fun _ hx ↦ (orthogonalSheet_mem_complRay_inter_complRay_neg p _ hx).2)) R (m + 1) := by
  rw [TopCat.mayerVietorisδ_eq_singularHomologyδ_left R (X := TopCat.of ({0}ᶜ : Set E))
    (isOpen_complRay p) (isOpen_complRay (-p)) (complRay_union_complRay_neg p) (m + 1) m] at h
  refine (@cancel_mono _ _ _ _ _ _ (mono_singularHomologyδ_interPair_comp R
    (X := TopCat.of ({0}ᶜ : Set E)) (complRay p) (complRay (-p))
    (TopPair.interPairSndIso _ _) m) _ _).1 ?_
  refine ((Category.assoc _ _ _).trans (whisker_eq gE ((Category.assoc _ _ _).trans
    (whisker_eq _ (Category.assoc _ _ _))))).trans (h.trans ?_)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine whisker_eq gG (singularHomologyMap_orthogonalSheetInterPairMap_singularHomologyδ R p _
    _ _ _ _ _ (fun _ ↦ ?_) m).symm
  -- The point of `complRay p ∩ complRay (-p)` is that of the subspace of the pair, which is
  -- `x ↦ x - p` only after unfolding `TopPair.interPair`.
  erw [TopPair.interPairSndIso_hom_apply, TopPair.coe_interPairSndHomeomorph_apply,
    TopPair.ofSubsetMap_snd_apply]
  rfl

/-- The excision preimage in `(complRay (-p), complRay (-p) ∩ complRay p)` of the image of a class
`gE ≫ δ` of `E ∖ {0}` is minus the image of `gG` under the sheet at `1`, under the hypothesis of
`singularHomologyδ_singularHomologyπ_inv_excisionMap_left`. -/
private theorem singularHomologyδ_singularHomologyπ_inv_excisionMap_right (p : sphere (0 : E) 1)
    {m : ℕ} {D : C}
    (gE : D ⟶ (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomology R (m + 2))
    (gG : D ⟶ (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (ℝ ∙ (p : E))ᗮ))).singularHomology R
      (m + 1))
    (h : gE ≫ (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomologyδ R (m + 2) (m + 1) ≫
        TopCat.mayerVietorisδ R (X := TopCat.of ({0}ᶜ : Set E)) (isOpen_complRay p)
          (isOpen_complRay (-p)) (complRay_union_complRay_neg p) (m + 1) m =
      gG ≫ (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (ℝ ∙ (p : E))ᗮ))).singularHomologyδ R
        (m + 1) m ≫
        ((singularHomologyFunctor C m).obj R).map (TopCat.ofHom (complZeroOrthogonalInclusion p))) :
    gE ≫ (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomologyδ R (m + 2) (m + 1) ≫
      (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set E)) (complRay p)).singularHomologyπ R
        (m + 1) ≫
        (haveI := TopPair.isIso_singularHomologyMap_excisionMap R (X := TopCat.of ({0}ᶜ : Set E))
          (complRay (-p)) (complRay p) (by rw [(isOpen_complRay p).interior_eq,
            (isOpen_complRay (-p)).interior_eq, Set.union_comm, complRay_union_complRay_neg p])
            (m + 1)
        inv (TopPair.singularHomologyMap (TopPair.excisionMap (X := TopCat.of ({0}ᶜ : Set E))
          (complRay (-p)) (complRay p)) R (m + 1))) =
    -(gG ≫ TopPair.singularHomologyMap (orthogonalSheetInterPairMap p one_ne_zero _ _
      (orthogonalSheet_mem_complRay_neg_of_pos p zero_lt_one)
      (fun _ hx ↦ (orthogonalSheet_mem_complRay_inter_complRay_neg p _ hx).1)) R (m + 1)) := by
  rw [TopCat.mayerVietorisδ_eq_neg_singularHomologyδ_right R (X := TopCat.of ({0}ᶜ : Set E))
    (isOpen_complRay p) (isOpen_complRay (-p)) (complRay_union_complRay_neg p) (m + 1) m] at h
  refine (@cancel_mono _ _ _ _ _ _ (mono_singularHomologyδ_interPair_comp R
    (X := TopCat.of ({0}ᶜ : Set E)) (complRay (-p)) (complRay p)
    (TopPair.interPairSndIso _ _ ≪≫ TopCat.isoOfHomeo
      (X := TopCat.of ↥(complRay (-p) ∩ complRay p))
      (Y := TopCat.of ↥(complRay p ∩ complRay (-p)))
      (Homeomorph.setCongr (Set.inter_comm (complRay (-p)) (complRay p)))) m) _ _).1 ?_
  refine ((Category.assoc _ _ _).trans (whisker_eq gE ((Category.assoc _ _ _).trans
    (whisker_eq _ (Category.assoc _ _ _))))).trans ?_
  refine (neg_eq_iff_eq_neg.1 (((whisker_eq gE (Preadditive.comp_neg _ _)).trans
    (Preadditive.comp_neg _ _)).symm.trans h)).trans ?_
  rw [Preadditive.neg_comp]
  refine congrArg Neg.neg (Eq.trans ?_ (Category.assoc _ _ _).symm)
  refine whisker_eq gG (singularHomologyMap_orthogonalSheetInterPairMap_singularHomologyδ R p _
    _ _ _ _ _ (fun _ ↦ ?_) m).symm
  -- As in `singularHomologyδ_singularHomologyπ_inv_excisionMap_left`.
  erw [Iso.trans_hom, ConcreteCategory.comp_apply, TopPair.interPairSndIso_hom_apply,
    TopPair.coe_interPairSndHomeomorph_apply, TopPair.ofSubsetMap_snd_apply]
  rfl

end Pieces

section InnerProductSpace

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {m : ℕ} (b : OrthonormalBasis (Fin (m + 2)) ℝ E)

/-- **The local homology generator read on the sheets over the orthogonal complement.** Let `b`
be an orthonormal basis of a real inner product space `E` of dimension `m + 2`, `p` its last
vector and `G = (ℝ ∙ p)ᗮ`. The connecting morphism of `(E, E ∖ {0})`, followed by the map to the
homology of `E ∖ {0}` relative to the complement of the line through `p`, agrees on the local
homology generator selected by the orientation of `b` with the difference of the maps induced by
the sheets `x ↦ x - p` and `x ↦ x + p` of `G` on the generator selected by the orientation of
`b.orthogonalLast`. -/
theorem singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_singularHomologyπ :
    let p : sphere (0 : E) 1 := ⟨b (Fin.last _), by simp⟩
    (singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl E) (x := 0)
        (OpenPartialHomeomorph.mem_refl_source _) b.toBasis.orientation
        ((finrank_eq_card_basis b.toBasis).trans (Fintype.card_fin _))).inv ≫
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomologyδ R (m + 2) (m + 1) ≫
      (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set E))
        (complRay p ∩ complRay (-p))).singularHomologyπ R (m + 1) =
    (singularHomologyComplSingletonIsoOfOrientation R
        (OpenPartialHomeomorph.refl (ℝ ∙ (p : E))ᗮ) (x := 0)
        (OpenPartialHomeomorph.mem_refl_source _) b.orthogonalLast.toBasis.orientation
        ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans (Fintype.card_fin _))).inv ≫
      (TopPair.singularHomologyMap (orthogonalSheetPairMap p (neg_ne_zero.2 one_ne_zero)) R
          (m + 1) -
        TopPair.singularHomologyMap (orthogonalSheetPairMap p one_ne_zero) R (m + 1)) := by
  intro p
  have hsusp :=
    singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_mayerVietorisδ R b
  dsimp only at hsusp
  generalize (singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl E)
    (x := 0) (OpenPartialHomeomorph.mem_refl_source _) b.toBasis.orientation
    ((finrank_eq_card_basis b.toBasis).trans (Fintype.card_fin _))).inv = gE at hsusp ⊢
  generalize (singularHomologyComplSingletonIsoOfOrientation R
    (OpenPartialHomeomorph.refl (ℝ ∙ (p : E))ᗮ) (x := 0)
    (OpenPartialHomeomorph.mem_refl_source _) b.orthogonalLast.toBasis.orientation
    ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans (Fintype.card_fin _))).inv = gG
    at hsusp ⊢
  have pU := singularHomologyδ_singularHomologyπ_inv_excisionMap_left R p gE gG hsusp
  have pV := singularHomologyδ_singularHomologyπ_inv_excisionMap_right R p gE gG hsusp
  rw [TopCat.singularHomologyπ_ofSubset_inter_eq_add R (X := TopCat.of ({0}ᶜ : Set E))
    (isOpen_complRay p) (isOpen_complRay (-p)) (complRay_union_complRay_neg p) (m + 1)]
  -- Each sheet factors through the pair of the member of the cover containing it.
  have e₁ : orthogonalSheetPairMap p (neg_ne_zero.2 one_ne_zero) =
      orthogonalSheetInterPairMap p (neg_ne_zero.2 one_ne_zero) _ _
        (orthogonalSheet_mem_complRay_of_neg p (neg_lt_zero.2 zero_lt_one))
        (fun _ hx ↦ (orthogonalSheet_mem_complRay_inter_complRay_neg p _ hx).2) ≫
        TopPair.ofSubsetMap (B := Subtype.val ⁻¹' complRay (-p))
          (B' := complRay p ∩ complRay (-p)) (TopCat.ofHom (ContinuousMap.subtypeVal (complRay p)))
          fun (x : complRay p) (hx : x.val ∈ complRay (-p)) ↦ ⟨x.property, hx⟩ := by
    unfold orthogonalSheetPairMap orthogonalSheetInterPairMap
    -- Both continuous maps send `x` to `x - p`.
    exact (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (by ext; rfl)).symm
  have e₂ : orthogonalSheetPairMap p one_ne_zero =
      orthogonalSheetInterPairMap p one_ne_zero _ _
        (orthogonalSheet_mem_complRay_neg_of_pos p zero_lt_one)
        (fun _ hx ↦ (orthogonalSheet_mem_complRay_inter_complRay_neg p _ hx).1) ≫
        TopPair.ofSubsetMap (B := Subtype.val ⁻¹' complRay p)
          (B' := complRay p ∩ complRay (-p))
          (TopCat.ofHom (ContinuousMap.subtypeVal (complRay (-p))))
          fun (x : complRay (-p)) (hx : x.val ∈ complRay p) ↦ ⟨hx, x.property⟩ := by
    unfold orthogonalSheetPairMap orthogonalSheetInterPairMap
    exact (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (by ext; rfl)).symm
  rw [e₁, e₂, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_comp,
    Preadditive.comp_sub, sub_eq_add_neg]
  -- Reassociate by `Eq.trans`, as the homology of `E ∖ {0}` appears under several names.
  refine ((whisker_eq gE (Preadditive.comp_add _ _ _ _ _ _)).trans
    (Preadditive.comp_add _ _ _ _ _ _)).trans (congrArg₂ (· + ·) ?_ ?_)
  · refine Eq.trans ?_ ((eq_whisker pU _).trans (Category.assoc _ _ _))
    exact Eq.symm ((Category.assoc _ _ _).trans (whisker_eq gE ((Category.assoc _ _ _).trans
      (whisker_eq _ (Category.assoc _ _ _)))))
  · refine Eq.trans ?_ ((eq_whisker pV _).trans ((Preadditive.neg_comp _ _).trans
      (congrArg Neg.neg (Category.assoc _ _ _))))
    exact Eq.symm ((Category.assoc _ _ _).trans (whisker_eq gE ((Category.assoc _ _ _).trans
      (whisker_eq _ (Category.assoc _ _ _)))))

/-- **The local orientation read on the sheets over the orthogonal complement.** Let `b` be an
orthonormal basis of a real inner product space `E` of dimension `m + 2`, `p` its last vector and
`G = (ℝ ∙ p)ᗮ`. The connecting morphism of `(E, E ∖ {0})`, followed by the map to the homology of
`E ∖ {0}` relative to the complement of the line through `p`, sends the local orientation of `E`
selected by the orientation of `b` to the image of the local orientation of `G` selected by the
orientation of `b.orthogonalLast` under the sheet `x ↦ x - p`, minus its image under the sheet
`x ↦ x + p`. -/
theorem singularHomologyπ_singularHomologyδ_localOrientation :
    let p : sphere (0 : E) 1 := ⟨b (Fin.last _), by simp⟩
    (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set E))
        (complRay p ∩ complRay (-p))).singularHomologyπ (ModuleCat.of ℤ (ULift.{w} ℤ)) (m + 1)
        ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomologyδ
          (ModuleCat.of ℤ (ULift.{w} ℤ)) (m + 2) (m + 1) rfl
          (b.toBasis.orientation.localOrientation
            ((finrank_eq_card_basis b.toBasis).trans (Fintype.card_fin _))).val) =
      TopPair.singularHomologyMap (orthogonalSheetPairMap p (neg_ne_zero.2 one_ne_zero))
          (ModuleCat.of ℤ (ULift.{w} ℤ)) (m + 1)
          (b.orthogonalLast.toBasis.orientation.localOrientation
            ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans (Fintype.card_fin _))).val -
        TopPair.singularHomologyMap (orthogonalSheetPairMap p one_ne_zero)
          (ModuleCat.of ℤ (ULift.{w} ℤ)) (m + 1)
          (b.orthogonalLast.toBasis.orientation.localOrientation
            ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans (Fintype.card_fin _))).val := by
  intro p
  rw [Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl,
    Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  -- Evaluate the identity of morphisms at `1`; a composite applied to an element is the
  -- composition of the applications by definition.
  exact congrArg (fun f ↦ f 1)
    (singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_singularHomologyπ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) b)

end InnerProductSpace

section Prod

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The sheet `x ↦ (x, t)` of `F × ℝ` at height `t ≠ 0`, as a map into `(F × ℝ) ∖ {0}`. -/
def prodSheet {t : ℝ} (ht : t ≠ 0) : C(F, ({0}ᶜ : Set (F × ℝ))) where
  toFun x := ⟨(x, t), fun h ↦ ht (congrArg Prod.snd h)⟩
  continuous_toFun := by fun_prop

omit [NormedSpace ℝ F] in
@[simp]
theorem coe_prodSheet_apply {t : ℝ} (ht : t ≠ 0) (x : F) : (prodSheet ht x : F × ℝ) = (x, t) :=
  (rfl)

/-- **The sheets of `F × ℝ`.** For `t ≠ 0`, the map of pairs
`(F, F ∖ {0}) ⟶ ((F × ℝ) ∖ {0}, (F ∖ {0}) × ℝ)`, `x ↦ (x, t)`. -/
def prodSheetPairMap {t : ℝ} (ht : t ≠ 0) :
    TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F)) ⟶
      TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ))) {x | (x : F × ℝ).1 ≠ 0} :=
  TopPair.ofSubsetMap (TopCat.ofHom (prodSheet ht)) fun _ hx ↦ hx

omit [NormedSpace ℝ F] in
theorem prodSheetPairMap_fst {t : ℝ} (ht : t ≠ 0) :
    TopPair.Hom.fst (prodSheetPairMap (F := F) ht) = TopCat.ofHom (prodSheet ht) :=
  TopPair.ofSubsetMap_fst _ _

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The identity of `TauCeti.LocalOrientation.singularHomologyπ_singularHomologyδ_prod` follows
from the same identity in `E`, along a continuous linear equivalence `φ : F × ℝ ≃L[ℝ] E` with
`φ (x, t) = ψ x + t • p` for a continuous linear equivalence `ψ : F ≃L[ℝ] (ℝ ∙ p)ᗮ`. -/
private theorem singularHomologyπ_singularHomologyδ_of_continuousLinearEquiv {m : ℕ}
    (p : sphere (0 : E) 1) (φ : (F × ℝ) ≃L[ℝ] E) (ψ : F ≃L[ℝ] (ℝ ∙ (p : E))ᗮ)
    (hφ : ∀ x t, φ (x, t) = (ψ x : E) + t • (p : E))
    (w : LocalOrientation (F × ℝ) 0 (m + 1 + 1)) (z : LocalOrientation F 0 (m + 1))
    (h : (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set E))
        (complRay p ∩ complRay (-p))).singularHomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)
        ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomologyδ
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) (m + 1) rfl (w.map φ.complZeroPairIso).val) =
      TopPair.singularHomologyMap (orthogonalSheetPairMap p (neg_ne_zero.2 one_ne_zero))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) (z.map ψ.complZeroPairIso).val -
        TopPair.singularHomologyMap (orthogonalSheetPairMap p one_ne_zero)
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) (z.map ψ.complZeroPairIso).val) :
    (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ)))
        {x | (x : F × ℝ).1 ≠ 0}).singularHomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)
      ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (F × ℝ)))).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) (m + 1) rfl w.val) =
    TopPair.singularHomologyMap (prodSheetPairMap (F := F) (neg_ne_zero.2 one_ne_zero))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) z.val -
      TopPair.singularHomologyMap (prodSheetPairMap (F := F) one_ne_zero)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) z.val := by
  -- `φ` carries `(F ∖ {0}) × ℝ` onto the complement of the line through `p`.
  let eφ : ({0}ᶜ : Set (F × ℝ)) ≃ₜ ({0}ᶜ : Set E) :=
    φ.toHomeomorph.subtype fun _ ↦ φ.map_ne_zero_iff.symm
  have hI : ∀ x : ({0}ᶜ : Set (F × ℝ)), x ∈ {x : ({0}ᶜ : Set (F × ℝ)) | (x : F × ℝ).1 ≠ 0} ↔
      eφ x ∈ complRay p ∩ complRay (-p) := by
    rintro ⟨⟨y, t⟩, hx⟩
    rw [mem_complRay_inter_complRay_neg_iff]
    -- The point `eφ x` of `E ∖ {0}` is `φ x` by definition.
    change y ≠ 0 ↔ φ (y, t) ∉ ℝ ∙ (p : E)
    rw [hφ, add_smul_mem_span_singleton_iff, ψ.map_eq_zero_iff]
  let I := TopPair.ofSubsetIso (X := TopCat.of ({0}ᶜ : Set (F × ℝ)))
    (Y := TopCat.of ({0}ᶜ : Set E)) eφ hI
  have hinj : Function.Injective
      (TopPair.singularHomologyMap I.hom (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)) := by
    intro a a' h
    have h' := congrArg (TopPair.singularHomologyMap I.inv (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)) h
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← TopPair.singularHomologyMap_comp, I.hom_inv_id, TopPair.singularHomologyMap_id,
      ConcreteCategory.id_apply, ConcreteCategory.id_apply] at h'
  have hfst : TopPair.Hom.fst I.hom = TopPair.Hom.snd φ.complZeroPairIso.hom := by
    ext x
    refine Subtype.ext ?_
    rw [ContinuousLinearEquiv.complZeroPairIso_hom, TopPair.ofSubsetIso_hom]
    -- Both sides are `φ x`; the subspace of `TopPair.ofSubset` is the subtype only after
    -- unfolding, and `eφ` is `φ` on the subtype by definition.
    erw [TopPair.ofSubsetMap_snd_apply, TopPair.ofSubsetMap_fst_apply]
    rfl
  have M₁ : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (F × ℝ)))).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) (m + 1) ≫
      (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ)))
        {x | (x : F × ℝ).1 ≠ 0}).singularHomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) ≫
      TopPair.singularHomologyMap I.hom (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) =
    TopPair.singularHomologyMap φ.complZeroPairIso.hom (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) ≫
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) (m + 1) ≫
      (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set E))
        (complRay p ∩ complRay (-p))).singularHomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) := by
    refine (whisker_eq _ (TopPair.singularHomologyπ_naturality (f := I.hom)
      (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (n := m + 1)).symm).trans ?_
    refine Eq.trans ?_ (TopPair.singularHomologyδ_naturality_assoc _ φ.complZeroPairIso.hom
      (m + 2) (m + 1) rfl _)
    rw [hfst]
    exact (Category.assoc _ _ _).symm
  have M₂ : ∀ {s : ℝ} (hs : s ≠ 0), (prodSheetPairMap (F := F) hs ≫ I.hom :) =
      ψ.complZeroPairIso.hom ≫ orthogonalSheetPairMap p hs := fun {s} hs ↦
    TopPair.hom_ext_of_fst _ (by
      ext x
      refine Subtype.ext ?_
      rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, TopPair.ofSubsetIso_hom, prodSheetPairMap,
        orthogonalSheetPairMap, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      -- The sources of the maps of pairs are the punctured spaces only after unfolding
      -- `TopPair.ofSubset`.
      erw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
        TopPair.ofSubsetMap_fst_apply]
      exact (hφ x s).trans (congrArg (· + s • (p : E))
        (congrArg Subtype.val (ψ.complZeroPairIso_hom_fst_apply x).symm)))
  apply hinj
  rw [map_sub, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp, M₂, M₂,
    TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_comp]
  rw [LocalOrientation.coe_map, LocalOrientation.coe_map] at h
  exact (congrArg (fun f ↦ f w.val) M₁).trans h

/-- **The product local orientation of `F × ℝ` read on the sheets `F × {±1}`.** Let `F` be a real
normed space of dimension `m + 1`, `z` a local orientation of `F` at `0`, and
`w = TauCeti.LocalOrientation.prod z ι` the local orientation of `F × ℝ` at `0`, where `ι` is the
local orientation of `ℝ` selected by its standard orientation. The connecting morphism of
`(F × ℝ, (F × ℝ) ∖ {0})`, followed by the map
`Hₘ₊₁((F × ℝ) ∖ {0}) ⟶ Hₘ₊₁((F × ℝ) ∖ {0}, (F ∖ {0}) × ℝ)`, sends `w` to `j₋₁ z - j₁ z`, where
`jₜ` is the sheet `x ↦ (x, t)` (`TauCeti.prodSheetPairMap`): the sign `s m` with
`w ↦ s m • (j₁ z - j₋₁ z)` is `-1` in every dimension. -/
theorem LocalOrientation.singularHomologyπ_singularHomologyδ_prod {m : ℕ}
    (hF : finrank ℝ F = m + 1) (z : LocalOrientation F 0 (m + 1)) :
    (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ)))
        {x | (x : F × ℝ).1 ≠ 0}).singularHomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)
      ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (F × ℝ)))).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) (m + 1) rfl
        (LocalOrientation.prod (n := 0) (d := m + 1) hF (finrank_self ℝ) rfl z
          ((Basis.singleton (Fin 1) ℝ).orientation.localOrientation (finrank_self ℝ))).val) =
    TopPair.singularHomologyMap (prodSheetPairMap (F := F) (neg_ne_zero.2 one_ne_zero))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) z.val -
      TopPair.singularHomologyMap (prodSheetPairMap (F := F) one_ne_zero)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) z.val := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  obtain ⟨ω, rfl⟩ := Orientation.localOrientation_surjective hF z
  -- A basis `e` of `F` with orientation `ω`, and the basis `B` of `F × ℝ` listing `e` before
  -- `(0, 1)`, whose orientation is the product orientation.
  set e := (Module.finBasisOfFinrankEq ℝ F hF).adjustToOrientation ω
  have he : e.orientation = ω := Basis.orientation_adjustToOrientation _ _
  have hd : m + 1 + (0 + 1) = m + 1 + 1 := rfl
  set B := ((e.prod (Basis.singleton (Fin 1) ℝ)).reindex finSumFinEquiv).reindex (finCongr hd)
  have hFR : finrank ℝ (F × ℝ) = m + 1 + 1 := (finrank_eq_card_basis B).trans (Fintype.card_fin _)
  have hw : LocalOrientation.prod (n := 0) (d := m + 1) hF (finrank_self ℝ) rfl
      (ω.localOrientation hF) ((Basis.singleton (Fin 1) ℝ).orientation.localOrientation
        (finrank_self ℝ)) = B.orientation.localOrientation hFR := by
    rw [LocalOrientation.prod_localOrientation, ← he, Orientation.prod_basis_orientation,
      ← Basis.orientation_reindex]
  -- `φ` carries `B` to the standard basis `b` of the Euclidean space, and `ψ` carries `e` to
  -- `b.orthogonalLast`.
  let b : OrthonormalBasis (Fin (m + 2)) ℝ (EuclideanSpace ℝ (Fin (m + 2))) :=
    EuclideanSpace.basisFun _ ℝ
  let φ : (F × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 2)) :=
    (B.equiv b.toBasis (Equiv.refl _)).toContinuousLinearEquiv
  let p : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 := ⟨b (Fin.last _), by simp⟩
  let ψ : F ≃L[ℝ] (ℝ ∙ (p : EuclideanSpace ℝ (Fin (m + 2))))ᗮ :=
    (e.equiv b.orthogonalLast.toBasis (Equiv.refl _)).toContinuousLinearEquiv
  have hB : ∀ j : Fin (m + 1), B j.castSucc = (e j, 0) := fun j ↦ by simp [B, Basis.prod_apply]
  have hB' : B (Fin.last _) = (0, 1) := by simp [B, Basis.prod_apply]
  have hφ₀ : ∀ x, φ (x, 0) = (ψ x : EuclideanSpace ℝ (Fin (m + 2))) := by
    have h : (φ : F × ℝ →L[ℝ] EuclideanSpace ℝ (Fin (m + 2))).toLinearMap ∘ₗ LinearMap.inl ℝ F ℝ =
        (ℝ ∙ (p : EuclideanSpace ℝ (Fin (m + 2))))ᗮ.subtype ∘ₗ
          (ψ : F →L[ℝ] (ℝ ∙ (p : EuclideanSpace ℝ (Fin (m + 2))))ᗮ).toLinearMap := by
      refine e.ext fun j ↦ ?_
      have h₁ : φ (e j, 0) = b j.castSucc := by
        rw [← hB]; exact (B.equiv_apply j.castSucc b.toBasis (Equiv.refl _)).trans (by simp)
      have h₂ : ψ (e j) = b.orthogonalLast j :=
        (e.equiv_apply j b.orthogonalLast.toBasis (Equiv.refl _)).trans (by simp)
      simp [h₁, h₂]
    exact fun x ↦ LinearMap.congr_fun h x
  have hφ₁ : φ (0, 1) = (p : EuclideanSpace ℝ (Fin (m + 2))) := by
    rw [← hB']; exact (B.equiv_apply _ b.toBasis (Equiv.refl _)).trans (by simp [p])
  have hφ : ∀ x t, φ (x, t) = (ψ x : EuclideanSpace ℝ (Fin (m + 2))) + t • (p : _) := by
    intro x t
    rw [← hφ₀, ← hφ₁, ← map_smul, ← map_add, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one,
      Prod.mk_add_mk, add_zero, zero_add]
  have hwE : (B.orientation.localOrientation hFR).map φ.complZeroPairIso =
      b.toBasis.orientation.localOrientation
        ((finrank_eq_card_basis b.toBasis).trans (Fintype.card_fin _)) := by
    rw [← Orientation.localOrientation_map φ _ hFR, ← Basis.orientation_map]
    rw [show B.map (φ : (F × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 2))) = b.toBasis from
      (B.map_equiv b.toBasis (Equiv.refl _)).trans b.toBasis.reindex_refl]
  have hzG : (ω.localOrientation hF).map ψ.complZeroPairIso =
      b.orthogonalLast.toBasis.orientation.localOrientation
        ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans (Fintype.card_fin _)) := by
    rw [← Orientation.localOrientation_map ψ _ hF, ← he, ← Basis.orientation_map]
    rw [show e.map (ψ : F ≃ₗ[ℝ] (ℝ ∙ (p : EuclideanSpace ℝ (Fin (m + 2))))ᗮ) =
        b.orthogonalLast.toBasis from
      (e.map_equiv b.orthogonalLast.toBasis (Equiv.refl _)).trans
        b.orthogonalLast.toBasis.reindex_refl]
  rw [hw]
  refine singularHomologyπ_singularHomologyδ_of_continuousLinearEquiv p φ ψ hφ _ _ ?_
  rw [hwE, hzG]
  exact singularHomologyπ_singularHomologyδ_localOrientation b

end Prod

end TauCeti
