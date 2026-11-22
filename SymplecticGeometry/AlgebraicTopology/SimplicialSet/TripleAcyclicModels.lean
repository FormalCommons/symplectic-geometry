/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.AlgebraicTopology.SimplicialSet.EilenbergZilber

/-!
# Acyclic models for three factors of simplicial chains

Let `φ` and `ψ` be two families of chain maps
`(C(K; R) ⊗ C(L; S)) ⊗ C(M; T) ⟶ C((K × L) × M; U)`, one for each triple of simplicial sets,
natural in maps `K ⟶ K'`, `L ⟶ L'` and `M ⟶ M'`, and equal in degree zero.  Then `φ K L M` and
`ψ K L M` are chain homotopic (`SSet.tripleTensorChainComplexHomotopy`), through a homotopy which
is natural in all three simplicial sets (`SSet.tripleTensorChainComplexHomotopy_hom_naturality`).

This is the method of acyclic models, in the form of Tau Ceti's two-factor statements of
`TauCeti/AlgebraicTopology/SimplicialSet/EilenbergZilber.lean`.  The source is free on models, as
in `SSet.tensorChainComplexHomotopy`: the summand of a triple of simplices `x`, `y`, `z` of
dimensions `p`, `q`, `r` is the image of the summand of the triple of top simplices of `Δ[p]`,
`Δ[q]` and `Δ[r]` under the maps classifying `x`, `y` and `z`.  The target is acyclic on models, as
in `SSet.prodChainComplexHomotopy`: on the simplicial chains of `(Δ[p] × Δ[q]) × Δ[r]`, the cone
from the vertex `((0, 0), 0)` (`SSet.stdSimplex.tripleProdConeChain`) is a contracting homotopy in
positive degrees (`SSet.stdSimplex.tripleProdConeChain_d`).  This cone is the cone
`SSet.stdSimplex.prodCone` of Tau Ceti on the first two factors together with the cone
`SSet.stdSimplex.cone` on the third; the product `Δ[p] × Δ[q]` is not a standard simplex, so the
existing cone `SSet.stdSimplex.prodConeChain` does not apply to the triple product as it stands.
The homotopy is then built degree by degree on the models, and extended to all simplicial sets by
naturality.

The proofs adapt those of Tau Ceti's `SSet.tensorChainComplexHomotopy`,
`SSet.tensorChainComplexHomotopy_hom_naturality` and their auxiliary lemmas, and the cone and its
boundary formula adapt Tau Ceti's `SSet.stdSimplex.prodConeChain` and
`SSet.stdSimplex.prodConeChain_d`.  Maps out of the triple tensor products of chain groups are
described as in Tau Ceti's `SSet.tensorChainComplexXDesc`.

## Main definitions and results

* `SSet.stdSimplex.tripleProdConeChain`: the cone from `((0, 0), 0)` on the simplicial chains of
  `(Δ[a] × Δ[b]) × Δ[c]`, with `SSet.stdSimplex.tripleProdConeChain_d` its boundary formula.
* `SSet.tripleTensorChainComplexXDesc`: the morphism out of
  `(Cₚ(K; R) ⊗ C_q(L; S)) ⊗ C_r(M; T)` given on the summand of each triple of simplices, with
  `SSet.tripleTensorChainComplexX_hom_ext`.
* `SSet.ιTripleTensorChainComplex`: the summand of a triple of simplices in the chains of degree `n`
  of `(C(K; R) ⊗ C(L; S)) ⊗ C(M; T)`, with the extensionality lemma
  `SSet.tripleTensorChainComplex_X_hom_ext`.
* `SSet.tripleTensorChainComplexHomotopy`: two natural families of chain maps
  `(C(K; R) ⊗ C(L; S)) ⊗ C(M; T) ⟶ C((K × L) × M; U)` which agree in degree zero are chain
  homotopic, and `SSet.tripleTensorChainComplexHomotopy_hom_naturality`: the homotopy is natural.

## References

* S. Eilenberg and S. Mac Lane, *Acyclic models*, Amer. J. Math. 75 (1953).
* C. Weibel, *An Introduction to Homological Algebra*, Section 8.6.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial HomologicalComplex

universe w v u

namespace SSet

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

namespace stdSimplex

/-- The cone from the vertex `((0, 0), 0)` on a simplex of the product `(Δ[a] ⊗ Δ[b]) ⊗ Δ[c]`:
the cone `SSet.stdSimplex.prodCone` on the first two components and the cone
`SSet.stdSimplex.cone` on the third. -/
def tripleProdCone {a b c m : ℕ} (x : (((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]) _⦋m⦌) :
    (((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]) _⦋m + 1⦌ :=
  (prodCone x.1, cone x.2)

lemma tripleProdCone_def {a b c m : ℕ} (x : (((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]) _⦋m⦌) :
    tripleProdCone x = (prodCone x.1, cone x.2) :=
  (rfl)

/-- The zeroth face of the cone on a simplex `x` of `(Δ[a] ⊗ Δ[b]) ⊗ Δ[c]` is `x`. -/
lemma δ_zero_tripleProdCone {a b c m : ℕ} (x : (((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]) _⦋m⦌) :
    (((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]).δ 0 (tripleProdCone x) = x :=
  Prod.ext (δ_zero_prodCone _) (δ_zero_cone _)

/-- The `(i + 1)`-st face of the cone on a simplex `x` of `(Δ[a] ⊗ Δ[b]) ⊗ Δ[c]` is the cone on
the `i`-th face of `x`. -/
lemma δ_succ_tripleProdCone {a b c m : ℕ} (x : (((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]) _⦋m + 1⦌)
    (i : Fin (m + 2)) :
    (((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]).δ i.succ (tripleProdCone x) =
      tripleProdCone ((((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]).δ i x) :=
  Prod.ext (δ_succ_prodCone _ _) (δ_succ_cone _ _)

section Chain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

variable (a b c : ℕ) (T : C)

/-- The cone from the vertex `((0, 0), 0)`, as a map raising the degree of the simplicial chains of
`(Δ[a] ⊗ Δ[b]) ⊗ Δ[c]` by one.  It is a contracting homotopy in positive degrees
(`SSet.stdSimplex.tripleProdConeChain_d`). -/
def tripleProdConeChain (m : ℕ) :
    ((((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]).chainComplex T).X m ⟶
      ((((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]).chainComplex T).X (m + 1) :=
  Cofan.IsColimit.desc (isColimitChainComplexXCofan _ T m) fun x ↦
    (((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]).ιChainComplex (tripleProdCone x)

@[reassoc (attr := simp)]
lemma ιChainComplex_tripleProdConeChain {m : ℕ}
    (x : (((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]) _⦋m⦌) :
    (((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]).ιChainComplex (R := T) x ≫ tripleProdConeChain a b c T m =
      (((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]).ιChainComplex (tripleProdCone x) :=
  Cofan.IsColimit.fac _ _ x

/-- The cone on the simplicial chains of `(Δ[a] ⊗ Δ[b]) ⊗ Δ[c]` is a contracting homotopy in
positive degrees: `∂ (c ∘ σ) = σ - c ∘ ∂ σ` for a chain `σ` of positive degree. -/
lemma tripleProdConeChain_d (m : ℕ) :
    tripleProdConeChain a b c T (m + 1) ≫
        ((((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]).chainComplex T).d (m + 1 + 1) (m + 1) =
      𝟙 _ - ((((Δ[a] : SSet.{w}) ⊗ Δ[b]) ⊗ Δ[c]).chainComplex T).d (m + 1) m ≫
        tripleProdConeChain a b c T m := by
  ext x
  simp only [ιChainComplex_tripleProdConeChain_assoc, ιChainComplex_d, Preadditive.comp_sub,
    Category.comp_id, ιChainComplex_d_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp,
    ιChainComplex_tripleProdConeChain]
  rw [Fin.sum_univ_succ, δ_zero_tripleProdCone, Fin.val_zero, pow_zero, one_smul]
  simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    sub_eq_add_neg, δ_succ_tripleProdCone]

end Chain

end stdSimplex

section TripleTensor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  {K L M : SSet.{w}} {R S T A : C} {p q r : ℕ}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft R)]
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft (R ⊗ S))]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]

/-- The morphism out of `(Cₚ(K; R) ⊗ C_q(L; S)) ⊗ C_r(M; T)` given by a morphism
`φ x y z : (R ⊗ S) ⊗ T ⟶ A` for each `p`-simplex `x` of `K`, `q`-simplex `y` of `L` and
`r`-simplex `z` of `M` (`SSet.ιChainComplex_tensorHom_tensorHom_tripleTensorChainComplexXDesc`).
When tensoring preserves coproducts, `(Cₚ(K; R) ⊗ C_q(L; S)) ⊗ C_r(M; T)` is the coproduct of one
copy of `(R ⊗ S) ⊗ T` for each such triple. -/
def tripleTensorChainComplexXDesc (φ : K _⦋p⦌ → L _⦋q⦌ → M _⦋r⦌ → ((R ⊗ S) ⊗ T ⟶ A)) :
    ((K.chainComplex R).X p ⊗ (L.chainComplex S).X q) ⊗ (M.chainComplex T).X r ⟶ A :=
  Cofan.IsColimit.desc (isColimitCofanMkObjOfIsColimit
    (tensorRight ((L.chainComplex S).X q) ⋙ tensorRight ((M.chainComplex T).X r)) _ _
      (K.isColimitChainComplexXCofan R p)) fun x ↦
    Cofan.IsColimit.desc (isColimitCofanMkObjOfIsColimit
      (tensorLeft R ⋙ tensorRight ((M.chainComplex T).X r)) _ _
        (L.isColimitChainComplexXCofan S q)) fun y ↦
      Cofan.IsColimit.desc (isColimitCofanMkObjOfIsColimit (tensorLeft (R ⊗ S)) _ _
        (M.isColimitChainComplexXCofan T r)) (φ x y)

/-- The morphism `SSet.tripleTensorChainComplexXDesc φ` on the summand of a triple of simplices
`(x, y, z)` is `φ x y z`. -/
@[reassoc]
lemma ιChainComplex_tensorHom_tensorHom_tripleTensorChainComplexXDesc
    (φ : K _⦋p⦌ → L _⦋q⦌ → M _⦋r⦌ → ((R ⊗ S) ⊗ T ⟶ A)) (x : K _⦋p⦌) (y : L _⦋q⦌)
    (z : M _⦋r⦌) :
    ((K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ⊗ₘ M.ιChainComplex z) ≫
        tripleTensorChainComplexXDesc φ = φ x y z := by
  have h₁ := Cofan.IsColimit.fac (isColimitCofanMkObjOfIsColimit
    (tensorRight ((L.chainComplex S).X q) ⋙ tensorRight ((M.chainComplex T).X r)) _ _
      (K.isColimitChainComplexXCofan R p)) (fun x ↦
    Cofan.IsColimit.desc (isColimitCofanMkObjOfIsColimit
      (tensorLeft R ⋙ tensorRight ((M.chainComplex T).X r)) _ _
        (L.isColimitChainComplexXCofan S q)) fun y ↦
      Cofan.IsColimit.desc (isColimitCofanMkObjOfIsColimit (tensorLeft (R ⊗ S)) _ _
        (M.isColimitChainComplexXCofan T r)) (φ x y)) x
  have h₂ := Cofan.IsColimit.fac (isColimitCofanMkObjOfIsColimit
      (tensorLeft R ⋙ tensorRight ((M.chainComplex T).X r)) _ _
        (L.isColimitChainComplexXCofan S q)) (fun y ↦
      Cofan.IsColimit.desc (isColimitCofanMkObjOfIsColimit (tensorLeft (R ⊗ S)) _ _
        (M.isColimitChainComplexXCofan T r)) (φ x y)) y
  have h₃ := Cofan.IsColimit.fac (isColimitCofanMkObjOfIsColimit (tensorLeft (R ⊗ S)) _ _
        (M.isColimitChainComplexXCofan T r)) (φ x y) z
  simp only [cofan_mk_inj, Functor.comp_map, Functor.flip_obj_map, curriedTensor_map_app,
    curriedTensor_obj_map] at h₁ h₂ h₃
  rw [tensorHom_def', tensorHom_def', comp_whiskerRight, Category.assoc, Category.assoc,
    tripleTensorChainComplexXDesc, h₁, h₂, h₃]

/-- Morphisms out of `(Cₚ(K; R) ⊗ C_q(L; S)) ⊗ C_r(M; T)` are determined on the summands of
triples of simplices. -/
lemma tripleTensorChainComplexX_hom_ext
    {f g : ((K.chainComplex R).X p ⊗ (L.chainComplex S).X q) ⊗ (M.chainComplex T).X r ⟶ A}
    (h : ∀ (x : K _⦋p⦌) (y : L _⦋q⦌) (z : M _⦋r⦌),
      ((K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ⊗ₘ M.ιChainComplex z) ≫ f =
        ((K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ⊗ₘ M.ιChainComplex z) ≫ g) :
    f = g := by
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit
    (tensorRight ((L.chainComplex S).X q) ⋙ tensorRight ((M.chainComplex T).X r)) _ _
      (K.isColimitChainComplexXCofan R p)) _ _ fun x ↦ Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (tensorLeft R ⋙ tensorRight ((M.chainComplex T).X r)) _ _
      (L.isColimitChainComplexXCofan S q)) _ _ fun y ↦ Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (tensorLeft (R ⊗ S)) _ _
      (M.isColimitChainComplexXCofan T r)) _ _ fun z ↦ ?_
  simpa [tensorHom_def', comp_whiskerRight] using h x y z

end TripleTensor

section TripleAcyclicModels

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T U : C}

/-- The inclusion of the summand `(R ⊗ S) ⊗ T` of a triple of simplices `(x, y, z)` of
dimensions `p`, `q` and `r`, with `p + q + r = n`, into the chains of degree `n` of
`(C(K; R) ⊗ C(L; S)) ⊗ C(M; T)`.  These inclusions determine maps out of that object
(`SSet.tripleTensorChainComplex_X_hom_ext`). -/
def ιTripleTensorChainComplex {K L M : SSet.{w}} {p q r : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌)
    (z : M _⦋r⦌) (n : ℕ) (h : p + q + r = n) :
    (R ⊗ S) ⊗ T ⟶ ((K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T).X n :=
  ((K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ⊗ₘ M.ιChainComplex z) ≫
    (ιTensorObj _ _ p q (p + q) rfl ▷ _) ≫
      ιTensorObj (K.chainComplex R ⊗ L.chainComplex S) (M.chainComplex T) (p + q) r n h

lemma ιTripleTensorChainComplex_def {K L M : SSet.{w}} {p q r : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌)
    (z : M _⦋r⦌) (n : ℕ) (h : p + q + r = n) :
    ιTripleTensorChainComplex (R := R) (S := S) (T := T) x y z n h =
      ((K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ⊗ₘ M.ιChainComplex z) ≫
        (ιTensorObj _ _ p q (p + q) rfl ▷ _) ≫
          ιTensorObj (K.chainComplex R ⊗ L.chainComplex S) (M.chainComplex T) (p + q) r n h :=
  (rfl)

/-- The tensor product of the chain maps of `f`, `g` and `h'` sends the summand of a triple of
simplices `(x, y, z)` to the summand of `(f x, g y, h' z)`. -/
@[reassoc]
lemma ιTripleTensorChainComplex_tensorHom_f {K K' L L' M M' : SSet.{w}} (f : K ⟶ K') (g : L ⟶ L')
    (h' : M ⟶ M') {p q r : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) (z : M _⦋r⦌) (n : ℕ)
    (h : p + q + r = n) :
    ιTripleTensorChainComplex (R := R) (S := S) (T := T) x y z n h ≫
        ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h' T).f n =
      ιTripleTensorChainComplex (f.app _ x) (g.app _ y) (h'.app _ z) n h := by
  rw [ιTripleTensorChainComplex_def, ιTripleTensorChainComplex_def, Category.assoc, Category.assoc,
    tensorHom_eq_mapBifunctorMap (f₁ := chainComplexMap f R ⊗ₘ chainComplexMap g S),
    HomologicalComplex.ι_tensorHom, whiskerRight_comp_tensorHom_assoc,
    tensorHom_eq_mapBifunctorMap (f₁ := chainComplexMap f R),
    HomologicalComplex.ι_tensorHom,
    ← tensorHom_comp_whiskerRight_assoc, ← Category.assoc, ← Category.assoc,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ι_chainComplexMap_f, ι_chainComplexMap_f,
    ι_chainComplexMap_f, Category.assoc]

/-- The top simplex of the model `Δ[p]`. -/
private abbrev topSimplex (p : ℕ) : (Δ[p] : SSet.{w}) _⦋p⦌ := yonedaEquiv (𝟙 _)

/-- The summand of a triple of simplices `(x, y, z)` is the image of the summand of the triple of
top simplices of the models `Δ[p]`, `Δ[q]` and `Δ[r]` under the maps classifying `x`, `y`
and `z`. -/
private lemma ιTripleTensorChainComplex_eq_model {K L M : SSet.{w}} {p q r : ℕ} (x : K _⦋p⦌)
    (y : L _⦋q⦌) (z : M _⦋r⦌) (n : ℕ) (h : p + q + r = n) :
    ιTripleTensorChainComplex (R := R) (S := S) (T := T) x y z n h =
      ιTripleTensorChainComplex (topSimplex p) (topSimplex q) (topSimplex r) n h ≫
        ((chainComplexMap (yonedaEquiv.symm x) R ⊗ₘ chainComplexMap (yonedaEquiv.symm y) S) ⊗ₘ
          chainComplexMap (yonedaEquiv.symm z) T).f n := by
  rw [ιTripleTensorChainComplex_tensorHom_f, yonedaEquiv_symm_app_id, yonedaEquiv_symm_app_id,
    yonedaEquiv_symm_app_id]

/-- A natural family of maps out of `(C(K; R) ⊗ C(L; S)) ⊗ C(M; T)` is determined by its values on
the models: on the summand of a triple of simplices `(x, y, z)` it is the image of its value on
the triple of top simplices of `Δ[p]`, `Δ[q]` and `Δ[r]` under the map classifying
`((x, y), z)`. -/
private lemma ιTripleTensorChainComplex_comp_eq_model {n m : ℕ}
    (u : ∀ K L M : SSet.{w}, ((K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T).X n ⟶
      (((K ⊗ L) ⊗ M).chainComplex U).X m)
    (hu : ∀ ⦃K K' L L' M M' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L') (h' : M ⟶ M'),
      ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h' T).f n ≫ u K' L' M' =
        u K L M ≫ (chainComplexMap ((f ⊗ₘ g) ⊗ₘ h') U).f m)
    {K L M : SSet.{w}} {p q r : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) (z : M _⦋r⦌) (h : p + q + r = n) :
    ιTripleTensorChainComplex x y z n h ≫ u K L M =
      ιTripleTensorChainComplex (topSimplex p) (topSimplex q) (topSimplex r) n h ≫ u _ _ _ ≫
        (chainComplexMap ((yonedaEquiv.symm x ⊗ₘ yonedaEquiv.symm y) ⊗ₘ yonedaEquiv.symm z) U).f
          m := by
  rw [ιTripleTensorChainComplex_eq_model, Category.assoc, hu]

variable [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft R)]
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft (R ⊗ S))]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)] in
/-- Morphisms out of the chains of degree `n` of `(C(K; R) ⊗ C(L; S)) ⊗ C(M; T)` are equal if
they agree on the summand `SSet.ιTripleTensorChainComplex` of each triple of simplices whose
dimensions add up to `n`. -/
lemma tripleTensorChainComplex_X_hom_ext {K L M : SSet.{w}} {n : ℕ} {A : C}
    {f g : ((K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T).X n ⟶ A}
    (H : ∀ (p q r : ℕ) (h : p + q + r = n) (x : K _⦋p⦌) (y : L _⦋q⦌) (z : M _⦋r⦌),
      ιTripleTensorChainComplex x y z n h ≫ f = ιTripleTensorChainComplex x y z n h ≫ g) :
    f = g := by
  refine mapBifunctor₁₂.hom_ext fun p q r h ↦ tripleTensorChainComplexX_hom_ext fun x y z ↦ ?_
  rw [mapBifunctor₁₂.ι_eq_whiskerRight _ _ _ p q r (p + q) n rfl h]
  simpa only [ιTripleTensorChainComplex_def, Category.assoc] using H p q r h x y z

variable [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]

/-- The natural extension of a family `c` of chains of `(Δ[p] ⊗ Δ[q]) ⊗ Δ[r]` of degree `n + 1`,
indexed by `p + q + r = n`: the map raising degrees from `(C(K; R) ⊗ C(L; S)) ⊗ C(M; T)` to
`C((K ⊗ L) ⊗ M; U)` by one which sends the summand of a triple of simplices `(x, y, z)` of
dimensions `(p, q, r)` to the image of `c p q r` under the map classifying `((x, y), z)`. -/
private def tripleExtend {n : ℕ}
    (c : ∀ p q r : ℕ, p + q + r = n →
      ((R ⊗ S) ⊗ T ⟶ ((((Δ[p] : SSet.{w}) ⊗ Δ[q]) ⊗ Δ[r]).chainComplex U).X (n + 1)))
    (K L M : SSet.{w}) :
    ((K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T).X n ⟶
      (((K ⊗ L) ⊗ M).chainComplex U).X (n + 1) :=
  mapBifunctor₁₂.mapBifunctor₁₂Desc fun p q r h ↦ tripleTensorChainComplexXDesc fun x y z ↦
    c p q r h ≫
      (chainComplexMap ((yonedaEquiv.symm x ⊗ₘ yonedaEquiv.symm y) ⊗ₘ yonedaEquiv.symm z) U).f
        (n + 1)

@[reassoc]
private lemma ιTripleTensorChainComplex_tripleExtend {n : ℕ}
    (c : ∀ p q r : ℕ, p + q + r = n →
      ((R ⊗ S) ⊗ T ⟶ ((((Δ[p] : SSet.{w}) ⊗ Δ[q]) ⊗ Δ[r]).chainComplex U).X (n + 1)))
    {K L M : SSet.{w}} {p q r : ℕ} (x : K _⦋p⦌) (y : L _⦋q⦌) (z : M _⦋r⦌) (h : p + q + r = n) :
    ιTripleTensorChainComplex x y z n h ≫ tripleExtend c K L M =
      c p q r h ≫
        (chainComplexMap ((yonedaEquiv.symm x ⊗ₘ yonedaEquiv.symm y) ⊗ₘ yonedaEquiv.symm z) U).f
          (n + 1) := by
  rw [ιTripleTensorChainComplex_def, ← mapBifunctor₁₂.ι_eq_whiskerRight _ _ _ p q r (p + q) n rfl h,
    Category.assoc, tripleExtend, mapBifunctor₁₂.ι_mapBifunctor₁₂Desc,
    ιChainComplex_tensorHom_tensorHom_tripleTensorChainComplexXDesc]

@[reassoc]
private lemma tensorHom_f_tripleExtend {n : ℕ}
    (c : ∀ p q r : ℕ, p + q + r = n →
      ((R ⊗ S) ⊗ T ⟶ ((((Δ[p] : SSet.{w}) ⊗ Δ[q]) ⊗ Δ[r]).chainComplex U).X (n + 1)))
    {K K' L L' M M' : SSet.{w}} (f : K ⟶ K') (g : L ⟶ L') (h' : M ⟶ M') :
    ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h' T).f n ≫
        tripleExtend c K' L' M' =
      tripleExtend c K L M ≫ (chainComplexMap ((f ⊗ₘ g) ⊗ₘ h') U).f (n + 1) := by
  refine tripleTensorChainComplex_X_hom_ext fun p q r h x y z ↦ ?_
  rw [ιTripleTensorChainComplex_tensorHom_f_assoc, ιTripleTensorChainComplex_tripleExtend,
    ιTripleTensorChainComplex_tripleExtend_assoc, chainComplexMap_f_comp,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, yonedaEquiv_symm_comp,
    yonedaEquiv_symm_comp, yonedaEquiv_symm_comp]

private lemma tripleExtend_zero {n : ℕ} (K L M : SSet.{w}) :
    tripleExtend (fun p q r (_ : p + q + r = n) ↦
      (0 : (R ⊗ S) ⊗ T ⟶ ((((Δ[p] : SSet.{w}) ⊗ Δ[q]) ⊗ Δ[r]).chainComplex U).X (n + 1)))
        K L M = 0 := by
  refine tripleTensorChainComplex_X_hom_ext fun p q r h x y z ↦ ?_
  rw [ιTripleTensorChainComplex_tripleExtend, zero_comp, comp_zero]

variable (θ : ∀ K L M : SSet.{w},
  (K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T ⟶ ((K ⊗ L) ⊗ M).chainComplex U)

/-- The values of the homotopy on the models, defined by induction on `n`.  In degree zero they
vanish.  In degree `n + 1` and dimensions `(p, q, r)`, the value is the cone
`SSet.stdSimplex.tripleProdConeChain` on the chain `θ (ι) - h (∂ ι)` of
`C((Δ[p] ⊗ Δ[q]) ⊗ Δ[r]; U)`, where `ι` is the summand of the triple of top simplices and `h` is
the natural extension of the values in degree `n`. -/
private def tripleModelHom : (n : ℕ) → ∀ p q r : ℕ, p + q + r = n →
    ((R ⊗ S) ⊗ T ⟶ ((((Δ[p] : SSet.{w}) ⊗ Δ[q]) ⊗ Δ[r]).chainComplex U).X (n + 1))
  | 0 => fun _ _ _ _ ↦ 0
  | n + 1 => fun p q r h ↦
      ιTripleTensorChainComplex (topSimplex p) (topSimplex q) (topSimplex r) (n + 1) h ≫
        ((θ (Δ[p]) (Δ[q]) (Δ[r])).f (n + 1) -
          (((Δ[p] : SSet.{w}).chainComplex R ⊗ (Δ[q] : SSet.{w}).chainComplex S) ⊗
            (Δ[r] : SSet.{w}).chainComplex T).d (n + 1) n ≫
              tripleExtend (tripleModelHom n) (Δ[p]) (Δ[q]) (Δ[r])) ≫
        stdSimplex.tripleProdConeChain p q r U (n + 1)

variable {θ}

variable (hθ : ∀ ⦃K K' L L' M M' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L') (h' : M ⟶ M'),
  ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h' T) ≫ θ K' L' M' =
    θ K L M ≫ chainComplexMap ((f ⊗ₘ g) ⊗ₘ h') U)
include hθ

/-- The inductive step: if the extension `h` of the model values in degree `n` satisfies
`∂ h ∂ = ∂ θ` in degree `n`, then the extension of the model values in degree `n + 1` satisfies
`∂ h = θ - h ∂` in degree `n + 1`. -/
private lemma tripleExtend_tripleModelHom_succ_d (n : ℕ)
    (hcyc : ∀ K L M : SSet.{w},
      ((K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T).d (n + 1) n ≫
          tripleExtend (tripleModelHom θ n) K L M ≫ (((K ⊗ L) ⊗ M).chainComplex U).d (n + 1) n =
        ((K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T).d (n + 1) n ≫ (θ K L M).f n)
    (K L M : SSet.{w}) :
    tripleExtend (tripleModelHom θ (n + 1)) K L M ≫
        (((K ⊗ L) ⊗ M).chainComplex U).d (n + 2) (n + 1) =
      (θ K L M).f (n + 1) -
        ((K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T).d (n + 1) n ≫
          tripleExtend (tripleModelHom θ n) K L M := by
  -- the map `θ - h ∂` raising degrees by one is natural
  have hnat : ∀ ⦃K K' L L' M M' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L') (h' : M ⟶ M'),
      ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h' T).f (n + 1) ≫
          ((θ K' L' M').f (n + 1) -
            ((K'.chainComplex R ⊗ L'.chainComplex S) ⊗ M'.chainComplex T).d (n + 1) n ≫
              tripleExtend (tripleModelHom θ n) K' L' M') =
        ((θ K L M).f (n + 1) -
            ((K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T).d (n + 1) n ≫
              tripleExtend (tripleModelHom θ n) K L M) ≫
          (chainComplexMap ((f ⊗ₘ g) ⊗ₘ h') U).f (n + 1) := fun _ _ _ _ _ _ f g h' ↦ by
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
      ← tensorHom_f_tripleExtend, Hom.comm_assoc, ← HomologicalComplex.comp_f, hθ]
  -- on the models, the chain `(θ - h ∂) (ι)` is a cycle, so the cone on it bounds it
  have hmodel : ∀ p q r (h : p + q + r = n + 1), tripleModelHom θ (n + 1) p q r h ≫
      ((((Δ[p] : SSet.{w}) ⊗ Δ[q]) ⊗ Δ[r]).chainComplex U).d (n + 2) (n + 1) =
        ιTripleTensorChainComplex (topSimplex p) (topSimplex q) (topSimplex r) (n + 1) h ≫
          ((θ (Δ[p]) (Δ[q]) (Δ[r])).f (n + 1) -
            (((Δ[p] : SSet.{w}).chainComplex R ⊗ (Δ[q] : SSet.{w}).chainComplex S) ⊗
              (Δ[r] : SSet.{w}).chainComplex T).d (n + 1) n ≫
                tripleExtend (tripleModelHom θ n) (Δ[p]) (Δ[q]) (Δ[r])) := fun p q r h ↦ by
    have hcyc' : ((θ (Δ[p]) (Δ[q]) (Δ[r])).f (n + 1) -
        (((Δ[p] : SSet.{w}).chainComplex R ⊗ (Δ[q] : SSet.{w}).chainComplex S) ⊗
          (Δ[r] : SSet.{w}).chainComplex T).d (n + 1) n ≫
            tripleExtend (tripleModelHom θ n) (Δ[p]) (Δ[q]) (Δ[r])) ≫
        ((((Δ[p] : SSet.{w}) ⊗ Δ[q]) ⊗ Δ[r]).chainComplex U).d (n + 1) n = 0 := by
      simp only [Preadditive.sub_comp, Category.assoc, Hom.comm, hcyc, sub_self]
    simp only [tripleModelHom, Category.assoc, stdSimplex.tripleProdConeChain_d,
      Preadditive.comp_sub, Category.comp_id, reassoc_of% hcyc', zero_comp, sub_zero]
  -- by naturality, the identity on a triple of simplices is the image of the identity on the
  -- models
  refine tripleTensorChainComplex_X_hom_ext fun p q r h x y z ↦ ?_
  rw [ιTripleTensorChainComplex_tripleExtend_assoc, Hom.comm, reassoc_of% hmodel,
    ιTripleTensorChainComplex_comp_eq_model (fun K L M ↦ (θ K L M).f (n + 1) -
      ((K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T).d (n + 1) n ≫
        tripleExtend (tripleModelHom θ n) K L M) hnat]

variable (h₀ : ∀ K L M : SSet.{w}, (θ K L M).f 0 = 0)
include h₀

/-- The extension `h` of the model values satisfies `∂ h = θ - h ∂` in every positive degree. -/
private lemma tripleExtend_tripleModelHom_succ_d' (n : ℕ) (K L M : SSet.{w}) :
    tripleExtend (tripleModelHom θ (n + 1)) K L M ≫
        (((K ⊗ L) ⊗ M).chainComplex U).d (n + 2) (n + 1) =
      (θ K L M).f (n + 1) -
        ((K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T).d (n + 1) n ≫
          tripleExtend (tripleModelHom θ n) K L M := by
  induction n generalizing K L M with
  | zero =>
    refine tripleExtend_tripleModelHom_succ_d hθ 0 (fun K L M ↦ ?_) K L M
    rw [tripleModelHom, tripleExtend_zero, zero_comp, comp_zero, h₀, comp_zero]
  | succ n ih =>
    refine tripleExtend_tripleModelHom_succ_d hθ (n + 1) (fun K L M ↦ ?_) K L M
    rw [ih, Preadditive.comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp, sub_zero]

end TripleAcyclicModels

section TripleHomotopy

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  {R S T U : C}
  (φ ψ : ∀ K L M : SSet.{w},
    (K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T ⟶ ((K ⊗ L) ⊗ M).chainComplex U)
  (hφ : ∀ ⦃K K' L L' M M' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M'),
    ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h T) ≫ φ K' L' M' =
      φ K L M ≫ chainComplexMap ((f ⊗ₘ g) ⊗ₘ h) U)
  (hψ : ∀ ⦃K K' L L' M M' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M'),
    ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h T) ≫ ψ K' L' M' =
      ψ K L M ≫ chainComplexMap ((f ⊗ₘ g) ⊗ₘ h) U)
  (h₀ : ∀ K L M : SSet.{w}, (φ K L M).f 0 = (ψ K L M).f 0)

/-- **Acyclic models for three factors of simplicial chains.**  Two families `φ` and `ψ` of chain
maps `(C(K; R) ⊗ C(L; S)) ⊗ C(M; T) ⟶ C((K × L) × M; U)`, natural in the three simplicial sets
and equal in degree zero, are chain homotopic.  The homotopy is natural in `K`, `L` and `M`
(`SSet.tripleTensorChainComplexHomotopy_hom_naturality`). -/
def tripleTensorChainComplexHomotopy (K L M : SSet.{w}) : Homotopy (φ K L M) (ψ K L M) where
  hom i j :=
    if h : i + 1 = j then
      tripleExtend (tripleModelHom (fun K L M ↦ φ K L M - ψ K L M) i) K L M ≫
        eqToHom (congrArg _ h)
    else 0
  zero _ _ h := dite_eq_right_iff.mpr fun h' ↦ absurd h' h
  comm i := by
    have hθ : ∀ ⦃K K' L L' M M' : SSet.{w}⦄ (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M'),
        ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h T) ≫
            (φ K' L' M' - ψ K' L' M') =
          (φ K L M - ψ K L M) ≫ chainComplexMap ((f ⊗ₘ g) ⊗ₘ h) U :=
      fun _ _ _ _ _ _ f g h ↦ by rw [Preadditive.comp_sub, Preadditive.sub_comp, hφ, hψ]
    have h₀' : ∀ K L M : SSet.{w}, (φ K L M - ψ K L M).f 0 = 0 := fun K L M ↦ by
      rw [HomologicalComplex.sub_f_apply, h₀, sub_self]
    cases i with
    | zero =>
      simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, ↓reduceDIte,
        eqToHom_refl, Category.comp_id]
      rw [tripleModelHom, tripleExtend_zero, zero_comp, zero_add, zero_add, h₀]
    | succ n =>
      simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, ↓reduceDIte,
        eqToHom_refl, Category.comp_id]
      rw [tripleExtend_tripleModelHom_succ_d' hθ h₀' n K L M, HomologicalComplex.sub_f_apply]
      abel

/-- The homotopy of `SSet.tripleTensorChainComplexHomotopy` is natural in the three simplicial
sets. -/
@[reassoc]
lemma tripleTensorChainComplexHomotopy_hom_naturality {K K' L L' M M' : SSet.{w}} (f : K ⟶ K')
    (g : L ⟶ L') (h : M ⟶ M') (i j : ℕ) :
    ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h T).f i ≫
        (tripleTensorChainComplexHomotopy φ ψ hφ hψ h₀ K' L' M').hom i j =
      (tripleTensorChainComplexHomotopy φ ψ hφ hψ h₀ K L M).hom i j ≫
        (chainComplexMap ((f ⊗ₘ g) ⊗ₘ h) U).f j := by
  simp only [tripleTensorChainComplexHomotopy]
  split_ifs with hij
  · subst hij
    simp only [eqToHom_refl, Category.comp_id]
    exact tensorHom_f_tripleExtend _ f g h
  · rw [comp_zero, zero_comp]

end TripleHomotopy

end SSet

end
