/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.RelativePair
public import SymplecticGeometry.Topology.Category.TopCat.Monoidal
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Prod
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Prod
import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.Assoc
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Sphere
import TauCeti.Geometry.Manifold.Instances.TopCatSphere

/-!
# The cross product of local orientations

For points `x` of a space `X` and `y` of a space `Y`, the homology cross product of the pairs
`(X, X ∖ {x})` and `(Y, Y ∖ {y})` (`TopCat.singularHomologyCrossRelPair`), with integral
coefficients `ULift ℤ`, lands in the homology of `X × Y` relative to
`(X ∖ {x}) × Y ∪ X × (Y ∖ {y})`, which is the complement of `(x, y)`. With the coefficients
`ULift ℤ ⊗ ULift ℤ` multiplied back to `ULift ℤ` (`ModuleCat.uliftTensorSelfIso`), this is the
**cross product of local homology classes**

`Hₚ(X, X ∖ {x}; ℤ) ⊗ H_q(Y, Y ∖ {y}; ℤ) ⟶ Hₙ(X × Y, X × Y ∖ {(x, y)}; ℤ)`, for `p + q = n`

(`SymplecticGeometry.localHomologyCross`). It is natural in maps of pairs
(`SymplecticGeometry.localHomologyMap_tensorHom_localHomologyMap_localHomologyCross`), and on
classes coming from absolute homology it is the absolute cross product
(`SymplecticGeometry.singularHomologyπ_tensorHom_singularHomologyπ_localHomologyCross`). Read back
relative to `(X ∖ {x}) × Y ∪ X × (Y ∖ {y})`, with the coefficients split again by the inverse of
`ModuleCat.uliftTensorSelfIso`, it is the cross product of pairs
(`SymplecticGeometry.localHomologyCross_comp_homologyMap_uliftTensorSelfIso_inv`).

The main result is that the cross product of two local orientations of real vector spaces at the
origin is a local orientation of their product
(`SymplecticGeometry.isLocalOrientation_localHomologyCross`). The proof reduces to compact
manifolds. On compact connected manifolds `M` and `N` with integral fundamental classes `μ` and `ν`,
the cross product `μ × ν` is a fundamental class of `M × N` (Tau Ceti's
`TauCeti.IsFundamentalClass.singularHomologyCross`), and its image in the local homology at `(x, y)`
is the cross product of the images of `μ` and `ν`, so the cross product of local orientations is a
local orientation there
(`SymplecticGeometry.isLocalOrientation_localHomologyCross_of_isFundamentalClass`). Open embeddings
identify local homology groups compatibly with the cross product
(`SymplecticGeometry.forall_isLocalOrientation_localHomologyCross_iff`), and a vector space of
dimension `k + 1` embeds near the origin into the sphere `Sᵏ⁺¹`, whose standard generator is an
integral fundamental class (Tau Ceti's
`TauCeti.isFundamentalClass_singularHomologyTopCatSphereGenerator`).

This gives the cross product of local orientations of vector spaces
(`TauCeti.LocalOrientation.cross`). It reverses when either factor reverses
(`TauCeti.LocalOrientation.cross_neg_left`, `TauCeti.LocalOrientation.cross_neg_right`) and it is
natural under continuous linear equivalences
(`TauCeti.LocalOrientation.cross_map_complZeroPairIso`), as Tau Ceti's ordered product
`TauCeti.LocalOrientation.prod` is. Hence the two differ by a sign `crossSign m n` that depends
only on the dimensions `m + 1` and `n + 1` (`TauCeti.LocalOrientation.coe_cross_eq_crossSign_smul`),
defined by comparing them on `(Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ)`. Its value is not computed
here.

## Main definitions

* `SymplecticGeometry.localHomologyCross`: the cross product of local homology classes.
* `TauCeti.LocalOrientation.cross`: the cross product of local orientations of vector spaces.
* `TauCeti.LocalOrientation.crossSign`: the sign comparing it with `TauCeti.LocalOrientation.prod`.

## Main results

* `SymplecticGeometry.isLocalOrientation_localHomologyCross`: the cross product of local
  orientations of vector spaces is a local orientation.
* `TauCeti.LocalOrientation.cross_map_complZeroPairIso`: naturality.
* `TauCeti.LocalOrientation.coe_cross_eq_crossSign_smul`: the cross product is `crossSign m n`
  times the ordered product, for all spaces of dimensions `m + 1` and `n + 1`.
* `SymplecticGeometry.localHomologyCross_assoc`, `TauCeti.LocalOrientation.map_prodAssoc_cross`:
  associativity of the cross product of local homology classes and of local orientations, the
  latter stated as Tau Ceti's `TauCeti.LocalOrientation.map_prodAssoc_prod` is for the ordered
  product.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.2 and 3.3 (cross products, local orientations, fundamental classes) and Section 3.B
  (the relative cross product).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Set Topology Module
open TopCat (mapsTo_preimage_fst_compl_union_preimage_snd_compl
  mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl)

namespace SymplecticGeometry

open TauCeti

section Cross

variable {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X']
  [TopologicalSpace Y']

/-- **The cross product of local homology classes**
`Hₚ(X, X ∖ {x}; ℤ) ⊗ H_q(Y, Y ∖ {y}; ℤ) ⟶ Hₙ(X × Y, X × Y ∖ {(x, y)}; ℤ)` for `p + q = n`: the
cross product of the pairs `(X, X ∖ {x})` and `(Y, Y ∖ {y})`, read in the homology of `X × Y`
relative to the complement of `(x, y)`, with the coefficients `ℤ ⊗ ℤ` multiplied to `ℤ`. -/
def localHomologyCross (x : X) (y : Y) (p q n : ℕ) (h : p + q = n) :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({x} : Set X) p ⊗
      localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({y} : Set Y) q ⟶
      localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
        ({(x, y)} : Set (X × Y)) n :=
  TopCat.singularHomologyCrossRelPair (TopCat.of X) (TopCat.of Y) {x}ᶜ {y}ᶜ
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p q n h ≫
  TopPair.singularHomologyMap
    (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_union_preimage_snd_compl x y)) _ n ≫
  HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
    (ModuleCat.uliftTensorSelfIso ℤ).hom).app _) n

theorem localHomologyCross_def (x : X) (y : Y) (p q n : ℕ) (h : p + q = n) :
    localHomologyCross x y p q n h =
      TopCat.singularHomologyCrossRelPair (TopCat.of X) (TopCat.of Y) {x}ᶜ {y}ᶜ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p q n h ≫
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_union_preimage_snd_compl x y)) _ n ≫
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).hom).app _) n :=
  (rfl)

/-- The local homology cross product is the cross product of pairs, then the multiplication of
coefficients, then the map of pairs given by the identity of `X × Y`: the two maps after the cross
product of pairs in `SymplecticGeometry.localHomologyCross_def` commute. -/
theorem localHomologyCross_eq (x : X) (y : Y) (p q n : ℕ) (h : p + q = n) :
    localHomologyCross x y p q n h =
      TopCat.singularHomologyCrossRelPair (TopCat.of X) (TopCat.of Y) {x}ᶜ {y}ᶜ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p q n h ≫
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).hom).app _) n ≫
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_union_preimage_snd_compl x y)) _ n := by
  rw [localHomologyCross_def, TopPair.singularHomologyMap_coefficient_naturality]

/-- The local homology cross product, read back in the homology of `X × Y` relative to
`(X ∖ {x}) × Y ∪ X × (Y ∖ {y})` with the coefficients split again by the inverse of
`ModuleCat.uliftTensorSelfIso ℤ`, is the cross product of the pairs `(X, X ∖ {x})` and
`(Y, Y ∖ {y})`. -/
@[elementwise]
theorem localHomologyCross_comp_homologyMap_uliftTensorSelfIso_inv (x : X) (y : Y)
    (p q n : ℕ) (h : p + q = n) :
    localHomologyCross x y p q n h ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetMap _
        (mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl x y)) _ n ≫
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).inv).app _) n =
      TopCat.singularHomologyCrossRelPair (TopCat.of X) (TopCat.of Y) {x}ᶜ {y}ᶜ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p q n h := by
  have hpm : TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_union_preimage_snd_compl x y) ≫
      TopPair.ofSubsetMap _
        (mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl x y) = 𝟙 _ :=
    (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ (fun _ hv ↦ hv)
      (TopCat.tensorObjIsoProd X Y).hom_inv_id).trans
      (TopPair.ofSubsetMap_id _)
  have key : TopCat.singularHomologyCrossRelPair (TopCat.of X) (TopCat.of Y) {x}ᶜ {y}ᶜ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p q n h ≫
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).hom).app _) n ≫
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_union_preimage_snd_compl x y) ≫
          TopPair.ofSubsetMap _
            (mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl x y)) _ n ≫
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).inv).app _) n =
      TopCat.singularHomologyCrossRelPair (TopCat.of X) (TopCat.of Y) {x}ᶜ {y}ᶜ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p q n h := by
    rw [hpm, TopPair.singularHomologyMap_id, Category.id_comp]
    simp [← HomologicalComplex.homologyMap_comp, ← NatTrans.comp_app, ← Functor.map_comp]
  rw [TopPair.singularHomologyMap_comp
    (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_union_preimage_snd_compl x y))] at key
  rw [localHomologyCross_eq, Category.assoc, Category.assoc]
  -- `localHomology` is an abbreviation for the homology of the pair, so `key` is the goal.
  exact key

/-- **The cross product of local homology classes on absolute classes.** For `a ∈ Hₚ(X; ℤ)` and
`b ∈ H_q(Y; ℤ)`, the cross product of their images in the local homology at `x` and `y` is the
image of the absolute cross product `a × b ∈ Hₙ(X × Y; ℤ ⊗ ℤ)` in the local homology at `(x, y)`,
with the coefficients multiplied to `ℤ`. -/
@[elementwise]
theorem singularHomologyπ_tensorHom_singularHomologyπ_localHomologyCross (x : X) (y : Y)
    (p q n : ℕ) (h : p + q = n) :
    ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of X))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) p ⊗ₘ
      (TopPair.ofSubset ({y}ᶜ : Set (TopCat.of Y))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) q) ≫ localHomologyCross x y p q n h =
      TopCat.singularHomologyCross (TopCat.of X) (TopCat.of Y) (ModuleCat.of ℤ (ULift.{0} ℤ))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) p q n h ≫
        (TopPair.ofSubset ({(x, y)}ᶜ : Set (TopCat.of (X × Y)))).singularHomologyπ
          (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) n ≫
        HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
          (ModuleCat.uliftTensorSelfIso ℤ).hom).app
            (TopPair.toSSetPair.obj
              (TopPair.ofSubset ({(x, y)}ᶜ : Set (TopCat.of (X × Y)))))) n := by
  have hπ := TopPair.singularHomologyπ_naturality
    (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_union_preimage_snd_compl x y))
    (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) n
  rw [TopPair.ofSubsetMap_fst] at hπ
  -- The map of ambient spaces is the identity of `X × Y`, written between `X ⊗ Y` and `X × Y`.
  have hid : SSet.homologyMap (TopCat.toSSet.map (TopCat.tensorObjIsoProd X Y).hom)
      (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) n = 𝟙 _ :=
    (congrArg (fun φ ↦ SSet.homologyMap (TopCat.toSSet.map φ) _ n)
      (TopCat.tensorObjIsoProd_hom_eq_id X Y)).trans
      ((congrArg (SSet.homologyMap · _ n) (TopCat.toSSet.map_id _)).trans
        (SSet.homologyMap_id _ _ n))
  replace hπ := hπ.symm.trans ((congrArg (· ≫ _) hid).trans (Category.id_comp _))
  rw [localHomologyCross, ← Category.assoc,
    ← TopCat.singularHomologyCross_comp_singularHomologyπ_eq_singularHomologyCrossRelPair]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((reassoc_of% hπ) _))

/-- **Naturality of the cross product of local homology classes.** For maps `f : X → X'` and
`g : Y → Y'` with `f⁻¹(x') ⊆ {x}` and `g⁻¹(y') ⊆ {y}`, `f_* a × g_* b = (f × g)_* (a × b)`. -/
@[elementwise]
theorem localHomologyMap_tensorHom_localHomologyMap_localHomologyCross (f : C(X, X'))
    (g : C(Y, Y')) {x : X} {x' : X'} {y : Y} {y' : Y'} (hf : f ⁻¹' {x'} ⊆ {x})
    (hg : g ⁻¹' {y'} ⊆ {y}) (p q n : ℕ) (h : p + q = n) :
    (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) f hf p ⊗ₘ
        localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) g hg q) ≫
        localHomologyCross x' y' p q n h =
      localHomologyCross x y p q n h ≫ localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (f.prodMap g) (by
          rintro ⟨a, b⟩ hab
          simp only [mem_preimage, ContinuousMap.prodMap_apply, Prod.map, mem_singleton_iff,
            Prod.mk.injEq] at hab
          exact Prod.ext (hf hab.1) (hg hab.2)) n := by
  rw [localHomologyMap_def, localHomologyMap_def, localHomologyCross, localHomologyCross,
    TopCat.singularHomologyCrossRelPair_naturality_assoc]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (TopCat.singularHomologyCrossRelPair (TopCat.of X) (TopCat.of Y) {x}ᶜ {y}ᶜ
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p q n h ≫ ·) ?_
  have hf' : MapsTo (TopCat.ofHom f) ({x}ᶜ : Set (TopCat.of X)) ({x'}ᶜ : Set (TopCat.of X')) :=
    fun a ha ha' ↦ ha (hf ha')
  have hg' : MapsTo (TopCat.ofHom g) ({y}ᶜ : Set (TopCat.of Y)) ({y'}ᶜ : Set (TopCat.of Y')) :=
    fun a ha ha' ↦ ha (hg ha')
  have hL : MapsTo (TopCat.ofHom (f.prodMap g)) ({(x, y)}ᶜ : Set (TopCat.of (X × Y)))
      ({(x', y')}ᶜ : Set (TopCat.of (X' × Y'))) := by
    rintro ⟨a, b⟩ hab h'
    simp only [TopCat.hom_ofHom, ContinuousMap.prodMap_apply, Prod.map] at h'
    exact hab (Prod.ext (hf (congrArg Prod.fst h')) (hg (congrArg Prod.snd h')))
  -- The maps of pairs commute, and the coefficient change is natural.
  have hpair : TopPair.ofSubsetMap _ (TopCat.mapsTo_tensorHom_preimage_union _ _ hf' hg') ≫
      TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_union_preimage_snd_compl x' y') =
      TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_union_preimage_snd_compl x y) ≫
        TopPair.ofSubsetMap _ hL := by
    have hk : MapsTo ((TopCat.ofHom f ⊗ₘ TopCat.ofHom g) ≫
        (TopCat.tensorObjIsoProd X' Y').hom)
        (CartesianMonoidalCategory.fst (TopCat.of X) (TopCat.of Y) ⁻¹' ({x}ᶜ : Set (TopCat.of X)) ∪
          CartesianMonoidalCategory.snd (TopCat.of X) (TopCat.of Y) ⁻¹' ({y}ᶜ : Set (TopCat.of Y)))
        ({(x', y')}ᶜ : Set (TopCat.of (X' × Y'))) :=
      (mapsTo_preimage_fst_compl_union_preimage_snd_compl x' y').comp
        (TopCat.mapsTo_tensorHom_preimage_union _ _ hf' hg')
    exact (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ hk rfl).trans
      (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ hk
        (TopCat.tensorObjIsoProd_hom_comp_ofHom_prodMap f g)).symm
  have h1 := congrArg (TopPair.singularHomologyMap ·
    (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) n) hpair
  simp only [TopPair.singularHomologyMap_comp] at h1
  have h2 := congrArg (HomologicalComplex.homologyMap · n)
    (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
      (ModuleCat.uliftTensorSelfIso ℤ).hom).naturality
        (TopPair.toSSetPair.map (TopPair.ofSubsetMap _ hL)))
  simp only [HomologicalComplex.homologyMap_comp] at h2
  rw [reassoc_of% h1, localHomologyMap_def]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)

/-- **The cross product of local orientations of compact manifolds with fundamental classes.**
Let `M` and `N` be compact connected manifolds of dimensions `p` and `q` with integral
fundamental classes. Then the cross product of local orientations at `x ∈ M` and `y ∈ N` is a
local orientation of `M × N` at `(x, y)`. -/
theorem isLocalOrientation_localHomologyCross_of_isFundamentalClass
    {M N E F : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
    [TopologicalSpace N] [T2Space N] [CompactSpace N] [ConnectedSpace N]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F N]
    {p q n : ℕ} (hp : finrank ℝ E = p) (hq : finrank ℝ F = q) (h : p + q = n)
    {μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) p :
      ModuleCat.{0} ℤ)} (hμ : IsFundamentalClass μ)
    {ν : ((TopCat.toSSet.obj (TopCat.of N)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) q :
      ModuleCat.{0} ℤ)} (hν : IsFundamentalClass ν)
    {x : M} {y : N} (z₁ : LocalOrientation M x p) (z₂ : LocalOrientation N y q) :
    IsLocalOrientation (x, y) n ((localHomologyCross x y p q n h).hom (z₁.val ⊗ₜ z₂.val)) := by
  subst h
  -- The cross product `μ × ν` is a fundamental class of `M × N`.
  let g : ((TopCat.toSSet.obj (TopCat.of (M × N))).homology
      (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (p + q) : ModuleCat.{0} ℤ) :=
    (TopCat.singularHomologyCross (TopCat.of M) (TopCat.of N) (ModuleCat.of ℤ (ULift.{0} ℤ))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) p q (p + q) rfl).hom (μ ⊗ₜ ν)
  have hg : IsFundamentalClass g :=
    hμ.singularHomologyCross ULift.moduleEquiv ULift.moduleEquiv hp hq hν
  replace hg := (isFundamentalClass_iff g).1 hg (x, y)
  rw [singularHomologyToLocalHomology_eq_singularHomologyπ] at hg
  set c := HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
    (ModuleCat.uliftTensorSelfIso ℤ).hom).app
      (TopPair.toSSetPair.obj (TopPair.ofSubset ({(x, y)}ᶜ : Set (TopCat.of (M × N)))))) (p + q)
  have hc : Function.Surjective c := (ConcreteCategory.bijective_of_isIso c).2
  -- So the cross product of the local classes of `μ` and `ν` generates the local homology.
  have hG : (localHomologyCross x y p q (p + q) rfl).hom
      (((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) p μ) ⊗ₜ
      ((TopPair.ofSubset ({y}ᶜ : Set (TopCat.of N))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) q ν)) =
      c (((TopPair.ofSubset ({(x, y)}ᶜ : Set (TopCat.of (M × N)))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (p + q)).hom g) :=
    singularHomologyπ_tensorHom_singularHomologyπ_localHomologyCross_apply x y p q (p + q) rfl
      (μ ⊗ₜ ν)
  have hspan : Submodule.span ℤ (Set.singleton ((localHomologyCross x y p q (p + q) rfl).hom
      (((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) p μ) ⊗ₜ
      ((TopPair.ofSubset ({y}ᶜ : Set (TopCat.of N))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) q ν)))) = ⊤ := by
    rw [hG]
    have h1 := Submodule.map_span c.hom {((TopPair.ofSubset ({(x, y)}ᶜ :
      Set (TopCat.of (M × N)))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (p + q)).hom g}
    rw [Set.image_singleton, hg, Submodule.map_top, LinearMap.range_eq_top.2 hc] at h1
    exact h1.symm
  -- The local classes of `μ` and `ν` are multiples of `z₁` and `z₂`.
  obtain ⟨a, ha⟩ := (isLocalOrientation_iff _ _ _).1 z₁.property
    ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) p μ)
  obtain ⟨b, hb⟩ := (isLocalOrientation_iff _ _ _).1 z₂.property
    ((TopPair.ofSubset ({y}ᶜ : Set (TopCat.of N))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) q ν)
  have e : (a • z₁.val) ⊗ₜ[ℤ] (b • z₂.val) = (a * b) • (z₁.val ⊗ₜ[ℤ] z₂.val) :=
    calc (a • z₁.val) ⊗ₜ[ℤ] (b • z₂.val) = a • (z₁.val ⊗ₜ[ℤ] (b • z₂.val)) :=
          map_zsmul (AddMonoidHom.mk' (· ⊗ₜ[ℤ] (b • z₂.val))
            fun _ _ ↦ TensorProduct.add_tmul _ _ _) a z₁.val
      _ = a • b • (z₁.val ⊗ₜ[ℤ] z₂.val) :=
          congrArg (a • ·) (map_zsmul (TensorProduct.mk ℤ _ _ z₁.val) b z₂.val)
      _ = (a * b) • (z₁.val ⊗ₜ[ℤ] z₂.val) := by rw [mul_comm, mul_zsmul']
  rw [← ha, ← hb, e, map_zsmul] at hspan
  exact (isLocalOrientation_iff_span_eq_top _ _ _).2 (top_le_iff.1
    (hspan.symm.le.trans (Submodule.span_singleton_smul_le ℤ (a * b) _)))

/-- Open embeddings `j₁ : X → X'` and `j₂ : Y → Y'` into `T₁` spaces carry the cross product of
local homology classes at `x` and `y` to the cross product of their images at `j₁ x` and
`j₂ y`. -/
theorem localHomologyCross_localHomologyIsoOfIsOpenEmbedding [T1Space X'] [T1Space Y']
    {j₁ : X → X'} {j₂ : Y → Y'} (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) (x : X)
    (y : Y) (p q n : ℕ) (h : p + q = n)
    (a : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({x} : Set X) p)
    (b : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({y} : Set Y) q) :
    (localHomologyCross (j₁ x) (j₂ y) p q n h).hom
        ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj₁ x p).hom a ⊗ₜ
          (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj₂ y q).hom b) =
      (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) (hj₁.prodMap hj₂) (x, y)
        n).hom ((localHomologyCross x y p q n h).hom (a ⊗ₜ b)) := by
  have hn := localHomologyMap_tensorHom_localHomologyMap_localHomologyCross_apply
    ⟨j₁, hj₁.continuous⟩ ⟨j₂, hj₂.continuous⟩
    (by rw [ContinuousMap.coe_mk, ← image_singleton, hj₁.injective.preimage_image])
    (by rw [ContinuousMap.coe_mk, ← image_singleton, hj₂.injective.preimage_image]) p q n h
    (a ⊗ₜ b)
  simp only [ModuleCat.MonoidalCategory.tensorHom_tmul] at hn
  simp only [localHomologyIsoOfIsOpenEmbedding_hom]
  exact hn

/-- For open embeddings `j₁ : X → X'` and `j₂ : Y → Y'` into `T₁` spaces, cross products of local
orientations at `j₁ x` and `j₂ y` are local orientations exactly when cross products of local
orientations at `x` and `y` are. -/
theorem forall_isLocalOrientation_localHomologyCross_iff [T1Space X'] [T1Space Y']
    {j₁ : X → X'} {j₂ : Y → Y'} (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) (x : X)
    (y : Y) {p q n : ℕ} (h : p + q = n) :
    (∀ (z₁ : LocalOrientation X' (j₁ x) p) (z₂ : LocalOrientation Y' (j₂ y) q),
      IsLocalOrientation (j₁ x, j₂ y) n
        ((localHomologyCross (j₁ x) (j₂ y) p q n h).hom (z₁.val ⊗ₜ z₂.val))) ↔
    ∀ (z₁ : LocalOrientation X x p) (z₂ : LocalOrientation Y y q),
      IsLocalOrientation (x, y) n ((localHomologyCross x y p q n h).hom (z₁.val ⊗ₜ z₂.val)) := by
  set e := localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) (hj₁.prodMap hj₂)
    (x, y) n
  refine ⟨fun H z₁ z₂ ↦ ?_, fun H z₁ z₂ ↦ ?_⟩
  · have := (H (hj₁.localOrientationEquiv x p z₁) (hj₂.localOrientationEquiv y q z₂)).map e.symm
    rwa [IsOpenEmbedding.coe_localOrientationEquiv, IsOpenEmbedding.coe_localOrientationEquiv,
      localHomologyCross_localHomologyIsoOfIsOpenEmbedding, Iso.symm_hom, e.hom_inv_id_apply]
      at this
  · obtain ⟨w₁, rfl⟩ := (hj₁.localOrientationEquiv x p).surjective z₁
    obtain ⟨w₂, rfl⟩ := (hj₂.localOrientationEquiv y q).surjective z₂
    rw [IsOpenEmbedding.coe_localOrientationEquiv, IsOpenEmbedding.coe_localOrientationEquiv,
      localHomologyCross_localHomologyIsoOfIsOpenEmbedding]
    exact (H w₁ w₂).map e

/-- For partial homeomorphisms `φ : X → X'` and `ψ : Y → Y'` between `T₁` spaces, defined at `x`
and `y`, cross products of local orientations at `φ x` and `ψ y` are local orientations exactly
when cross products of local orientations at `x` and `y` are. -/
theorem forall_isLocalOrientation_localHomologyCross_iff_of_openPartialHomeomorph [T1Space X]
    [T1Space Y] [T1Space X'] [T1Space Y'] (φ : OpenPartialHomeomorph X X')
    (ψ : OpenPartialHomeomorph Y Y') {x : X} {y : Y} (hx : x ∈ φ.source) (hy : y ∈ ψ.source)
    {p q n : ℕ} (h : p + q = n) :
    (∀ (z₁ : LocalOrientation X' (φ x) p) (z₂ : LocalOrientation Y' (ψ y) q),
      IsLocalOrientation (φ x, ψ y) n
        ((localHomologyCross (φ x) (ψ y) p q n h).hom (z₁.val ⊗ₜ z₂.val))) ↔
    ∀ (z₁ : LocalOrientation X x p) (z₂ : LocalOrientation Y y q),
      IsLocalOrientation (x, y) n ((localHomologyCross x y p q n h).hom (z₁.val ⊗ₜ z₂.val)) :=
  (forall_isLocalOrientation_localHomologyCross_iff φ.isOpenEmbedding_restrict
      ψ.isOpenEmbedding_restrict (⟨x, hx⟩ : φ.source) (⟨y, hy⟩ : ψ.source) h).trans
    (forall_isLocalOrientation_localHomologyCross_iff φ.open_source.isOpenEmbedding_subtypeVal
      ψ.open_source.isOpenEmbedding_subtypeVal (⟨x, hx⟩ : φ.source) (⟨y, hy⟩ : ψ.source) h).symm

end Cross

section Assoc

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- **Associativity of the cross product of local homology classes.** The map of local homology
induced by the associator `(X × Y) × Z ≃ₜ X × (Y × Z)` sends `(a × b) × c` to `a × (b × c)`. -/
@[elementwise]
theorem localHomologyCross_assoc (x : X) (y : Y) (z : Z) (p q r pq qr n : ℕ) (hpq : p + q = pq)
    (hqr : q + r = qr) (hn : pq + r = n) (hn' : p + qr = n) :
    (localHomologyCross x y p q pq hpq ▷
        localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({z} : Set Z) r) ≫
      localHomologyCross (x, y) z pq r n hn ≫
        localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
          ((Homeomorph.prodAssoc X Y Z : (X × Y) × Z ≃ₜ X × Y × Z) : C((X × Y) × Z, X × Y × Z))
          (by rintro ⟨⟨a, b⟩, c⟩ h; simpa [Homeomorph.prodAssoc, and_assoc] using h) n =
      (α_ _ _ _).hom ≫
        (localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({x} : Set X) p ◁
          localHomologyCross y z q r qr hqr) ≫
        localHomologyCross x (y, z) p qr n hn' := by
  -- The two ambient maps from `(X ⊗ Y) ⊗ Z` to `X × (Y × Z)` agree.
  have hK₁ : ((TopCat.tensorObjIsoProd X Y).hom ⊗ₘ 𝟙 (TopCat.of Z)) ≫
      (TopCat.tensorObjIsoProd (X × Y) Z).hom ≫
        TopCat.ofHom ((Homeomorph.prodAssoc X Y Z : (X × Y) × Z ≃ₜ X × Y × Z) :
          C((X × Y) × Z, X × Y × Z)) =
      (α_ (TopCat.of X) (TopCat.of Y) (TopCat.of Z)).hom ≫
        (𝟙 (TopCat.of X) ⊗ₘ (TopCat.tensorObjIsoProd Y Z).hom) ≫
          (TopCat.tensorObjIsoProd X (Y × Z)).hom := by
    simp only [TopCat.tensorObjIsoProd_hom_eq_id]
    -- Both sides are now `((a, b), c) ↦ (a, (b, c))`: the associator of `TopCat` is that of the
    -- product, and no lemma states it as `Homeomorph.prodAssoc`.
    rfl
  -- The cross products of pairs are natural in the maps that identify the subspaces with the
  -- complements of points, the identity on the other factor.
  -- `hZ` and `hX` are stated for `𝟙`, not `id`, so that `TopPair.ofSubsetMap_id` applies below.
  have hZ : MapsTo (𝟙 (TopCat.of Z)) ({z}ᶜ : Set (TopCat.of Z)) {z}ᶜ := fun _ h ↦ h
  have hX : MapsTo (𝟙 (TopCat.of X)) ({x}ᶜ : Set (TopCat.of X)) {x}ᶜ := fun _ h ↦ h
  have hnatL := TopCat.singularHomologyCrossRelPair_naturality (TopCat.of X ⊗ TopCat.of Y)
    (TopCat.of Z) _ ({z}ᶜ : Set (TopCat.of Z)) (ModuleCat.of ℤ (ULift.{0} ℤ))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) pq r n hn (TopCat.tensorObjIsoProd X Y).hom
    (mapsTo_preimage_fst_compl_union_preimage_snd_compl x y) (𝟙 _) hZ
  have hnatR := TopCat.singularHomologyCrossRelPair_naturality (TopCat.of X)
    (TopCat.of Y ⊗ TopCat.of Z) ({x}ᶜ : Set (TopCat.of X)) _ (ModuleCat.of ℤ (ULift.{0} ℤ))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) p qr n hn' (𝟙 _) hX
    (TopCat.tensorObjIsoProd Y Z).hom (mapsTo_preimage_fst_compl_union_preimage_snd_compl y z)
  simp only [TopPair.ofSubsetMap_id, TopPair.singularHomologyMap_id, tensorHom_id] at hnatL
  simp only [TopPair.ofSubsetMap_id, TopPair.singularHomologyMap_id, id_tensorHom] at hnatR
  have hA := TopCat.singularHomologyCrossRelPair_uliftTensorSelfIso_assoc (TopCat.of X)
    (TopCat.of Y) (TopCat.of Z) {x}ᶜ {y}ᶜ {z}ᶜ p q r pq qr n hpq hqr hn hn'
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc] at hA
  -- Write each local cross product as a cross product of pairs, then the coefficient map, then the
  -- map of pairs, and move the maps of pairs to the end of both sides.
  rw [localHomologyCross_eq, localHomologyCross_eq, localHomologyCross_eq, localHomologyCross_eq]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hnatL, reassoc_of% hnatR]
  rw [← reassoc_of% (TopPair.singularHomologyMap_coefficient_naturality _
      (ModuleCat.uliftTensorSelfIso ℤ).hom n),
    ← reassoc_of% (TopPair.singularHomologyMap_coefficient_naturality _
      (ModuleCat.uliftTensorSelfIso ℤ).hom n)]
  simp only [localHomologyMap_def]
  -- Both sides now start with the two sides of `hA`; the maps of pairs that follow agree.
  rw [← reassoc_of% hA, ← TopPair.singularHomologyMap_comp,
    ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp,
    ← TopPair.singularHomologyMap_comp]
  refine congrArg (fun φ ↦ _ ≫ _ ≫ _ ≫ _ ≫ TopPair.singularHomologyMap φ _ n) ?_
  refine TopPair.hom_ext_of_fst _ ?_
  simp only [TopPair.Hom.fst_comp, TopPair.ofSubsetMap_fst]
  exact hK₁

end Assoc

/-- **The cross product of local orientations of vector spaces is a local orientation.** For
real normed spaces `F₁` and `F₂` of dimensions `m + 1` and `n + 1` and local orientations `z₁`
and `z₂` at their origins, the cross product `z₁ × z₂` generates the integral local homology
`H_{d+1}(F₁ × F₂, F₁ × F₂ ∖ {0}; ℤ)`, where `(m + 1) + (n + 1) = d + 1`. -/
theorem isLocalOrientation_localHomologyCross {F₁ F₂ : Type} [NormedAddCommGroup F₁]
    [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {m n d : ℕ}
    (hF₁ : finrank ℝ F₁ = m + 1) (hF₂ : finrank ℝ F₂ = n + 1) (h : m + 1 + (n + 1) = d + 1)
    (z₁ : LocalOrientation F₁ 0 (m + 1)) (z₂ : LocalOrientation F₂ 0 (n + 1)) :
    IsLocalOrientation (0 : F₁ × F₂) (d + 1)
      ((localHomologyCross (0 : F₁) (0 : F₂) (m + 1) (n + 1) (d + 1) h).hom
        (z₁.val ⊗ₜ z₂.val)) := by
  have := FiniteDimensional.of_finrank_eq_succ hF₁
  have := FiniteDimensional.of_finrank_eq_succ hF₂
  -- The spheres `Sᵐ⁺¹` and `Sⁿ⁺¹`, charted on `ULift (Fin (k + 1)) → ℝ`, are compact connected
  -- manifolds, and the standard generator of `Hₖ₊₁(Sᵏ⁺¹; ℤ)`, with the coefficients `ℤ` read as
  -- `ULift ℤ`, is a fundamental class.
  have hE (k : ℕ) : finrank ℝ (ULift.{0} (Fin (k + 1)) → ℝ) = k + 1 := by simp
  have hμ (k : ℕ) : IsFundamentalClass
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) (k + 1)).map
        (ULift.moduleEquiv.{0, 0, 0} (R := ℤ) (M := ℤ)).symm.toModuleIso.hom).app
          (TopCat.of (TopCat.sphere.{0} (k + 1))) (singularHomologyTopCatSphereGenerator ℤ k)) :=
    (isFundamentalClass_singularHomologyFunctor_map_app_iff _ _).2
      (isFundamentalClass_singularHomologyTopCatSphereGenerator ℤ k)
  obtain ⟨x₁⟩ : Nonempty (TopCat.sphere.{0} (m + 1)) := ConnectedSpace.toNonempty
  obtain ⟨x₂⟩ : Nonempty (TopCat.sphere.{0} (n + 1)) := ConnectedSpace.toNonempty
  -- A partial homeomorphism from `Fᵢ` to the sphere defined at `0`: a linear identification of
  -- `Fᵢ` with the model, a translation, and the inverse of the chart at `xᵢ`.
  let φ₁ : OpenPartialHomeomorph F₁ (TopCat.sphere.{0} (m + 1)) :=
    ((ContinuousLinearEquiv.ofFinrankEq (hF₁.trans (hE m).symm)).toHomeomorph.trans
      (Homeomorph.addRight (chartAt (ULift.{0} (Fin (m + 1)) → ℝ) x₁ x₁)))
      |>.toOpenPartialHomeomorph.trans (chartAt (ULift.{0} (Fin (m + 1)) → ℝ) x₁).symm
  let φ₂ : OpenPartialHomeomorph F₂ (TopCat.sphere.{0} (n + 1)) :=
    ((ContinuousLinearEquiv.ofFinrankEq (hF₂.trans (hE n).symm)).toHomeomorph.trans
      (Homeomorph.addRight (chartAt (ULift.{0} (Fin (n + 1)) → ℝ) x₂ x₂)))
      |>.toOpenPartialHomeomorph.trans (chartAt (ULift.{0} (Fin (n + 1)) → ℝ) x₂).symm
  have h₁ : (0 : F₁) ∈ φ₁.source := by simp [φ₁]
  have h₂ : (0 : F₂) ∈ φ₂.source := by simp [φ₂]
  exact (forall_isLocalOrientation_localHomologyCross_iff_of_openPartialHomeomorph φ₁ φ₂ h₁ h₂
    h).1 (fun w₁ w₂ ↦ isLocalOrientation_localHomologyCross_of_isFundamentalClass (hE m) (hE n) h
      (hμ m) (hμ n) w₁ w₂) z₁ z₂

end SymplecticGeometry

/-- The map of local homology at the origins induced by the isomorphism of pairs
`f.complZeroPairIso` is the map induced by `f`. -/
theorem ContinuousLinearEquiv.singularHomologyMap_complZeroPairIso_hom {E E' : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : E ≃L[ℝ] E') (k : ℕ) :
    TopPair.singularHomologyMap f.complZeroPairIso.hom (ModuleCat.of ℤ (ULift.{0} ℤ)) k =
      TauCeti.localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ((f : E →L[ℝ] E') : C(E, E'))
        (fun a ha ↦ by simpa using ha) k := by
  rw [complZeroPairIso_hom]
  exact (TauCeti.localHomologyMap_def _ _ _ _).symm

namespace TauCeti.LocalOrientation

open SymplecticGeometry

variable {E F E' F' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] {m n d : ℕ}

/-- **The cross product of local orientations.** For local orientations `z` of `E` and `z'` of
`F` at the origin, their cross product `z × z'` is a local orientation of `E × F` at the origin
(`SymplecticGeometry.isLocalOrientation_localHomologyCross`). Its degree is written `d + 1` with
`(m + 1) + (n + 1) = d + 1`, as for `TauCeti.LocalOrientation.prod`. -/
def cross (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1) (hd : m + 1 + (n + 1) = d + 1)
    (z : LocalOrientation E 0 (m + 1)) (z' : LocalOrientation F 0 (n + 1)) :
    LocalOrientation (E × F) 0 (d + 1) :=
  ⟨(localHomologyCross (0 : E) (0 : F) (m + 1) (n + 1) (d + 1) hd).hom (z.val ⊗ₜ z'.val),
    isLocalOrientation_localHomologyCross hE hF hd z z'⟩

/-- The class of the cross product of local orientations is their cross product as local
homology classes. -/
@[simp]
theorem coe_cross (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (z : LocalOrientation E 0 (m + 1))
    (z' : LocalOrientation F 0 (n + 1)) :
    (cross hE hF hd z z').val =
      (localHomologyCross (0 : E) (0 : F) (m + 1) (n + 1) (d + 1) hd).hom (z.val ⊗ₜ z'.val) :=
  (rfl)

/-- Reversing the first factor reverses the cross product. -/
@[simp]
theorem cross_neg_left (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (z : LocalOrientation E 0 (m + 1))
    (z' : LocalOrientation F 0 (n + 1)) : cross hE hF hd (-z) z' = -cross hE hF hd z z' :=
  Subtype.ext (by
    rw [coe_cross, coe_neg, coe_neg, coe_cross, TensorProduct.neg_tmul, _root_.map_neg])

/-- Reversing the second factor reverses the cross product. -/
@[simp]
theorem cross_neg_right (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (z : LocalOrientation E 0 (m + 1))
    (z' : LocalOrientation F 0 (n + 1)) : cross hE hF hd z (-z') = -cross hE hF hd z z' :=
  Subtype.ext (by
    rw [coe_cross, coe_neg, coe_neg, coe_cross, TensorProduct.tmul_neg, _root_.map_neg])

/-- **Naturality of the cross product.** Transporting the factors along continuous linear
equivalences `f` and `g` transports the cross product along `f × g`. -/
theorem cross_map_complZeroPairIso (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hE' : finrank ℝ E' = m + 1) (hF' : finrank ℝ F' = n + 1) (hd : m + 1 + (n + 1) = d + 1)
    (f : E ≃L[ℝ] E') (g : F ≃L[ℝ] F') (z : LocalOrientation E 0 (m + 1))
    (z' : LocalOrientation F 0 (n + 1)) :
    cross hE' hF' hd (z.map f.complZeroPairIso) (z'.map g.complZeroPairIso) =
      (cross hE hF hd z z').map (f.prodCongr g).complZeroPairIso := by
  refine Subtype.ext ?_
  rw [coe_cross, coe_map, coe_map, coe_map, coe_cross,
    ContinuousLinearEquiv.singularHomologyMap_complZeroPairIso_hom,
    ContinuousLinearEquiv.singularHomologyMap_complZeroPairIso_hom,
    ContinuousLinearEquiv.singularHomologyMap_complZeroPairIso_hom]
  have hn := localHomologyMap_tensorHom_localHomologyMap_localHomologyCross_apply
    ((f : E →L[ℝ] E') : C(E, E')) ((g : F →L[ℝ] F') : C(F, F'))
    (x := 0) (x' := 0) (y := 0) (y' := 0)
    (fun a ha ↦ by simpa using ha) (fun a ha ↦ by simpa using ha) (m + 1) (n + 1) (d + 1) hd
    (z.val ⊗ₜ z'.val)
  simp only [ModuleCat.MonoidalCategory.tensorHom_tmul] at hn
  refine hn.trans ?_
  -- The product map `f × g` appears as `ContinuousMap.prodMap` and as `f.prodCongr g`.
  congr 3

section Assoc

variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {p : ℕ}

/-- **Associativity of the cross product of local orientations.** Transport along
`(E × F) × G ≃ E × (F × G)` carries `(z × z') × z''` to `z × (z' × z'')`. -/
theorem map_prodAssoc_cross {e f : ℕ} (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hG : finrank ℝ G = p + 1) (he : m + 1 + (n + 1) = e + 1) (hf : n + 1 + (p + 1) = f + 1)
    (hd : e + 1 + (p + 1) = d + 1) (he' : m + 1 + (f + 1) = d + 1)
    (z : LocalOrientation E 0 (m + 1)) (z' : LocalOrientation F 0 (n + 1))
    (z'' : LocalOrientation G 0 (p + 1)) :
    (cross (finrank_prod_eq_succ hE hF he) hG hd (cross hE hF he z z') z'').map
        (ContinuousLinearEquiv.prodAssoc ℝ E F G).complZeroPairIso =
      cross hE (finrank_prod_eq_succ hF hG hf) he' z (cross hF hG hf z' z'') := by
  refine Subtype.ext ?_
  rw [coe_map, coe_cross, coe_cross, coe_cross, coe_cross,
    ContinuousLinearEquiv.singularHomologyMap_complZeroPairIso_hom]
  -- Apply associativity to `(z ⊗ z') ⊗ z''`, with `z ⊗ z'` typed as an element of the tensor
  -- product in `ModuleCat`, whose module structure the outer tensor product uses.
  have h (w : ↑(localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set E)
      (m + 1) ⊗ localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set F)
        (n + 1))) := localHomologyCross_assoc_apply (0 : E) (0 : F) (0 : G)
    (m + 1) (n + 1) (p + 1) (e + 1) (f + 1) (d + 1) he hf hd he' (w ⊗ₜ z''.val)
  specialize h (z.val ⊗ₜ z'.val)
  simp only [ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.associator_hom_apply] at h
  rw [localHomologyMap_congr _ (j₁ := ((Homeomorph.prodAssoc E F G : (E × F) × G ≃ₜ E × F × G) :
    C((E × F) × G, E × F × G))) (j₂ := ((ContinuousLinearEquiv.prodAssoc ℝ E F G :
    (E × F) × G →L[ℝ] E × F × G) : C((E × F) × G, E × F × G))) (ContinuousMap.ext fun _ ↦ rfl),
    ModuleCat.MonoidalCategory.whiskerLeft_apply] at h
  simp only [Prod.mk_zero_zero] at h
  exact h

end Assoc

open Classical in
/-- **The sign of the cross product of local orientations**, `±1`: the sign comparing the cross
product of the local orientations of `ℝᵐ⁺¹ = Fin (m + 1) → ℝ` and `ℝⁿ⁺¹` selected by their
standard bases with their ordered product `TauCeti.LocalOrientation.prod`. The same sign compares
the two products on all spaces of these dimensions
(`TauCeti.LocalOrientation.coe_cross_eq_crossSign_smul`). -/
def crossSign (m n : ℕ) : ℤˣ :=
  if cross (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ)
      (by omega : m + 1 + (n + 1) = m + n + 1 + 1)
      ((Pi.basisFun ℝ (Fin (m + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ))
      ((Pi.basisFun ℝ (Fin (n + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ)) =
    prod (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ)
      (by omega : m + 1 + (n + 1) = m + n + 1 + 1)
      ((Pi.basisFun ℝ (Fin (m + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ))
      ((Pi.basisFun ℝ (Fin (n + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ))
    then 1 else -1

open Classical in
theorem crossSign_def (m n : ℕ) :
    crossSign m n =
      if cross (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ)
          (by omega : m + 1 + (n + 1) = m + n + 1 + 1)
          ((Pi.basisFun ℝ (Fin (m + 1))).orientation.localOrientation
            (Module.finrank_fin_fun ℝ))
          ((Pi.basisFun ℝ (Fin (n + 1))).orientation.localOrientation
            (Module.finrank_fin_fun ℝ)) =
        prod (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ)
          (by omega : m + 1 + (n + 1) = m + n + 1 + 1)
          ((Pi.basisFun ℝ (Fin (m + 1))).orientation.localOrientation
            (Module.finrank_fin_fun ℝ))
          ((Pi.basisFun ℝ (Fin (n + 1))).orientation.localOrientation
            (Module.finrank_fin_fun ℝ))
        then 1 else -1 :=
  (rfl)

/-- The defining comparison of `crossSign` on the standard spaces. -/
private theorem coe_cross_pi_basisFun (m n : ℕ) (hd : m + 1 + (n + 1) = d + 1) :
    (cross (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ) hd
      ((Pi.basisFun ℝ (Fin (m + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ))
      ((Pi.basisFun ℝ (Fin (n + 1))).orientation.localOrientation
        (Module.finrank_fin_fun ℝ))).val =
      (crossSign m n : ℤ) • (prod (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ) hd
        ((Pi.basisFun ℝ (Fin (m + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ))
        ((Pi.basisFun ℝ (Fin (n + 1))).orientation.localOrientation
          (Module.finrank_fin_fun ℝ))).val := by
  obtain rfl : d = m + n + 1 := by omega
  have hX : finrank ℝ ((Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ)) = m + n + 1 + 1 :=
    finrank_prod_eq_succ (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ) hd
  have hor := eq_or_eq_neg (singularHomologyComplZeroIso hX)
    (cross (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ) hd
      ((Pi.basisFun ℝ (Fin (m + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ))
      ((Pi.basisFun ℝ (Fin (n + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ)))
    (prod (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ) hd
      ((Pi.basisFun ℝ (Fin (m + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ))
      ((Pi.basisFun ℝ (Fin (n + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ)))
  rw [crossSign_def]
  split_ifs with h
  · rw [Units.val_one, one_smul]
    exact congrArg Subtype.val h
  · rw [Units.val_neg, Units.val_one, neg_one_zsmul]
    exact congrArg Subtype.val (hor.resolve_left h)

/-- **The cross product and the ordered product differ by a sign depending only on the
dimensions.** For local orientations `z` of `E` and `z'` of `F` at the origin, of dimensions
`m + 1` and `n + 1`, the cross product `z × z'` is `crossSign m n` times the ordered product
`TauCeti.LocalOrientation.prod`, as local homology classes. -/
theorem coe_cross_eq_crossSign_smul (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (z : LocalOrientation E 0 (m + 1))
    (z' : LocalOrientation F 0 (n + 1)) :
    (cross hE hF hd z z').val = (crossSign m n : ℤ) • (prod hE hF hd z z').val := by
  have := FiniteDimensional.of_finrank_eq_succ hE
  have := FiniteDimensional.of_finrank_eq_succ hF
  -- Up to sign, `z` and `z'` are transported from the standard spaces, where both products are
  -- compared by definition; both products are natural and reverse with either factor.
  let f := ContinuousLinearEquiv.ofFinrankEq ((Module.finrank_fin_fun ℝ (n := m + 1)).trans hE.symm)
  let g := ContinuousLinearEquiv.ofFinrankEq ((Module.finrank_fin_fun ℝ (n := n + 1)).trans hF.symm)
  let s := (Pi.basisFun ℝ (Fin (m + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ)
  let s' := (Pi.basisFun ℝ (Fin (n + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ)
  have key : (cross hE hF hd (s.map f.complZeroPairIso) (s'.map g.complZeroPairIso)).val =
      (crossSign m n : ℤ) •
        (prod hE hF hd (s.map f.complZeroPairIso) (s'.map g.complZeroPairIso)).val := by
    rw [cross_map_complZeroPairIso (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ),
      prod_map_complZeroPairIso (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ), coe_map,
      coe_map, coe_cross_pi_basisFun, map_zsmul]
  rcases eq_or_eq_neg (singularHomologyComplZeroIso hE) z (s.map f.complZeroPairIso) with
    rfl | rfl <;>
  rcases eq_or_eq_neg (singularHomologyComplZeroIso hF) z' (s'.map g.complZeroPairIso) with
    rfl | rfl <;>
  simp only [cross_neg_left, cross_neg_right, prod_neg_left, prod_neg_right, coe_neg, zsmul_neg,
    key]

end TauCeti.LocalOrientation
