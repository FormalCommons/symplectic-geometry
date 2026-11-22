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
import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import TauCeti.Geometry.Manifold.Orientation.AddCircle

/-!
# The cross product of local orientations

For points `x` of a space `X` and `y` of a space `Y`, the homology cross product of the pairs
`(X, X ∖ {x})` and `(Y, Y ∖ {y})` (`TopCat.singularHomologyCrossRelPair`), with integral
coefficients `ULift ℤ`, lands in the homology of `X × Y` relative to
`(X ∖ {x}) × Y ∪ X × (Y ∖ {y})`, which is the complement of `(x, y)`. With the coefficients
`ULift ℤ ⊗ ULift ℤ` multiplied back to `ULift ℤ` (`ModuleCat.uliftTensorSelfIso`), this is the
**cross product of local homology classes**

`Hₚ(X, X ∖ {x}; ℤ) ⊗ H_q(Y, Y ∖ {y}; ℤ) ⟶ Hₙ(X × Y, X × Y ∖ {(x, y)}; ℤ)`, for `p + q = n`

(`TauCeti.localHomologyCross`). It is natural in maps of pairs
(`TauCeti.localHomologyMap_tensorHom_localHomologyMap_localHomologyCross`), and on classes coming
from absolute homology it is the absolute cross product
(`TauCeti.singularHomologyπ_tensorHom_singularHomologyπ_localHomologyCross`).

The main result is that the cross product of two local orientations of real vector spaces at the
origin is a local orientation of their product (`TauCeti.isLocalOrientation_localHomologyCross`).
The proof reduces to compact manifolds. On compact connected manifolds `M` and `N` with integral
fundamental classes `μ` and `ν`, the cross product `μ × ν` is a fundamental class of `M × N`
(Tau Ceti's `TauCeti.IsFundamentalClass.singularHomologyCross`), and its image in the local
homology at `(x, y)` is the cross product of the images of `μ` and `ν`, so the cross product of
local orientations is a local orientation there
(`TauCeti.isLocalOrientation_localHomologyCross_of_isFundamentalClass`). Open embeddings
identify local homology groups compatibly with the cross product
(`TauCeti.forall_isLocalOrientation_localHomologyCross_iff`), and a vector space of dimension
`k + 1` embeds near the origin into the circle (`k = 0`) or into the sphere `Sᵏ⁺¹`, which have
integral fundamental classes (`TauCeti.exists_compact_manifold_isFundamentalClass`).

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

* `TauCeti.localHomologyCross`: the cross product of local homology classes.
* `TauCeti.LocalOrientation.cross`: the cross product of local orientations of vector spaces.
* `TauCeti.LocalOrientation.crossSign`: the sign comparing it with `TauCeti.LocalOrientation.prod`.

## Main results

* `TauCeti.isLocalOrientation_localHomologyCross`: the cross product of local orientations of
  vector spaces is a local orientation.
* `TauCeti.LocalOrientation.cross_map_complZeroPairIso`: naturality.
* `TauCeti.LocalOrientation.coe_cross_eq_crossSign_smul`,
  `TauCeti.LocalOrientation.coe_cross_localOrientation`: the cross product is `crossSign m n`
  times the ordered product, for all spaces of dimensions `m + 1` and `n + 1`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.2 and 3.3 (cross products, local orientations, fundamental classes) and Section 3.B
  (the relative cross product).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Set Topology Module

namespace TauCeti

section Cross

variable {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X']
  [TopologicalSpace Y']

/-- The identity of `X × Y` carries `(X ∖ {x}) × Y ∪ X × (Y ∖ {y})` into the complement of
`(x, y)`. -/
theorem mapsTo_preimage_fst_compl_union_preimage_snd_compl (x : X) (y : Y) :
    MapsTo (TopCat.tensorObjIsoOfProd X Y).hom
      (CartesianMonoidalCategory.fst (TopCat.of X) (TopCat.of Y) ⁻¹' ({x}ᶜ : Set (TopCat.of X)) ∪
        CartesianMonoidalCategory.snd (TopCat.of X) (TopCat.of Y) ⁻¹' ({y}ᶜ : Set (TopCat.of Y)))
      ({(x, y)}ᶜ : Set (TopCat.of (X × Y))) := by
  rintro p (hz | hz) h <;>
    simp only [TopCat.tensorObjIsoOfProd_hom_apply, mem_singleton_iff, Prod.mk.injEq] at h
  · exact hz h.1
  · exact hz h.2

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

/-- **The cross product of local homology classes on absolute classes.** For `a ∈ Hₚ(X; ℤ)` and
`b ∈ H_q(Y; ℤ)`, the cross product of their images in the local homology at `x` and `y` is the
image of the absolute cross product `a × b ∈ Hₙ(X × Y; ℤ ⊗ ℤ)` in the local homology at `(x, y)`,
with the coefficients multiplied to `ℤ`. -/
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
  have he : (TopCat.tensorObjIsoOfProd X Y).hom = 𝟙 (TopCat.of (X × Y)) := by
    -- `rfl` evaluates the identity, whose source `TopCat.of (X × Y)` is `TopCat.of X ⊗ TopCat.of Y`
    -- only after unfolding, so that `TopCat.hom_id` does not apply.
    ext p <;> simp <;> rfl
  have hid : SSet.homologyMap (TopCat.toSSet.map (TopCat.tensorObjIsoOfProd X Y).hom)
      (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) n = 𝟙 _ :=
    (congrArg (fun φ ↦ SSet.homologyMap (TopCat.toSSet.map φ) _ n) he).trans
      ((congrArg (SSet.homologyMap · _ n) (TopCat.toSSet.map_id _)).trans
        (SSet.homologyMap_id _ _ n))
  replace hπ := hπ.symm.trans ((congrArg (· ≫ _) hid).trans (Category.id_comp _))
  rw [localHomologyCross, ← Category.assoc,
    ← TopCat.singularHomologyCross_comp_singularHomologyπ_eq_singularHomologyCrossRelPair]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((reassoc_of% hπ) _))

/-- **Naturality of the cross product of local homology classes.** For maps `f : X → X'` and
`g : Y → Y'` with `f⁻¹(x') ⊆ {x}` and `g⁻¹(y') ⊆ {y}`, `f_* a × g_* b = (f × g)_* (a × b)`. -/
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
        (TopCat.tensorObjIsoOfProd X' Y').hom)
        (CartesianMonoidalCategory.fst (TopCat.of X) (TopCat.of Y) ⁻¹' ({x}ᶜ : Set (TopCat.of X)) ∪
          CartesianMonoidalCategory.snd (TopCat.of X) (TopCat.of Y) ⁻¹' ({y}ᶜ : Set (TopCat.of Y)))
        ({(x', y')}ᶜ : Set (TopCat.of (X' × Y'))) :=
      (mapsTo_preimage_fst_compl_union_preimage_snd_compl x' y').comp
        (TopCat.mapsTo_tensorHom_preimage_union _ _ hf' hg')
    have hkk : (TopCat.tensorObjIsoOfProd X Y).hom ≫ TopCat.ofHom (f.prodMap g) =
        (TopCat.ofHom f ⊗ₘ TopCat.ofHom g) ≫ (TopCat.tensorObjIsoOfProd X' Y').hom := by
      ext p <;> simp only [ConcreteCategory.comp_apply, TopCat.tensorObjIsoOfProd_hom_apply] <;>
        simp
    exact (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ hk rfl).trans
      (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ hk hkk).symm
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
    ConcreteCategory.congr_hom
      (singularHomologyπ_tensorHom_singularHomologyπ_localHomologyCross x y p q (p + q) rfl)
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
  refine (isLocalOrientation_iff _ _ _).2 fun w ↦ ?_
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.1 (hspan ▸ Submodule.mem_top : w ∈ _)
  exact ⟨k * (a * b), by rw [mul_comm, mul_zsmul']; exact (int_smul_eq_zsmul _ k _).symm.trans hk⟩

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
  have hn := ConcreteCategory.congr_hom
    (localHomologyMap_tensorHom_localHomologyMap_localHomologyCross
      ⟨j₁, hj₁.continuous⟩ ⟨j₂, hj₂.continuous⟩
      (by rw [ContinuousMap.coe_mk, ← image_singleton, hj₁.injective.preimage_image])
      (by rw [ContinuousMap.coe_mk, ← image_singleton, hj₂.injective.preimage_image]) p q n h)
    (a ⊗ₜ b)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hn
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

open Metric in
/-- In every positive dimension `k + 1` there is a compact connected manifold with an integral
fundamental class: the circle `AddCircle 1` for `k = 0`, and the sphere `Sᵏ⁺¹`, which is simply
connected, otherwise. -/
theorem exists_compact_manifold_isFundamentalClass (k : ℕ) :
    ∃ (M E : Type) (_ : TopologicalSpace M) (_ : T2Space M) (_ : CompactSpace M)
      (_ : ConnectedSpace M) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E)
      (_ : FiniteDimensional ℝ E) (_ : ChartedSpace E M),
      finrank ℝ E = k + 1 ∧
        ∃ μ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) (k + 1) :
          ModuleCat.{0} ℤ), IsFundamentalClass μ := by
  cases k with
  | zero =>
    have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
    exact ⟨AddCircle (1 : ℝ), ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, finrank_self ℝ,
      _, HomologicalOrientation.isFundamentalClass_fundamentalClass
        ((AddCircle.orientation 1).toHomologicalOrientation (finrank_self ℝ)) (finrank_self ℝ)⟩
  | succ k =>
    have := simplyConnectedSpace_sphere_euclideanSpace (n := k + 2) (by omega)
    have hE : finrank ℝ (EuclideanSpace ℝ (Fin (k + 2))) = k + 1 + 1 := by simp
    obtain ⟨o⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace
      (M := sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) hE
    exact ⟨sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1, EuclideanSpace ℝ (Fin (k + 2)),
      inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, hE,
      _, o.isFundamentalClass_fundamentalClass hE⟩

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
  obtain ⟨M₁, E₁, _, _, _, _, _, _, _, _, hE₁, μ₁, hμ₁⟩ :=
    exists_compact_manifold_isFundamentalClass m
  obtain ⟨M₂, E₂, _, _, _, _, _, _, _, _, hE₂, μ₂, hμ₂⟩ :=
    exists_compact_manifold_isFundamentalClass n
  obtain ⟨x₁⟩ : Nonempty M₁ := ConnectedSpace.toNonempty
  obtain ⟨x₂⟩ : Nonempty M₂ := ConnectedSpace.toNonempty
  -- A partial homeomorphism from `Fᵢ` to `Mᵢ` defined at `0`: a linear identification of `Fᵢ`
  -- with the model `Eᵢ`, a translation, and the inverse of the chart at `xᵢ`.
  let φ₁ : OpenPartialHomeomorph F₁ M₁ :=
    ((ContinuousLinearEquiv.ofFinrankEq (hF₁.trans hE₁.symm)).toHomeomorph.trans
      (Homeomorph.addRight (chartAt E₁ x₁ x₁))).toOpenPartialHomeomorph.trans
        (chartAt E₁ x₁).symm
  let φ₂ : OpenPartialHomeomorph F₂ M₂ :=
    ((ContinuousLinearEquiv.ofFinrankEq (hF₂.trans hE₂.symm)).toHomeomorph.trans
      (Homeomorph.addRight (chartAt E₂ x₂ x₂))).toOpenPartialHomeomorph.trans
        (chartAt E₂ x₂).symm
  have h₁ : (0 : F₁) ∈ φ₁.source := by simp [φ₁]
  have h₂ : (0 : F₂) ∈ φ₂.source := by simp [φ₂]
  exact (forall_isLocalOrientation_localHomologyCross_iff_of_openPartialHomeomorph φ₁ φ₂ h₁ h₂
    h).1 (fun w₁ w₂ ↦ isLocalOrientation_localHomologyCross_of_isFundamentalClass hE₁ hE₂ h
      hμ₁ hμ₂ w₁ w₂) z₁ z₂

end TauCeti

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

variable {E F E' F' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] {m n d : ℕ}

/-- A real vector space of positive dimension has two local orientations at the origin, opposite
to each other. -/
theorem eq_or_eq_neg (hE : finrank ℝ E = m + 1) (z z' : LocalOrientation E 0 (m + 1)) :
    z' = z ∨ z' = -z := by
  have := FiniteDimensional.of_finrank_eq_succ hE
  obtain ⟨ω, rfl⟩ := Orientation.localOrientation_surjective hE z
  obtain ⟨ω', rfl⟩ := Orientation.localOrientation_surjective hE z'
  rcases ω'.eq_or_eq_neg ω (by simp [hE]) with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Orientation.localOrientation_neg _ _)

/-- **The cross product of local orientations.** For local orientations `z` of `E` and `z'` of
`F` at the origin, their cross product `z × z'` is a local orientation of `E × F` at the origin
(`TauCeti.isLocalOrientation_localHomologyCross`). Its degree is written `d + 1` with
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
  have hn := ConcreteCategory.congr_hom
    (localHomologyMap_tensorHom_localHomologyMap_localHomologyCross
      ((f : E →L[ℝ] E') : C(E, E')) ((g : F →L[ℝ] F') : C(F, F'))
      (x := 0) (x' := 0) (y := 0) (y' := 0)
      (fun a ha ↦ by simpa using ha) (fun a ha ↦ by simpa using ha) (m + 1) (n + 1) (d + 1) hd)
    (z.val ⊗ₜ z'.val)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hn
  refine hn.trans ?_
  -- The product map `f × g` appears as `ContinuousMap.prodMap` and as `f.prodCongr g`.
  congr 3

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
  have hor := eq_or_eq_neg hX
    (prod (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ) hd
      ((Pi.basisFun ℝ (Fin (m + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ))
      ((Pi.basisFun ℝ (Fin (n + 1))).orientation.localOrientation (Module.finrank_fin_fun ℝ)))
    (cross (Module.finrank_fin_fun ℝ) (Module.finrank_fin_fun ℝ) hd
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
  rcases eq_or_eq_neg hE (s.map f.complZeroPairIso) z with rfl | rfl <;>
  rcases eq_or_eq_neg hF (s'.map g.complZeroPairIso) z' with rfl | rfl <;>
  simp only [cross_neg_left, cross_neg_right, prod_neg_left, prod_neg_right, coe_neg, zsmul_neg,
    key]

/-- The cross product of the local orientations selected by orientations `ω` and `ω'` is
`crossSign m n` times the local orientation selected by their product orientation. -/
theorem coe_cross_localOrientation (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (ω : Orientation ℝ E (Fin (m + 1)))
    (ω' : Orientation ℝ F (Fin (n + 1))) :
    (cross hE hF hd (ω.localOrientation hE) (ω'.localOrientation hF)).val =
      haveI := FiniteDimensional.of_finrank_eq_succ hE
      haveI := FiniteDimensional.of_finrank_eq_succ hF
      (crossSign m n : ℤ) • ((Orientation.reindex ℝ (E × F) (finCongr hd)
        (ω.prod ω' hE hF)).localOrientation (finrank_prod_eq_succ hE hF hd)).val := by
  rw [coe_cross_eq_crossSign_smul, prod_localOrientation]

end TauCeti.LocalOrientation
