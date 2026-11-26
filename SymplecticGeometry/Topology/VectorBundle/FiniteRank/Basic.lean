/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback

/-!
# The fibrewise equivalences of an isomorphism of finite-rank cores

Tau Ceti's `TauCeti.FiniteRankBundleCore.isoOfContinuousEquiv` builds an isomorphism of
finite-rank cores from a family of fibrewise continuous linear equivalences that is continuous on
total spaces. This file gives the converse construction.

It begins with three rules for fibre maps that Tau Ceti's files do not state:

* `TauCeti.FiniteRankBundleCore.fiberMap_sub`: the fibre map of a difference of bundle maps is
  the difference of their fibre maps;
* `TauCeti.FiniteRankBundleCore.fiberMap_comp_apply`: the fibre map of a composite, applied to a
  vector;
* `TauCeti.FiniteRankBundleCore.id_apply_pullback`: the identity of the coordinates of `A`, read
  as a map of the coordinates of a pullback `A.pullback f`, fixes each vector. It is a `simp`
  lemma, since `ContinuousLinearMap.id_apply` does not see through the rank of the pullback.

Then:

* `TauCeti.FiniteRankBundleCore.fiberMap_hom_inv_id` and
  `TauCeti.FiniteRankBundleCore.fiberMap_inv_hom_id`: the fibre maps of the two halves of an
  isomorphism are inverse to each other;
* `TauCeti.FiniteRankBundleCore.fiberMap_eqToHom`: the fibre map of a cast `eqToHom h`, as a
  function of the vector, reindexes coordinates along the equality of ranks. Unlike Tau Ceti's
  `fiberMap_eqToHom_apply`, it rewrites before a coordinate is applied, under another fibre map;
* `TauCeti.FiniteRankBundleCore.coordChange_apply_of_eq`: equal cores have the same transitions,
  up to reindexing coordinates along the equality of ranks;
* `TauCeti.FiniteRankBundleCore.isoFiberEquiv e x`: the continuous linear equivalence between the
  fibres over `x`, in coordinates, given by an isomorphism `e : A ≅ D` of finite-rank cores, with
  the fibre map of `e.hom` as the map and that of `e.inv` as its inverse;
* `TauCeti.FiniteRankBundleCore.isInvertible_fiberMap_hom` and
  `TauCeti.FiniteRankBundleCore.inverse_fiberMap_hom`: the fibre map of `e.hom` is invertible, and
  its inverse is the fibre map of `e.inv`;
* `TauCeti.FiniteRankBundleCore.continuous_isoFiberEquiv`: this family is continuous on total
  spaces, in the form that `isoOfContinuousEquiv` takes;
* `TauCeti.FiniteRankBundleCore.isoFiberEquiv_isoOfContinuousEquiv` and
  `TauCeti.FiniteRankBundleCore.isoOfContinuousEquiv_isoFiberEquiv`: the two constructions are
  inverse to each other.
* `TauCeti.FiniteRankBundleCore.continuous_isoFiberEquiv_const`: an isomorphism from a trivial core
  carries a constant section to a continuous one;
* `TauCeti.FiniteRankBundleCore.isoFiberEquiv_apply_eq_smul`: two isomorphisms that differ over a
  point by a scalar have fibrewise equivalences that differ by that scalar there.
* `TauCeti.FiniteRankBundleCore.fiberMap_trans_trans_symm_hom`: being a scalar multiple of the
  identity on a fibre is invariant under conjugation by isomorphisms.

Finally it treats the fibre functors `TauCeti.FiniteRankBundleCore.fiberFunctor x` as a family:

* `TauCeti.FiniteRankBundleCore.jointlyFaithful_fiberFunctor`: they are jointly faithful in the
  sense of Mathlib's `CategoryTheory.JointlyFaithful`, which is Tau Ceti's
  `TauCeti.FiniteRankBundleCore.hom_ext_of_fiberFunctor`;

and, since jointly faithful functors jointly reflect monomorphisms and epimorphisms, Mathlib's
`CategoryTheory.JointlyFaithful.jointlyReflectMonomorphisms` and
`CategoryTheory.JointlyFaithful.jointlyReflectEpimorphisms` give fibrewise criteria:

* `TauCeti.FiniteRankBundleCore.mono_of_injective_fiberMap`: a bundle map that is injective on
  every fibre is a monomorphism;
* `TauCeti.FiniteRankBundleCore.epi_of_surjective_fiberMap`: a bundle map that is surjective on
  every fibre is an epimorphism;
* `TauCeti.FiniteRankBundleCore.isIso_of_injective_fiberMap`: an endomorphism that is injective on
  every fibre is an isomorphism, the fibres being finite-dimensional.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §2 (isomorphisms of vector bundles).
-/

public section

open Bundle CategoryTheory

namespace TauCeti

namespace FiniteRankBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {A D : FiniteRankBundleCore 𝕜 B}

/-- The fibre map of a difference of bundle maps of finite-rank cores is the difference of their
fibre maps. -/
@[simp] theorem fiberMap_sub (f g : A ⟶ D) (x : B) :
    (f - g).fiberMap x = f.fiberMap x - g.fiberMap x := by
  rw [sub_eq_add_neg, fiberMap_add, fiberMap_neg, ← sub_eq_add_neg]

/-- The fibre map of a composite `f ≫ g` of bundle maps of finite-rank cores sends a vector `v` to
the image under the fibre map of `g` of its image under the fibre map of `f`. -/
theorem fiberMap_comp_apply {C : FiniteRankBundleCore 𝕜 B} (f : A ⟶ D) (g : D ⟶ C) (x : B)
    (v : Fin A.rank → 𝕜) : (f ≫ g).fiberMap x v = g.fiberMap x (f.fiberMap x v) := by
  rw [fiberMap_comp, ContinuousLinearMap.comp_apply]

/-- The identity of the coordinates `Fin A.rank → 𝕜` of `A` fixes each vector of the coordinates
of the pullback `A.pullback f`. These are the same space, since the pullback has the rank of `A`
(`rank_pullback`), but only up to unfolding `pullback`: `ContinuousLinearMap.id_apply` does not
apply to the term that the fibre map of a pulled-back map (`fiberMap_pullbackMap`) leaves, whose
coercion to functions is on the coordinates of the pullback. -/
@[simp] theorem id_apply_pullback {Z : Type*} [TopologicalSpace Z] (A : FiniteRankBundleCore 𝕜 B)
    (f : C(Z, B)) (v : Fin (A.pullback f).rank → 𝕜) :
    (ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :
      (Fin (A.pullback f).rank → 𝕜) →L[𝕜] (Fin (A.pullback f).rank → 𝕜)) v = v :=
  -- `rfl` rather than `(rfl)`, so that `simp` may use the lemma as a definitional rewrite,
  -- which a goal whose vector lives over an iterated pullback needs.
  rfl

/-- The fibre map of `e.inv` after that of `e.hom`, for an isomorphism `e : A ≅ D` of finite-rank
cores, is the identity of the fibre of `A`. -/
@[simp] theorem fiberMap_hom_inv_id (e : A ≅ D) (x : B) :
    (e.inv.fiberMap x).comp (e.hom.fiberMap x) = .id 𝕜 _ := by
  rw [← fiberMap_comp, Iso.hom_inv_id, fiberMap_id]

/-- The fibre map of `e.hom` after that of `e.inv`, for an isomorphism `e : A ≅ D` of finite-rank
cores, is the identity of the fibre of `D`. -/
@[simp] theorem fiberMap_inv_hom_id (e : A ≅ D) (x : B) :
    (e.hom.fiberMap x).comp (e.inv.fiberMap x) = .id 𝕜 _ := by
  rw [← fiberMap_comp, Iso.inv_hom_id, fiberMap_id]

/-- The fibre map over `x` of the cast `eqToHom h`, for an equality `h : A = D` of finite-rank
cores, reindexes the coordinates of a vector along the equality of ranks that `h` gives. -/
@[simp] theorem fiberMap_eqToHom (h : A = D) (x : B) (v : Fin A.rank → 𝕜) :
    (eqToHom h).fiberMap x v = v ∘ Fin.cast (congrArg rank h).symm :=
  funext (fiberMap_eqToHom_apply h x v)

/-- The transitions of equal finite-rank cores agree, once the coordinates of the second are
reindexed along the equality of ranks that `h : A = D` gives. -/
theorem coordChange_apply_of_eq (h : A = D) (i j x : B) (v : Fin A.rank → 𝕜) :
    A.core.coordChange i j x v =
      D.core.coordChange i j x (v ∘ Fin.cast (congrArg rank h).symm) ∘
        Fin.cast (congrArg rank h) := by
  subst h
  rfl

/-- The continuous linear equivalence between the fibres over `x` of two finite-rank cores, in
their coordinates `Fin A.rank → 𝕜` and `Fin D.rank → 𝕜`, given by an isomorphism `e : A ≅ D`: the
fibre map of `e.hom`, with inverse the fibre map of `e.inv`. -/
def isoFiberEquiv (e : A ≅ D) (x : B) : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜) :=
  ContinuousLinearEquiv.ofContinuousLinearMap (e.hom.fiberMap x) (e.inv.fiberMap x)
    (fiberMap_inv_hom_id e x) (fiberMap_hom_inv_id e x)

@[simp] theorem toContinuousLinearMap_isoFiberEquiv (e : A ≅ D) (x : B) :
    (isoFiberEquiv e x : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) = e.hom.fiberMap x := by
  rw [isoFiberEquiv, ContinuousLinearEquiv.toContinuousLinearMap_ofContinuousLinearMap]

@[simp] theorem isoFiberEquiv_apply (e : A ≅ D) (x : B) (v : Fin A.rank → 𝕜) :
    isoFiberEquiv e x v = e.hom.fiberMap x v := by
  rw [isoFiberEquiv, ContinuousLinearEquiv.coe_ofContinuousLinearMap]

@[simp] theorem isoFiberEquiv_symm (e : A ≅ D) (x : B) :
    (isoFiberEquiv e x).symm = isoFiberEquiv e.symm x := by
  apply ContinuousLinearEquiv.coe_injective
  rw [toContinuousLinearMap_isoFiberEquiv, Iso.symm_hom, isoFiberEquiv,
    ContinuousLinearEquiv.symm_ofContinuousLinearMap,
    ContinuousLinearEquiv.toContinuousLinearMap_ofContinuousLinearMap]

/-- The fibre map over `x` of the forward half of an isomorphism `e : A ≅ D` of finite-rank cores
is an invertible continuous linear map. -/
@[simp] theorem isInvertible_fiberMap_hom (e : A ≅ D) (x : B) :
    (e.hom.fiberMap x).IsInvertible :=
  .of_inverse (fiberMap_inv_hom_id e x) (fiberMap_hom_inv_id e x)

/-- The inverse of the fibre map over `x` of the forward half of an isomorphism `e : A ≅ D` of
finite-rank cores is the fibre map over `x` of its backward half. -/
@[simp] theorem inverse_fiberMap_hom (e : A ≅ D) (x : B) :
    (e.hom.fiberMap x).inverse = e.inv.fiberMap x :=
  ContinuousLinearMap.inverse_eq (fiberMap_inv_hom_id e x) (fiberMap_hom_inv_id e x)

@[simp] theorem isoFiberEquiv_refl (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    isoFiberEquiv (Iso.refl A) x = ContinuousLinearEquiv.refl 𝕜 (Fin A.rank → 𝕜) := by
  apply ContinuousLinearEquiv.coe_injective
  rw [toContinuousLinearMap_isoFiberEquiv, Iso.refl_hom, fiberMap_id,
    ContinuousLinearEquiv.coe_refl]

@[simp] theorem isoFiberEquiv_trans {C : FiniteRankBundleCore 𝕜 B} (e : A ≅ D) (f : D ≅ C)
    (x : B) : isoFiberEquiv (e ≪≫ f) x = (isoFiberEquiv e x).trans (isoFiberEquiv f x) := by
  apply ContinuousLinearEquiv.coe_injective
  rw [← ContinuousLinearEquiv.comp_coe, toContinuousLinearMap_isoFiberEquiv,
    toContinuousLinearMap_isoFiberEquiv, toContinuousLinearMap_isoFiberEquiv, Iso.trans_hom,
    fiberMap_comp]

/-- The fibrewise equivalences of an isomorphism of finite-rank cores are continuous on total
spaces. -/
theorem continuous_isoFiberEquiv (e : A ≅ D) :
    Continuous fun p : A.core.TotalSpace ↦
      TotalSpace.mk' (Fin D.rank → 𝕜) (E := D.core.Fiber) p.proj (isoFiberEquiv e p.proj p.snd) :=
  e.hom.continuous_totalSpaceMap.congr fun p ↦ by
    -- `exact` identifies the fibre `A.core.Fiber p.proj` with the coordinates `Fin A.rank → 𝕜`,
    -- which it is by definition.
    rw [VectorBundleCore.CoordinateHom.totalSpaceMap_def]
    exact congrArg (TotalSpace.mk' _ p.proj) (isoFiberEquiv_apply e p.proj p.snd).symm

/-- The fibrewise equivalences of the isomorphism built from a continuous family `ψ` of fibrewise
equivalences are those of `ψ`. -/
@[simp] theorem isoFiberEquiv_isoOfContinuousEquiv [CompleteSpace 𝕜]
    (ψ : B → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hψ : Continuous fun p : A.core.TotalSpace ↦
      TotalSpace.mk' (Fin D.rank → 𝕜) (E := D.core.Fiber) p.proj (ψ p.proj p.snd)) (x : B) :
    isoFiberEquiv (isoOfContinuousEquiv ψ hψ) x = ψ x := by
  apply ContinuousLinearEquiv.coe_injective
  rw [toContinuousLinearMap_isoFiberEquiv, fiberMap_isoOfContinuousEquiv_hom]

/-- The isomorphism built from the fibrewise equivalences of an isomorphism `e` of finite-rank
cores is `e`. -/
@[simp] theorem isoOfContinuousEquiv_isoFiberEquiv [CompleteSpace 𝕜] (e : A ≅ D) :
    isoOfContinuousEquiv (isoFiberEquiv e) (continuous_isoFiberEquiv e) = e := by
  ext x : 2
  simp

/-- An isomorphism `e` from a trivial core carries a constant section `x ↦ v` to a section of `D`
that is continuous on total spaces. -/
theorem continuous_isoFiberEquiv_const {n : ℕ} (e : trivial 𝕜 B n ≅ D) (v : Fin n → 𝕜) :
    Continuous fun x : B ↦
      TotalSpace.mk' (Fin D.rank → 𝕜) (E := D.core.Fiber) x (isoFiberEquiv e x v) := by
  have hv : Continuous fun x : B ↦
      TotalSpace.mk' (Fin (trivial 𝕜 B n).rank → 𝕜) (E := (trivial 𝕜 B n).core.Fiber) x v :=
    continuous_trivial_iff.2 ⟨continuous_id, continuous_const⟩
  exact (continuous_isoFiberEquiv e).comp hv

/-- If two isomorphisms `d d' : A ≅ D` differ over `x` by multiplication by `c`, in the sense
that `d' ≪≫ d.symm` acts on the fibre over `x` as `c` times the identity, then their fibrewise
equivalences over `x` differ by the factor `c`. -/
theorem isoFiberEquiv_apply_eq_smul (d d' : A ≅ D) {x : B} {c : 𝕜}
    (h : (d' ≪≫ d.symm).hom.fiberMap x = c • ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜))
    (v : Fin A.rank → 𝕜) :
    isoFiberEquiv d' x v = c • isoFiberEquiv d x v := by
  have hd : d'.hom = (d' ≪≫ d.symm).hom ≫ d.hom := by simp
  rw [isoFiberEquiv_apply, isoFiberEquiv_apply, hd, fiberMap_comp, ContinuousLinearMap.comp_apply,
    h, smul_apply, ContinuousLinearMap.id_apply, map_smul]

/-- If `d' ≪≫ d.symm` acts on the fibre over `x` as `c` times the identity, then so does its
conjugate `(a ≪≫ d' ≪≫ b) ≪≫ (a ≪≫ d ≪≫ b).symm`. -/
theorem fiberMap_trans_trans_symm_hom {P Q R : FiniteRankBundleCore 𝕜 B} (a : A ≅ P)
    (d d' : P ≅ Q) (b : Q ≅ R) {x : B} {c : 𝕜}
    (h : (d' ≪≫ d.symm).hom.fiberMap x = c • ContinuousLinearMap.id 𝕜 (Fin P.rank → 𝕜)) :
    ((a ≪≫ d' ≪≫ b) ≪≫ (a ≪≫ d ≪≫ b).symm).hom.fiberMap x =
      c • ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  have he : (a ≪≫ d' ≪≫ b) ≪≫ (a ≪≫ d ≪≫ b).symm = a ≪≫ (d' ≪≫ d.symm) ≪≫ a.symm := by
    simp
  rw [he, Iso.trans_hom, Iso.trans_hom, fiberMap_comp, fiberMap_comp, h,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, ContinuousLinearMap.smul_comp,
    Iso.symm_hom, fiberMap_hom_inv_id]

/-- The fibre functors `fiberFunctor x`, for `x : B`, are jointly faithful: two bundle maps of
finite-rank cores with the same fibre maps are equal. -/
theorem jointlyFaithful_fiberFunctor : JointlyFaithful (fiberFunctor (𝕜 := 𝕜) (B := B)) :=
  ⟨hom_ext_of_fiberFunctor⟩

/-- A bundle map of finite-rank cores whose fibre maps are all injective is a monomorphism. -/
theorem mono_of_injective_fiberMap (f : A ⟶ D) (hf : ∀ x, Function.Injective (f.fiberMap x)) :
    Mono f :=
  -- The underlying function of `(fiberFunctor x).map f` is `f.fiberMap x` by definition, with
  -- the carrier of `(fiberFunctor x).obj A` in place of `Fin A.rank → 𝕜`, so that Tau Ceti's
  -- `fiberFunctor_map_apply` does not rewrite it.
  have (x : B) : Mono ((fiberFunctor x).map f) := (ModuleCat.mono_iff_injective _).2 (hf x)
  jointlyFaithful_fiberFunctor.jointlyReflectMonomorphisms.mono f

/-- A bundle map of finite-rank cores whose fibre maps are all surjective is an epimorphism. -/
theorem epi_of_surjective_fiberMap (f : A ⟶ D) (hf : ∀ x, Function.Surjective (f.fiberMap x)) :
    Epi f :=
  -- As in `mono_of_injective_fiberMap`, this is `hf x` by definition of `fiberFunctor`.
  have (x : B) : Epi ((fiberFunctor x).map f) := (ModuleCat.epi_iff_surjective _).2 (hf x)
  jointlyFaithful_fiberFunctor.jointlyReflectEpimorphisms.epi f

/-- An endomorphism of a finite-rank core over a complete field whose fibre maps are all injective
is an isomorphism: each fibre map is an injective endomorphism of a finite-dimensional space. -/
theorem isIso_of_injective_fiberMap [CompleteSpace 𝕜] (f : A ⟶ A)
    (hf : ∀ x, Function.Injective (f.fiberMap x)) : IsIso f :=
  (isIso_iff_bijective f).2 fun x ↦ by
    have h : Function.Injective (f.fiberMap x).toLinearMap := hf x
    exact ⟨h, LinearMap.injective_iff_surjective.1 h⟩

end FiniteRankBundleCore

end TauCeti

end
