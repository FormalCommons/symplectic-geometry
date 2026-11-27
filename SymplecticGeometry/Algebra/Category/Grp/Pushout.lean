/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Pushouts of groups

This file describes pushout squares in `GrpCat` in two ways.

## Pushouts over `Bool` as `Monoid.PushoutI`

For a group `H` and a family `φ : ∀ b : Bool, H →* G b` of homomorphisms, Mathlib's amalgamated
product `Monoid.PushoutI φ` is a pushout in `GrpCat` of `φ false` and `φ true`. So every pushout
square of `φ false` and `φ true` in `GrpCat` is identified with it.

* `Monoid.PushoutI.isPushout`: the square formed by `φ false`, `φ true` and the inclusions
  `Monoid.PushoutI.of false`, `Monoid.PushoutI.of true` is a pushout in `GrpCat`.
* `CategoryTheory.IsPushout.mulEquivPushoutI`: for any pushout square
  ```
  H      --φ false-->  G false
  |                    |
  φ true               inl
  v                    v
  G true --inr------>  P
  ```
  in `GrpCat`, the isomorphism `P ≃* Monoid.PushoutI φ`, which sends `inl x` to
  `Monoid.PushoutI.of false x` and `inr x` to `Monoid.PushoutI.of true x`. Its `simp` lemmas
  have two forms: one for legs that are any morphisms of `GrpCat`, and one for legs
  `GrpCat.ofHom i` and `GrpCat.ofHom j` given by group homomorphisms.

The square is a pushout because `Monoid.PushoutI.lift` gives the map out of it to any cocone, and
`Monoid.PushoutI.hom_ext_nonempty` its uniqueness; the isomorphism is then
`CategoryTheory.IsPushout.isoIsPushout`.

## Pushouts along a surjection

Consider a pushout square of groups
```
H  --f-->  G₁
|          |
g          inl
v          v
G₂ --inr-> P
```
in `GrpCat`, with `f` surjective. Then `P` is the quotient of `G₂` by the normal closure of the
image under `g` of the kernel of `f`.

* `CategoryTheory.IsPushout.surjective_inr_of_surjective`: `inr` is surjective.
* `CategoryTheory.IsPushout.ker_inr_eq_normalClosure`: the kernel of `inr` is the normal closure
  of `g '' ker f`.
* `CategoryTheory.IsPushout.ker_inr_eq_normalClosure_image_of_ker_eq`: if moreover the kernel of
  `f` is the normal closure of `S`, the kernel of `inr` is the normal closure of `g '' S`.
* `CategoryTheory.IsPushout.quotientNormalClosureMulEquiv`: the resulting isomorphism
  `G₂ ⧸ normalClosure (g '' ker f) ≃* P`.
* `CategoryTheory.IsPushout.bijective_inr_of_ker_le` and
  `CategoryTheory.IsPushout.inrMulEquivOfKerLe`: if moreover `g` kills the kernel of `f`, then
  `inr` is an isomorphism.

The surjectivity of `inr` is Mathlib's `CategoryTheory.IsPushout.epi_inr_of_epi` together with
`GrpCat.epi_iff_surjective`. For the kernel, the quotient map `G₂ → G₂ ⧸ N` and the map
`G₁ → G₂ ⧸ N` that it induces through `f` (by `MonoidHom.liftOfSurjective`) form a cocone on the
span, and the map out of the pushout that this cocone gives splits `inr` onto the quotient.
-/

public section

universe u

namespace Monoid.PushoutI

open CategoryTheory Limits

variable {G : Bool → Type u} [∀ b, Group (G b)] {H : Type u} [Group H] (φ : ∀ b, H →* G b)

/-- The amalgamated product `Monoid.PushoutI φ` of a family `φ` of group homomorphisms indexed by
`Bool` is a pushout of `φ false` and `φ true` in `GrpCat`, with the inclusions `of false` and
`of true`. -/
theorem isPushout :
    IsPushout (GrpCat.ofHom (φ false)) (GrpCat.ofHom (φ true))
      (GrpCat.ofHom (of (φ := φ) false)) (GrpCat.ofHom (of (φ := φ) true)) := by
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk
    (by ext x; simp [of_apply_eq_base]) (fun s => GrpCat.ofHom (lift
      (Bool.rec (motive := fun b => G b →* s.pt) s.inl.hom s.inr.hom) (s.inl.hom.comp (φ false))
      ?_)) (fun s => ?_) (fun s => ?_) fun s m h₁ h₂ => ?_)
  · have := congrArg GrpCat.Hom.hom s.condition
    simp only [GrpCat.hom_comp, GrpCat.hom_ofHom] at this
    rintro (_ | _)
    · rfl
    · exact this.symm
  · ext x
    simp
  · ext x
    simp
  · refine GrpCat.hom_ext (hom_ext_nonempty fun b => ?_)
    cases b
    · ext x
      simpa using ConcreteCategory.congr_hom h₁ x
    · ext x
      simpa using ConcreteCategory.congr_hom h₂ x

end Monoid.PushoutI

namespace CategoryTheory.IsPushout

section PushoutI

variable {G : Bool → Type u} [∀ b, Group (G b)] {H : Type u} [Group H] {φ : ∀ b, H →* G b}
  {P : GrpCat.{u}} {inl : GrpCat.of (G false) ⟶ P} {inr : GrpCat.of (G true) ⟶ P}

/-- A pushout in `GrpCat` of the two homomorphisms of a family `φ` indexed by `Bool` is
isomorphic to the amalgamated product `Monoid.PushoutI φ`, by the isomorphism that sends the
legs `inl` and `inr` of the square to `Monoid.PushoutI.of false` and `Monoid.PushoutI.of true`. -/
noncomputable def mulEquivPushoutI
    (hP : IsPushout (GrpCat.ofHom (φ false)) (GrpCat.ofHom (φ true)) inl inr) :
    P ≃* Monoid.PushoutI φ :=
  (hP.isoIsPushout _ _ (Monoid.PushoutI.isPushout φ)).groupIsoToMulEquiv

/-! The left sides of the next lemmas name the types `G false` and `G true` of the argument of
`inl` and `inr` explicitly, rather than the inferred `GrpCat.of (G false)` and
`GrpCat.of (G true)`. The `simp` index reduces `GrpCat.of X` to `X` in a goal but not in the
statement of a lemma, so with the inferred types `simp` would never try these lemmas. The two
forms are defeq, so the proofs are unchanged. -/

@[simp]
theorem mulEquivPushoutI_inl
    (hP : IsPushout (GrpCat.ofHom (φ false)) (GrpCat.ofHom (φ true)) inl inr) (x : G false) :
    hP.mulEquivPushoutI
      (@DFunLike.coe (G false →* P) (G false) _ _ (ConcreteCategory.hom inl) x) =
      Monoid.PushoutI.of false x :=
  ConcreteCategory.congr_hom (hP.inl_isoIsPushout_hom _ _ (Monoid.PushoutI.isPushout φ)) x

@[simp]
theorem mulEquivPushoutI_inr
    (hP : IsPushout (GrpCat.ofHom (φ false)) (GrpCat.ofHom (φ true)) inl inr) (x : G true) :
    hP.mulEquivPushoutI
      (@DFunLike.coe (G true →* P) (G true) _ _ (ConcreteCategory.hom inr) x) =
      Monoid.PushoutI.of true x :=
  ConcreteCategory.congr_hom (hP.inr_isoIsPushout_hom _ _ (Monoid.PushoutI.isPushout φ)) x

@[simp]
theorem mulEquivPushoutI_symm_of_false
    (hP : IsPushout (GrpCat.ofHom (φ false)) (GrpCat.ofHom (φ true)) inl inr) (x : G false) :
    hP.mulEquivPushoutI.symm (Monoid.PushoutI.of false x) = inl x := by
  rw [MulEquiv.symm_apply_eq, mulEquivPushoutI_inl]

@[simp]
theorem mulEquivPushoutI_symm_of_true
    (hP : IsPushout (GrpCat.ofHom (φ false)) (GrpCat.ofHom (φ true)) inl inr) (x : G true) :
    hP.mulEquivPushoutI.symm (Monoid.PushoutI.of true x) = inr x := by
  rw [MulEquiv.symm_apply_eq, mulEquivPushoutI_inr]

/-! The same lemmas for a square whose legs are `GrpCat.ofHom i` and `GrpCat.ofHom j`, stated
with `i x` and `j x`, the form to which `simp` brings `GrpCat.ofHom i x`. For the same reason
as above, their left sides give the domain of `mulEquivPushoutI` and the codomain of its
inverse as `Q`, not as the inferred `GrpCat.of Q`. They have low priority: a bundled leg `inl`
is also `GrpCat.ofHom inl.hom` up to eta, and on such a square the lemmas above are the ones
wanted. -/

section ofHom

variable {Q : Type u} [Group Q] {i : G false →* Q} {j : G true →* Q}

@[simp low]
theorem mulEquivPushoutI_ofHom_inl (hP : IsPushout (GrpCat.ofHom (φ false))
    (GrpCat.ofHom (φ true)) (GrpCat.ofHom i) (GrpCat.ofHom j)) (x : G false) :
    @DFunLike.coe (Q ≃* Monoid.PushoutI φ) Q _ _ hP.mulEquivPushoutI (i x) =
      Monoid.PushoutI.of false x := by
  simpa using hP.mulEquivPushoutI_inl x

@[simp low]
theorem mulEquivPushoutI_ofHom_inr (hP : IsPushout (GrpCat.ofHom (φ false))
    (GrpCat.ofHom (φ true)) (GrpCat.ofHom i) (GrpCat.ofHom j)) (x : G true) :
    @DFunLike.coe (Q ≃* Monoid.PushoutI φ) Q _ _ hP.mulEquivPushoutI (j x) =
      Monoid.PushoutI.of true x := by
  simpa using hP.mulEquivPushoutI_inr x

@[simp low]
theorem mulEquivPushoutI_symm_of_false_ofHom (hP : IsPushout (GrpCat.ofHom (φ false))
    (GrpCat.ofHom (φ true)) (GrpCat.ofHom i) (GrpCat.ofHom j)) (x : G false) :
    @DFunLike.coe (Monoid.PushoutI φ ≃* Q) _ _ _ (MulEquiv.symm (M := Q) hP.mulEquivPushoutI)
      (Monoid.PushoutI.of false x) = i x := by
  simpa using hP.mulEquivPushoutI_symm_of_false x

@[simp low]
theorem mulEquivPushoutI_symm_of_true_ofHom (hP : IsPushout (GrpCat.ofHom (φ false))
    (GrpCat.ofHom (φ true)) (GrpCat.ofHom i) (GrpCat.ofHom j)) (x : G true) :
    @DFunLike.coe (Monoid.PushoutI φ ≃* Q) _ _ _ (MulEquiv.symm (M := Q) hP.mulEquivPushoutI)
      (Monoid.PushoutI.of true x) = j x := by
  simpa using hP.mulEquivPushoutI_symm_of_true x

end ofHom

end PushoutI

open Subgroup

variable {H G₁ G₂ P : GrpCat.{u}} {f : H ⟶ G₁} {g : H ⟶ G₂} {inl : G₁ ⟶ P} {inr : G₂ ⟶ P}

/-- In a pushout square of groups, `inr` is surjective if `f` is. -/
theorem surjective_inr_of_surjective (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) : Function.Surjective inr := by
  have : Epi f := (GrpCat.epi_iff_surjective f).2 hf
  exact (GrpCat.epi_iff_surjective inr).1 (hP.epi_inr_of_epi)

/-- In a pushout square of groups with `f` surjective, the kernel of `inr` is the normal closure
of the image under `g` of the kernel of `f`. -/
theorem ker_inr_eq_normalClosure (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) :
    inr.hom.ker = normalClosure (g.hom '' f.hom.ker) := by
  set N := normalClosure (g.hom '' f.hom.ker)
  refine le_antisymm (fun x hx => ?_) (normalClosure_le_normal ?_)
  · have hle : f.hom.ker ≤ ((QuotientGroup.mk' N).comp g.hom).ker := fun h hh => by
      simpa [QuotientGroup.eq_one_iff] using subset_normalClosure (Set.mem_image_of_mem g.hom hh)
    let ψ : G₁ ⟶ GrpCat.of (G₂ ⧸ N) :=
      GrpCat.ofHom (f.hom.liftOfSurjective hf ⟨(QuotientGroup.mk' N).comp g.hom, hle⟩)
    have w : f ≫ ψ = g ≫ GrpCat.ofHom (QuotientGroup.mk' N) := by
      ext h
      simp [ψ]
    have hx' : (QuotientGroup.mk x : G₂ ⧸ N) = hP.desc ψ _ w (inr x) := by
      rw [← ConcreteCategory.comp_apply, hP.inr_desc, GrpCat.ofHom_apply, QuotientGroup.mk'_apply]
    rw [MonoidHom.mem_ker.1 hx, map_one, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  · rintro _ ⟨h, hh, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, ← ConcreteCategory.comp_apply, ← hP.w,
      ConcreteCategory.comp_apply]
    exact (congrArg inl.hom (MonoidHom.mem_ker.1 hh)).trans (map_one _)

/-- In a pushout square of groups with `f` surjective and the kernel of `f` the normal closure of
a set `S`, the kernel of `inr` is the normal closure of `g '' S`. -/
theorem ker_inr_eq_normalClosure_image_of_ker_eq (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) {S : Set H} (hS : f.hom.ker = normalClosure S) :
    inr.hom.ker = normalClosure (g.hom '' S) := by
  rw [hP.ker_inr_eq_normalClosure hf, hS]
  -- `normalClosure (g '' normalClosure S) = normalClosure (g '' S)`
  refine le_antisymm (normalClosure_le_normal ?_)
    (normalClosure_mono (Set.image_mono subset_normalClosure))
  rw [Set.image_subset_iff]
  exact comap_normalClosure_image_ge S _

/-- A pushout of groups along a surjection `f` is the quotient of `G₂` by the normal closure of
the image under `g` of the kernel of `f`, through the map induced by `inr`. -/
noncomputable def quotientNormalClosureMulEquiv (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) : G₂ ⧸ normalClosure (g.hom '' f.hom.ker) ≃* P :=
  (QuotientGroup.quotientMulEquivOfEq (hP.ker_inr_eq_normalClosure hf).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective inr.hom (hP.surjective_inr_of_surjective hf))

@[simp low]
theorem quotientNormalClosureMulEquiv_mk (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) (x : G₂) :
    hP.quotientNormalClosureMulEquiv hf (QuotientGroup.mk x) = inr x := by
  simp [quotientNormalClosureMulEquiv, QuotientGroup.quotientKerEquivOfSurjective]

@[simp low]
theorem quotientNormalClosureMulEquiv_symm_inr (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) (x : G₂) :
    (hP.quotientNormalClosureMulEquiv hf).symm (inr x) = QuotientGroup.mk x := by
  rw [MulEquiv.symm_apply_eq, quotientNormalClosureMulEquiv_mk]

/-- In a pushout square of groups with `f` surjective, if `g` kills the kernel of `f`, then
`inr` is bijective. -/
theorem bijective_inr_of_ker_le (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) (hfg : f.hom.ker ≤ g.hom.ker) : Function.Bijective inr := by
  refine ⟨(injective_iff_map_eq_one inr.hom).2 fun x hx => ?_,
    hP.surjective_inr_of_surjective hf⟩
  rw [← MonoidHom.mem_ker, hP.ker_inr_eq_normalClosure hf] at hx
  have : g.hom '' f.hom.ker ⊆ (⊥ : Subgroup G₂) := by
    rintro _ ⟨h, hh, rfl⟩
    exact hfg hh
  exact (Subgroup.mem_bot).1 (normalClosure_le_normal this hx)

/-- In a pushout square of groups with `f` surjective and `g` killing the kernel of `f`: the map
`inr`, as an isomorphism of groups. -/
noncomputable def inrMulEquivOfKerLe (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) (hfg : f.hom.ker ≤ g.hom.ker) : G₂ ≃* P :=
  MulEquiv.ofBijective inr.hom (hP.bijective_inr_of_ker_le hf hfg)

@[simp low]
theorem inrMulEquivOfKerLe_apply (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) (hfg : f.hom.ker ≤ g.hom.ker) (x : G₂) :
    hP.inrMulEquivOfKerLe hf hfg x = inr x := by
  simp [inrMulEquivOfKerLe]

@[simp low]
theorem inrMulEquivOfKerLe_symm_inr (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) (hfg : f.hom.ker ≤ g.hom.ker) (x : G₂) :
    (hP.inrMulEquivOfKerLe hf hfg).symm (inr x) = x := by
  rw [MulEquiv.symm_apply_eq, inrMulEquivOfKerLe_apply]

end CategoryTheory.IsPushout

end
