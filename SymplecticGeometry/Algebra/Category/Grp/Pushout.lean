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
  apply to legs that are any morphisms of `GrpCat`, with object `P` or `GrpCat.of Q`, and, for
  the images of the legs, also to a leg `GrpCat.ofHom i` given by a group homomorphism.

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

The `simp` lemmas for these two isomorphisms apply to squares with any objects, whether
`GrpCat.of` objects or not, with a leg `inr` that is any morphism or `GrpCat.ofHom j`. `simp`
does not use the lemma for the inverse of `quotientNormalClosureMulEquiv` when `f` or `g` is
`GrpCat.ofHom`.

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

/-! The next lemmas are stated for a square whose object is `GrpCat.of Q`, and their left sides
name the types `Q`, `G false` and `G true` explicitly, rather than the inferred `GrpCat.of Q`,
`GrpCat.of (G false)` and `GrpCat.of (G true)`. The `simp` index reduces `GrpCat.of X` to `X`
in a goal but not in the statement of a lemma, so with the inferred types, or with an object
variable `P`, `simp` would not try them on a square whose object is `GrpCat.of Q`. They still
apply to a square with any object `P`, since `P` is `GrpCat.of P` up to eta. -/

section ofQ

variable {Q : Type u} [Group Q]

section bundled

variable {inl : GrpCat.of (G false) ⟶ GrpCat.of Q} {inr : GrpCat.of (G true) ⟶ GrpCat.of Q}

@[simp]
theorem mulEquivPushoutI_inl
    (hP : IsPushout (GrpCat.ofHom (φ false)) (GrpCat.ofHom (φ true)) inl inr) (x : G false) :
    @DFunLike.coe (Q ≃* Monoid.PushoutI φ) Q _ _ hP.mulEquivPushoutI
      (@DFunLike.coe (G false →* Q) (G false) _ _ (ConcreteCategory.hom inl) x) =
      Monoid.PushoutI.of false x :=
  ConcreteCategory.congr_hom (hP.inl_isoIsPushout_hom _ _ (Monoid.PushoutI.isPushout φ)) x

@[simp]
theorem mulEquivPushoutI_inr
    (hP : IsPushout (GrpCat.ofHom (φ false)) (GrpCat.ofHom (φ true)) inl inr) (x : G true) :
    @DFunLike.coe (Q ≃* Monoid.PushoutI φ) Q _ _ hP.mulEquivPushoutI
      (@DFunLike.coe (G true →* Q) (G true) _ _ (ConcreteCategory.hom inr) x) =
      Monoid.PushoutI.of true x :=
  ConcreteCategory.congr_hom (hP.inr_isoIsPushout_hom _ _ (Monoid.PushoutI.isPushout φ)) x

/-- The inverse of `mulEquivPushoutI` sends `Monoid.PushoutI.of false x` to `inl x`. For a leg
`GrpCat.ofHom i`, `simp` then brings the right side to `i x`. -/
@[simp]
theorem mulEquivPushoutI_symm_of_false
    (hP : IsPushout (GrpCat.ofHom (φ false)) (GrpCat.ofHom (φ true)) inl inr) (x : G false) :
    @DFunLike.coe (Monoid.PushoutI φ ≃* Q) _ _ _ (MulEquiv.symm (M := Q) hP.mulEquivPushoutI)
      (Monoid.PushoutI.of false x) = inl x := by
  rw [MulEquiv.symm_apply_eq, mulEquivPushoutI_inl]

/-- The inverse of `mulEquivPushoutI` sends `Monoid.PushoutI.of true x` to `inr x`. For a leg
`GrpCat.ofHom j`, `simp` then brings the right side to `j x`. -/
@[simp]
theorem mulEquivPushoutI_symm_of_true
    (hP : IsPushout (GrpCat.ofHom (φ false)) (GrpCat.ofHom (φ true)) inl inr) (x : G true) :
    @DFunLike.coe (Monoid.PushoutI φ ≃* Q) _ _ _ (MulEquiv.symm (M := Q) hP.mulEquivPushoutI)
      (Monoid.PushoutI.of true x) = inr x := by
  rw [MulEquiv.symm_apply_eq, mulEquivPushoutI_inr]

end bundled

/-! The images of the legs, for a leg `GrpCat.ofHom i` given by a group homomorphism, stated
with `i x`, the form to which `simp` brings `GrpCat.ofHom i x`. The other leg is any morphism. -/

@[simp]
theorem mulEquivPushoutI_ofHom_inl {i : G false →* Q} {inr : GrpCat.of (G true) ⟶ GrpCat.of Q}
    (hP : IsPushout (GrpCat.ofHom (φ false)) (GrpCat.ofHom (φ true)) (GrpCat.ofHom i) inr)
    (x : G false) :
    @DFunLike.coe (Q ≃* Monoid.PushoutI φ) Q _ _ hP.mulEquivPushoutI (i x) =
      Monoid.PushoutI.of false x := by
  simpa using hP.mulEquivPushoutI_inl x

@[simp]
theorem mulEquivPushoutI_ofHom_inr {inl : GrpCat.of (G false) ⟶ GrpCat.of Q} {j : G true →* Q}
    (hP : IsPushout (GrpCat.ofHom (φ false)) (GrpCat.ofHom (φ true)) inl (GrpCat.ofHom j))
    (x : G true) :
    @DFunLike.coe (Q ≃* Monoid.PushoutI φ) Q _ _ hP.mulEquivPushoutI (j x) =
      Monoid.PushoutI.of true x := by
  simpa using hP.mulEquivPushoutI_inr x

end ofQ

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

/-! The next lemmas are stated for a square whose objects are `GrpCat.of A`, `GrpCat.of B`,
`GrpCat.of C` and `GrpCat.of D`, and their left sides name these types explicitly, down to the
subgroup in the quotient, for the reason given before `mulEquivPushoutI_inl`. They still apply to
a square with any objects, since an object `G` is `GrpCat.of G` up to eta.

`quotientNormalClosureMulEquiv_mk` is moreover stated for legs `GrpCat.ofHom φ` and
`GrpCat.ofHom ψ`, so that its subgroup reads `normalClosure (ψ '' φ.ker)`. The `simp` index
reduces a leg `GrpCat.ofHom φ` of a goal to `φ`, and a leg `f` of a lemma does not match that.
A bundled leg `f` still matches the lemma, as `GrpCat.ofHom f.hom'` up to eta. The lemma about
the inverse of `quotientNormalClosureMulEquiv` cannot take this form: its right side lies in the
quotient, which would then name `f.hom'` in place of the goal's `f.hom`, and `simp` could not
close the result. So it is stated for bundled legs `f` and `g`, and `simp` does not use it when
`f` or `g` is `GrpCat.ofHom`. The lemmas about `inrMulEquivOfKerLe` and its inverse have no
quotient on either side, and `simp` uses them for bundled and for `GrpCat.ofHom` legs alike. For
a leg `inr = GrpCat.ofHom j`, `simp` brings `inr x` to `j x`, so the lemmas
about the inverses have companions stated with `j x`. -/

section ofTypes

variable {A B C D : Type u} [Group A] [Group B] [Group C] [Group D]
  {inl : GrpCat.of B ⟶ GrpCat.of D}

@[simp]
theorem quotientNormalClosureMulEquiv_mk {φ : A →* B} {ψ : A →* C}
    {inr : GrpCat.of C ⟶ GrpCat.of D} (hP : IsPushout (GrpCat.ofHom φ) (GrpCat.ofHom ψ) inl inr)
    (hf : Function.Surjective (GrpCat.ofHom φ)) (x : C) :
    @DFunLike.coe (C ⧸ normalClosure (ψ '' φ.ker) ≃* D) _ _ _
      (hP.quotientNormalClosureMulEquiv hf) (QuotientGroup.mk x) =
      @DFunLike.coe (C →* D) C _ _ (ConcreteCategory.hom inr) x := by
  simp [quotientNormalClosureMulEquiv, QuotientGroup.quotientKerEquivOfSurjective]

variable {f : GrpCat.of A ⟶ GrpCat.of B} {g : GrpCat.of A ⟶ GrpCat.of C}

@[simp]
theorem quotientNormalClosureMulEquiv_symm_inr {inr : GrpCat.of C ⟶ GrpCat.of D}
    (hP : IsPushout f g inl inr) (hf : Function.Surjective f) (x : C) :
    @DFunLike.coe (D ≃* C ⧸ @normalClosure C _ (@Set.image A C
        (@DFunLike.coe (A →* C) A _ _ (ConcreteCategory.hom g))
        (@SetLike.coe (Subgroup A) A _ (@MonoidHom.ker A _ B _ (ConcreteCategory.hom f))))) _ _ _
      (MulEquiv.symm (M := C ⧸ _) (N := D) (hP.quotientNormalClosureMulEquiv hf))
      (@DFunLike.coe (C →* D) C _ _ (ConcreteCategory.hom inr) x) = QuotientGroup.mk x := by
  rw [MulEquiv.symm_apply_eq, quotientNormalClosureMulEquiv_mk]

@[simp]
theorem quotientNormalClosureMulEquiv_symm_ofHom_inr {j : C →* D}
    (hP : IsPushout f g inl (GrpCat.ofHom j)) (hf : Function.Surjective f) (x : C) :
    @DFunLike.coe (D ≃* C ⧸ @normalClosure C _ (@Set.image A C
        (@DFunLike.coe (A →* C) A _ _ (ConcreteCategory.hom g))
        (@SetLike.coe (Subgroup A) A _ (@MonoidHom.ker A _ B _ (ConcreteCategory.hom f))))) _ _ _
      (MulEquiv.symm (M := C ⧸ _) (N := D) (hP.quotientNormalClosureMulEquiv hf)) (j x) =
      QuotientGroup.mk x := by
  simpa using hP.quotientNormalClosureMulEquiv_symm_inr hf x

@[simp]
theorem inrMulEquivOfKerLe_apply {inr : GrpCat.of C ⟶ GrpCat.of D} (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) (hfg : f.hom.ker ≤ g.hom.ker) (x : C) :
    @DFunLike.coe (C ≃* D) C _ _ (hP.inrMulEquivOfKerLe hf hfg) x =
      @DFunLike.coe (C →* D) C _ _ (ConcreteCategory.hom inr) x := by
  simp [inrMulEquivOfKerLe]

@[simp]
theorem inrMulEquivOfKerLe_symm_inr {inr : GrpCat.of C ⟶ GrpCat.of D}
    (hP : IsPushout f g inl inr) (hf : Function.Surjective f) (hfg : f.hom.ker ≤ g.hom.ker)
    (x : C) :
    @DFunLike.coe (D ≃* C) D _ _ (MulEquiv.symm (M := C) (N := D) (hP.inrMulEquivOfKerLe hf hfg))
      (@DFunLike.coe (C →* D) C _ _ (ConcreteCategory.hom inr) x) = x := by
  rw [MulEquiv.symm_apply_eq, inrMulEquivOfKerLe_apply]

@[simp]
theorem inrMulEquivOfKerLe_symm_ofHom_inr {j : C →* D}
    (hP : IsPushout f g inl (GrpCat.ofHom j)) (hf : Function.Surjective f)
    (hfg : f.hom.ker ≤ g.hom.ker) (x : C) :
    @DFunLike.coe (D ≃* C) D _ _ (MulEquiv.symm (M := C) (N := D) (hP.inrMulEquivOfKerLe hf hfg))
      (j x) = x := by
  simpa using hP.inrMulEquivOfKerLe_symm_inr hf hfg x

end ofTypes

end CategoryTheory.IsPushout

end
