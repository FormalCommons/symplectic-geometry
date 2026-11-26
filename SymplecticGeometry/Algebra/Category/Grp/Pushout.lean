/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Pushouts of groups along a surjection

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

## Main results

* `CategoryTheory.IsPushout.surjective_inr_of_surjective`: `inr` is surjective.
* `CategoryTheory.IsPushout.ker_inr_eq_normalClosure`: the kernel of `inr` is the normal closure
  of `g '' ker f`.
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

namespace CategoryTheory.IsPushout

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

/-- A pushout of groups along a surjection `f` is the quotient of `G₂` by the normal closure of
the image under `g` of the kernel of `f`, through the map induced by `inr`. -/
noncomputable def quotientNormalClosureMulEquiv (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) : G₂ ⧸ normalClosure (g.hom '' f.hom.ker) ≃* P :=
  (QuotientGroup.quotientMulEquivOfEq (hP.ker_inr_eq_normalClosure hf).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective inr.hom (hP.surjective_inr_of_surjective hf))

@[simp]
theorem quotientNormalClosureMulEquiv_mk (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) (x : G₂) :
    hP.quotientNormalClosureMulEquiv hf (QuotientGroup.mk x) = inr x := by
  simp [quotientNormalClosureMulEquiv, QuotientGroup.quotientKerEquivOfSurjective]

@[simp]
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

@[simp]
theorem inrMulEquivOfKerLe_apply (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) (hfg : f.hom.ker ≤ g.hom.ker) (x : G₂) :
    hP.inrMulEquivOfKerLe hf hfg x = inr x := by
  simp [inrMulEquivOfKerLe]

@[simp]
theorem inrMulEquivOfKerLe_symm_inr (hP : IsPushout f g inl inr)
    (hf : Function.Surjective f) (hfg : f.hom.ker ≤ g.hom.ker) (x : G₂) :
    (hP.inrMulEquivOfKerLe hf hfg).symm (inr x) = x := by
  rw [MulEquiv.symm_apply_eq, inrMulEquivOfKerLe_apply]

end CategoryTheory.IsPushout

end
