/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Components of a lift into a biproduct of cochain complexes of modules

Let `r : A ⟶ C`, `b : A ⟶ D`, `t : C ⟶ B` and `l : D ⟶ B` be maps of cochain complexes of
modules. Given a cochain `x` of `C ⊞ D` in degree `p` whose coboundary is the image of a cochain
`z` of `A` under `(r, b)`, and whose image under `t - l` is `a`, its two components `u` of `C`
and `v` of `D` have coboundaries `r(z)` and `b(z)`, and `t(u) - l(v) = a`
(`HomologicalComplex.moduleCat_exists_components_of_biprod_lift`). This is the step of the
description of a Mayer–Vietoris connecting map that splits a cochain into its two pieces.

This lemma is from Tau Ceti's main branch (`TauCeti/Algebra/Homology/ModuleCat/Basic.lean`, same
name), as of the commit `e48a7f81a81426270765022681d165be592a3231`, not yet in the pinned release;
it is stated here under its Tau Ceti name, so that moving Tau Ceti past it deletes this file
without renames.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

/-- Components of a biproduct cochain lift have the prescribed coboundaries and difference. -/
lemma moduleCat_exists_components_of_biprod_lift {R : Type*} [Ring R]
    {A B C D : CochainComplex (ModuleCat R) ℕ}
    (r : A ⟶ C) (b : A ⟶ D) (t : C ⟶ B) (l : D ⟶ B)
    (p : ℕ) (x : (C ⊞ D).X p) (z : A.X (p + 1)) (a : B.X p)
    (hx : ((C ⊞ D).d p (p + 1)).hom x = ((biprod.lift r b).f (p + 1)).hom z)
    (ha : ((biprod.desc t (-l)).f p).hom x = a) :
    ∃ (u : C.X p) (v : D.X p),
      (C.d p (p + 1)).hom u = (r.f (p + 1)).hom z ∧
      (D.d p (p + 1)).hom v = (b.f (p + 1)).hom z ∧
      (t.f p).hom u - (l.f p).hom v = a := by
  refine ⟨((biprod.fst : C ⊞ D ⟶ C).f p).hom x,
    ((biprod.snd : C ⊞ D ⟶ D).f p).hom x, ?_, ?_, ?_⟩
  · have h := congrArg (((biprod.fst : C ⊞ D ⟶ C).f (p + 1)).hom) hx
    simpa only [← ConcreteCategory.comp_apply, ← HomologicalComplex.Hom.comm,
      ← HomologicalComplex.comp_f, biprod.lift_fst] using h
  · have h := congrArg (((biprod.snd : C ⊞ D ⟶ D).f (p + 1)).hom) hx
    simpa only [← ConcreteCategory.comp_apply, ← HomologicalComplex.Hom.comm,
      ← HomologicalComplex.comp_f, biprod.lift_snd] using h
  · simpa only [biprod.desc_eq, Preadditive.comp_neg, ← sub_eq_add_neg,
      HomologicalComplex.sub_f_apply, ModuleCat.hom_sub, LinearMap.sub_apply,
      HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using ha

end HomologicalComplex

end
