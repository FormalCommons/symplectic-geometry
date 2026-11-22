/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex.Quotient
public import TauCeti.Geometry.Symplectic.Complex.Module.Hom
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.LinearAlgebra.Complex.Orientation

/-!
# The orientation induced by an almost complex structure

Let `V` be a finite-dimensional real vector space. Each almost complex structure `J` on `V`
makes it a complex vector space (Tau Ceti's `TauCeti.AlmostComplexStructure.complexModule`),
which carries Tau Ceti's canonical real orientation `TauCeti.complexOrientation`: the orientation of
`(v₁, J v₁, …, vₙ, J vₙ)` for any complex basis `(v₁, …, vₙ)`. This file names it
`TauCeti.AlmostComplexStructure.orientation`, indexed by `Fin (finrank ℝ V)`, and shows how it
meets complex-linear isomorphisms, direct sums, and quotients by invariant subspaces.

## Main definitions

* `TauCeti.AlmostComplexStructure.orientation`: the real orientation induced by `J`.

## Main results

* `TauCeti.AlmostComplexStructure.map_orientation`: a real-linear isomorphism that intertwines
  two almost complex structures carries the orientation of one to that of the other.
* `TauCeti.AlmostComplexStructure.orientation_prod`: the orientation of the direct sum `J₁ × J₂`
  is the product of the orientations of `J₁` and `J₂`.
* `TauCeti.AlmostComplexStructure.orientation_eq_of_apply_one_eq`: in real dimension two, a
  basis `(e, J e)` induces the orientation of `J`.
* `TauCeti.AlmostComplexStructure.map_prodEquivOfIsCompl_orientation`: for a `J`-invariant
  subspace `W` with a `J`-invariant complement `W'`, the isomorphism `W × V ⧸ W ≃ V`,
  `(w, a) ↦ w + r a` with `r a` the representative of `a` in `W'`, carries the product of the
  orientations of the restricted and the quotient structures to the orientation of `J`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the canonical orientation of a complex vector space).
-/

public section

noncomputable section

open Module

namespace TauCeti.AlmostComplexStructure

variable {V V' : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup V'] [Module ℝ V'] [FiniteDimensional ℝ V']

/-- Under the complex structure induced by `J`, a finite-dimensional real space is
finite-dimensional over `ℂ`. -/
theorem finiteDimensional_complexModule (J : AlmostComplexStructure V) :
    letI := J.complexModule
    FiniteDimensional ℂ V :=
  let := J.complexModule
  have := J.complexModule_isScalarTower
  .of_restrictScalars_finite ℝ ℂ V

/-- The **orientation induced by an almost complex structure** `J` on `V`: the canonical real
orientation `TauCeti.complexOrientation` of `V` as a complex vector space with `i` acting as `J`,
the orientation of `(v₁, J v₁, …, vₙ, J vₙ)` for any complex basis `(v₁, …, vₙ)`. -/
def orientation (J : AlmostComplexStructure V) : Orientation ℝ V (Fin (finrank ℝ V)) :=
  let := J.complexModule
  have := J.complexModule_isScalarTower
  have := J.finiteDimensional_complexModule
  Orientation.reindex ℝ V (finCongr finrank_real_eq_two_mul_finrank_complex.symm)
    (complexOrientation V)

theorem orientation_def (J : AlmostComplexStructure V) :
    letI := J.complexModule
    haveI := J.complexModule_isScalarTower
    haveI := J.finiteDimensional_complexModule
    J.orientation = Orientation.reindex ℝ V
      (finCongr finrank_real_eq_two_mul_finrank_complex.symm) (complexOrientation V) :=
  (rfl)

/-- A real-linear isomorphism `e` that intertwines `J` and `J'` carries the orientation of `J` to
that of `J'`. -/
theorem map_orientation {J : AlmostComplexStructure V} {J' : AlmostComplexStructure V'}
    (e : V ≃ₗ[ℝ] V') (he : IsComplexLinearMap J J' e.toLinearMap) :
    Orientation.map _ e J.orientation =
      Orientation.reindex ℝ V' (finCongr e.finrank_eq.symm) J'.orientation := by
  let := J.complexModule
  let := J'.complexModule
  have := J.complexModule_isScalarTower
  have := J'.complexModule_isScalarTower
  have := J.finiteDimensional_complexModule
  have := J'.finiteDimensional_complexModule
  -- `e` as a complex-linear isomorphism, whose restriction of scalars is `e` again.
  let ec : V ≃ₗ[ℂ] V' := { he.toComplexLinearMap, e with }
  have hec : ec.restrictScalars ℝ = e := LinearEquiv.ext fun _ ↦ rfl
  rw [orientation_def, orientation_def, Orientation.map_reindex, ← hec,
    LinearEquiv.map_complexOrientation, ← Orientation.reindex_trans, ← Orientation.reindex_trans]
  -- Both sides reindex the same orientation along casts between the same index types.
  rfl

/-- If the complex structure induced by `J` is a given complex module structure on `V`, the
orientation of `J` is the canonical orientation of that complex vector space. -/
theorem orientation_eq_of_complexModule_eq (J : AlmostComplexStructure V) [m : Module ℂ V]
    [IsScalarTower ℝ ℂ V] (h : J.complexModule = m) :
    haveI : FiniteDimensional ℂ V := .of_restrictScalars_finite ℝ ℂ V
    J.orientation = Orientation.reindex ℝ V
      (finCongr finrank_real_eq_two_mul_finrank_complex.symm) (complexOrientation V) := by
  subst h
  rfl

/-- On a complex vector space, the orientation of multiplication by `i` is the canonical
orientation `TauCeti.complexOrientation`. -/
theorem orientation_ofComplexModule [Module ℂ V] [IsScalarTower ℝ ℂ V] :
    haveI : FiniteDimensional ℂ V := .of_restrictScalars_finite ℝ ℂ V
    (ofComplexModule V).orientation = Orientation.reindex ℝ V
      (finCongr finrank_real_eq_two_mul_finrank_complex.symm) (complexOrientation V) :=
  (ofComplexModule V).orientation_eq_of_complexModule_eq complexModule_ofComplexModule

/-- The orientation of the direct sum `J₁ × J₂` of two almost complex structures is the ordered
product of their orientations, the directions of the first factor before those of the second. -/
theorem orientation_prod (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure V') :
    (J₁.prod J₂).orientation =
      Orientation.reindex ℝ (V × V') (finCongr finrank_prod.symm)
        (J₁.orientation.prod J₂.orientation rfl rfl) := by
  let := J₁.complexModule
  let := J₂.complexModule
  have := J₁.complexModule_isScalarTower
  have := J₂.complexModule_isScalarTower
  have := J₁.finiteDimensional_complexModule
  have := J₂.finiteDimensional_complexModule
  -- `J₁ × J₂` is multiplication by `i` on the product of the complex spaces `(V, J₁)`, `(V', J₂)`.
  have hJ : J₁.prod J₂ = ofComplexModule (V × V') := by
    ext p <;> simp
  rw [hJ, orientation_ofComplexModule, orientation_def, orientation_def,
    Orientation.prod_reindex_finCongr, prod_complexOrientation, ← Orientation.reindex_trans,
    ← Orientation.reindex_trans]
  -- Both sides reindex the same orientation along casts between the same index types.
  rfl

/-- In real dimension two, a basis `(e, J e)` induces the orientation of `J`. -/
theorem orientation_eq_of_apply_one_eq (J : AlmostComplexStructure V) (hV : finrank ℝ V = 2)
    (b : Basis (Fin 2) ℝ V) (hb : b 1 = J (b 0)) :
    b.orientation = Orientation.reindex ℝ V (finCongr hV) J.orientation := by
  let := J.complexModule
  have := J.complexModule_isScalarTower
  have := J.finiteDimensional_complexModule
  have h1 : 1 = finrank ℂ V := by
    have := finrank_real_eq_two_mul_finrank_complex (V := V)
    omega
  -- The complex basis `(e)` of the complex line `(V, J)`, whose real basis is `(e, J e)`.
  let c : Basis (Fin 1) ℂ V := basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_unique_iff.2 (b.ne_zero 0) : LinearIndependent ℂ fun _ : Fin 1 ↦ b 0)
    (by simpa using h1)
  have he (k : Fin 2) : (TauCeti.complexRealIndexEquiv 1).symm k = (0, k) :=
    (Equiv.symm_apply_eq _).2
      (Fin.ext ((TauCeti.complexRealIndexEquiv_apply_val 1 0 k).trans (by simp)).symm)
  have hc : c.complexToReal.reindex (TauCeti.complexRealIndexEquiv 1) = b := by
    refine Basis.eq_of_apply_eq fun k ↦ ?_
    rw [Basis.reindex_apply, he, Basis.complexToReal_apply]
    fin_cases k
    · simp [c]
    · simp [c, hb]
  rw [orientation_def, ← Orientation.reindex_trans, ← hc, Basis.orientation_reindex,
    c.complexOrientation_eq_reindex h1]
  -- Both sides reindex the same orientation along equal equivalences of index types.
  rfl

/-- Let `W` be a `J`-invariant subspace with a `J`-invariant complement `W'`. The isomorphism
`W × V ⧸ W ≃ V`, `(w, a) ↦ w + r a` with `r a` the representative of `a` in `W'`, carries the
ordered product of the orientations of the restriction of `J` to `W` and of the structure `J`
induces on `V ⧸ W` to the orientation of `J`. -/
theorem map_prodEquivOfIsCompl_orientation (J : AlmostComplexStructure V)
    {W W' : Submodule ℝ V} (hW : ∀ v ∈ W, J v ∈ W) (hW' : ∀ v ∈ W', J v ∈ W')
    (h : IsCompl W W') :
    Orientation.map _ (((LinearEquiv.refl ℝ W).prodCongr (W.quotientEquivOfIsCompl W' h)).trans
        (W.prodEquivOfIsCompl W' h))
      ((J.restrict W hW).orientation.prod (J.quotient W hW).orientation rfl rfl) =
      Orientation.reindex ℝ V (finCongr (by rw [← W.finrank_quotient_add_finrank, add_comm]))
        J.orientation := by
  set e := ((LinearEquiv.refl ℝ W).prodCongr (W.quotientEquivOfIsCompl W' h)).trans
    (W.prodEquivOfIsCompl W' h)
  -- The representative in `W'` of the class of `J v` is `J` of the representative of `v`.
  have hr (a : V ⧸ W) : (W.quotientEquivOfIsCompl W' h (J.quotient W hW a) : V) =
      J (W.quotientEquivOfIsCompl W' h a) := by
    conv_lhs => rw [← W.mk_quotientEquivOfIsCompl_apply h a, quotient_mk]
    exact congrArg Subtype.val (W.quotientEquivOfIsCompl_apply_mk_right h
      ⟨_, hW' _ (W.quotientEquivOfIsCompl W' h a).property⟩)
  have he : IsComplexLinearMap ((J.restrict W hW).prod (J.quotient W hW)) J e.toLinearMap := by
    rw [isComplexLinearMap_iff_apply]
    rintro ⟨w, a⟩
    simp [e, hr]
  have hp : (J.restrict W hW).orientation.prod (J.quotient W hW).orientation rfl rfl =
      Orientation.reindex ℝ _ (finCongr finrank_prod)
        ((J.restrict W hW).prod (J.quotient W hW)).orientation := by
    rw [orientation_prod, ← Orientation.reindex_trans,
      show (finCongr finrank_prod.symm).trans (finCongr finrank_prod) = Equiv.refl _ from
        Equiv.ext fun _ ↦ rfl, Orientation.reindex_refl, Equiv.refl_apply]
  rw [hp, Orientation.map_reindex, map_orientation e he, ← Orientation.reindex_trans]
  -- Both sides reindex the same orientation along casts between the same index types.
  rfl

end TauCeti.AlmostComplexStructure

end
