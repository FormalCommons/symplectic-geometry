/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.ComplexStructure.Hom
public import TauCeti.Geometry.Symplectic.Orientation
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.LinearAlgebra.Complex.Orientation
public import TauCeti.LinearAlgebra.Exact
public import TauCeti.LinearAlgebra.Orientation.ShortExact

/-!
# The orientation induced by an almost complex structure

Let `V` be a finite-dimensional real vector space. Each almost complex structure `J` on `V`
makes it a complex vector space (Tau Ceti's `TauCeti.AlmostComplexStructure.complexModule`),
which carries Tau Ceti's canonical real orientation `TauCeti.complexOrientation`: the orientation of
`(v₁, J v₁, …, vₙ, J vₙ)` for any complex basis `(v₁, …, vₙ)`. This file shows that it is Tau
Ceti's complex orientation `TauCeti.AlmostComplexStructure.orientation` of `J`, and how that
orientation meets direct sums and short exact sequences of complex-linear maps.

## Main results

* `TauCeti.AlmostComplexStructure.orientation_eq_complexOrientation`: the complex orientation of
  `J` is the canonical orientation of the complex vector space `(V, J)`.
* `TauCeti.AlmostComplexStructure.orientation_prod`: the orientation of the direct sum `J₁ × J₂`
  is the product of the orientations of `J₁` and `J₂`.
* `TauCeti.AlmostComplexStructure.orientation_eq_of_apply_one_eq`: in real dimension two, a
  basis `(e, J e)` induces the orientation of `J`.
* `TauCeti.AlmostComplexStructure.shortExact_orientation`: for a short exact sequence of
  complex-linear maps, Tau Ceti's `Orientation.shortExact` induces the orientation of the middle
  structure from those of the outer ones.

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

/-- Tau Ceti's complex orientation `TauCeti.AlmostComplexStructure.orientation` of `J`, indexed by
`Fin (finrank ℝ V)`, is the canonical real orientation `TauCeti.complexOrientation` of `V` as a
complex vector space with `i` acting as `J`. -/
theorem orientation_eq_complexOrientation (J : AlmostComplexStructure V) :
    letI := J.complexModule
    haveI := J.complexModule_isScalarTower
    haveI := J.finiteDimensional_complexModule
    J.orientation rfl = Orientation.reindex ℝ V
      (finCongr finrank_real_eq_two_mul_finrank_complex.symm) (complexOrientation V) := by
  let := J.complexModule
  have := J.complexModule_isScalarTower
  have := J.finiteDimensional_complexModule
  have h := orientation_ofComplexModule V (k := finrank ℝ V) rfl
  rwa [ofComplexModule_complexModule] at h

/-- Tau Ceti's complex orientation for a given dimension `k` is that for `finrank ℝ V`,
reindexed. -/
theorem orientation_eq_reindex (J : AlmostComplexStructure V) {k : ℕ} (hk : finrank ℝ V = k) :
    J.orientation hk = Orientation.reindex ℝ V (finCongr hk) (J.orientation rfl) := by
  subst hk
  rw [finCongr_refl, Orientation.reindex_refl, Equiv.refl_apply]

/-- If the complex structure induced by `J` is a given complex module structure on `V`, the
orientation of `J` is the canonical orientation of that complex vector space. -/
theorem orientation_eq_of_complexModule_eq (J : AlmostComplexStructure V) [m : Module ℂ V]
    [IsScalarTower ℝ ℂ V] (h : J.complexModule = m) :
    haveI : FiniteDimensional ℂ V := .of_restrictScalars_finite ℝ ℂ V
    J.orientation rfl = Orientation.reindex ℝ V
      (finCongr finrank_real_eq_two_mul_finrank_complex.symm) (complexOrientation V) := by
  subst h
  exact J.orientation_eq_complexOrientation

/-- The orientation of the direct sum `J₁ × J₂` of two almost complex structures is the ordered
product of their orientations, the directions of the first factor before those of the second. -/
theorem orientation_prod (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure V') :
    (J₁.prod J₂).orientation rfl =
      Orientation.reindex ℝ (V × V') (finCongr finrank_prod.symm)
        ((J₁.orientation rfl).prod (J₂.orientation rfl) rfl rfl) := by
  let := J₁.complexModule
  let := J₂.complexModule
  have := J₁.complexModule_isScalarTower
  have := J₂.complexModule_isScalarTower
  have := J₁.finiteDimensional_complexModule
  have := J₂.finiteDimensional_complexModule
  -- `J₁ × J₂` is multiplication by `i` on the product of the complex spaces `(V, J₁)`, `(V', J₂)`.
  have hJ : J₁.prod J₂ = ofComplexModule (V × V') := by
    ext p <;> simp
  rw [hJ, orientation_ofComplexModule, orientation_eq_complexOrientation,
    orientation_eq_complexOrientation,
    Orientation.prod_reindex_finCongr, prod_complexOrientation, ← Orientation.reindex_trans,
    ← Orientation.reindex_trans]
  -- Both sides reindex the same orientation along casts between the same index types.
  rfl

/-- In real dimension two, a basis `(e, J e)` induces the orientation of `J`. -/
theorem orientation_eq_of_apply_one_eq (J : AlmostComplexStructure V) (hV : finrank ℝ V = 2)
    (b : Basis (Fin 2) ℝ V) (hb : b 1 = J (b 0)) :
    b.orientation = Orientation.reindex ℝ V (finCongr hV) (J.orientation rfl) := by
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
  rw [orientation_eq_complexOrientation, ← Orientation.reindex_trans, ← hc,
    Basis.orientation_reindex, c.complexOrientation_eq_reindex h1]
  -- Both sides reindex the same orientation along equal equivalences of index types.
  rfl

/-- Let `0 → U → V → W → 0` be a short exact sequence whose maps are complex linear for almost
complex structures `J₁` on `U`, `J` on `V` and `J₂` on `W`. Then the orientation it induces from
the orientations of `J₁` and `J₂`, with `U` first, is the orientation of `J`. -/
theorem shortExact_orientation {U W : Type*} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W] {J₁ : AlmostComplexStructure U}
    {J : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W} {f : U →ₗ[ℝ] V}
    {g : V →ₗ[ℝ] W} (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (hJf : IsComplexLinearMap J₁ J f)
    (hJg : IsComplexLinearMap J J₂ g) :
    Orientation.shortExact hf hfg hg (J₁.orientation rfl) (J₂.orientation rfl) rfl rfl =
      Orientation.reindex ℝ V (finCongr (hfg.finrank_eq_add hf hg)) (J.orientation rfl) := by
  -- A complex-linear section `s` of `g`.
  obtain ⟨s, hJs, hs⟩ := hJg.exists_rightInverse_of_surjective hg
  rw [Orientation.shortExact_eq_map_prod _ _ _ _ _ _ _ s hs]
  set e := (hfg.splitSurjectiveEquiv hf ⟨s, hs⟩).val.symm
  have he₁ (u : U) (w : W) : e (u, w) = f u + s w := by
    -- Mathlib has no application lemma for `splitSurjectiveEquiv`: unfold it to the
    -- `LinearEquiv.ofBijective` it is built from, and use that constructor's `apply` lemma.
    simp only [e, Function.Exact.splitSurjectiveEquiv, Equiv.coe_fn_mk, LinearEquiv.symm_symm]
    exact (LinearEquiv.ofBijective_apply _ _).trans (by simp)
  have he : IsComplexLinearMap (J₁.prod J₂) J e.toLinearMap := by
    rw [isComplexLinearMap_iff_apply]
    rintro ⟨u, w⟩
    simp [he₁, (isComplexLinearMap_iff_apply _ _ _).1 hJf,
      (isComplexLinearMap_iff_apply _ _ _).1 hJs]
  have hp : (J₁.orientation rfl).prod (J₂.orientation rfl) rfl rfl =
      Orientation.reindex ℝ _ (finCongr finrank_prod) ((J₁.prod J₂).orientation rfl) := by
    rw [orientation_prod, ← Orientation.reindex_trans,
      show (finCongr finrank_prod.symm).trans (finCongr finrank_prod) = Equiv.refl _ from
        Equiv.ext fun _ ↦ rfl, Orientation.reindex_refl, Equiv.refl_apply]
  rw [hp, Orientation.map_reindex, map_orientation he, orientation_eq_reindex,
    ← Orientation.reindex_trans]
  -- Both sides reindex the same orientation along casts between the same index types.
  rfl

end TauCeti.AlmostComplexStructure

end
