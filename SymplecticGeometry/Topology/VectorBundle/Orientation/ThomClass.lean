/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Orientation.RankZero
public import TauCeti.Topology.VectorBundle.Orientation.Comap
public import TauCeti.Topology.VectorBundle.Thom.FiberwiseEquiv
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Basic
public import SymplecticGeometry.AlgebraicTopology.Cohomology.PairChangeOfCoefficients
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.ZeroDimChart
import SymplecticGeometry.Topology.VectorBundle.Thom.ChangeOfCoefficients
import SymplecticGeometry.Topology.VectorBundle.EulerClass
import SymplecticGeometry.AlgebraicTopology.Cohomology.Local.PointClass
import SymplecticGeometry.LinearAlgebra.Orientation.Basic
import TauCeti.Algebra.Module.Equiv.SpanSingleton

/-!
# The canonical Thom class of an oriented bundle in any rank

An orientation `ω` of a real normed space `P` of finite dimension `r` selects a generator
`Orientation.modelThomGenerator ω hP` of the integral local cohomology `Hʳ(P, P ∖ {0}; ℤ)` of the
model pair, in every rank, `r = 0` included. In positive rank `n + 1` it is Tau Ceti's
`Orientation.localCohomologyClass`. In rank zero `P` is a point and `P ∖ {0}` is empty; the
generator is then the unit class when `ω` is the positive orientation of the empty index type, and
its negative otherwise, so that reversing `ω` negates it in every rank
(`Orientation.modelThomGenerator_neg`).

For an orientation `o` of a real vector bundle `E` over any base, with model fibre `F` of
dimension `r`, the *canonical Thom class* `TauCeti.VectorBundleOrientation.canonicalThomClass o hr`
is the class of `Hʳ(E, E₀; ℤ)` restricting on each fibre to the generator selected by the
orientation of that fibre, read in any linear trivialization. It takes no auxiliary choice: no
orientation of `F` and no class of the model pair. In positive rank it is Tau Ceti's
`TauCeti.VectorBundleOrientation.thomClass`
(`TauCeti.VectorBundleOrientation.canonicalThomClass_eq_thomClass`), and in rank zero it extends
it.

Integral coefficients are `ULift ℤ`, with the `ℤ`-linear structure that `ModuleCat ℤ` has as a
preadditive category, as for `Orientation.localCohomologyClass` and
`TauCeti.VectorBundleOrientation.thomClass`. Tau Ceti's
`TauCeti.VectorBundleOrientation.thomClassOfModel` is stated for an arbitrary commutative ring `K`,
and so with the `ℤ`-linear structure `ModuleCat.instLinear` of a category of modules. The two
structures agree only after unfolding, not at instance transparency, so the lemmas about
`thomClassOfModel` do not rewrite against integral classes built from `localCohomologyClass`. The
canonical class is therefore glued directly from the fibre generators, by Tau Ceti's
`TauCeti.exists_singularCohomology_thomPair_fiber` and
`TauCeti.singularCohomology_thomPair_ext`, which allow any linear structure.

Tau Ceti's Thom isomorphism `TauCeti.thomMap` takes chain coefficients and values `ℤ` with the
structure `ModuleCat.instLinear`. Over a base in `Type`, the canonical class carried there along
`TauCeti.uliftIntIso : ULift ℤ ≅ ℤ` by the linear equivalence
`TopPair.uliftIntegralCohomologyEquiv` is
`TauCeti.VectorBundleOrientation.intCanonicalThomClass`, again a Thom class
(`TauCeti.IsThomClass.uliftIntegralCohomologyEquiv`), in degree `finrank ℝ F`, the degree that
the Thom isomorphism takes. In rank zero it is Tau Ceti's
`TauCeti.VectorBundleOrientation.rankZeroThomClass` with coefficients `ℤ`
(`TauCeti.VectorBundleOrientation.intCanonicalThomClass_eq_rankZeroThomClass`), so that Tau Ceti's
rank-zero Euler class `TauCeti.VectorBundleOrientation.rankZeroEulerClass` applies to it. Both are
determined by their Euler classes, whose values are compared through the fibres with
`Orientation.singularCohomologyZeroEval_uliftIntegralCohomologyEquiv_modelThomGenerator_zero`.

The construction and the proofs of its properties follow those of Tau Ceti's
`TauCeti.VectorBundleOrientation.thomClass`, `singularCohomologyMap_fiberThomPairMap_thomClass`,
`eq_thomClass_iff`, `thomClass_neg` and `isThomClass_thomClass`
(`TauCeti/Topology/VectorBundle/Orientation/ThomClass.lean`), with `modelThomGenerator` in place of
`localCohomologyClass`. The naturality of the generator under a linear isomorphism,
`Orientation.singularCohomologyMap_modelThomGenerator`, is Tau Ceti's
`Orientation.singularCohomologyMap_localCohomologyClass` in positive rank; in rank zero it says
that the isomorphism carries the class of the origin to the class of the origin
(`TauCeti.localOrientationOfZeroDimChart_map`). From it, the
independence of the trivialization, `Orientation.singularCohomologyMap_modelThomGenerator_map_eq`,
is proved as Tau Ceti's `Orientation.singularCohomologyMap_localCohomologyClass_map_eq` is.

The naturality of the canonical class under fibrewise isomorphisms, and its proof, follow Tau
Ceti's `TauCeti.VectorBundleOrientation.singularCohomologyMap_thomPairMapOfFiberwise_thomClass`,
`singularCohomologyMap_thomPairMapOfFiberwise_thomClass_of_map_eq_neg` and
`singularCohomologyMap_thomPairMapOfFiberwise_thomClass_comap`
(`TauCeti/Topology/VectorBundle/Orientation/FiberwiseEquiv.lean`), again with `modelThomGenerator`
in place of `localCohomologyClass`, so that they hold in rank zero too.

## Main definitions

* `Orientation.modelThomGenerator`: the generator of the model pair selected by an orientation.
* `TauCeti.VectorBundleOrientation.canonicalThomClass`: the canonical Thom class of an oriented
  bundle in any rank.
* `TauCeti.VectorBundleOrientation.intCanonicalThomClass`: the same class with chain coefficients
  and values `ℤ`, in the convention of `TauCeti.thomMap`.

## Main results

* `Orientation.modelThomGenerator_neg` and `Orientation.span_modelThomGenerator`: reversing the
  orientation negates the generator, and it generates.
* `Orientation.modelThomGenerator_eq_localCohomologyClass`: in positive rank it is Tau Ceti's
  generator, and `Orientation.kronecker_modelThomGenerator_zero` gives its pairing with the point
  class in rank zero, which `Orientation.eq_modelThomGenerator_zero_iff` shows determines it.
* `Orientation.singularCohomologyπ_uliftIntegralCohomologyEquiv_modelThomGenerator_zero` and
  `Orientation.singularCohomologyZeroEval_uliftIntegralCohomologyEquiv_modelThomGenerator_zero`:
  in rank zero, read with chain coefficients and values `ℤ` in `H⁰(P; ℤ)`, the generator is `±1`,
  with value `±1` at the point, the sign `+` exactly for the positive orientation, as for Tau Ceti's
  `TauCeti.VectorBundleOrientation.rankZeroThomClass`.
* `TauCeti.VectorBundleOrientation.singularCohomologyMap_fiberThomPairMap_canonicalThomClass`: the
  restriction of the canonical class to the fibre pair over `b`, read in any linear trivialization
  at `b`, and `TauCeti.VectorBundleOrientation.eq_canonicalThomClass_iff`, the characterization by
  these restrictions.
* `TauCeti.VectorBundleOrientation.isThomClass_canonicalThomClass`: it is a Thom class.
* `TauCeti.VectorBundleOrientation.canonicalThomClass_neg`: reversing the orientation negates it.
* `TauCeti.VectorBundleOrientation.canonicalThomClass_eq_thomClass`: in rank `n + 1` it is Tau
  Ceti's `thomClass`.
* `TauCeti.VectorBundleOrientation.isThomClass_intCanonicalThomClass` and
  `TauCeti.VectorBundleOrientation.intCanonicalThomClass_neg`: the integral class is a Thom class,
  and reversing the orientation negates it.
* `TauCeti.VectorBundleOrientation.intCanonicalThomClass_eq_rankZeroThomClass`: in rank zero the
  integral class is Tau Ceti's `TauCeti.VectorBundleOrientation.rankZeroThomClass`, and
  `uliftIntegralCohomologyEquiv_canonicalThomClass_eq_rankZeroThomClass` states the same in degree
  `0`.
* `Orientation.singularCohomologyMap_modelThomGenerator`: a linear isomorphism `h` pulls the
  generator selected by `ω.map h` back to the generator selected by `ω`.
* `TauCeti.VectorBundleOrientation.singularCohomologyMap_thomPairMapOfFiberwise_canonicalThomClass`:
  for a fibrewise isomorphism `φ` over `g : B' → B` carrying the orientation `o'` of `E'` to the
  orientation `o` of `E`, the map of Thom pairs of `φ` pulls the canonical Thom class of `o` back
  to that of `o'`, in every rank; `..._of_map_eq_neg` gives the sign when `φ` reverses the
  orientations, and `..._comap` the form with the transported orientation
  `TauCeti.VectorBundleOrientation.comap`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom class of an oriented bundle).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

noncomputable section

open Bundle CategoryTheory Module TauCeti

universe w

namespace Orientation

variable {P : Type w} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The integral class of `Hᵈ(P, P ∖ {0}; ℤ)` dual to a local orientation of `P` at the origin, in
a degree `d` equal to `finrank ℝ P`. -/
private def dualClass {d : ℕ} (hd : finrank ℝ P = d) (z : LocalOrientation P 0 d) :
    (TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) d := by
  subst hd
  exact z.cohomologyClass (OpenPartialHomeomorph.refl P) (OpenPartialHomeomorph.mem_refl_source _)

private theorem dualClass_neg {d : ℕ} (hd : finrank ℝ P = d) (z : LocalOrientation P 0 d) :
    dualClass hd (-z) = -dualClass hd z := by
  subst hd
  exact LocalOrientation.cohomologyClass_neg _ _ _

private theorem span_dualClass {d : ℕ} (hd : finrank ℝ P = d) (z : LocalOrientation P 0 d) :
    Submodule.span ℤ {dualClass hd z} = ⊤ := by
  subst hd
  exact LocalOrientation.span_cohomologyClass _ _ _

private theorem eq_dualClass_iff {d : ℕ} (hd : finrank ℝ P = d) (z : LocalOrientation P 0 d)
    (α : (TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) d) :
    α = dualClass hd z ↔
      ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularKronecker ℤ d α).hom
        z.val = 1 := by
  subst hd
  exact LocalOrientation.eq_cohomologyClass_iff _ _ _ α

/-- **The generator of the model pair selected by an orientation.** An orientation `ω` of a real
normed space `P` of dimension `r` selects a generator of the integral local cohomology
`Hʳ(P, P ∖ {0}; ℤ)`. For `r = n + 1` it is Tau Ceti's `ω.localCohomologyClass hP`, the class whose
pairing with the local orientation selected by `ω` is one. For `r = 0`, `P` is a point and
`P ∖ {0}` is empty: it is the class whose pairing with the local orientation
`ω.localOrientationOfZeroDim hP` is one, that is the unit class when `ω` is the positive
orientation of the empty index type, and its negative otherwise. -/
def modelThomGenerator : ∀ {r : ℕ}, Orientation ℝ P (Fin r) → finrank ℝ P = r →
    (TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) r
  | 0, ω, hP => dualClass hP (ω.localOrientationOfZeroDim hP)
  | _ + 1, ω, hP => ω.localCohomologyClass hP

/-- In positive rank `n + 1`, the generator of the model pair selected by `ω` is Tau Ceti's
`Orientation.localCohomologyClass`. -/
@[simp]
theorem modelThomGenerator_eq_localCohomologyClass {n : ℕ} (ω : Orientation ℝ P (Fin (n + 1)))
    (hP : finrank ℝ P = n + 1) : ω.modelThomGenerator hP = ω.localCohomologyClass hP :=
  (rfl)

/-- **The rank-zero generator by its Kronecker pairing.** In rank zero, a class `α` of
`H⁰(P, P ∖ {0}; ℤ)` is the generator of the model pair selected by `ω` if and only if it pairs to
`1` with the local orientation `ω.localOrientationOfZeroDim hP` selected by `ω`. -/
theorem eq_modelThomGenerator_zero_iff (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0)
    (α : (TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) 0) :
    α = ω.modelThomGenerator hP ↔
      ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularKronecker ℤ 0 α).hom
          (ω.localOrientationOfZeroDim hP).val = 1 :=
  eq_dualClass_iff hP _ α

/-- In rank zero, the generator of the model pair selected by `ω` pairs to `1` with the local
orientation `ω.localOrientationOfZeroDim hP` selected by `ω`. -/
theorem kronecker_modelThomGenerator_zero (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0) :
    ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularKronecker ℤ 0
      (ω.modelThomGenerator hP)).hom (ω.localOrientationOfZeroDim hP).val = 1 :=
  (eq_modelThomGenerator_zero_iff ω hP _).1 rfl

/-- Reversing an orientation negates the generator of the model pair it selects. -/
@[simp]
theorem modelThomGenerator_neg {r : ℕ} (ω : Orientation ℝ P (Fin r)) (hP : finrank ℝ P = r) :
    (-ω).modelThomGenerator hP = -ω.modelThomGenerator hP := by
  cases r with
  | zero => simp only [modelThomGenerator, localOrientationOfZeroDim_neg, dualClass_neg]
  | succ n => exact localCohomologyClass_neg ω hP

/-- The generator selected by an orientation generates the integral local cohomology of the model
pair. -/
theorem span_modelThomGenerator {r : ℕ} (ω : Orientation ℝ P (Fin r)) (hP : finrank ℝ P = r) :
    Submodule.span ℤ {ω.modelThomGenerator hP} = ⊤ := by
  cases r with
  | zero => exact span_dualClass _ _
  | succ n => exact span_localCohomologyClass ω hP

/-- **Naturality of the selected generators.** A continuous linear equivalence `h : P ≃L[ℝ] P'`
pulls the generator of the model pair of `P'` selected by the transported orientation `ω.map h`
back to the generator of the model pair of `P` selected by `ω`, in every rank `r`. -/
theorem singularCohomologyMap_modelThomGenerator {P' : Type w} [NormedAddCommGroup P']
    [NormedSpace ℝ P'] [FiniteDimensional ℝ P'] {r : ℕ} (h : P ≃L[ℝ] P')
    (ω : Orientation ℝ P (Fin r)) (hP : finrank ℝ P = r) (hP' : finrank ℝ P' = r) :
    TopPair.singularCohomologyMap h.complZeroPairIso.hom r
        ((ω.map _ h.toLinearEquiv).modelThomGenerator hP') =
      ω.modelThomGenerator hP := by
  cases r with
  | zero =>
    -- The map of pairs carries the local orientation selected by `ω` to the one selected by
    -- `ω.map h`.
    have hpt := congrArg Subtype.val (localOrientationOfZeroDim_map h ω hP hP')
    rw [LocalOrientation.coe_map] at hpt
    refine (eq_modelThomGenerator_zero_iff ω hP _).2 ?_
    rw [TopPair.singularKronecker_naturality, ModuleCat.hom_comp, LinearMap.comp_apply, ← hpt,
      kronecker_modelThomGenerator_zero]
  | succ n => exact singularCohomologyMap_localCohomologyClass h ω hP hP'

/-- **The selected generator read through a linear equivalence.** For an orientation `ω` of a
real topological vector space `V`, not necessarily normed, pulling back the generator of the model
pair selected by the transported orientation `ω.map f` along a continuous linear equivalence
`f : V ≃L[ℝ] P` gives a class of `Hʳ(V, V ∖ {0}; ℤ)` that does not depend on `f`, nor on the
target `P`. -/
theorem singularCohomologyMap_modelThomGenerator_map_eq {V : Type w} [TopologicalSpace V]
    [AddCommMonoid V] [Module ℝ V] {P' : Type w} [NormedAddCommGroup P'] [NormedSpace ℝ P']
    [FiniteDimensional ℝ P'] {r : ℕ} (ω : Orientation ℝ V (Fin r)) (f : V ≃L[ℝ] P)
    (f' : V ≃L[ℝ] P') (hP : finrank ℝ P = r) (hP' : finrank ℝ P' = r) :
    TopPair.singularCohomologyMap f.complZeroPairIso.hom r
        ((ω.map _ f.toLinearEquiv).modelThomGenerator hP) =
      TopPair.singularCohomologyMap f'.complZeroPairIso.hom r
        ((ω.map _ f'.toLinearEquiv).modelThomGenerator hP') := by
  -- `f'` is `f` followed by the isomorphism `h = f⁻¹ ≫ f' : P ≃ P'`.
  obtain ⟨h, rfl⟩ : ∃ h : P ≃L[ℝ] P', f' = f.trans h := ⟨f.symm.trans f', by ext; simp⟩
  have hmap : ω.map _ (f.trans h).toLinearEquiv =
      (ω.map _ f.toLinearEquiv).map _ h.toLinearEquiv :=
    Orientation.map_trans f.toLinearEquiv h.toLinearEquiv ω
  rw [hmap, ContinuousLinearEquiv.complZeroPairIso_trans, Iso.trans_hom,
    TopPair.singularCohomologyMap_comp_apply, singularCohomologyMap_modelThomGenerator h _ hP hP']

section RankZeroIntegral

/-! ### The rank-zero generator with coefficients `ℤ` -/

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

open Classical in
/-- In rank zero, the image of the generator of the model pair selected by `ω` in the absolute
cohomology `H⁰(P; ULift ℤ)`, carried to integral cohomology by
`TopCat.uliftIntegralCohomologyIso`, is the unit class `TopCat.integralCohomologyOne` when `ω` is
the positive orientation of the empty index type, and its negative otherwise. -/
theorem uliftIntegralCohomologyIso_singularCohomologyπ_modelThomGenerator_zero
    (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0) :
    ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).fst.uliftIntegralCohomologyIso 0).hom
        ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularCohomologyπ _ ℤ _ 0
          (ω.modelThomGenerator hP)) =
      (if ω = positiveOrientation then 1 else -1 : ℤ) •
        (TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).fst.integralCohomologyOne := by
  have : Subsingleton P := finrank_zero_iff.1 hP
  -- The positive orientation: a degree-zero class is determined by its Kronecker pairing with the
  -- class of the point, and on it the image of the generator pairs as the generator does with the
  -- local point class.
  have hpos : ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).fst.uliftIntegralCohomologyIso
      0).hom ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularCohomologyπ _ ℤ _ 0
        ((positiveOrientation : Orientation ℝ P (Fin 0)).modelThomGenerator hP)) =
      (TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).fst.integralCohomologyOne := by
    have h := (positiveOrientation : Orientation ℝ P (Fin 0)).kronecker_modelThomGenerator_zero hP
    rw [localOrientationOfZeroDim_positiveOrientation hP, localOrientationOfZeroDimChart_coe] at h
    refine ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).fst
      |>.singularKronecker_bijective_zero ℤ).1 (singularHomology₀_hom_ext _ fun x ↦ ?_)
    rw [TopCat.singularKronecker_integralCohomologyOne,
      singularHomology₀Section_singularHomology₀ε_assoc]
    obtain rfl : x = (0 : P) := Subsingleton.elim (α := P) _ _
    rw [TopCat.singularKronecker_uliftIntegralCohomologyIso_hom, ← Category.assoc,
      ← localHomologyPointClass_comp_singularKronecker]
    ext ⟨r⟩
    rw [show (⟨r⟩ : ULift ℤ) = r • (1 : ULift ℤ) by ext; simp, map_zsmul, map_zsmul]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, h, ModuleCat.hom_ofHom,
      LinearEquiv.coe_coe, ULift.moduleEquiv_apply, ULift.one_down]
    rw [uliftIntIso_hom_apply, ULift.one_down]
  rcases eq_or_eq_neg_of_isEmpty ω with rfl | rfl
  · rw [ite_eq_left rfl, one_smul, hpos]
  · rw [modelThomGenerator_neg, map_neg, map_neg, hpos,
      ite_eq_right (Module.Ray.ne_neg_self _).symm, neg_one_zsmul]

open Classical in
/-- **The rank-zero generator with coefficients `ℤ`.** In rank zero, the generator of the model
pair selected by `ω`, carried to chain coefficients and values `ℤ` by
`TopPair.uliftIntegralCohomologyEquiv` and then to the absolute cohomology `H⁰(P; ℤ)`, is the unit
class `TopCat.singularCohomologyZeroOne` when `ω` is the positive orientation of the empty index
type, and its negative otherwise. -/
theorem singularCohomologyπ_uliftIntegralCohomologyEquiv_modelThomGenerator_zero
    (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0) :
    @TopPair.singularCohomologyπ (ModuleCat.{0} ℤ) _ _ _
        (TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)) (ModuleCat.of ℤ ℤ) ℤ _
        ModuleCat.instLinear (ModuleCat.of ℤ ℤ) 0
        ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).uliftIntegralCohomologyEquiv 0
          (ω.modelThomGenerator hP)) =
      (if ω = positiveOrientation then 1 else -1 : ℤ) •
        (TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).fst.singularCohomologyZeroOne := by
  rw [TopPair.singularCohomologyπ_uliftIntegralCohomologyEquiv,
    uliftIntegralCohomologyIso_singularCohomologyπ_modelThomGenerator_zero, map_zsmul,
    ← TopCat.integralCohomologyEquiv_symm_singularCohomologyZeroOne, LinearEquiv.apply_symm_apply]

open Classical in
/-- In rank zero, the generator of the model pair selected by `ω`, read in `H⁰(P; ℤ)` as in
`Orientation.singularCohomologyπ_uliftIntegralCohomologyEquiv_modelThomGenerator_zero`, has the
value `1` at the point of `P` when `ω` is the positive orientation of the empty index type, and
`-1` otherwise. -/
theorem singularCohomologyZeroEval_uliftIntegralCohomologyEquiv_modelThomGenerator_zero
    (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0)
    (x : (TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).fst) :
    singularCohomologyZeroEval x
        (@TopPair.singularCohomologyπ (ModuleCat.{0} ℤ) _ _ _
          (TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)) (ModuleCat.of ℤ ℤ) ℤ _
          ModuleCat.instLinear (ModuleCat.of ℤ ℤ) 0
          ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).uliftIntegralCohomologyEquiv 0
            (ω.modelThomGenerator hP))) =
      if ω = positiveOrientation then 1 else -1 := by
  rw [singularCohomologyπ_uliftIntegralCohomologyEquiv_modelThomGenerator_zero, map_zsmul,
    singularCohomologyZeroEval_singularCohomologyZeroOne, zsmul_eq_mul, Int.cast_id, mul_one]

end RankZeroIntegral

end Orientation

namespace TauCeti.VectorBundleOrientation

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {r : ℕ} (o : VectorBundleOrientation F E (Fin r)) (hr : finrank ℝ F = r)

/-- A class of `Hʳ(E, E₀; ℤ)` restricting on every fibre to the generator selected by the fibre
orientation, read in the trivialization at that point. -/
private theorem exists_canonicalThomClass :
    ∃ x : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) r,
      ∀ b, TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ x =
        TopPair.singularCohomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
          (FiberBundle.mem_baseSet_trivializationAt' b)).complZeroPairIso.hom r
          (((trivializationAt F E b).mapOrientation (Fin r)
            (FiberBundle.mem_baseSet_trivializationAt' b) (o b)).modelThomGenerator hr) := by
  refine (hr ▸ exists_singularCohomology_thomPair_fiber (F := F) (E := E)
    (R := ModuleCat.of ℤ (ULift.{w} ℤ)) (k := ℤ) (M := ModuleCat.of ℤ (ULift.{w} ℤ))) _
    fun c ↦ ?_
  -- Near `c` the fibre orientations read in the trivialization `e` at `c` are a single
  -- orientation `ω` of `F`; pull back the generator it selects along `e`.
  let e := trivializationAt F E c
  have hc : c ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' c
  obtain ⟨t, ht, hto, hct⟩ := eventually_nhds_iff.1 (o.eventually_mapOrientation_eq' c)
  obtain ⟨u, hu⟩ := e.exists_singularCohomology_thomPairOver_fiber ℝ (W := t ∩ e.baseSet)
    Set.inter_subset_right ((e.mapOrientation (Fin r) hc (o c)).modelThomGenerator hr)
  refine ⟨t ∩ e.baseSet, hto.inter e.open_baseSet, ⟨hct, hc⟩,
    ⟨e, inferInstance, Set.inter_subset_right⟩, u, fun b hb ↦ ?_⟩
  have hω : e.mapOrientation (Fin r) hb.2 (o b) = e.mapOrientation (Fin r) hc (o c) :=
    ht b hb.1 hb.2
  rw [hu b hb, ← hω, Trivialization.mapOrientation_apply, Trivialization.mapOrientation_apply]
  exact Orientation.singularCohomologyMap_modelThomGenerator_map_eq (o b) _ _ hr hr

/-- **The canonical Thom class of an oriented vector bundle**, in any rank. For an orientation
`o` of a real vector bundle `E` over an arbitrary base, with model fibre `F` of dimension `r`,
`r = 0` included, this is the class `U ∈ Hʳ(E, E₀; ℤ)` whose restriction to the fibre pair
`(E_b, E_b ∖ {0})` over every point `b` is the generator selected by the orientation `o b`: the
pull-back, along any linear trivialization at `b`, of the generator of the model pair selected by
`o b` read in that trivialization
(`TauCeti.VectorBundleOrientation.singularCohomologyMap_fiberThomPairMap_canonicalThomClass`).
This property determines it (`TauCeti.VectorBundleOrientation.eq_canonicalThomClass_iff`). In
positive rank it is `TauCeti.VectorBundleOrientation.thomClass`. -/
def canonicalThomClass :
    (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) r :=
  (exists_canonicalThomClass o hr).choose

/-- The canonical Thom class restricts on the fibre pair over every point `b` to the generator
selected by the orientation of `E_b`, read in any linear trivialization `e` at `b`: the pull-back
along `e` of the generator of the model pair selected by `e.mapOrientation _ hb (o b)`. -/
theorem singularCohomologyMap_fiberThomPairMap_canonicalThomClass (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ (o.canonicalThomClass hr) =
      TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom r
        ((e.mapOrientation (Fin r) hb (o b)).modelThomGenerator hr) :=
  ((exists_canonicalThomClass o hr).choose_spec b).trans <| by
    rw [Trivialization.mapOrientation_apply, Trivialization.mapOrientation_apply]
    exact Orientation.singularCohomologyMap_modelThomGenerator_map_eq (o b) _ _ hr hr

/-- **Uniqueness of the canonical Thom class.** A class of `Hʳ(E, E₀; ℤ)` is the canonical Thom
class exactly when it restricts on every fibre to the generator selected by the fibre orientation,
read in a linear trivialization at that point. -/
theorem eq_canonicalThomClass_iff
    (u : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) r) :
    u = o.canonicalThomClass hr ↔ ∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B)
      (hb : b ∈ e.baseSet), TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
        TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom r
          ((e.mapOrientation (Fin r) hb (o b)).modelThomGenerator hr) := by
  refine ⟨fun h e _ b hb ↦ h ▸ o.singularCohomologyMap_fiberThomPairMap_canonicalThomClass hr e hb,
    fun h ↦ (hr ▸ fun u v ↦ singularCohomology_thomPair_ext (F := F) (E := E)
      (R := ModuleCat.of ℤ (ULift.{w} ℤ)) (k := ℤ) (M := ModuleCat.of ℤ (ULift.{w} ℤ)) (x := u)
      (y := v)) u _ fun b ↦ ?_⟩
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
  rw [h _ b hb, o.singularCohomologyMap_fiberThomPairMap_canonicalThomClass hr _ hb]

/-- In positive rank `n + 1`, the canonical Thom class is Tau Ceti's integral Thom class
`TauCeti.VectorBundleOrientation.thomClass`. -/
theorem canonicalThomClass_eq_thomClass {n : ℕ} (o : VectorBundleOrientation F E (Fin (n + 1)))
    (hF : finrank ℝ F = n + 1) : o.canonicalThomClass hF = o.thomClass hF :=
  (o.eq_thomClass_iff hF _).2 fun e _ _ hb ↦
    o.singularCohomologyMap_fiberThomPairMap_canonicalThomClass hF e hb

/-- Reversing the orientation negates the canonical Thom class. -/
@[simp]
theorem canonicalThomClass_neg : (-o).canonicalThomClass hr = -o.canonicalThomClass hr := by
  symm
  refine ((-o).eq_canonicalThomClass_iff hr _).2 fun e _ b hb ↦ ?_
  rw [map_neg, o.singularCohomologyMap_fiberThomPairMap_canonicalThomClass hr e hb, neg_apply,
    Trivialization.mapOrientation_neg, Orientation.modelThomGenerator_neg, map_neg]

/-- **The canonical Thom class is a Thom class**: transported to the degree `finrank ℝ F = r`, it
restricts to a generator of the integral cohomology of every fibre pair. -/
theorem isThomClass_canonicalThomClass :
    IsThomClass F E (hr ▸ o.canonicalThomClass hr :
      (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ F)) := by
  -- Transport along `finrank ℝ F = d` commutes with the fibre restrictions.
  have key {d : ℕ} (hd : finrank ℝ F = d)
      (x : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) d)
      (hx : ∀ b, Submodule.span ℤ
        {(TopPair.singularCohomologyMap (fiberThomPairMap F E b) d x)} = ⊤) :
      IsThomClass F E (hd ▸ x : (thomPair F E).singularCohomology
        (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ F)) := by
    subst hd
    exact isThomClass_iff.2 ⟨inferInstance, hx⟩
  refine key hr _ fun b ↦ ?_
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
  rw [o.singularCohomologyMap_fiberThomPairMap_canonicalThomClass hr _ hb]
  -- An isomorphism of pairs induces a linear isomorphism in cohomology, carrying generators to
  -- generators.
  exact ((TopPair.singularCohomologyFunctor (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
    (ModuleCat.of ℤ (ULift.{w} ℤ)) r).mapIso
      ((trivializationAt F E b).continuousLinearEquivAt ℝ b hb).complZeroPairIso.op
    ).toLinearEquiv.span_singleton_apply_eq_top_iff.2 (Orientation.span_modelThomGenerator _ _)

section BaseMap

/-! ### Naturality under fibrewise isomorphisms -/

variable {B' : Type w} [TopologicalSpace B'] {F' : Type w} [NormedAddCommGroup F']
  [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] {E' : B' → Type w}
  [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
  [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  (o' : VectorBundleOrientation F' E' (Fin r)) (hr' : finrank ℝ F' = r) {g : C(B', B)}
  {φ : ∀ b', E' b' ≃L[ℝ] E (g b')}
  (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.snd))

include hφ

/-- **Naturality of the canonical Thom class under orientation-preserving bundle maps.** For a
fibrewise isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over `g` carrying the orientation `o' b'` to
`o (g b')` for every `b'`, the map of Thom pairs of `φ` pulls the canonical Thom class of `(E, o)`
back to the canonical Thom class of `(E', o')`, in every rank `r`. -/
theorem singularCohomologyMap_thomPairMapOfFiberwise_canonicalThomClass
    (ho : ∀ b', Orientation.map (Fin r) (φ b').toLinearEquiv (o' b') = o (g b')) :
    TopPair.singularCohomologyMap (thomPairMapOfFiberwise hφ) r (o.canonicalThomClass hr) =
      o'.canonicalThomClass hr' := by
  refine (o'.eq_canonicalThomClass_iff hr' _).2 fun e' _ b' hb' ↦ ?_
  -- On the fibre over `b'`, the pulled-back class is the generator selected by `o (g b')`, pulled
  -- back along `φ b'` followed by the preferred trivialization at `g b'`.
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) (g b')
  rw [← TopPair.singularCohomologyMap_comp_apply, fiberThomPairMap_comp_thomPairMapOfFiberwise,
    TopPair.singularCohomologyMap_comp_apply,
    o.singularCohomologyMap_fiberThomPairMap_canonicalThomClass hr _ hb,
    ← TopPair.singularCohomologyMap_comp_apply, ← Iso.trans_hom,
    ← ContinuousLinearEquiv.complZeroPairIso_trans, Trivialization.mapOrientation_apply,
    Trivialization.mapOrientation_apply, ← ho, ← Orientation.map_trans]
  -- The generator selected by `o' b'` does not depend on the linear isomorphism with a model
  -- fibre used to read it.
  exact Orientation.singularCohomologyMap_modelThomGenerator_map_eq (o' b') _ _ hr hr'

/-- **Orientation-reversing bundle maps negate the canonical Thom class.** For a fibrewise
isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over `g` carrying the orientation `o' b'` to `-o (g b')`
for every `b'`, the map of Thom pairs of `φ` pulls the canonical Thom class of `(E, o)` back to the
negative of the canonical Thom class of `(E', o')`. -/
theorem singularCohomologyMap_thomPairMapOfFiberwise_canonicalThomClass_of_map_eq_neg
    (ho : ∀ b', Orientation.map (Fin r) (φ b').toLinearEquiv (o' b') = -o (g b')) :
    TopPair.singularCohomologyMap (thomPairMapOfFiberwise hφ) r (o.canonicalThomClass hr) =
      -o'.canonicalThomClass hr' := by
  have h := (-o).singularCohomologyMap_thomPairMapOfFiberwise_canonicalThomClass hr o' hr' hφ ho
  rw [canonicalThomClass_neg, map_neg] at h
  exact neg_eq_iff_eq_neg.1 h

/-- **The canonical Thom class of a transported orientation.** For a fibrewise isomorphism
`φ b' : E'_{b'} ≃ E_{g b'}` over `g`, the map of Thom pairs of `φ` pulls the canonical Thom class
of `(E, o)` back to the canonical Thom class of `E'` with the transported orientation `φ^* o`, in
every rank `r`. -/
theorem singularCohomologyMap_thomPairMapOfFiberwise_canonicalThomClass_comap :
    TopPair.singularCohomologyMap (thomPairMapOfFiberwise hφ) r (o.canonicalThomClass hr) =
      (o.comap ((Fintype.card_fin _).trans hr'.symm) hφ).canonicalThomClass hr' :=
  o.singularCohomologyMap_thomPairMapOfFiberwise_canonicalThomClass hr _ hr' hφ
    (map_comap_apply _ o hφ)

end BaseMap

section Integral

/-! ### The canonical Thom class with coefficients `ℤ` -/

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {r : ℕ} (o : VectorBundleOrientation F E (Fin r)) (hr : finrank ℝ F = r)

/-- **The canonical Thom class with integer coefficients.** For an orientation `o` of a real
vector bundle `E` of rank `r` over a base in `Type`, this is the canonical Thom class
`o.canonicalThomClass hr`, moved to the degree `finrank ℝ F = r` and carried along
`ULift ℤ ≅ ℤ` by `TopPair.uliftIntegralCohomologyEquiv` to chain coefficients and values `ℤ`,
with the structure `ModuleCat.instLinear` of `ModuleCat ℤ` that the Thom map `TauCeti.thomMap`
takes. -/
def intCanonicalThomClass :
    @TopPair.singularCohomology (ModuleCat.{0} ℤ) _ _ _ (thomPair F E) (ModuleCat.of ℤ ℤ) ℤ _
      ModuleCat.instLinear (ModuleCat.of ℤ ℤ) (finrank ℝ F) :=
  (thomPair F E).uliftIntegralCohomologyEquiv _ (hr ▸ o.canonicalThomClass hr)

/-- The canonical Thom class with integer coefficients, unfolded. -/
theorem intCanonicalThomClass_def :
    o.intCanonicalThomClass hr =
      (thomPair F E).uliftIntegralCohomologyEquiv _ (hr ▸ o.canonicalThomClass hr) :=
  (rfl)

/-- **The canonical Thom class with integer coefficients is a Thom class**: it restricts to a
generator of the cohomology with coefficients `ℤ` of every fibre pair. -/
theorem isThomClass_intCanonicalThomClass :
    @IsThomClass _ _ _ _ (ModuleCat.of ℤ ℤ) ℤ _ ModuleCat.instLinear (ModuleCat.of ℤ ℤ) B _ F _ E
      _ _ _ _ _ _ (o.intCanonicalThomClass hr) :=
  (o.isThomClass_canonicalThomClass hr).uliftIntegralCohomologyEquiv

/-- Reversing the orientation negates the canonical Thom class with integer coefficients. -/
@[simp]
theorem intCanonicalThomClass_neg :
    (-o).intCanonicalThomClass hr = -o.intCanonicalThomClass hr := by
  subst hr
  simp only [intCanonicalThomClass_def, canonicalThomClass_neg, map_neg]

/-- **The canonical Thom class in rank zero is Tau Ceti's.** For a bundle with zero model fibre,
oriented by `Fin 0`, the canonical Thom class read with chain coefficients and values `ℤ` in
degree `0` is Tau Ceti's `TauCeti.VectorBundleOrientation.rankZeroThomClass` with coefficients
`ℤ`. -/
theorem uliftIntegralCohomologyEquiv_canonicalThomClass_eq_rankZeroThomClass [Subsingleton F]
    (o : VectorBundleOrientation F E (Fin 0)) :
    (thomPair F E).uliftIntegralCohomologyEquiv 0
        (o.canonicalThomClass (finrank_zero_of_subsingleton (R := ℝ) (M := F))) =
      o.rankZeroThomClass ℤ := by
  classical
  -- Both classes are determined by their Euler classes; compare the values at each point `b`,
  -- through the fibre over `b` and a trivialization at `b`.
  refine (o.eq_rankZeroThomClass_iff ℤ _).2 (singularCohomologyZero_ext fun b ↦ ?_)
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
  rw [singularCohomologyZeroEval_rankZeroEulerClass, singularCohomologyZeroEval_eulerClass,
    ← TopPair.uliftIntegralCohomologyEquiv_naturality,
    o.singularCohomologyMap_fiberThomPairMap_canonicalThomClass _ _ hb,
    TopPair.uliftIntegralCohomologyEquiv_naturality]
  -- As in `TauCeti.singularCohomologyZeroEval_eulerClass`
  -- (`SymplecticGeometry/Topology/VectorBundle/EulerClass.lean`), the point is the zero vector of
  -- `E b`, so the map to absolute cohomology is moved past the trivialization by `Eq.trans`.
  have h := ConcreteCategory.congr_hom (@TopPair.singularCohomologyπ_naturality (ModuleCat.{0} ℤ)
    _ _ _ (ModuleCat.of ℤ ℤ) ℤ _ ModuleCat.instLinear (ModuleCat.of ℤ ℤ) _ _
    ((trivializationAt F E b).continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom 0)
    ((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).uliftIntegralCohomologyEquiv 0
      (((trivializationAt F E b).mapOrientation (Fin 0) hb (o b)).modelThomGenerator
        (finrank_zero_of_subsingleton (R := ℝ) (M := F))))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  refine (congrArg (singularCohomologyZeroEval _) h).symm.trans ?_
  refine (singularCohomologyZeroEval_naturality _ _ _).trans ?_
  rw [Orientation.singularCohomologyZeroEval_uliftIntegralCohomologyEquiv_modelThomGenerator_zero,
    Trivialization.mapOrientation_apply]
  -- Reading an orientation of `E b` in the trivialization keeps it positive or negative.
  exact if_congr (Orientation.map_eq_positiveOrientation_iff _ _) rfl rfl

/-- **The canonical Thom class with integer coefficients in rank zero** is Tau Ceti's
`TauCeti.VectorBundleOrientation.rankZeroThomClass` with coefficients `ℤ`, moved to the degree
`finrank ℝ F = 0`. -/
theorem intCanonicalThomClass_eq_rankZeroThomClass [Subsingleton F]
    (o : VectorBundleOrientation F E (Fin 0)) :
    o.intCanonicalThomClass (finrank_zero_of_subsingleton (R := ℝ) (M := F)) =
      (finrank_zero_of_subsingleton (R := ℝ) (M := F)).symm ▸ o.rankZeroThomClass ℤ := by
  rw [intCanonicalThomClass_def,
    ← uliftIntegralCohomologyEquiv_canonicalThomClass_eq_rankZeroThomClass]
  -- Transport along `0 = finrank ℝ F` commutes with `TopPair.uliftIntegralCohomologyEquiv`.
  have key {d : ℕ} (hd : 0 = d) (x : (thomPair F E).singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{0} ℤ)) 0) :
      (thomPair F E).uliftIntegralCohomologyEquiv d (hd ▸ x) =
        hd ▸ (thomPair F E).uliftIntegralCohomologyEquiv 0 x := by
    subst hd
    rfl
  -- `rankZeroThomClass` takes the coefficients `𝟙_ (ModuleCat ℤ)`, which Mathlib defines to be
  -- `ModuleCat.of ℤ ℤ`, the coefficients of `intCanonicalThomClass`.
  exact key _ _

end Integral

end TauCeti.VectorBundleOrientation

end
