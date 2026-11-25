/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Basic
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

The construction and the proofs of its properties follow those of Tau Ceti's
`TauCeti.VectorBundleOrientation.thomClass`, `singularCohomologyMap_fiberThomPairMap_thomClass`,
`eq_thomClass_iff`, `thomClass_neg` and `isThomClass_thomClass`
(`TauCeti/Topology/VectorBundle/Orientation/ThomClass.lean`), with `modelThomGenerator` in place of
`localCohomologyClass`; the independence of the trivialization,
`Orientation.singularCohomologyMap_modelThomGenerator_map_eq`, reduces to Tau Ceti's
`Orientation.singularCohomologyMap_localCohomologyClass_map_eq` in positive rank.

## Main definitions

* `Orientation.modelThomGenerator`: the generator of the model pair selected by an orientation.
* `TauCeti.VectorBundleOrientation.canonicalThomClass`: the canonical Thom class of an oriented
  bundle in any rank.

## Main results

* `Orientation.modelThomGenerator_neg` and `Orientation.span_modelThomGenerator`: reversing the
  orientation negates the generator, and it generates.
* `Orientation.modelThomGenerator_eq_localCohomologyClass`: in positive rank it is Tau Ceti's
  generator, and `Orientation.kronecker_modelThomGenerator_zero` gives its pairing with the point
  class in rank zero.
* `TauCeti.VectorBundleOrientation.singularCohomologyMap_fiberThomPairMap_canonicalThomClass`: the
  restriction of the canonical class to the fibre pair over `b`, read in any linear trivialization
  at `b`, and `TauCeti.VectorBundleOrientation.eq_canonicalThomClass_iff`, the characterization by
  these restrictions.
* `TauCeti.VectorBundleOrientation.isThomClass_canonicalThomClass`: it is a Thom class.
* `TauCeti.VectorBundleOrientation.canonicalThomClass_neg`: reversing the orientation negates it.
* `TauCeti.VectorBundleOrientation.canonicalThomClass_eq_thomClass`: in rank `n + 1` it is Tau
  Ceti's `thomClass`.

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

private theorem kronecker_dualClass {d : ℕ} (hd : finrank ℝ P = d) (z : LocalOrientation P 0 d) :
    ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularKronecker ℤ d
      (dualClass hd z)).hom z.val = 1 := by
  subst hd
  exact LocalOrientation.kronecker_cohomologyClass _ _ _

open Classical in
/-- **The generator of the model pair selected by an orientation.** An orientation `ω` of a real
normed space `P` of dimension `r` selects a generator of the integral local cohomology
`Hʳ(P, P ∖ {0}; ℤ)`. For `r = n + 1` it is Tau Ceti's `ω.localCohomologyClass hP`, the class whose
pairing with the local orientation selected by `ω` is one. For `r = 0`, `P` is a point and
`P ∖ {0}` is empty: it is the class dual to the class of the point, that is the unit class, when
`ω` is the positive orientation of the empty index type, and its negative otherwise. -/
def modelThomGenerator : ∀ {r : ℕ}, Orientation ℝ P (Fin r) → finrank ℝ P = r →
    (TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) r
  | 0, ω, hP => dualClass hP <|
      if ω = positiveOrientation then
        localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
          (OpenPartialHomeomorph.mem_refl_source _) hP
      else -localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
          (OpenPartialHomeomorph.mem_refl_source _) hP
  | _ + 1, ω, hP => ω.localCohomologyClass hP

/-- In positive rank `n + 1`, the generator of the model pair selected by `ω` is Tau Ceti's
`Orientation.localCohomologyClass`. -/
@[simp]
theorem modelThomGenerator_eq_localCohomologyClass {n : ℕ} (ω : Orientation ℝ P (Fin (n + 1)))
    (hP : finrank ℝ P = n + 1) : ω.modelThomGenerator hP = ω.localCohomologyClass hP :=
  (rfl)

open Classical in
/-- In rank zero, the generator of the model pair selected by `ω` pairs to `1` with the point
class of `P`, the local orientation of the zero-dimensional chart `P → P`, when `ω` is the
positive orientation of the empty index type, and to `-1` otherwise. -/
theorem kronecker_modelThomGenerator_zero (ω : Orientation ℝ P (Fin 0)) (hP : finrank ℝ P = 0) :
    ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularKronecker ℤ 0
      (ω.modelThomGenerator hP)).hom
        (localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
          (OpenPartialHomeomorph.mem_refl_source _) hP).val =
      if ω = positiveOrientation then 1 else -1 := by
  simp only [modelThomGenerator]
  split_ifs
  · exact kronecker_dualClass hP _
  · have h := kronecker_dualClass hP (-localOrientationOfZeroDimChart
      (OpenPartialHomeomorph.refl P) (OpenPartialHomeomorph.mem_refl_source _) hP)
    rw [LocalOrientation.coe_neg, map_neg] at h
    exact neg_eq_iff_eq_neg.1 h

/-- Reversing an orientation negates the generator of the model pair it selects. -/
@[simp]
theorem modelThomGenerator_neg {r : ℕ} (ω : Orientation ℝ P (Fin r)) (hP : finrank ℝ P = r) :
    (-ω).modelThomGenerator hP = -ω.modelThomGenerator hP := by
  cases r with
  | zero =>
    classical
    rcases eq_or_eq_neg_of_isEmpty ω with rfl | rfl
    · simp [modelThomGenerator, dualClass_neg, (Module.Ray.ne_neg_self _).symm]
    · rw [neg_neg (G := Orientation ℝ P (Fin 0))]
      simp [modelThomGenerator, dualClass_neg, (Module.Ray.ne_neg_self _).symm]
  | succ n => exact localCohomologyClass_neg ω hP

/-- The generator selected by an orientation generates the integral local cohomology of the model
pair. -/
theorem span_modelThomGenerator {r : ℕ} (ω : Orientation ℝ P (Fin r)) (hP : finrank ℝ P = r) :
    Submodule.span ℤ {ω.modelThomGenerator hP} = ⊤ := by
  cases r with
  | zero =>
    classical
    simp only [modelThomGenerator]
    split_ifs <;> exact span_dualClass _ _
  | succ n => exact span_localCohomologyClass ω hP

/-- **The selected generator read through a linear equivalence.** For an orientation `ω` of a
real topological vector space `V`, not necessarily normed, pulling back the generator of the model
pair selected by the transported orientation `ω.map f` along a continuous linear equivalence
`f : V ≃L[ℝ] P` gives a class of `Hʳ(V, V ∖ {0}; ℤ)` that does not depend on `f`. -/
theorem singularCohomologyMap_modelThomGenerator_map_eq {V : Type w} [TopologicalSpace V]
    [AddCommMonoid V] [Module ℝ V] {r : ℕ} (ω : Orientation ℝ V (Fin r)) (f f' : V ≃L[ℝ] P)
    (hP : finrank ℝ P = r) :
    TopPair.singularCohomologyMap f.complZeroPairIso.hom r
        ((ω.map _ f.toLinearEquiv).modelThomGenerator hP) =
      TopPair.singularCohomologyMap f'.complZeroPairIso.hom r
        ((ω.map _ f'.toLinearEquiv).modelThomGenerator hP) := by
  cases r with
  | zero =>
    -- `P` is a point, so there is only one map `V → P`.
    have : Subsingleton P := finrank_zero_iff.1 hP
    obtain rfl : f = f' := ContinuousLinearEquiv.ext (funext fun _ ↦ Subsingleton.elim _ _)
    rfl
  | succ n => exact singularCohomologyMap_localCohomologyClass_map_eq ω f f' hP hP

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
  exact Orientation.singularCohomologyMap_modelThomGenerator_map_eq (o b) _ _ hr

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
    exact Orientation.singularCohomologyMap_modelThomGenerator_map_eq (o b) _ _ hr

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

end TauCeti.VectorBundleOrientation

end
