/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.PairRealImage
public import SymplecticGeometry.Topology.VectorBundle.Orientation.ThomClass
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Cohomology.Local.Orientation

/-!
# The real Thom class of an oriented bundle

For an orientation `o` of a real vector bundle `E` of rank `r` over a base in `Type`, the
*real canonical Thom class* `TauCeti.VectorBundleOrientation.realCanonicalThomClass o hr` is the
real image (`TopPair.singularCohomologyRealImage`) of the canonical Thom class
`o.canonicalThomClass hr`: a class of `Hʳ(E, E₀; ℝ)`, with real chains and real values. It is a
Thom class with coefficients `ℝ`
(`TauCeti.VectorBundleOrientation.isThomClass_realCanonicalThomClass`),
so that Tau Ceti's Thom isomorphism and `TauCeti.IsThomClass.exists_eq_smul` apply to it with
`K = ℝ`.

The key fact is about the model pair `(P, P ∖ {0})` of a real normed space `P` of dimension `r`:
the real image of the integral generator `Orientation.modelThomGenerator ω hP` generates
`Hʳ(P, P ∖ {0}; ℝ)` (`Orientation.span_singularCohomologyRealImage_modelThomGenerator`), in
every rank, `r = 0` included. The integral generator pairs to `1` with a local orientation, a
class of `Hᵣ(P, P ∖ {0}; ℤ)`; the change of values along `ℤ → ℝ` commutes with the Kronecker
pairing (`TopPair.singularKronecker_singularCohomologyValueMap`), so its real image pairs to `1`
as well and is not zero. Since Tau Ceti's `TauCeti.singularCohomologyComplSingletonFinrankEquivSelf`
identifies `Hʳ(P, P ∖ {0}; ℝ)` with `ℝ`, a nonzero class generates it. The bundle statement then
follows on each fibre from the naturality of the real image
(`TopPair.singularCohomologyRealImage_naturality`) and the fibre restrictions of the canonical
class (`TauCeti.VectorBundleOrientation.singularCohomologyMap_fiberThomPairMap_canonicalThomClass`),
as in the proof of `TauCeti.VectorBundleOrientation.isThomClass_canonicalThomClass`.

## Main definitions

* `TauCeti.VectorBundleOrientation.realCanonicalThomClass`: the real image of the canonical Thom
  class.

## Main results

* `Orientation.span_singularCohomologyRealImage_modelThomGenerator`: the real image of the
  generator of the model pair selected by an orientation generates its real local cohomology.
* `TauCeti.VectorBundleOrientation.singularCohomologyMap_fiberThomPairMap_realCanonicalThomClass`:
  its restriction to each fibre pair is the real image of the generator selected there.
* `TauCeti.VectorBundleOrientation.isThomClass_realCanonicalThomClass`: the real canonical Thom
  class is a Thom class with coefficients `ℝ`.
* `TauCeti.VectorBundleOrientation.realCanonicalThomClass_neg`: reversing the orientation negates
  it.
* `VectorBundleOrientation.singularCohomologyMap_thomPairMapOfFiberwise_realCanonicalThomClass`:
  an orientation-preserving fibrewise isomorphism pulls it back to the real canonical Thom class.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 and §10 (the Thom class with coefficients in a ring).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (change of
  coefficients).
-/

public section

noncomputable section

open Bundle CategoryTheory Module TauCeti

namespace Orientation

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The generator of the model pair selected by an orientation pairs to `1` with a class of the
integral local homology `Hᵣ(P, P ∖ {0}; ℤ)`, in every rank `r`. -/
private theorem exists_singularKronecker_modelThomGenerator_eq_one {r : ℕ}
    (ω : Orientation ℝ P (Fin r)) (hP : finrank ℝ P = r) :
    ∃ z, ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularKronecker ℤ r
      (ω.modelThomGenerator hP)).hom z = 1 := by
  cases r with
  | zero => exact ⟨_, kronecker_modelThomGenerator_zero ω hP⟩
  | succ n => exact ⟨_, (modelThomGenerator_eq_localCohomologyClass ω hP).symm ▸
    kronecker_localCohomologyClass ω hP⟩

/-- **The real image of the model generator generates.** For an orientation `ω` of a real normed
space `P` of dimension `r`, the real image of the integral generator `ω.modelThomGenerator hP`
generates the real local cohomology `Hʳ(P, P ∖ {0}; ℝ)`, in every rank, `r = 0` included. -/
theorem span_singularCohomologyRealImage_modelThomGenerator {r : ℕ}
    (ω : Orientation ℝ P (Fin r))
    (hP : finrank ℝ P = r) :
    Submodule.span ℝ
      {((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularCohomologyRealImage
      r (ω.modelThomGenerator hP) : (TopPair.ofSubset (X := TopCat.of P)
        ({0}ᶜ : Set P)).singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) r)} = ⊤ := by
  obtain ⟨z, hz⟩ := exists_singularKronecker_modelThomGenerator_eq_one ω hP
  -- Computed from integral chains, the real image is the class with real values that pairs to
  -- `1` with `z`, so it is not zero.
  have hne : ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularCohomologyRealImage r
      (ω.modelThomGenerator hP) : (TopPair.ofSubset (X := TopCat.of P)
        ({0}ᶜ : Set P)).singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) r) ≠ 0 := by
    have hx := ConcreteCategory.congr_hom
      (TopPair.singularCohomologyRealImage_comp_singularCohomologyIntChainsIso_hom
        (TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)) r) (ω.modelThomGenerator hP)
    rw [ConcreteCategory.comp_apply] at hx
    have hk := congrArg (fun x : (TopPair.ofSubset (X := TopCat.of P)
        ({0}ᶜ : Set P)).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ ℝ) r ↦
      ((TopPair.ofSubset (X := TopCat.of P) ({0}ᶜ : Set P)).singularKronecker ℤ r x).hom z) hx
    simp only [TopPair.singularKronecker_singularCohomologyValueMap, ModuleCat.hom_comp,
      LinearMap.comp_apply, hz] at hk
    intro h
    rw [h, map_zero, map_zero] at hk
    exact zero_ne_one (hk.trans ((intToRealCoeff_apply 1).trans (by simp)))
  -- `Hʳ(P, P ∖ {0}; ℝ)` is a copy of `ℝ`, where a nonzero vector generates.
  subst hP
  let e := singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of ℝ ℝ)
    (OpenPartialHomeomorph.refl P) (Set.mem_univ 0)
  exact e.span_singleton_eq_top_iff_isUnit.2
    (isUnit_iff_ne_zero.2 ((map_ne_zero_iff e e.injective).2 hne))

end Orientation

namespace TauCeti.VectorBundleOrientation

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {r : ℕ} (o : VectorBundleOrientation F E (Fin r)) (hr : finrank ℝ F = r)

/-- **The real canonical Thom class of an oriented vector bundle.** For an orientation `o` of a
real vector bundle `E` of rank `r` over a base in `Type`, this is the class of `Hʳ(E, E₀; ℝ)`,
with real chains and real values, that is the real image of the canonical Thom class
`o.canonicalThomClass hr`. -/
def realCanonicalThomClass :
    (thomPair F E).singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) r :=
  (thomPair F E).singularCohomologyRealImage r (o.canonicalThomClass hr)

/-- The real canonical Thom class is the real image of the canonical Thom class. -/
theorem realCanonicalThomClass_def :
    o.realCanonicalThomClass hr =
      (thomPair F E).singularCohomologyRealImage r (o.canonicalThomClass hr) :=
  (rfl)

/-- The real canonical Thom class restricts on the fibre pair over every point `b` to the real
image of the generator selected by the orientation of `E_b`, read in any linear trivialization `e`
at `b`. -/
theorem singularCohomologyMap_fiberThomPairMap_realCanonicalThomClass
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    TopPair.singularCohomologyMap (fiberThomPairMap F E b) r (o.realCanonicalThomClass hr) =
      TopPair.singularCohomologyMap (R := ModuleCat.of ℝ ℝ) (k := ℝ) (M := ModuleCat.of ℝ ℝ)
        (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom r
        (((TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomologyRealImage r
          ((e.mapOrientation (Fin r) hb (o b)).modelThomGenerator hr)) :
            (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
              (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) r) := by
  rw [realCanonicalThomClass_def,
    ← TopPair.singularCohomologyRealImage_naturality_apply,
    o.singularCohomologyMap_fiberThomPairMap_canonicalThomClass hr e hb,
    TopPair.singularCohomologyRealImage_naturality_apply]

/-- **The real canonical Thom class is a Thom class** with coefficients `ℝ`: transported to the
degree `finrank ℝ F = r`, it restricts to a generator of the real cohomology of every fibre
pair. -/
theorem isThomClass_realCanonicalThomClass :
    IsThomClass F E (hr ▸ o.realCanonicalThomClass hr :
      (thomPair F E).singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) (finrank ℝ F)) := by
  -- Transport along `finrank ℝ F = d` commutes with the fibre restrictions.
  have key {d : ℕ} (hd : finrank ℝ F = d)
      (x : (thomPair F E).singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) d)
      (hx : ∀ b, Submodule.span ℝ
        {(TopPair.singularCohomologyMap (fiberThomPairMap F E b) d x)} = ⊤) :
      IsThomClass F E (hd ▸ x : (thomPair F E).singularCohomology
        (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) (finrank ℝ F)) := by
    subst hd
    exact isThomClass_iff.2 ⟨inferInstance, hx⟩
  refine key hr _ fun b ↦ ?_
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
  rw [o.singularCohomologyMap_fiberThomPairMap_realCanonicalThomClass hr _ hb]
  -- An isomorphism of pairs induces a linear isomorphism in cohomology, carrying generators to
  -- generators.
  exact ((TopPair.singularCohomologyFunctor (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) r).mapIso
      ((trivializationAt F E b).continuousLinearEquivAt ℝ b hb).complZeroPairIso.op
    ).toLinearEquiv.span_singleton_apply_eq_top_iff.2
      (Orientation.span_singularCohomologyRealImage_modelThomGenerator (P := F) _ hr)

/-- Reversing the orientation negates the real canonical Thom class. -/
@[simp]
theorem realCanonicalThomClass_neg :
    (-o).realCanonicalThomClass hr = -o.realCanonicalThomClass hr := by
  rw [realCanonicalThomClass_def, realCanonicalThomClass_def, canonicalThomClass_neg, map_neg]
  -- The negation of the real image is taken in its restriction of scalars to `ℤ`, whose additive
  -- group is that of real cohomology.
  rfl

section BaseMap

variable {B' : Type} [TopologicalSpace B'] {F' : Type} [NormedAddCommGroup F']
  [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] {E' : B' → Type}
  [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
  [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  (o' : VectorBundleOrientation F' E' (Fin r)) (hr' : finrank ℝ F' = r) {g : C(B', B)}
  {φ : ∀ b', E' b' ≃L[ℝ] E (g b')}
  (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.snd))

/-- **Naturality of the real canonical Thom class under orientation-preserving bundle maps.** For
a fibrewise isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over `g` carrying the orientation `o' b'` to
`o (g b')` for every `b'`, the map of Thom pairs of `φ` pulls the real canonical Thom class of
`(E, o)` back to the real canonical Thom class of `(E', o')`. -/
theorem singularCohomologyMap_thomPairMapOfFiberwise_realCanonicalThomClass
    (ho : ∀ b', Orientation.map (Fin r) (φ b').toLinearEquiv (o' b') = o (g b')) :
    TopPair.singularCohomologyMap (thomPairMapOfFiberwise hφ) r (o.realCanonicalThomClass hr) =
      o'.realCanonicalThomClass hr' := by
  rw [realCanonicalThomClass_def, realCanonicalThomClass_def,
    ← o.singularCohomologyMap_thomPairMapOfFiberwise_canonicalThomClass hr o' hr' hφ ho,
    TopPair.singularCohomologyRealImage_naturality_apply]

end BaseMap

end TauCeti.VectorBundleOrientation

end
