/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Basic
public import SymplecticGeometry.Topology.VectorBundle.Orientation.RealThomClass
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Multiple
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Slice

/-!
# The real relative dual class of a submanifold

Let `f : Z → X` be a smooth embedding of boundaryless manifolds with closed range, `X` Hausdorff
and second countable, and `o` an orientation of its normal bundle `ν`, of rank `r`. The *real
relative dual class* `TauCeti.SmoothEmbedding.realRelDualClass f hn hdim hf o hr` is the class
`relDualClassOf f hn hdim hf u ∈ Hʳ(X, X ∖ f(Z); ℝ)` of the real canonical Thom class
`u = o.realCanonicalThomClass hr` (`Orientation/RealThomClass.lean`), with real chains and real
values.

In the degree of the rank, `relDualClassOf` commutes with the real image of a pair
(`TopPair.singularCohomologyRealImage`):
`TauCeti.SmoothEmbedding.relDualClassOf_singularCohomologyRealImage`. Both sides restrict, by
excision, to the image of the real image of `u` under the pair isomorphism of any normalized tube,
by the naturality of the real image (`TopPair.singularCohomologyRealImage_naturality`), and such
a restriction determines the class (`relDualClassOf_eq_of_isNormalizedTube`, in
`DualClass/Slice.lean`).
As the real canonical Thom class is the real image of the integral one, the real relative dual
class is the real image of `relDualClass f hn hdim hf o hr`, and its image in `Hʳ(X; ℝ)` is the
real image of `dualClass f hn hdim hf o hr`.

When `Z` is connected, the real canonical Thom class is a Thom class with coefficients `ℝ`
(`TauCeti.VectorBundleOrientation.isThomClass_realCanonicalThomClass`). So, by
`TauCeti.SmoothEmbedding.exists_eq_smul_relDualClassOf` (`DualClass/Multiple.lean`), every class
of `Hʳ(X, X ∖ f(Z); ℝ)` is a real multiple of the real relative dual class, and, by the exact
sequence of the pair, every class of `Hʳ(X; ℝ)` that vanishes on `X ∖ f(Z)` is a real multiple
of the real image of the dual class.

## Main definitions

* `TauCeti.SmoothEmbedding.realRelDualClass`: the real relative dual class.

## Main results

* `TauCeti.SmoothEmbedding.relDualClassOf_singularCohomologyRealImage`: `relDualClassOf` commutes
  with the real image in the degree of the rank.
* `TauCeti.SmoothEmbedding.realRelDualClass_eq_singularCohomologyRealImage`: the real relative
  dual class is the real image of the relative dual class.
* `TauCeti.SmoothEmbedding.singularCohomologyπ_realRelDualClass`: its image in `Hʳ(X; ℝ)` is the
  real image of the dual class.
* `TauCeti.SmoothEmbedding.exists_eq_smul_realRelDualClass`: for connected `Z`, every class of
  `Hʳ(X, X ∖ f(Z); ℝ)` is a real multiple of the real relative dual class.
* `exists_eq_smul_singularCohomologyRealImageAddMonoidHom_dualClass_of_restrict_compl`, in the
  namespace `TauCeti.SmoothEmbedding`: for connected `Z`, every class of `Hʳ(X; ℝ)` vanishing
  on `X ∖ f(Z)` is a real multiple of the real image of the dual class.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism with coefficients in a field).
-/

public section

open Bundle CategoryTheory Module Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E H G : Type*} {V P Z X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ V G} [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X]
  [I.Boundaryless] [J.Boundaryless] [T2Space X] [SecondCountableTopology X] {r : ℕ}

/-- **The relative class of a submanifold commutes with the real image.** For a class
`u ∈ Hʳ(ν, ν ∖ 0; ULift ℤ)` of the Thom pair of the normal bundle in the degree `r = finrank ℝ P`
of its rank, the relative class in `Hʳ(X, X ∖ f(Z); ℝ)` of the real image of `u` is the real
image of the relative class of `u`. -/
theorem relDualClassOf_singularCohomologyRealImage (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f))
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCohomology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{0} ℤ)) (finrank ℝ P)) :
    letI := f.normalSpaceFiberBundle hn hdim
    f.relDualClassOf (R := ModuleCat.of ℝ ℝ) (k := ℝ) (M := ModuleCat.of ℝ ℝ) hn hdim hf
        ((thomPair P (fun x ↦ f.isImmersion.NormalSpace x hn)).singularCohomologyRealImage _ u) =
      ((TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomologyRealImage _
        (f.relDualClassOf hn hdim hf u) : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ
          ).singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) (finrank ℝ P)) := by
  let := f.normalSpaceFiberBundle hn hdim
  obtain ⟨W, Φ, hΦ, h⟩ :=
    exists_isNormalizedTube_singularCohomologyMap_excisionMap_relDualClassOf
      (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := ModuleCat.of ℤ (ULift.{0} ℤ)) f hn hdim
      hf
  refine relDualClassOf_eq_of_isNormalizedTube f hn hdim hf hΦ ?_
  rw [← TopPair.singularCohomologyRealImage_naturality_apply]
  exact (congrArg _ (h _ u)).trans (TopPair.singularCohomologyRealImage_naturality_apply _ _ _)

/-- **The real relative dual class of a normally oriented submanifold.** For a smooth embedding
`f : Z → X` with closed range and an orientation `o` of its normal bundle, of rank `r`, the class
`relDualClassOf f hn hdim hf u ∈ Hʳ(X, X ∖ f(Z); ℝ)` of the real canonical Thom class
`u = o.realCanonicalThomClass hr`, with real chains and real values. -/
noncomputable def realRelDualClass (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
    (hr : finrank ℝ P = r) :
    (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology
      (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) r :=
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  f.relDualClassOf hn hdim hf (o.realCanonicalThomClass hr)

/-- The real relative dual class, unfolded. -/
theorem realRelDualClass_def (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
    (hr : finrank ℝ P = r) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    f.realRelDualClass hn hdim hf o hr =
      f.relDualClassOf hn hdim hf (o.realCanonicalThomClass hr) :=
  (rfl)

/-- **The real relative dual class is the real image of the relative dual class**
`relDualClass f hn hdim hf o hr ∈ Hʳ(X, X ∖ f(Z); ULift ℤ)`. -/
theorem realRelDualClass_eq_singularCohomologyRealImage (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
    (hr : finrank ℝ P = r) :
    f.realRelDualClass hn hdim hf o hr =
      (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomologyRealImage r
        (f.relDualClass hn hdim hf o hr) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  subst hr
  rw [realRelDualClass_def, o.realCanonicalThomClass_def,
    relDualClassOf_singularCohomologyRealImage, relDualClass_def]

/-- **The image of the real relative dual class in `Hʳ(X; ℝ)`** is the real image of the dual
class `dualClass f hn hdim hf o hr`, in the additive form
`TopCat.singularCohomologyRealImageAddMonoidHom` whose codomain is `Hʳ(X; ℝ)` itself. -/
theorem singularCohomologyπ_realRelDualClass (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
    (hr : finrank ℝ P = r) :
    (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomologyπ
        (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) r (f.realRelDualClass hn hdim hf o hr) =
      (TopCat.of X).singularCohomologyRealImageAddMonoidHom r (f.dualClass hn hdim hf o hr) := by
  rw [realRelDualClass_eq_singularCohomologyRealImage,
    dualClass_eq_singularCohomologyπ_relDualClass]
  exact (TopPair.singularCohomologyπ_singularCohomologyRealImage_apply _ _ _).symm.trans
    (TopCat.singularCohomologyRealImageAddMonoidHom_apply _ _ _).symm

/-- Reversing the normal orientation negates the real relative dual class. -/
@[simp]
theorem realRelDualClass_neg (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
    (hr : finrank ℝ P = r) :
    f.realRelDualClass hn hdim hf (-o) hr = -f.realRelDualClass hn hdim hf o hr := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  rw [realRelDualClass_def, realRelDualClass_def, o.realCanonicalThomClass_neg,
    relDualClassOf_neg]

section Connected

variable [ConnectedSpace Z]

/-- **The real relative dual class of a connected submanifold generates.** For a smooth embedding
`f : Z → X` with closed range and connected (so nonempty) source, and an orientation `o` of its
normal bundle of rank `r`, every class of `Hʳ(X, X ∖ f(Z); ℝ)` is
`m • realRelDualClass f hn hdim hf o hr` for some real `m`. -/
theorem exists_eq_smul_realRelDualClass (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
    (hr : finrank ℝ P = r)
    (c : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology
      (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) r) :
    ∃ m : ℝ, c = m • f.realRelDualClass hn hdim hf o hr := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  subst hr
  rw [realRelDualClass_def]
  exact exists_eq_smul_relDualClassOf f hn hdim hf (o.isThomClass_realCanonicalThomClass rfl) c

/-- **A real class vanishing off a connected submanifold is a multiple of its dual class.** For a
smooth embedding `f : Z → X` with closed range and connected (so nonempty) source, and an
orientation `o` of its normal bundle of rank `r`, every class `a ∈ Hʳ(X; ℝ)` whose restriction to
`X ∖ f(Z)` is zero is `m •` the real image of `dualClass f hn hdim hf o hr`, for some real `m`.
The real image is taken in its additive form `TopCat.singularCohomologyRealImageAddMonoidHom`. -/
theorem exists_eq_smul_singularCohomologyRealImageAddMonoidHom_dualClass_of_restrict_compl
    (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
    (hr : finrank ℝ P = r)
    {a : (TopCat.of X).singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) r}
    (ha : TopCat.singularCohomologyMap (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).map r a =
      0) :
    ∃ m : ℝ, a = m • (TopCat.of X).singularCohomologyRealImageAddMonoidHom r
      (f.dualClass hn hdim hf o hr) := by
  -- By exactness of the sequence of the pair, `a` comes from `Hʳ(X, X ∖ f(Z); ℝ)`.
  obtain ⟨c, rfl⟩ : ∃ c, (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomologyπ
      _ ℝ _ r c = a := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology_exact_space _ ℝ _ r)
      a).1 ha
  obtain ⟨m, rfl⟩ := exists_eq_smul_realRelDualClass f hn hdim hf o hr c
  exact ⟨m, (map_smul _ m _).trans
    (congrArg (m • ·) (singularCohomologyπ_realRelDualClass f hn hdim hf o hr))⟩

end Connected

end TauCeti.SmoothEmbedding

end
