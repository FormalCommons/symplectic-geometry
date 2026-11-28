/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Slice
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Simplex
public import SymplecticGeometry.Topology.VectorBundle.Orientation.RealThomClass
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Multiple

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

The normal slices of the real relative dual class are the real images of the model generators.
For a normalized tube `Φ`, a point `x : Z` and a linear isomorphism `m : Q ≃ ν_x` carrying an
orientation `ν` of `Q` to `o x`, the class pulled back along `m` and the normal slice of `Φ` at
`x` is the real image of `ν.modelThomGenerator hQ`
(`TauCeti.SmoothEmbedding.singularCohomologyMap_normalSlice_realRelDualClass`). This is the real
image of the integral statement `singularCohomologyMap_normalSlice_relDualClass` of
`DualClass/Slice.lean`, since the real relative dual class is the real image of the integral one
and the real image commutes with maps of pairs. In rank two, with `Q = ℝ²` oriented by its
standard basis, the generator pairs to `-1` with the class of a smooth `2`-simplex of `ℝ²` that
is positively oriented around `0`
(`TauCeti.SmoothSimplex.singularKronecker_localCohomologyClass_relClass`), and the real image
pairs as its cast. So the slice of the real relative dual class pairs with such a simplex to `-1`
(`TauCeti.SmoothEmbedding.singularKronecker_normalSlice_realRelDualClass_relClass`).
The same holds on any disc transverse to `f` at `x`: a map `g` from a neighbourhood `B` of `0`
in `ℝ²` that meets `f(Z)` only at `g 0 = f x`, and whose derivative at `0`, followed by the
quotient onto `ν_x`, is an isomorphism `m` as above. By the local-degree lemma
`singularCohomologyMap_slice_eq_of_hasFDerivAt` (`DualClass/Slice.lean`), `g` pulls
the class back as the inclusion of `B` into `ℝ²` followed by the slice read through `m`; by the
naturality of the Kronecker pairing and of the class of a simplex, a simplex of `B` carried to
`σ` then pairs to `-1` with the pull-back
(`TauCeti.SmoothEmbedding.singularKronecker_realRelDualClass_relClass_of_hasFDerivAt`).
If `σ` lies in `B`, a singular simplex `s` of `X` that agrees with `g ∘ σ` on `Δ²` has its faces
off `f(Z)` (`TauCeti.SmoothSimplex.range_toSSetObjEquiv_δ_subset_compl_of_eq_comp`, in
`LocalHomology/Orientation/Simplex.lean`, with `K = f(Z)`), and the real
relative dual class pairs to `-1` with its class in `H₂(X, X ∖ f(Z); ℝ)`
(`singularKronecker_realRelDualClass_relClass_of_hasFDerivAt_of_eq_comp`): `s` is the image
under `g` of the lift of `σ` to `B`, the comparison of real and integral chains
(`TopPair.singularKronecker_singularCohomologyIntChainsIso_hom_relClass`) reads the pairing
through integral chains, and the naturality of that comparison and of the pairing brings it
back to the pairing on `B`.

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
* `TauCeti.SmoothEmbedding.singularCohomologyMap_normalSlice_realRelDualClass`: read through a
  linear isomorphism `Q ≃ ν_x` that preserves orientation, the normal slice at `x` of the real
  relative dual class is the real image of the model generator of `Q`.
* `TauCeti.SmoothEmbedding.singularKronecker_normalSlice_realRelDualClass_relClass`: in rank
  two, read on `(ℝ², ℝ² ∖ {0})`, it pairs to `-1` with a positively oriented smooth `2`-simplex
  around `0`.
* `TauCeti.SmoothEmbedding.singularKronecker_realRelDualClass_relClass_of_hasFDerivAt`: in rank
  two, pulled back along a disc `g` through `f x` that meets `f(Z)` only there and whose
  derivative at `0` is read on `ν_x` through an oriented isomorphism, it pairs to `-1` with a
  positively oriented smooth `2`-simplex around `0`.
* `singularKronecker_realRelDualClass_relClass_of_hasFDerivAt_of_eq_comp`, in the namespace
  `TauCeti.SmoothEmbedding`: in rank two, the real relative dual class pairs to `-1` with the
  class in `H₂(X, X ∖ f(Z); ℝ)` of a singular simplex of `X` that agrees with `g ∘ σ` on `Δ²`,
  for such a `σ` with values in the neighbourhood `B` of `0` on which `g` is continuous.
* `TauCeti.SmoothEmbedding.exists_eq_smul_realRelDualClass`: for connected `Z`, every class of
  `Hʳ(X, X ∖ f(Z); ℝ)` is a real multiple of the real relative dual class.
* `exists_eq_smul_singularCohomologyRealImageAddMonoidHom_dualClass_of_restrict_compl`, in the
  namespace `TauCeti.SmoothEmbedding`: for connected `Z`, every class of `Hʳ(X; ℝ)` vanishing
  on `X ∖ f(Z)` is a real multiple of the real image of the dual class.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom isomorphism with coefficients in a field).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (local
  orientations and the class of a simplex in local homology).
-/

public section

open Bundle CategoryTheory Module Set Topology
open scoped Manifold ContDiff Simplicial

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

/-- **The normal slices of the real relative dual class.** Let `Φ` be a normalized tube of `f`,
`x : Z`, and `m : Q ≃ ν_x` a linear isomorphism from a real normed space `Q` of dimension `r`
that carries an orientation `ν` of `Q` to the normal orientation `o x`. The pull-back of
`realRelDualClass f hn hdim hf o hr` along `m` followed by the normal slice of `Φ` at `x` is
the real image of the generator `ν.modelThomGenerator hQ` of `Hʳ(Q, Q ∖ {0}; ℤ)` selected by
`ν`. -/
theorem singularCohomologyMap_normalSlice_realRelDualClass (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
    (hr : finrank ℝ P = r) {W : TopologicalSpace.Opens X}
    {Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    (hΦ : f.IsNormalizedTube hn hdim Φ) (x : Z) {Q : Type} [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] (ν : Orientation ℝ Q (Fin r))
    (hQ : finrank ℝ Q = r) (m : Q ≃L[ℝ] f.isImmersion.NormalSpace x hn)
    (hm : ν.map (Fin r) m.toLinearEquiv = o x) :
    TopPair.singularCohomologyMap (m.complZeroPairIso.hom ≫
        f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) r (f.realRelDualClass hn hdim hf o hr) =
      ((TopPair.ofSubset (X := TopCat.of Q) ({0}ᶜ : Set Q)).singularCohomologyRealImage r
        (ν.modelThomGenerator hQ) : (TopPair.ofSubset (X := TopCat.of Q) ({0}ᶜ : Set Q)
          ).singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) r) := by
  rw [realRelDualClass_eq_singularCohomologyRealImage,
    ← TopPair.singularCohomologyRealImage_naturality_apply,
    singularCohomologyMap_normalSlice_relDualClass f hn hdim hf o hr hΦ x ν hQ m hm]

/-- **The value of the real dual class of a codimension-two submanifold on a normal disc.** Let
the normal bundle have rank two, `Φ` be a normalized tube of `f`, `x : Z`, and
`m : ℝ² ≃ ν_x` a linear isomorphism carrying the standard orientation of `ℝ²` to `o x`. Pull
`realRelDualClass f hn hdim hf o hr` back to `(ℝ², ℝ² ∖ {0})` along `m` followed by the normal
slice of `Φ` at `x`. Let `σ` be a smooth `2`-simplex of `ℝ²`, the restriction to `Δ²` of a map
`g` that is an open embedding preserving the standard orientation on an open neighbourhood `U` of
`Δ²`, with `0 ∈ g (interior Δ²)`. Then the pulled-back class, read through integral chains, pairs
with the class of `σ` in `H₂(ℝ², ℝ² ∖ {0}; ℤ)` to `-1`.

The sign is that of `TauCeti.SmoothSimplex.singularKronecker_localCohomologyClass_relClass`. -/
theorem singularKronecker_normalSlice_realRelDualClass_relClass
    (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin 2))
    (hr : finrank ℝ P = 2) {W : TopologicalSpace.Opens X}
    {Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W}
    (hΦ : f.IsNormalizedTube hn hdim Φ) (x : Z)
    (m : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] f.isImmersion.NormalSpace x hn)
    (hm : (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.map (Fin 2) m.toLinearEquiv =
      o x)
    (σ : SmoothSimplex 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) 2)
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hU : fullSimplex 2 ⊆ U)
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hgσ : ∀ y : fullSimplex 2, g y = σ.toContinuousMap y)
    (hg : IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2))))
    (ho : ∀ y ∈ U, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace 2) (Manifold.Orientation.euclideanSpace 2) g y)
    (h0 : 0 ∈ g '' interior (fullSimplex 2)) :
    ((TopPair.ofSubset (X := TopCat.of (EuclideanSpace ℝ (Fin 2))) {0}ᶜ).singularKronecker ℤ 2
        ((TopPair.ofSubset (X := TopCat.of (EuclideanSpace ℝ (Fin 2))) {0}ᶜ
          ).singularCohomologyIntChainsIso ℝ 2 |>.hom
          (TopPair.singularCohomologyMap (m.complZeroPairIso.hom ≫
            f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) 2
            (f.realRelDualClass hn hdim hf o hr)))).hom
      ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).relClass
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (n := 1) σ.val
        (SmoothSimplex.range_toSSetObjEquiv_δ_subset_compl σ hU hgσ hg
          (singleton_subset_iff.2 h0)) 1) = -1 := by
  have hE : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  rw [singularCohomologyMap_normalSlice_realRelDualClass f hn hdim hf o hr hΦ x _ hE m hm,
    TopPair.singularKronecker_singularCohomologyRealImage,
    Orientation.modelThomGenerator_eq_localCohomologyClass, ModuleCat.hom_comp,
    LinearMap.comp_apply,
    SmoothSimplex.singularKronecker_localCohomologyClass_relClass σ hU hgσ hg ho h0, map_neg,
    intToRealCoeff_apply, ULift.one_down, Int.cast_one]

/-- **The value of the real dual class of a codimension-two submanifold on a transverse disc.**
Let the normal bundle have rank two, `x : Z`, and `m : ℝ² ≃ ν_x` a linear isomorphism carrying
the standard orientation of `ℝ²` to `o x`. Let `B` be a neighbourhood of `0` in `ℝ²` and
`g : ℝ² → X` a map continuous on `B`, with `g 0 = f x`, sending no other point of `B` into
`f(Z)`, and with a derivative `A` at `0` such that the normal class of each `A w` is `m w`. Pull
`realRelDualClass f hn hdim hf o hr` back along `g`, as a map of pairs
`(B, B ∖ {0}) ⟶ (X, X ∖ f(Z))`. Let `σ` be a smooth `2`-simplex of `ℝ²`, the restriction to
`Δ²` of a map `φ` that is an open embedding preserving the standard orientation on an open
neighbourhood `U` of `Δ²`, with `0 ∈ φ (interior Δ²)`, and `τ` a singular simplex of `B` that
the inclusion carries to `σ`. Then the pulled-back class, read through integral chains, pairs
with the class of `τ` in `H₂(B, B ∖ {0}; ℤ)` to `-1`.

By `singularCohomologyMap_slice_eq_of_hasFDerivAt`, `g` pulls the class back as the
normal slice of a normalized tube read through `m` does, after the inclusion of `B` into `ℝ²`;
the inclusion carries the class of `τ` to that of `σ`. -/
theorem singularKronecker_realRelDualClass_relClass_of_hasFDerivAt
    (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin 2))
    (hr : finrank ℝ P = 2) (x : Z)
    (m : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] f.isImmersion.NormalSpace x hn)
    (hm : (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.map (Fin 2) m.toLinearEquiv =
      o x)
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : B ∈ 𝓝 0) {g : EuclideanSpace ℝ (Fin 2) → X}
    (hgB : ContinuousOn g B) (hg0 : g 0 = f x) (hgf : ∀ w ∈ B, g w ∈ range f → w = 0)
    {A : EuclideanSpace ℝ (Fin 2) →L[ℝ] V}
    (hg : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) J g 0 A)
    (hA : ∀ w, f.isImmersion.normalClassL x hn (A w) = m w)
    (σ : SmoothSimplex 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) 2)
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hU : fullSimplex 2 ⊆ U)
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hφσ : ∀ y : fullSimplex 2, φ y = σ.toContinuousMap y)
    (hφ : IsOpenEmbedding (φ ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2))))
    (ho : ∀ y ∈ U, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace 2) (Manifold.Orientation.euclideanSpace 2) φ y)
    (h0 : 0 ∈ φ '' interior (fullSimplex 2))
    (τ : (TopCat.toSSet.obj (TopCat.of B)) _⦋2⦌)
    (hτ : (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal B))).app _ τ = σ.val) :
    ((TopPair.ofSubset (X := TopCat.of B) {⟨0, mem_of_mem_nhds hB⟩}ᶜ).singularKronecker ℤ 2
        ((TopPair.ofSubset (X := TopCat.of B) {⟨0, mem_of_mem_nhds hB⟩}ᶜ
          ).singularCohomologyIntChainsIso ℝ 2 |>.hom
          (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (X := TopCat.of B) (Y := TopCat.of X)
              (TopCat.ofHom ⟨B.domRestrict g, hgB.domRestrict⟩)
              (B := {⟨0, mem_of_mem_nhds hB⟩}ᶜ) (B' := (range f)ᶜ)
              fun w hw h ↦ hw (Subtype.ext (hgf w w.property h))) 2
            (f.realRelDualClass hn hdim hf o hr)))).hom
      ((TopPair.ofSubset ({(⟨0, mem_of_mem_nhds hB⟩ : B)}ᶜ : Set (TopCat.of B))).relClass
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (n := 1) τ
        (TopPair.range_toSSetObjEquiv_δ_subset_of_toSSet_map_app (ContinuousMap.subtypeVal B)
          (S := {(⟨0, mem_of_mem_nhds hB⟩ : B)}) (T := {0}) (fun _ h ↦ by simp_all) τ
          (hτ ▸ SmoothSimplex.range_toSSetObjEquiv_δ_subset_compl σ hU hφσ hφ
            (singleton_subset_iff.2 h0))) 1) = -1 := by
  obtain ⟨W, Φ, hΦ, -⟩ :=
    exists_isNormalizedTube_singularCohomologyMap_excisionMap_relDualClassOf
      (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := ModuleCat.of ℤ (ULift.{0} ℤ)) f hn hdim
      hf
  -- The inclusion `(B, B ∖ {0}) ⟶ (ℝ², ℝ² ∖ {0})`.
  set ι := TopPair.ofSubsetMap (X := TopCat.of B) (Y := TopCat.of (EuclideanSpace ℝ (Fin 2)))
    (TopCat.ofHom (ContinuousMap.subtypeVal B)) (B := {⟨0, mem_of_mem_nhds hB⟩}ᶜ)
    (B' := {0}ᶜ) (fun _ hw h ↦ hw (Subtype.ext (Set.mem_singleton_iff.1 h)))
  set y := TopPair.singularCohomologyMap (m.complZeroPairIso.hom ≫
    f.normalSlice hn hdim Φ hΦ.apply_zeroSection x) 2 (f.realRelDualClass hn hdim hf o hr)
  -- By the local-degree lemma, `g` pulls the class back as the normal slice read through `m`.
  rw [singularCohomologyMap_slice_eq_of_hasFDerivAt hΦ x m hB hgB hg0 hgf hg hA,
    TopPair.singularCohomologyMap_comp_apply,
    ← TopPair.singularCohomologyMap_comp_apply m.complZeroPairIso.hom]
  -- Read through integral chains, the pull-back along the inclusion is the integral one.
  have hι : ((TopPair.ofSubset (X := TopCat.of B) {⟨0, mem_of_mem_nhds hB⟩}ᶜ
        ).singularCohomologyIntChainsIso ℝ 2).hom (TopPair.singularCohomologyMap ι 2 y) =
      TopPair.singularCohomologyMap ι 2
        (((TopPair.ofSubset (X := TopCat.of (EuclideanSpace ℝ (Fin 2))) {0}ᶜ
          ).singularCohomologyIntChainsIso ℝ 2).hom y) :=
    congrArg (fun φ ↦ φ.hom y) (TopPair.singularCohomologyIntChainsIso_hom_naturality ℝ ι 2)
  rw [hι, TopPair.singularKronecker_naturality, ModuleCat.hom_comp, LinearMap.comp_apply]
  refine (congrArg _ ?_).trans (singularKronecker_normalSlice_realRelDualClass_relClass f hn hdim
    hf o hr hΦ x m hm σ hU hφσ hφ ho h0)
  -- The inclusion carries the class of `τ` to that of `σ`.
  rw [← localHomologyMap_def (j := ContinuousMap.subtypeVal B)
    (S := {(⟨0, mem_of_mem_nhds hB⟩ : B)}) (T := {0}) _ (fun _ h ↦ Subtype.ext h)]
  exact TopPair.relClass_localHomologyMap_apply _ _ _ τ _ _ hτ 1

/-- **The value of the real dual class of a codimension-two submanifold on a simplex through a
transverse disc.** Take the hypotheses of
`singularKronecker_realRelDualClass_relClass_of_hasFDerivAt`: a normal bundle of rank two, an
isomorphism `m : ℝ² ≃ ν_x` carrying the standard orientation to `o x`, a map `g : ℝ² → X`
continuous on a neighbourhood `B` of `0`, with `g 0 = f x`, sending no other point of `B` into
`f(Z)`, and with a derivative `A` at `0` whose normal class is `m`, and a smooth `2`-simplex `σ`
of `ℝ²` that is the restriction to `Δ²` of an orientation-preserving open embedding `φ` near
`Δ²`, with `0 ∈ φ (interior Δ²)`. Suppose moreover that `σ` takes its values in `B`. Then
`realRelDualClass f hn hdim hf o hr` pairs to `-1` with the class in `H₂(X, X ∖ f(Z); ℝ)` of
any singular `2`-simplex `s` of `X` that agrees with `g ∘ σ` on `Δ²`.

The faces of `s` lie in `X ∖ f(Z)` by
`SmoothSimplex.range_toSSetObjEquiv_δ_subset_compl_of_eq_comp`. -/
theorem singularKronecker_realRelDualClass_relClass_of_hasFDerivAt_of_eq_comp
    (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin 2))
    (hr : finrank ℝ P = 2) (x : Z)
    (m : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] f.isImmersion.NormalSpace x hn)
    (hm : (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.map (Fin 2) m.toLinearEquiv =
      o x)
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : B ∈ 𝓝 0) {g : EuclideanSpace ℝ (Fin 2) → X}
    (hgB : ContinuousOn g B) (hg0 : g 0 = f x) (hgf : ∀ w ∈ B, g w ∈ range f → w = 0)
    {A : EuclideanSpace ℝ (Fin 2) →L[ℝ] V}
    (hg : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) J g 0 A)
    (hA : ∀ w, f.isImmersion.normalClassL x hn (A w) = m w)
    (σ : SmoothSimplex 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) 2)
    {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2))} (hU : fullSimplex 2 ⊆ U)
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hφσ : ∀ y : fullSimplex 2, φ y = σ.toContinuousMap y)
    (hφ : IsOpenEmbedding (φ ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2))))
    (ho : ∀ y ∈ U, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace 2) (Manifold.Orientation.euclideanSpace 2) φ y)
    (h0 : 0 ∈ φ '' interior (fullSimplex 2)) (hσB : ∀ y, σ.toContinuousMap y ∈ B)
    (s : (TopCat.toSSet.obj (TopCat.of X)) _⦋2⦌)
    (hs : ∀ y, (TopCat.of X).toSSetObjEquiv _ s (fullSimplexEquivStdSimplex 2 y) =
      g (σ.toContinuousMap y)) :
    (TopPair.ofSubset ((range f)ᶜ : Set (TopCat.of X))).singularKronecker ℝ 2
        (f.realRelDualClass hn hdim hf o hr)
        ((TopPair.ofSubset ((range f)ᶜ : Set (TopCat.of X))).relClass (ModuleCat.of ℝ ℝ) (n := 1)
          s (SmoothSimplex.range_toSSetObjEquiv_δ_subset_compl_of_eq_comp hgf σ hU hφσ hφ h0 hσB
            s hs) 1) =
      -1 := by
  have hσB' : ∀ p, (TopCat.of _).toSSetObjEquiv _ σ.val p ∈ B := fun p ↦ by
    simpa [SmoothSimplex.toContinuousMap_apply] using hσB ((fullSimplexEquivStdSimplex 2).symm p)
  -- The lift `τ` of `σ` to `B`, which `g` carries to `s`.
  obtain ⟨τ, hτ⟩ := (Topology.IsInducing.mem_range_toSSet_map_app_iff
    (f := TopCat.ofHom (ContinuousMap.subtypeVal B)) .subtypeVal _ σ.val).2
    (Set.range_subset_iff.2 fun p ↦ ⟨⟨_, hσB' p⟩, rfl⟩)
  have hsτ : (TopCat.toSSet.map (TopCat.ofHom ⟨B.domRestrict g, hgB.domRestrict⟩)).app _ τ =
      s := by
    refine ((TopCat.of X).toSSetObjEquiv _).injective (ContinuousMap.ext fun p ↦ ?_)
    have hp := DFunLike.congr_fun (congrArg ((TopCat.of _).toSSetObjEquiv _) hτ) p
    have h := hs ((fullSimplexEquivStdSimplex 2).symm p)
    rw [Homeomorph.apply_symm_apply, SmoothSimplex.toContinuousMap_apply,
      Homeomorph.apply_symm_apply] at h
    rw [TopCat.toSSetObjEquiv_toSSet_map_app, ConcreteCategory.hom_ofHom,
      ContinuousMap.comp_apply] at hp ⊢
    rw [h, ← hp, ContinuousMap.coe_mk, Set.domRestrict_apply,
      ContinuousMap.subtypeVal_apply]
  have key := singularKronecker_realRelDualClass_relClass_of_hasFDerivAt f hn hdim hf o hr x m hm
    hB hgB hg0 hgf hg hA σ hU hφσ hφ ho h0 τ hτ
  refine (TopPair.singularKronecker_singularCohomologyIntChainsIso_hom_relClass ℝ _
    (f.realRelDualClass hn hdim hf o hr) s _).symm.trans (Eq.trans ?_ key)
  set F := TopPair.ofSubsetMap (X := TopCat.of B) (Y := TopCat.of X)
    (TopCat.ofHom ⟨B.domRestrict g, hgB.domRestrict⟩) (B := {⟨0, mem_of_mem_nhds hB⟩}ᶜ)
    (B' := (range f)ᶜ) fun w hw h ↦ hw (Subtype.ext (hgf w w.property h))
  have hI : ((TopPair.ofSubset (X := TopCat.of B) {⟨0, mem_of_mem_nhds hB⟩}ᶜ
        ).singularCohomologyIntChainsIso ℝ 2).hom
        (TopPair.singularCohomologyMap F 2 (f.realRelDualClass hn hdim hf o hr)) =
      TopPair.singularCohomologyMap F 2
        (((TopPair.ofSubset ((range f)ᶜ : Set (TopCat.of X))).singularCohomologyIntChainsIso ℝ 2
          ).hom (f.realRelDualClass hn hdim hf o hr)) :=
    congrArg (fun φ ↦ φ.hom (f.realRelDualClass hn hdim hf o hr))
      (TopPair.singularCohomologyIntChainsIso_hom_naturality ℝ F 2)
  rw [hI, TopPair.singularKronecker_naturality, ModuleCat.hom_comp, LinearMap.comp_apply]
  refine congrArg _ ?_
  rw [← localHomologyMap_def (j := ⟨B.domRestrict g, hgB.domRestrict⟩)
    (S := {⟨0, mem_of_mem_nhds hB⟩}) (T := range f) _ (fun w h ↦ Subtype.ext (hgf w w.property h))]
  exact (TopPair.relClass_localHomologyMap_apply _ _ _ τ _ _ hsτ 1).symm

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
