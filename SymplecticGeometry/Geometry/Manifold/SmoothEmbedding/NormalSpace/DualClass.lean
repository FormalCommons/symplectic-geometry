/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ThomClass
public import SymplecticGeometry.Geometry.Manifold.TubularNeighborhood.Normalized
public import TauCeti.AlgebraicTopology.Cohomology.Excision
public import TauCeti.Topology.VectorBundle.Orientation.EulerClass

/-!
# The dual class of a closed embedded submanifold

Let `f : Z → X` be a smooth embedding of boundaryless manifolds with closed range, `X` Hausdorff
and second countable, and let `ν` be its normal bundle, with model fibre `P`. A tube `Φ` of `f`, a
diffeomorphism of the total space of `ν` onto an open set `W ⊆ X` equal to `f` on the zero
section, is injective, so it carries the nonzero vectors exactly onto `W ∖ f(Z)`: it is an
isomorphism of pairs `(ν, ν ∖ 0) ≅ (W, W ∖ f(Z))` (`TauCeti.SmoothEmbedding.tubePairIso`). Since
`f(Z)` is closed and lies in the open set `W`, excision identifies
`Hⁿ(X, X ∖ f(Z)) ≅ Hⁿ(W, W ∖ f(Z))` (Tau Ceti's
`TopPair.isIso_singularCohomologyMap_excisionMap_of_isClosed_subset`).

Through the normalized tube with image in `X` that `exists_isNormalizedTube_subset` gives, a
relative class `u ∈ Hⁿ(ν, ν ∖ 0)` therefore defines a class
`TauCeti.SmoothEmbedding.relDualClassOf f hn hdim hf u ∈ Hⁿ(X, X ∖ f(Z))`, and its image
`dualClassOf f hn hdim hf u ∈ Hⁿ(X)`. They are linear in `u`. For an orientation `o` of `ν` and
the canonical Thom class `o.canonicalThomClass hr` of
`SymplecticGeometry/Topology/VectorBundle/Orientation/ThomClass.lean`, with coefficients
`ULift ℤ`, these are `relDualClass f hn hdim hf o hr` and the *dual class*
`dualClass f hn hdim hf o hr ∈ Hʳ(X; ℤ)` of the oriented submanifold, `r` its codimension.

The dual class vanishes on `X ∖ f(Z)` (`dualClassOf_restrict_compl`, from the exact sequence of
the pair), and its pull-back along `f` is the Euler class of `u` (`dualClassOf_restrict`), since
the tube restricted to the zero section is `f`. For the canonical Thom class in positive rank this
is the Euler class `o.eulerClass` of the oriented normal bundle
(`dualClass_restrict_eq_eulerClass`). Reversing the orientation negates the dual class
(`dualClass_neg`).

That the class does not depend on the tube is proved in `NormalSpace/DualClass/Slice.lean`; here
`exists_isNormalizedTube_singularCohomologyMap_excisionMap_relDualClassOf` records the tube that
the definition uses.

## Main definitions

* `TauCeti.SmoothEmbedding.tubePairIso`: the isomorphism of pairs given by a tube.
* `TauCeti.SmoothEmbedding.relDualClassOf`, `TauCeti.SmoothEmbedding.dualClassOf`: the relative
  and absolute classes of `X` given by a relative class of the Thom pair of the normal bundle.
* `TauCeti.SmoothEmbedding.relDualClass`, `TauCeti.SmoothEmbedding.dualClass`: the same for the
  canonical Thom class of a normal orientation.

## Main results

* `TauCeti.SmoothEmbedding.dualClassOf_restrict_compl`, `dualClass_restrict_compl`: the classes
  vanish off the submanifold.
* `TauCeti.SmoothEmbedding.dualClassOf_restrict`, `dualClass_restrict`,
  `dualClass_restrict_eq_eulerClass`: their restriction to the submanifold is the Euler class.
* `TauCeti.SmoothEmbedding.dualClass_neg`: reversing the normal orientation negates the class.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6
  (Proposition 6.24, the Poincaré dual of a closed submanifold as the Thom class of its normal
  bundle carried to the manifold by a tubular neighbourhood).
* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §3.2 (Thom classes and Euler classes
  over the integers).
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set
open scoped Manifold ContDiff

universe u v w

namespace TauCeti.SmoothEmbedding

variable {E H G : Type*} {V P Z X : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ V G} [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X]

section TubePair

/-- The image of a tube that equals `f` on the zero section contains the range of `f`. -/
theorem range_subset_of_apply_zeroSection (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x) :
    range f ⊆ W :=
  range_subset_iff.2 fun x ↦ hΦ x ▸ (Φ _).property

/-- **The pair isomorphism of a tube.** A diffeomorphism `Φ` of the total space of the normal
bundle `ν` of `f` onto an open set `W` of `X`, equal to `f` on the zero section, is an isomorphism
of pairs `(ν, ν ∖ 0) ≅ (W, W ∖ f(Z))`: a vector is nonzero exactly when its image is off the range
of `f`. -/
def tubePairIso (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x) :
    letI := f.normalSpaceFiberBundle hn hdim
    thomPair P (fun x ↦ f.NormalSpace x hn) ≅
      TopPair.interPair (X := TopCat.of X) (W : Set X) (range f)ᶜ :=
  letI := f.normalSpaceFiberBundle hn hdim
  TopPair.ofSubsetIso Φ.toHomeomorph fun v ↦ by
    rw [zeroSectionCompl_eq_compl_range]
    refine not_congr ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, (hΦ x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, Φ.injective (Subtype.ext ?_)⟩
      exact (hΦ x).trans hx

/-- On total spaces, the pair isomorphism of a tube is the tube. -/
@[simp]
theorem tubePairIso_hom_fst_apply (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x) (v : TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    letI := f.normalSpaceFiberBundle hn hdim
    TopPair.Hom.fst (f.tubePairIso hn hdim Φ hΦ).hom v = Φ v := by
  rw [tubePairIso, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_fst_apply (X := TopCat.of (TotalSpace P fun x ↦ f.NormalSpace x hn))
    (B := zeroSectionCompl P (fun x ↦ f.NormalSpace x hn)) _ _ v

/-- On ambient spaces, the inverse of the pair isomorphism of a tube is the inverse of the tube. -/
@[simp]
theorem tubePairIso_inv_fst_apply (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {W : TopologicalSpace.Opens X}
    (Φ : letI := f.normalSpaceFiberBundle hn hdim
      TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
    (hΦ : letI := f.normalSpaceFiberBundle hn hdim
      ∀ x, (Φ (zeroSection P _ x) : X) = f x) (y : W) :
    letI := f.normalSpaceFiberBundle hn hdim
    TopPair.Hom.fst (f.tubePairIso hn hdim Φ hΦ).inv y = Φ.symm y := by
  rw [tubePairIso, TopPair.ofSubsetIso_inv]
  exact TopPair.ofSubsetMap_fst_apply (X := TopCat.of W)
    (B := Subtype.val ⁻¹' (range f)ᶜ) _ _ y

end TubePair

section DualClassOf

variable {C : Type u} [Category.{v} C] [Limits.HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}
  [I.Boundaryless] [J.Boundaryless] [T2Space X] [SecondCountableTopology X]

variable (R k M) in
/-- The map `Hⁿ(ν, ν ∖ 0) ⟶ Hⁿ(X, X ∖ f(Z))` through the chosen normalized tube and excision. -/
private def relDualClassHom (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) (n : ℕ) :
    letI := f.normalSpaceFiberBundle hn hdim
    (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M n ⟶
      (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology R k M n :=
  let := f.normalSpaceFiberBundle hn hdim
  let h := f.exists_isNormalizedTube_subset (P := P) hdim isOpen_univ (subset_univ _)
  let hΦ := h.choose_spec.2.choose_spec
  haveI := TopPair.isIso_singularCohomologyMap_excisionMap_of_isClosed_subset R k M
    (X := TopCat.of X) (U := (h.choose : Set X)) h.choose.isOpen hf
    (range_subset_of_apply_zeroSection f hn hdim _ hΦ.apply_zeroSection) n
  TopPair.singularCohomologyMap (f.tubePairIso hn hdim _ hΦ.apply_zeroSection).inv n ≫
    inv (TopPair.singularCohomologyMap
      (TopPair.excisionMap (X := TopCat.of X) (h.choose : Set X) (range f)ᶜ) n)

/-- The map `relDualClassHom` inverts excision after the pair isomorphism of a normalized tube. -/
private theorem exists_relDualClassHom (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) :
    letI := f.normalSpaceFiberBundle hn hdim
    ∃ (W : TopologicalSpace.Opens X)
      (Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
      (hΦ : f.IsNormalizedTube hn hdim Φ), ∀ n,
        relDualClassHom R k M f hn hdim hf n ≫ TopPair.singularCohomologyMap
            (TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ) n =
          TopPair.singularCohomologyMap (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).inv n := by
  let := f.normalSpaceFiberBundle hn hdim
  let h := f.exists_isNormalizedTube_subset (P := P) hdim isOpen_univ (subset_univ _)
  refine ⟨h.choose, h.choose_spec.2.choose, h.choose_spec.2.choose_spec, fun n ↦ ?_⟩
  rw [relDualClassHom, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **The relative class of a submanifold given by a class of its normal bundle.** For a smooth
embedding `f : Z → X` with closed range and a relative class `u ∈ Hⁿ(ν, ν ∖ 0)` of the Thom pair
of its normal bundle, the class of `Hⁿ(X, X ∖ f(Z))` that corresponds to `u` under the pair
isomorphism `tubePairIso` of a normalized tube onto an open set `W` and the excision isomorphism
`Hⁿ(X, X ∖ f(Z)) ≅ Hⁿ(W, W ∖ f(Z))`. The tube is one that `exists_isNormalizedTube_subset`
gives; `exists_isNormalizedTube_singularCohomologyMap_excisionMap_relDualClassOf` states the
property of it that the definition uses. -/
def relDualClassOf (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) {n : ℕ}
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M n) :
    (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology R k M n :=
  relDualClassHom R k M f hn hdim hf n u

/-- The relative class `relDualClassOf f hn hdim hf u` is defined through a normalized tube `Φ`
onto an open set `W`: restricted to `(W, W ∖ f(Z))` by excision, it is the image of `u` under the
pair isomorphism of `Φ`. -/
theorem exists_isNormalizedTube_singularCohomologyMap_excisionMap_relDualClassOf
    (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) :
    letI := f.normalSpaceFiberBundle hn hdim
    ∃ (W : TopologicalSpace.Opens X)
      (Φ : TotalSpace P (fun x ↦ f.NormalSpace x hn) ≃ₘ^∞⟮I.prod 𝓘(ℝ, P), J⟯ W)
      (hΦ : f.IsNormalizedTube hn hdim Φ), ∀ (n : ℕ)
        (u : (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M n),
        TopPair.singularCohomologyMap
            (TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ) n
            (f.relDualClassOf hn hdim hf u) =
          TopPair.singularCohomologyMap (f.tubePairIso hn hdim Φ hΦ.apply_zeroSection).inv n u := by
  obtain ⟨W, Φ, hΦ, h⟩ := exists_relDualClassHom (R := R) (k := k) (M := M) f hn hdim hf
  exact ⟨W, Φ, hΦ, fun n u ↦ by rw [relDualClassOf, ← ConcreteCategory.comp_apply, h]⟩

/-- The relative class of the zero class is zero. -/
@[simp]
theorem relDualClassOf_zero (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) (n : ℕ) :
    letI := f.normalSpaceFiberBundle hn hdim
    f.relDualClassOf hn hdim hf
      (0 : (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M n) = 0 :=
  map_zero _

/-- The relative class is additive in the class of the normal bundle. -/
@[simp]
theorem relDualClassOf_add (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) {n : ℕ}
    (u u' : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M n) :
    f.relDualClassOf hn hdim hf (u + u') =
      f.relDualClassOf hn hdim hf u + f.relDualClassOf hn hdim hf u' :=
  map_add _ _ _

/-- The relative class commutes with scalar multiplication by `k`. -/
@[simp]
theorem relDualClassOf_smul (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) {n : ℕ} (c : k)
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M n) :
    f.relDualClassOf hn hdim hf (c • u) = c • f.relDualClassOf hn hdim hf u :=
  map_smul _ _ _

/-- The relative class of the negative is the negative of the relative class. -/
@[simp]
theorem relDualClassOf_neg (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) {n : ℕ}
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M n) :
    f.relDualClassOf hn hdim hf (-u) = -f.relDualClassOf hn hdim hf u :=
  map_neg _ _

/-- **The absolute class of a submanifold given by a class of its normal bundle**: the image in
`Hⁿ(X)` of the relative class `relDualClassOf f hn hdim hf u ∈ Hⁿ(X, X ∖ f(Z))`. -/
def dualClassOf (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) {n : ℕ}
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M n) :
    (TopCat.of X).singularCohomology R k M n :=
  (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomologyπ R k M n
    (f.relDualClassOf hn hdim hf u)

/-- The absolute class, unfolded. -/
theorem dualClassOf_def (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) {n : ℕ}
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M n) :
    f.dualClassOf hn hdim hf u =
      (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomologyπ R k M n
        (f.relDualClassOf hn hdim hf u) :=
  (rfl)

/-- The absolute class of the negative is the negative of the absolute class. -/
@[simp]
theorem dualClassOf_neg (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) {n : ℕ}
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M n) :
    f.dualClassOf hn hdim hf (-u) = -f.dualClassOf hn hdim hf u := by
  rw [dualClassOf_def, dualClassOf_def, relDualClassOf_neg]
  exact map_neg _ _

/-- **The class vanishes off the submanifold**: the restriction of `dualClassOf f hn hdim hf u` to
`X ∖ f(Z)` is zero, by exactness of the sequence of the pair `(X, X ∖ f(Z))`. -/
theorem dualClassOf_restrict_compl (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) {n : ℕ}
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M n) :
    TopCat.singularCohomologyMap (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).map n
      (f.dualClassOf hn hdim hf u) = 0 := by
  rw [dualClassOf_def]
  exact TopPair.singularCohomologyπ_comp_singularCohomologyMap_apply ..

/-- **The restriction to the submanifold is the Euler class**: the pull-back along `f` of
`dualClassOf f hn hdim hf u` is the Euler class of `u`, its pull-back along the zero section of
the normal bundle. -/
theorem dualClassOf_restrict (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) {n : ℕ}
    (u : letI := f.normalSpaceFiberBundle hn hdim
      (thomPair P (fun x ↦ f.NormalSpace x hn)).singularCohomology R k M n) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, f.isEmbedding.continuous⟩) n
      (f.dualClassOf hn hdim hf u) = eulerClass R k M P (fun x ↦ f.NormalSpace x hn) n u := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  obtain ⟨W, Φ, hΦ, h⟩ := exists_relDualClassHom (R := R) (k := k) (M := M) f hn hdim hf
  set t := f.tubePairIso hn hdim Φ hΦ.apply_zeroSection
  -- `f` is the zero section, followed by the tube and the inclusion of its image.
  -- `f` is the zero section, followed by the tube and the inclusion of its image.
  have hfac : TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
      (TopCat.ofHom ⟨f, f.isEmbedding.continuous⟩) n =
      TopCat.singularCohomologyMap
          (TopPair.Hom.fst (TopPair.excisionMap (X := TopCat.of X) (W : Set X) (range f)ᶜ)) n ≫
        TopCat.singularCohomologyMap (TopPair.Hom.fst t.hom) n ≫
          TopCat.singularCohomologyMap (zeroSectionHom P _) n := by
    rw [← TopCat.singularCohomologyMap_comp, ← TopCat.singularCohomologyMap_comp]
    have hpt (x : Z) : TopPair.Hom.fst (TopPair.excisionMap (X := TopCat.of X) (W : Set X)
        (range f)ᶜ) (TopPair.Hom.fst t.hom (zeroSectionHom P _ x)) = f x := by
      rw [zeroSectionHom_apply, tubePairIso_hom_fst_apply]
      exact (TopPair.excisionMap_fst_apply _ _ _).trans (hΦ.apply_zeroSection x)
    exact congrArg (TopCat.singularCohomologyMap · n) (TopCat.ext fun x ↦ (hpt x).symm)
  have key : relDualClassHom R k M f hn hdim hf n ≫
      (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomologyπ R k M n ≫
        TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, f.isEmbedding.continuous⟩) n =
      eulerClass R k M P (fun x ↦ f.NormalSpace x hn) n := by
    rw [hfac, TopPair.singularCohomologyπ_naturality_assoc, reassoc_of% (h n),
      TopPair.singularCohomologyπ_naturality_assoc, ← TopPair.singularCohomologyMap_comp_assoc,
      Iso.hom_inv_id, TopPair.singularCohomologyMap_id, Category.id_comp, eulerClass_def]
  have := ConcreteCategory.congr_hom key u
  simp only [ConcreteCategory.comp_apply] at this
  exact this

end DualClassOf

section DualClass

variable [I.Boundaryless] [J.Boundaryless] [T2Space X] [SecondCountableTopology X] {r : ℕ}

/-- **The relative dual class of a normally oriented submanifold.** For a smooth embedding
`f : Z → X` with closed range and an orientation `o` of its normal bundle, of rank `r`, the class
`relDualClassOf f hn hdim hf u ∈ Hʳ(X, X ∖ f(Z); ℤ)` of the canonical Thom class
`u = o.canonicalThomClass hr`, with coefficients `ULift ℤ`. -/
def relDualClass (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.NormalSpace x hn) (Fin r)) (hr : finrank ℝ P = r) :
    (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) r :=
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  f.relDualClassOf hn hdim hf (o.canonicalThomClass hr)

/-- The relative dual class, unfolded. -/
theorem relDualClass_def (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.NormalSpace x hn) (Fin r)) (hr : finrank ℝ P = r) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    f.relDualClass hn hdim hf o hr = f.relDualClassOf hn hdim hf (o.canonicalThomClass hr) :=
  (rfl)

/-- **The dual class of a normally oriented submanifold.** For a smooth embedding `f : Z → X`
with closed range and an orientation `o` of its normal bundle, of rank `r`, the class
`dualClassOf f hn hdim hf u ∈ Hʳ(X; ℤ)` of the canonical Thom class `u = o.canonicalThomClass hr`,
with coefficients `ULift ℤ`: the image of `relDualClass f hn hdim hf o hr` in absolute
cohomology. -/
def dualClass (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.NormalSpace x hn) (Fin r)) (hr : finrank ℝ P = r) :
    (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) r :=
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  f.dualClassOf hn hdim hf (o.canonicalThomClass hr)

/-- The dual class, unfolded. -/
theorem dualClass_def (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.NormalSpace x hn) (Fin r)) (hr : finrank ℝ P = r) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    f.dualClass hn hdim hf o hr = f.dualClassOf hn hdim hf (o.canonicalThomClass hr) :=
  (rfl)

/-- The dual class is the image of the relative dual class in absolute cohomology. -/
theorem dualClass_eq_singularCohomologyπ_relDualClass (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.NormalSpace x hn) (Fin r)) (hr : finrank ℝ P = r) :
    f.dualClass hn hdim hf o hr =
      (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomologyπ _ _ _ r
        (f.relDualClass hn hdim hf o hr) :=
  dualClassOf_def f hn hdim hf _

/-- Reversing the normal orientation negates the relative dual class. -/
@[simp]
theorem relDualClass_neg (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.NormalSpace x hn) (Fin r)) (hr : finrank ℝ P = r) :
    f.relDualClass hn hdim hf (-o) hr = -f.relDualClass hn hdim hf o hr := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  rw [relDualClass_def, relDualClass_def, VectorBundleOrientation.canonicalThomClass_neg,
    relDualClassOf_neg]

/-- Reversing the normal orientation negates the dual class. -/
@[simp]
theorem dualClass_neg (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.NormalSpace x hn) (Fin r)) (hr : finrank ℝ P = r) :
    f.dualClass hn hdim hf (-o) hr = -f.dualClass hn hdim hf o hr := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  rw [dualClass_def, dualClass_def, VectorBundleOrientation.canonicalThomClass_neg,
    dualClassOf_neg]

/-- **The dual class vanishes off the submanifold**: its restriction to `X ∖ f(Z)` is zero. -/
theorem dualClass_restrict_compl (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.NormalSpace x hn) (Fin r)) (hr : finrank ℝ P = r) :
    TopCat.singularCohomologyMap (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).map r
      (f.dualClass hn hdim hf o hr) = 0 :=
  dualClassOf_restrict_compl f hn hdim hf _

/-- **The restriction of the dual class to the submanifold** is the Euler class of the canonical
Thom class of the normal orientation: its pull-back along the zero section. -/
theorem dualClass_restrict (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.NormalSpace x hn) (Fin r)) (hr : finrank ℝ P = r) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, f.isEmbedding.continuous⟩) r
        (f.dualClass hn hdim hf o hr) =
      eulerClass _ _ _ P (fun x ↦ f.NormalSpace x hn) r (o.canonicalThomClass hr) :=
  dualClassOf_restrict f hn hdim hf _

/-- **The restriction of the dual class to the submanifold is the Euler class** of the oriented
normal bundle, in positive codimension `m + 1`. -/
theorem dualClass_restrict_eq_eulerClass (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f)) {m : ℕ}
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.NormalSpace x hn) (Fin (m + 1)))
    (hr : finrank ℝ P = m + 1) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    TopCat.singularCohomologyMap (TopCat.ofHom ⟨f, f.isEmbedding.continuous⟩) (m + 1)
        (f.dualClass hn hdim hf o hr) = o.eulerClass hr := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  rw [dualClass_restrict, VectorBundleOrientation.canonicalThomClass_eq_thomClass,
    VectorBundleOrientation.eulerClass_def]

end DualClass

end TauCeti.SmoothEmbedding

end
