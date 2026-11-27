/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.DualClass.Basic
import SymplecticGeometry.Topology.VectorBundle.Thom.SecondCountable
import TauCeti.Geometry.Manifold.Topology

/-!
# Classes supported on a connected submanifold are multiples of its dual class

Let `f : Z → X` be a smooth embedding of boundaryless manifolds with closed range, `X` Hausdorff
and second countable, and `o` an orientation of its normal bundle `ν`, of rank `r`. Every class of
`Hʳ(X, X ∖ f(Z))` is `relDualClassOf f hn hdim hf u` for exactly one `u ∈ Hʳ(ν, ν ∖ 0)`
(`TauCeti.SmoothEmbedding.bijective_relDualClassOf`, in `DualClass/Basic.lean`).

When `Z` is connected, every class of `Hʳ(ν, ν ∖ 0; ℤ)` is an integer multiple of the canonical
Thom class (`TauCeti.IsThomClass.exists_eq_smul`, from the Thom isomorphism). So every
class of `Hʳ(X, X ∖ f(Z); ℤ)` is an integer multiple of the relative dual class
(`TauCeti.SmoothEmbedding.exists_eq_zsmul_relDualClass`). By exactness of the sequence of the
pair `(X, X ∖ f(Z))`, a class of `Hʳ(X; ℤ)` that restricts to zero on `X ∖ f(Z)` lifts
to `Hʳ(X, X ∖ f(Z); ℤ)`, and so is an integer multiple of the dual class
(`TauCeti.SmoothEmbedding.exists_eq_zsmul_dualClass_of_restrict_compl`).

## Main results

* `TauCeti.SmoothEmbedding.exists_eq_zsmul_relDualClass`: for connected `Z`, every class of
  `Hʳ(X, X ∖ f(Z); ℤ)` is an integer multiple of the relative dual class.
* `TauCeti.SmoothEmbedding.exists_eq_zsmul_dualClass_of_restrict_compl`: for connected `Z`, every
  class of `Hʳ(X; ℤ)` vanishing on `X ∖ f(Z)` is an integer multiple of the dual class.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), Theorem 10.4 (the Thom isomorphism).
-/

public section

open Bundle CategoryTheory Module Set
open scoped Manifold ContDiff


namespace TauCeti.SmoothEmbedding

section Connected

variable {E H G : Type*} {V P Z X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ V G} [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J ∞ X]
  [I.Boundaryless] [J.Boundaryless] [T2Space X] [SecondCountableTopology X] [ConnectedSpace Z]
  {r : ℕ}

/-- **The relative dual class of a connected submanifold generates.** For a smooth embedding
`f : Z → X` with closed range and connected (so nonempty) source, and an orientation `o` of its
normal bundle of rank `r`, every class of `Hʳ(X, X ∖ f(Z); ℤ)` is `m • relDualClass f hn hdim hf
o hr` for some integer `m`. -/
theorem exists_eq_zsmul_relDualClass (f : SmoothEmbedding I J ∞ Z X) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
    (hr : finrank ℝ P = r)
    (c : (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{0} ℤ)) r) :
    ∃ m : ℤ, c = m • f.relDualClass hn hdim hf o hr := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  subst hr
  have : T2Space Z := f.isEmbedding.t2Space
  have : SecondCountableTopology Z := f.isEmbedding.secondCountableTopology
  have : LocallyCompactSpace Z := Manifold.locallyCompact_of_finiteDimensional I
  have : PathConnectedSpace Z := I.pathConnectedSpace Z
  obtain ⟨u, rfl⟩ := (bijective_relDualClassOf f hn hdim hf _).surjective c
  obtain ⟨m, hm⟩ := (o.isThomClass_intCanonicalThomClass rfl).exists_eq_smul
    ((thomPair P _).uliftIntegralCohomologyEquiv _ u)
  rw [o.intCanonicalThomClass_def, ← LinearEquiv.map_smul] at hm
  refine ⟨m, ?_⟩
  dsimp only
  rw [relDualClass_def, (LinearEquiv.injective _) hm]
  exact (relDualClassOf_smul f hn hdim hf _ _).trans (int_smul_eq_zsmul _ _ _)

/-- **A class vanishing off a connected submanifold is a multiple of its dual class.** For a
smooth embedding `f : Z → X` with closed range and connected (so nonempty) source, and an
orientation `o` of its normal bundle of rank `r`, every class `a ∈ Hʳ(X; ℤ)` whose restriction to
`X ∖ f(Z)` is zero is `m • dualClass f hn hdim hf o hr` for some integer `m`. -/
theorem exists_eq_zsmul_dualClass_of_restrict_compl (f : SmoothEmbedding I J ∞ Z X)
    (hn : (∞ : ℕ∞ω) ≠ 0) (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (hf : IsClosed (range f))
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (fun x ↦ f.isImmersion.NormalSpace x hn) (Fin r))
    (hr : finrank ℝ P = r)
    {a : (TopCat.of X).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) r}
    (ha : TopCat.singularCohomologyMap (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).map r a =
      0) :
    ∃ m : ℤ, a = m • f.dualClass hn hdim hf o hr := by
  -- By exactness of the sequence of the pair, `a` comes from `Hʳ(X, X ∖ f(Z))`.
  obtain ⟨c, rfl⟩ : ∃ c, (TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomologyπ
      _ ℤ _ r c = a := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((TopPair.ofSubset (X := TopCat.of X) (range f)ᶜ).singularCohomology_exact_space _ ℤ _ r)
      a).1 ha
  obtain ⟨m, rfl⟩ := exists_eq_zsmul_relDualClass f hn hdim hf o hr c
  refine ⟨m, ?_⟩
  rw [dualClass_eq_singularCohomologyπ_relDualClass]
  exact map_zsmul _ _ _

end Connected

end TauCeti.SmoothEmbedding

end
