/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass
public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# The boundary class of a compact manifold with collared boundary

We work in the setting of Tau Ceti's relative fundamental class
(`TauCeti.HomologicalOrientation.fundamentalClassRel`): `X` is compact Hausdorff, `ι : M → X` is
an open embedding of an `(n + 1)`-manifold oriented by `o`, and the complement `∂X = X ∖ ι(M)` is
the image of a collared map. The connecting morphism of the pair `(X, ∂X)` carries the relative
fundamental class `[X, ∂X]` to the *boundary class* `∂[X, ∂X] ∈ Hₙ(∂X; ℤ)`.

## Main definitions

* `TauCeti.HomologicalOrientation.boundaryClass`: the boundary class `∂[X, ∂X]`.

## Main results

* `TauCeti.HomologicalOrientation.boundaryClass_neg`: reversing the orientation negates the
  boundary class.
* `TauCeti.HomologicalOrientation.map_subtypeVal_boundaryClass`: the boundary class vanishes in
  `Hₙ(X; ℤ)`, by exactness of the sequence of the pair.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3: the fundamental
  class of a compact manifold with boundary and its image in the homology of the boundary.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Set Topology Module

namespace TauCeti.HomologicalOrientation

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] [TopologicalSpace M]
  [T2Space X] [CompactSpace X] [T2Space M] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {ι : M → X} {f : N → X}

variable {n : ℕ} (o : HomologicalOrientation M E (n + 1)) (hn : finrank ℝ E = n + 1)
  (hι : IsOpenEmbedding ι) (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)

/-- **The boundary class** `∂[X, ∂X] ∈ Hₙ(∂X; ℤ)` of a compact `(n + 1)`-manifold `X` with
collared boundary `∂X`, the complement of `ι(M)`: the image of the relative fundamental class
`[X, ∂X]` under the connecting morphism of the pair `(X, ∂X)`. -/
def boundaryClass :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopCat.of ↥((range ι)ᶜ : Set X)) :=
  ((TopPair.ofSubset (X := TopCat.of X) (range ι)ᶜ).singularHomologyδ
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1) n rfl).hom (o.fundamentalClassRel hn hι hιf hf)

theorem boundaryClass_def :
    o.boundaryClass hn hι hιf hf =
      ((TopPair.ofSubset (X := TopCat.of X) (range ι)ᶜ).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1) n rfl).hom (o.fundamentalClassRel hn hι hιf hf) :=
  (rfl)

/-- Reversing the orientation negates the boundary class. -/
@[simp]
theorem boundaryClass_neg : (-o).boundaryClass hn hι hιf hf = -o.boundaryClass hn hι hιf hf := by
  rw [boundaryClass_def, boundaryClass_def, fundamentalClassRel_neg]
  exact map_neg _ _

/-- The boundary class vanishes in `Hₙ(X; ℤ)`, by exactness of the sequence of the pair
`(X, ∂X)`. -/
@[simp]
theorem map_subtypeVal_boundaryClass :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩ :
        TopCat.of ↥((range ι)ᶜ : Set X) ⟶ TopCat.of X)).hom
        (o.boundaryClass hn hι hιf hf) = 0 := by
  have h := (TopPair.ofSubset (X := TopCat.of X) (range ι)ᶜ).singularHomologyδ_comp
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1) n rfl
  -- `h` is the vanishing of the composite morphism; evaluate it at `[X, ∂X]`.
  exact ConcreteCategory.congr_hom h (o.fundamentalClassRel hn hι hιf hf)

end TauCeti.HomologicalOrientation

end
