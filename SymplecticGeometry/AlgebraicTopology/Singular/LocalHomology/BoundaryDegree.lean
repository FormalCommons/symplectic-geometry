/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.CircleMap
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.DiscBoundaryClass

/-!
# The boundary degree of a circle-valued map

We work in the setting of Tau Ceti's relative fundamental class
(`TauCeti.HomologicalOrientation.fundamentalClassRel`): `X` is compact Hausdorff, `ι : M → X` is
an open embedding of a manifold oriented by `o`, and the complement `∂X = X ∖ ι(M)` is the image of
a collared map. The connecting morphism of the pair `(X, ∂X)` carries the relative fundamental class
`[X, ∂X]` to the *boundary class* `∂[X, ∂X]` in the homology of `∂X`
(`TauCeti.HomologicalOrientation.boundaryClass`). It vanishes in the homology of `X`, by exactness,
and changes sign with the orientation.

When `M` is a surface, a map `u : ∂X → S¹` sends the boundary class to `H₁(S¹; ℤ) ≅ ℤ`
(`Circle.singularHomologyOneIso`); the resulting integer is the *boundary degree* of `u`
(`TauCeti.HomologicalOrientation.boundaryDegree`). Tau Ceti fixes no sign convention for its
connecting morphisms, so we check the sign on the closed unit disc of `ℂ`: there the boundary
class is the generator
(`SymplecticGeometry.singularHomologyOneIso_singularHomologyδ_fundamentalClassRel_closedBall`),
so the boundary circle, which runs counterclockwise, has boundary degree `1`
(`SymplecticGeometry.boundaryDegree_closedBallComplToCircle`). No sign has to be inserted.

## Main definitions

* `TauCeti.HomologicalOrientation.boundaryClass`: the boundary class `∂[X, ∂X]`.
* `TauCeti.HomologicalOrientation.boundaryDegree`: the boundary degree of `u : ∂X → S¹`.

## Main results

* `TauCeti.HomologicalOrientation.boundaryDegree_mul`: pointwise products add boundary degrees,
  since circle-valued maps act additively on `H₁` (`ContinuousMap.singularHomologyFunctor_map_mul`).
* `TauCeti.HomologicalOrientation.boundaryDegree_eq_of_homotopy`: homotopy invariance.
* `TauCeti.HomologicalOrientation.boundaryDegree_neg_orientation`: reversing the orientation
  negates the boundary degree.
* `TauCeti.HomologicalOrientation.boundaryDegree_eq_zero_of_extend`: a map that extends
  continuously over `X` has boundary degree `0`.
* `TauCeti.HomologicalOrientation.boundaryDegree_eq_sum_degree`: if loops in `∂X` represent the
  boundary class, the boundary degree is the sum of the degrees (`Circle.degree`) of `u` along them.
* `SymplecticGeometry.boundaryDegree_closedBallComplToCircle`: the sign on the unit disc.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3: the fundamental
  class of a compact manifold with boundary and its image in the homology of the boundary.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7: degrees
  of circle-valued maps on the boundary of a surface.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Set Topology Module

namespace TauCeti.HomologicalOrientation

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] [TopologicalSpace M]
  [T2Space X] [CompactSpace X] [T2Space M] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {ι : M → X} {f : N → X}

/-! ### The boundary class -/

section BoundaryClass

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

end BoundaryClass

/-! ### The boundary degree -/

variable (o : HomologicalOrientation M E 2) (hn : finrank ℝ E = 2) (hι : IsOpenEmbedding ι)
  (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)

/-- **The boundary degree of a circle-valued map.** For a compact surface `X` with collared
boundary `∂X`, the complement of `ι(M)`, and `u : ∂X → S¹`: the image under `u` of the boundary
class `∂[X, ∂X] ∈ H₁(∂X; ℤ)`, read in `ℤ` through `Circle.singularHomologyOneIso`. -/
def boundaryDegree (u : C(↥((range ι)ᶜ : Set X), Circle)) : ℤ :=
  ((Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom.hom
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
      (TopCat.ofHom u)).hom (o.boundaryClass hn hι hιf hf))).down

theorem boundaryDegree_def (u : C(↥((range ι)ᶜ : Set X), Circle)) :
    o.boundaryDegree hn hι hιf hf u =
      ((Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom.hom
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.ofHom u)).hom (o.boundaryClass hn hι hιf hf))).down :=
  (rfl)

/-- The boundary degree of a pointwise product is the sum of the boundary degrees. -/
theorem boundaryDegree_mul (u v : C(↥((range ι)ᶜ : Set X), Circle)) :
    o.boundaryDegree hn hι hιf hf (u * v) =
      o.boundaryDegree hn hι hιf hf u + o.boundaryDegree hn hι hιf hf v := by
  simp only [boundaryDegree_def, ContinuousMap.singularHomologyFunctor_map_mul, ModuleCat.hom_add,
    LinearMap.add_apply, map_add, ULift.add_down]

/-- Homotopic maps `∂X → S¹` have the same boundary degree. -/
theorem boundaryDegree_eq_of_homotopy {u v : C(↥((range ι)ᶜ : Set X), Circle)}
    (F : u.Homotopy v) :
    o.boundaryDegree hn hι hιf hf u = o.boundaryDegree hn hι hιf hf v := by
  have hF : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom u) =
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom v) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := TopCat.ofHom u) (g := TopCat.ofHom v) F (ModuleCat.of ℤ (ULift.{0} ℤ)) 1
  rw [boundaryDegree_def, boundaryDegree_def, hF]

/-- Reversing the orientation negates the boundary degree. -/
theorem boundaryDegree_neg_orientation (u : C(↥((range ι)ᶜ : Set X), Circle)) :
    (-o).boundaryDegree hn hι hιf hf u = -o.boundaryDegree hn hι hιf hf u := by
  simp only [boundaryDegree_def, boundaryClass_neg, map_neg, ULift.neg_down]

/-- A map `∂X → S¹` that extends continuously to `X` has boundary degree `0`, since the boundary
class vanishes in `H₁(X; ℤ)`. -/
theorem boundaryDegree_eq_zero_of_extend {u : C(↥((range ι)ᶜ : Set X), Circle)}
    (v : C(X, Circle)) (hv : ∀ z : ↥((range ι)ᶜ : Set X), v z = u z) :
    o.boundaryDegree hn hι hιf hf u = 0 := by
  have hu : TopCat.ofHom u =
      (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩ :
        TopCat.of ↥((range ι)ᶜ : Set X) ⟶ TopCat.of X) ≫ TopCat.ofHom v := by
    ext z
    exact congrArg _ (hv z).symm
  rw [boundaryDegree_def, hu, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    map_subtypeVal_boundaryClass, map_zero, map_zero, ULift.zero_down]

/-- **The boundary degree along loops.** Suppose that loops `γ i` in `∂X` represent the boundary
class: the sum of their classes in `H₁(∂X; ℤ)`, the push-forwards along `(γ i).toCircle` of the
generator of `Circle.singularHomologyOneIso`, is `∂[X, ∂X]`. Then the boundary degree of `u` is the
sum of the degrees of the loops `u ∘ γ i`. -/
theorem boundaryDegree_eq_sum_degree {κ : Type*} [Fintype κ] {x : κ → ↥((range ι)ᶜ : Set X)}
    (γ : ∀ i, Path (x i) (x i))
    (hγ : ∑ i, (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom (γ i).toCircle)).hom
          ((Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).inv.hom (ULift.up 1)) =
      o.boundaryClass hn hι hιf hf)
    (u : C(↥((range ι)ᶜ : Set X), Circle)) :
    o.boundaryDegree hn hι hιf hf u = ∑ i, Circle.degree ((γ i).map u.continuous) := by
  rw [boundaryDegree_def, ← hγ, map_sum, map_sum]
  rw [Finset.sum_congr rfl fun i _ ↦
    ContinuousMap.singularHomologyOneIso_hom_map_map_inv_one (γ i).toCircle u]
  -- `AddEquiv.ulift` is `ULift.down`, and the degree of a circle map is that of its based loop.
  refine (map_sum (AddEquiv.ulift (α := ℤ)) _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [← Circle.degree_toBasedLoop]
  exact (Circle.degree_congr _ _ fun t ↦ by
      rw [ContinuousMap.toBasedLoop_apply, ContinuousMap.comp_apply, Path.toCircle_unitToCircle,
        Path.map_coe, Function.comp_apply] :
    Circle.degree (u.comp (γ i).toCircle).toBasedLoop = Circle.degree ((γ i).map u.continuous))

end TauCeti.HomologicalOrientation

namespace SymplecticGeometry

open Metric TopologicalSpace

/-- **The sign of the boundary degree.** On the closed unit disc of `ℂ`, with the open disc
oriented as an open subset of `ℂ`, the boundary degree of the identification of the boundary with
`Circle` (`SymplecticGeometry.closedBallComplToCircle`), which runs once counterclockwise, is
`1`. -/
theorem boundaryDegree_closedBallComplToCircle :
    (TauCeti.complexHomologicalOrientation (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ)).boundaryDegree
      Complex.finrank_real_complex (.inclusion _ (isOpen_ball.preimage continuous_subtypeVal))
      (range_inclusion_ball_eq_compl 0 1) isCollared_inclusion_sphere_closedBall
      closedBallComplToCircle = 1 := by
  rw [TauCeti.HomologicalOrientation.boundaryDegree_def,
    TauCeti.HomologicalOrientation.boundaryClass_def]
  -- The disc lemma applies the connecting morphism and the isomorphism as coerced functions.
  erw [singularHomologyOneIso_singularHomologyδ_fundamentalClassRel_closedBall, ULift.one_down]

end SymplecticGeometry

end
