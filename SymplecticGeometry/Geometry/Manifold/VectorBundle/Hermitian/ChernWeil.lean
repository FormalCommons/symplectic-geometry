/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.RealImage
public import SymplecticGeometry.Geometry.Manifold.DeRham.FundamentalClass
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.RealChernClass
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.ChernWeil
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.RealChernClass
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass

/-!
# Chern–Weil in degree two

Let `V` be a smooth complex line bundle with a smooth Hermitian metric `g`, and `P` the principal
`Circle`-bundle of its unitary frames. The real first Chern class
`SymplecticGeometry.realFirstChernClass` of `P` is a de Rham class, and Tau Ceti's Euler class
`TauCeti.complexEulerClass` of `V` an integral singular class. Under the library's conventions
the de Rham homomorphism `TauCeti.deRhamHom` sends the first to **minus** the real image
(`TopCat.singularCohomologyRealImage`) of the second.

This file proves this over a closed connected orientable surface `M`. Both classes lie in
`H²(M; ℝ)`, where a class is determined by its value on a fundamental class
(`TauCeti.HomologicalOrientation.evalFundamentalClass_id_injective`). Choose an orientation `o`
of `M`, and take the fundamental class of the homological orientation of `-o`.

* The class `deRhamHom [φ]` of a closed two-form takes the value `∫_o φ` there
  (`evalFundamentalClass_singularCohomologyIntChainsIso_hom_deRhamHom_mk`, in the namespace
  `TauCeti.Manifold.Orientation`).
  Since the real first Chern class is `-(2π)⁻¹` times the class of a curvature `F_α`
  (`SymplecticGeometry.IsCircleConnectionForm.realFirstChernClass_eq`), its image takes the
  value `-(2π)⁻¹ ∫_o F_α`, the first Chern number for the homological orientation of `o`
  (`SymplecticGeometry.Bundle.chernNumber_eq_integral_curvature`).
* The real image of the Euler class takes the cast of the value of the Euler class
  (`TauCeti.HomologicalOrientation.evalFundamentalClass_singularCohomologyRealImage`). The Euler
  class is the first Chern class
  (`SymplecticGeometry.Bundle.firstChernClass_eq_complexEulerClass`), and reversing the
  orientation negates the Chern number (`SymplecticGeometry.Bundle.chernNumber_neg_orientation`),
  so this value is minus the same Chern number.

The identity moves along a smooth map `f : B' → B` between manifolds of any dimension. The sum
`deRhamHom c₁ + e_ℝ` is natural: the real first Chern class pulls back by
`SymplecticGeometry.Bundle.realFirstChernClass_circleFiber_pullback`, `deRhamHom` commutes with
pull-backs by `TauCeti.deRhamHom_map`, the Euler class by `TauCeti.complexEulerClass_pullback`,
and the real image by `TopCat.singularCohomologyRealImage_naturality`. So the identity for `V`
gives it for `f *ᵖ V`, and conversely when `f^*` is injective on `H²(B; ℝ)`.

## Main results

* `SymplecticGeometry.Bundle.deRhamHom_realFirstChernClass_eq_neg_of_connectedSpace`: over a
  closed connected orientable surface, `deRhamHom` of the real first Chern class of the unitary
  frame bundle is minus the real image of the Euler class.
* `SymplecticGeometry.Bundle.deRhamHom_realFirstChernClass_add_realImage_pullback`: the sum of the
  two classes for `f *ᵖ V` is the pull-back along `f` of the sum for `V`.
* `SymplecticGeometry.Bundle.deRhamHom_realFirstChernClass_pullback_eq_neg`: the identity for `V`
  implies it for `f *ᵖ V`.
* `SymplecticGeometry.Bundle.deRhamHom_realFirstChernClass_eq_neg_of_pullback`: if `f^*` is
  injective in degree two, the identity for `f *ᵖ V` implies it for `V`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Theorem 2.7.4.
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (the Euler
  class of a circle bundle as the class of the curvature of an angular form).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (fundamental classes and Poincaré duality).
-/

public section

noncomputable section

open Bundle CategoryTheory Module TauCeti TauCeti.OrthonormalFrameBundle
open scoped Manifold ContDiff

namespace SymplecticGeometry

namespace Bundle

attribute [local instance] finrank_real_complex_fact'

open scoped VectorBundle.ComplexToReal

section Surface

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M] [CompactSpace M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [Fact (finrank ℂ F = 1)]
  {V : M → Type} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

variable [ContMDiffVectorBundle ∞ F V (𝓡 2)] (g : ContMDiffRiemannianMetric (𝓡 2) ∞ F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)

/-- **Chern–Weil in degree two, over a surface.** Let `M` be a closed connected orientable smooth
surface, and `V` a smooth complex line bundle over `M` with a smooth Hermitian metric `g`. Then
the de Rham homomorphism sends the real first Chern class of the circle bundle of unitary frames
of `V` to minus the real image of the Euler class of `V` in `H²(M; ℝ)`. -/
theorem deRhamHom_realFirstChernClass_eq_neg_of_connectedSpace [ConnectedSpace M]
    [Orientable (𝓡 2) M] :
    deRhamHom (𝓡 2) M 2 (g.realFirstChernClass hI) =
      -((TopCat.of M).singularCohomologyRealImage 2).hom
        (complexEulerClass (r := 0) F V Fact.out) := by
  rw [ContMDiffRiemannianMetric.realFirstChernClass_def]
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) (𝓡 2) (𝓡 1) :=
    contMDiffFiberBundle_circleFiber g hI
  have hE := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)
  obtain ⟨o⟩ := Orientable.nonempty_orientation (I := 𝓡 2) (M := M)
  rw [hE] at o
  let e := (TopCat.of M).singularCohomologyIntChainsIso ℝ 2
  -- Both sides are determined by their value on the fundamental class of `-o`.
  refine (ConcreteCategory.bijective_of_isIso e.hom).1
    (((-o).toHomologicalOrientation hE).evalFundamentalClass_id_injective hE
      (ModuleCat.of ℤ ℝ) ?_)
  obtain ⟨α, hα⟩ := exists_isCircleConnectionForm (IB := 𝓡 2) (P := Fiber ℂ F V ℂ)
  have hφ : -(2 * Real.pi)⁻¹ • hα.curvature ∈ closedForms (𝓡 2) M 2 :=
    Submodule.smul_mem _ _ hα.curvature_mem_closedForms
  have hc : realFirstChernClass (𝓡 2) (Fiber ℂ F V ℂ) =
      deRhamCohomology.mk (𝓡 2) 2 ⟨_, hφ⟩ := by
    rw [hα.realFirstChernClass_eq, ← _root_.map_smul, SetLike.mk_smul_mk]
  rw [hc]
  refine (o.evalFundamentalClass_singularCohomologyIntChainsIso_hom_deRhamHom_mk hE
    ⟨_, hφ⟩).trans ?_
  rw [map_neg, map_neg,
    HomologicalOrientation.evalFundamentalClass_singularCohomologyRealImage,
    ← firstChernClass_eq_complexEulerClass, ← chernNumber_def,
    Manifold.Orientation.toHomologicalOrientation_neg, chernNumber_neg_orientation,
    Int.cast_neg, neg_neg, chernNumber_eq_integral_curvature g hI o hα]
  exact integralTopForm_smul o _ _

end Surface

section Pullback

variable {EB HB B : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  [IB.Boundaryless] [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B]
  {EB' HB' B' : Type} [NormedAddCommGroup EB'] [NormedSpace ℝ EB'] [TopologicalSpace HB']
  {IB' : ModelWithCorners ℝ EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B']
  [IsManifold IB' ∞ B'] [IB'.Boundaryless] [FiniteDimensional ℝ EB'] [T2Space B']
  [SigmaCompactSpace B']
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [Fact (finrank ℂ F = 1)]
  {V : B → Type} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V IB] (g : ContMDiffRiemannianMetric IB ∞ F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)
  (f : C(B', B)) (hf : ContMDiff IB' IB ∞ f)
  (g'' : ContMDiffRiemannianMetric IB' ∞ F ((⇑f) *ᵖ V))
  (hI'' : ∀ x (v w : ((⇑f) *ᵖ V) x),
    g''.inner x (Complex.I • v) (Complex.I • w) = g''.inner x v w)

/-- **The Chern–Weil identity in degree two is natural under pull-back.** Let `V` be a smooth
complex line bundle over `B` with a smooth Hermitian metric `g`, let `f : B' → B` be smooth, and
let `g''` be any smooth Hermitian metric on `f *ᵖ V`. The class in `H²(B'; ℝ)` that is the sum of
the de Rham image of the real first Chern class of the unitary frame bundle of `f *ᵖ V` and of
the real image of the Euler class of `f *ᵖ V` is the pull-back along `f` of the same sum for
`V`. -/
theorem deRhamHom_realFirstChernClass_add_realImage_pullback :
    haveI := _root_.Bundle.Pullback.contMDiffVectorBundle (F := F) (E := V) hf
    (HAdd.hAdd (α := (TopCat.of B').singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) 2)
      (β := (TopCat.of B').singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) 2)
      (deRhamHom IB' B' 2 (g''.realFirstChernClass hI''))
      (((TopCat.of B').singularCohomologyRealImage 2).hom
        (complexEulerClass (r := 0) F ((⇑f) *ᵖ V) Fact.out))) =
    TopCat.singularCohomologyMap (TopCat.ofHom f) 2
    (HAdd.hAdd (α := (TopCat.of B).singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) 2)
      (β := (TopCat.of B).singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) 2)
      (deRhamHom IB B 2 (g.realFirstChernClass hI))
      (((TopCat.of B).singularCohomologyRealImage 2).hom
        (complexEulerClass (r := 0) F V Fact.out))) := by
  rw [realFirstChernClass_circleFiber_pullback g hI f hf g'' hI'', deRhamHom_map,
    complexEulerClass_pullback, TopCat.singularCohomologyRealImage_naturality_apply]
  exact (map_add _ _ _).symm


/-- **The Chern–Weil identity in degree two passes to pull-backs.** If the de Rham image of the
real first Chern class of the unitary frame bundle of `V` is minus the real image of the Euler
class of `V`, then the same holds for `f *ᵖ V` along a smooth map `f : B' → B`, with any smooth
Hermitian metric on `f *ᵖ V`. -/
theorem deRhamHom_realFirstChernClass_pullback_eq_neg
    (h : deRhamHom IB B 2 (g.realFirstChernClass hI) =
        -((TopCat.of B).singularCohomologyRealImage 2).hom
          (complexEulerClass (r := 0) F V Fact.out)) :
    haveI := _root_.Bundle.Pullback.contMDiffVectorBundle (F := F) (E := V) hf
    deRhamHom IB' B' 2 (g''.realFirstChernClass hI'') =
      -((TopCat.of B').singularCohomologyRealImage 2).hom
        (complexEulerClass (r := 0) F ((⇑f) *ᵖ V) Fact.out) := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [deRhamHom_realFirstChernClass_add_realImage_pullback g hI f hf g'' hI'', h]
  exact (congrArg _ (neg_add_cancel _)).trans (map_zero _)

/-- **The Chern–Weil identity in degree two descends along an injective pull-back.** Let
`f : B' → B` be smooth, and suppose that the pull-back `f^* : H²(B; ℝ) → H²(B'; ℝ)` is injective.
If the de Rham image of the real first Chern class of the unitary frame bundle of `f *ᵖ V` (for
some smooth Hermitian metric on it) is minus the real image of the Euler class of `f *ᵖ V`, then
the same holds for `V`. -/
theorem deRhamHom_realFirstChernClass_eq_neg_of_pullback
    (hinj : Function.Injective
      (TopCat.singularCohomologyMap (R := ModuleCat.of ℝ ℝ) (k := ℝ) (M := ModuleCat.of ℝ ℝ)
        (TopCat.ofHom f) 2))
    (h : haveI := _root_.Bundle.Pullback.contMDiffVectorBundle (F := F) (E := V) hf
      deRhamHom IB' B' 2 (g''.realFirstChernClass hI'') =
        -((TopCat.of B').singularCohomologyRealImage 2).hom
          (complexEulerClass (r := 0) F ((⇑f) *ᵖ V) Fact.out)) :
    deRhamHom IB B 2 (g.realFirstChernClass hI) =
      -((TopCat.of B).singularCohomologyRealImage 2).hom
        (complexEulerClass (r := 0) F V Fact.out) := by
  refine eq_neg_of_add_eq_zero_left (hinj ?_)
  rw [← deRhamHom_realFirstChernClass_add_realImage_pullback g hI f hf g'' hI'', map_zero]
  rw [h]
  exact neg_add_cancel _
end Pullback

end Bundle

end SymplecticGeometry

end
