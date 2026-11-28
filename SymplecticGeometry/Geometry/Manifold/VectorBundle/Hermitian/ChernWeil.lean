/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.RealImage
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.RealChernClass
public import TauCeti.Geometry.Manifold.Projectivization.Atlas
public import TauCeti.Geometry.Manifold.Projectivization.LineBundle
public import TauCeti.Geometry.Manifold.SmoothSingular.SingularCohomology
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
import SymplecticGeometry.Geometry.Manifold.DeRham.FundamentalClass
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.RealChernClass
import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Normalization
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.ChernWeil
import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
public import SymplecticGeometry.Geometry.Manifold.Projectivization.TwistCore
import SymplecticGeometry.Topology.ComplexProjectiveSpace.RealCohomology
import TauCeti.Geometry.Sphere.Connected
import SymplecticGeometry.Topology.VectorBundle.Pullback

/-!
# Chern–Weil in degree two

Let `V` be a smooth complex line bundle with a smooth Hermitian metric `g`, and `P` the principal
`Circle`-bundle of its unitary frames. The real first Chern class
`SymplecticGeometry.realFirstChernClass` of `P` is a de Rham class, and Tau Ceti's Euler class
`TauCeti.complexEulerClass` of `V` an integral singular class. Under the library's conventions
the de Rham homomorphism `TauCeti.deRhamHom` sends the first to **minus** the real image
(`TopCat.singularCohomologyRealImageAddMonoidHom`) of the second.

This file proves this over a closed connected orientable surface `M`. Choose an orientation `o`
of `M`. The real first Chern class is the class of `φ = -(2π)⁻¹ F_α` for a curvature `F_α`
(`SymplecticGeometry.IsCircleConnectionForm.realFirstChernClass_eq`), and `∫_o φ` is the first
Chern number for the homological orientation of `o`
(`SymplecticGeometry.Bundle.chernNumber_eq_integral_curvature`), that is, the value of the
first Chern class, which is the Euler class
(`SymplecticGeometry.Bundle.firstChernClass_eq_complexEulerClass`), on the fundamental class.
The comparison of a closed two-form with an integral class on a surface,
`TauCeti.Manifold.Orientation.deRhamHom_mk_eq_neg_realImage_of_integralTopForm_eq`, then gives
the identity.

The identity moves along a smooth map `f : B' → B` between manifolds of any dimension. The sum
`deRhamHom c₁ + e_ℝ` is natural: the real first Chern class pulls back by
`Bundle.ContMDiffRiemannianMetric.realFirstChernClass_pullback`, `deRhamHom` commutes with
pull-backs by `TauCeti.deRhamHom_map`, the Euler class by `TauCeti.complexEulerClass_pullback`,
and the real image by `TopCat.singularCohomologyRealImageAddMonoidHom_naturality`. So the
identity for `V` gives it for `f *ᵖ V`, and conversely when `f^*` is injective on `H²(B; ℝ)`.

A homotopy equivalence induces an isomorphism on singular cohomology, so the identity holds over
every manifold `B` that receives a homotopy equivalence from a closed connected orientable surface
whose forward map is smooth: pull `V` back to the surface, give the pull-back a Hermitian metric
(`TauCeti.exists_contMDiffRiemannianMetric_inner_smul_I`) and descend. The projective line
`ℂP¹`, modelled on `Fin 1 → ℂ`, is such a manifold, through the analytic diffeomorphism
`SymplecticGeometry.sphereToProjectiveLine` from the unit sphere of `ℝ³`.

Over `ℂPᴺ = ℙ ℂ (Fin (N + 1) → ℂ)` with `N ≥ 1`, the map induced by the coordinate inclusion
`ℂ² → ℂᴺ⁺¹` (`Function.ExtendByZero.linearMap` of `Fin.castLE`) is injective on `H²(-; ℝ)`
(`Projectivization.injective_singularCohomologyMap_map_real`), so the identity for every smooth
complex line bundle over `ℂPᴺ` descends from the projective line; for `N = 0` the base is a point
and both sides vanish (`Projectivization.isZero_singularCohomology_of_finrank_eq_one`). Applied
to `𝒪(1) = Projectivization.twistCore 1` and pulled back along a smooth map `f : B' → ℂPᴺ`,
it gives the identity for `f^* 𝒪(1)`, with any smooth Hermitian metric.

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
* `SymplecticGeometry.Bundle.deRhamHom_realFirstChernClass_eq_neg_of_homotopyEquiv`: the
  identity over a manifold that receives a homotopy equivalence with smooth forward map from a
  closed connected orientable surface.
* `SymplecticGeometry.Bundle.deRhamHom_realFirstChernClass_eq_neg_projectiveLine`: the identity
  over `ℂP¹ = ℙ ℂ (Fin 2 → ℂ)`.
* `SymplecticGeometry.Bundle.deRhamHom_realFirstChernClass_eq_neg_projectiveSpace`: the identity
  over `ℂPᴺ = ℙ ℂ (Fin (N + 1) → ℂ)`.
* `SymplecticGeometry.Bundle.deRhamHom_realFirstChernClass_eq_neg`: the identity for the
  pull-back of `𝒪(1)` along any smooth map `B' → ℙ ℂ (Fin (N + 1) → ℂ)`, with any Hermitian
  metric. On a compact manifold these bundles realize every integral class of degree two
  (`SymplecticGeometry.exists_hermitianLineBundle_complexEulerClass_eq`).

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

open scoped ContMDiffHermitianMetric in
/-- **Chern–Weil in degree two, over a surface.** Let `M` be a closed connected orientable smooth
surface, and `V` a smooth complex line bundle over `M` with a smooth Hermitian metric `g`. Then
the de Rham homomorphism sends the real first Chern class of the circle bundle of unitary frames
of `V` to minus the real image of the Euler class of `V` in `H²(M; ℝ)`. -/
theorem deRhamHom_realFirstChernClass_eq_neg_of_connectedSpace [ConnectedSpace M]
    [Orientable (𝓡 2) M] :
    deRhamHom (𝓡 2) M 2 (g.realFirstChernClass hI) =
      -(TopCat.of M).singularCohomologyRealImageAddMonoidHom 2
        (complexEulerClass (r := 0) F V Fact.out) := by
  rw [ContMDiffRiemannianMetric.realFirstChernClass_def]
  let : ContMDiffHermitianMetric (𝓡 2) ∞ F V := ⟨g, hI⟩
  have hE := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)
  obtain ⟨o⟩ := Orientable.nonempty_orientation (I := 𝓡 2) (M := M)
  rw [hE] at o
  obtain ⟨α, hα⟩ := exists_isCircleConnectionForm (IB := 𝓡 2) (P := Fiber ℂ F V ℂ)
  have hφ : -(2 * Real.pi)⁻¹ • hα.curvature ∈ closedForms (𝓡 2) M 2 :=
    Submodule.smul_mem _ _ hα.curvature_mem_closedForms
  have hc : realFirstChernClass (𝓡 2) (Fiber ℂ F V ℂ) =
      deRhamCohomology.mk (𝓡 2) 2 ⟨_, hφ⟩ := by
    rw [hα.realFirstChernClass_eq, ← _root_.map_smul, SetLike.mk_smul_mk]
  rw [hc]
  refine Manifold.Orientation.deRhamHom_mk_eq_neg_realImage_of_integralTopForm_eq hE o
    ⟨_, hφ⟩ _ ?_
  rw [← firstChernClass_eq_complexEulerClass, ← chernNumber_def,
    chernNumber_eq_integral_curvature g hI o hα]
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
    deRhamHom IB' B' 2 (g''.realFirstChernClass hI'') +
        (TopCat.of B').singularCohomologyRealImageAddMonoidHom 2
          (complexEulerClass (r := 0) F ((⇑f) *ᵖ V) Fact.out) =
      TopCat.singularCohomologyMap (TopCat.ofHom f) 2
        (deRhamHom IB B 2 (g.realFirstChernClass hI) +
          (TopCat.of B).singularCohomologyRealImageAddMonoidHom 2
            (complexEulerClass (r := 0) F V Fact.out)) := by
  rw [g.realFirstChernClass_pullback hI f hf g'' hI'', deRhamHom_map,
    complexEulerClass_pullback, TopCat.singularCohomologyRealImageAddMonoidHom_naturality]
  exact (map_add _ _ _).symm


/-- **The Chern–Weil identity in degree two passes to pull-backs.** If the de Rham image of the
real first Chern class of the unitary frame bundle of `V` is minus the real image of the Euler
class of `V`, then the same holds for `f *ᵖ V` along a smooth map `f : B' → B`, with any smooth
Hermitian metric on `f *ᵖ V`. -/
theorem deRhamHom_realFirstChernClass_pullback_eq_neg
    (h : deRhamHom IB B 2 (g.realFirstChernClass hI) =
        -(TopCat.of B).singularCohomologyRealImageAddMonoidHom 2
          (complexEulerClass (r := 0) F V Fact.out)) :
    haveI := _root_.Bundle.Pullback.contMDiffVectorBundle (F := F) (E := V) hf
    deRhamHom IB' B' 2 (g''.realFirstChernClass hI'') =
      -(TopCat.of B').singularCohomologyRealImageAddMonoidHom 2
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
        -(TopCat.of B').singularCohomologyRealImageAddMonoidHom 2
          (complexEulerClass (r := 0) F ((⇑f) *ᵖ V) Fact.out)) :
    deRhamHom IB B 2 (g.realFirstChernClass hI) =
      -(TopCat.of B).singularCohomologyRealImageAddMonoidHom 2
        (complexEulerClass (r := 0) F V Fact.out) := by
  refine eq_neg_of_add_eq_zero_left (hinj ?_)
  rw [← deRhamHom_realFirstChernClass_add_realImage_pullback g hI f hf g'' hI'', map_zero]
  rw [h]
  exact neg_add_cancel _

/-- **Chern–Weil in degree two, over a manifold homotopy equivalent to a surface.** Let `M` be
a closed connected orientable smooth surface and `φ : M ≃ₕ B` a homotopy equivalence whose
forward map `M → B` is smooth. For every smooth complex line bundle `V` over `B` with a
smooth Hermitian metric `g`, the de Rham homomorphism sends the real first Chern class of the
circle bundle of unitary frames of `V` to minus the real image of the Euler class of `V` in
`H²(B; ℝ)`. -/
theorem deRhamHom_realFirstChernClass_eq_neg_of_homotopyEquiv {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [Orientable (𝓡 2) M]
    (φ : ContinuousMap.HomotopyEquiv M B) (hφ : ContMDiff (𝓡 2) IB ∞ φ.toFun) :
    deRhamHom IB B 2 (g.realFirstChernClass hI) =
      -(TopCat.of B).singularCohomologyRealImageAddMonoidHom 2
        (complexEulerClass (r := 0) F V Fact.out) := by
  have : ∀ b, ContinuousSMul ℂ (V b) := VectorBundle.continuousSMul ℂ F V
  let f : C(M, B) := φ.toFun
  have : ContMDiffVectorBundle ∞ F ((⇑f) *ᵖ V) (𝓡 2) :=
    _root_.Bundle.Pullback.contMDiffVectorBundle (F := F) (E := V) hφ
  obtain ⟨g'', hI''⟩ := exists_contMDiffRiemannianMetric_inner_smul_I (IB := 𝓡 2) (n := ⊤)
    (F := F) (V := (⇑f) *ᵖ V)
  have := φ.isIso_singularCohomologyMap (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) 2
  exact deRhamHom_realFirstChernClass_eq_neg_of_pullback g hI f hφ g'' hI''
    (ConcreteCategory.bijective_of_isIso _).1
    (deRhamHom_realFirstChernClass_eq_neg_of_connectedSpace g'' hI'')

end Pullback

section ProjectiveLine

open scoped LinearAlgebra.Projectivization

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [Fact (finrank ℂ F = 1)]
  {V : ℙ ℂ (Fin 2 → ℂ) → Type} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, Fin 1 → ℂ)]
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, Fin 1 → ℂ) ∞ F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)

/-- **Chern–Weil in degree two, over the projective line.** For every smooth complex line bundle
`V` over `ℂP¹ = ℙ ℂ (Fin 2 → ℂ)` with a smooth Hermitian metric `g`, the de Rham homomorphism
sends the real first Chern class of the circle bundle of unitary frames of `V` to minus the real
image of the Euler class of `V` in `H²(ℂP¹; ℝ)`. -/
theorem deRhamHom_realFirstChernClass_eq_neg_projectiveLine :
    deRhamHom 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ)) 2 (g.realFirstChernClass hI) =
      -(TopCat.of (ℙ ℂ (Fin 2 → ℂ))).singularCohomologyRealImageAddMonoidHom 2
        (complexEulerClass (r := 0) F V Fact.out) := by
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have := connectedSpace_euclideanSphere (ι := Fin 3) (by simp)
  have := orientable_sphere (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
  exact deRhamHom_realFirstChernClass_eq_neg_of_homotopyEquiv g hI
    sphereToProjectiveLine.toHomeomorph.toHomotopyEquiv
    (sphereToProjectiveLine.contMDiff.of_le le_top)

end ProjectiveLine

section ProjectiveSpace

open scoped LinearAlgebra.Projectivization

variable {N : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [Fact (finrank ℂ F = 1)]
  {V : ℙ ℂ (Fin (N + 1) → ℂ) → Type} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, Fin N → ℂ)]
  (g : ContMDiffRiemannianMetric 𝓘(ℝ, Fin N → ℂ) ∞ F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)

/-- **Chern–Weil in degree two, over complex projective space.** For every smooth complex line
bundle `V` over `ℙ ℂ (Fin (N + 1) → ℂ)` with a smooth Hermitian metric `g`, the de Rham
homomorphism sends the real first Chern class of the circle bundle of unitary frames of `V` to
minus the real image of the Euler class of `V`. -/
theorem deRhamHom_realFirstChernClass_eq_neg_projectiveSpace :
    deRhamHom 𝓘(ℝ, Fin N → ℂ) (ℙ ℂ (Fin (N + 1) → ℂ)) 2 (g.realFirstChernClass hI) =
      -(TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))).singularCohomologyRealImageAddMonoidHom 2
        (complexEulerClass (r := 0) F V Fact.out) := by
  rcases N with _ | n
  · -- `ℙ ℂ (Fin 1 → ℂ)` is a point, so its second cohomology vanishes.
    exact (ModuleCat.subsingleton_of_isZero
      (Projectivization.isZero_singularCohomology_of_finrank_eq_one (ModuleCat.of ℝ ℝ) ℝ
        (ModuleCat.of ℝ ℝ) (K := ℂ) (E := Fin (0 + 1) → ℂ) (by simp) two_ne_zero)).elim _ _
  · -- Restrict to a projective line, where the identity holds and `H²(-; ℝ)` injects.
    have : ∀ b, ContinuousSMul ℂ (V b) := VectorBundle.continuousSMul ℂ F V
    let ι := Function.ExtendByZero.linearMap ℂ ℂ
      (Fin.castLE (by omega) : Fin 2 → Fin (n + 1 + 1))
    have hι : Function.Injective ι := Function.extend_injective (Fin.castLE_injective _) 0
    let f : C(ℙ ℂ (Fin 2 → ℂ), ℙ ℂ (Fin (n + 1 + 1) → ℂ)) :=
      Projectivization.mapContinuousMap ι hι
    have hf : ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ f :=
      Projectivization.contMDiff_map_restrictScalars ι hι ∞
    have := _root_.Bundle.Pullback.contMDiffVectorBundle (F := F) (E := V) hf
    obtain ⟨g'', hI''⟩ := exists_contMDiffRiemannianMetric_inner_smul_I
      (IB := 𝓘(ℝ, Fin 1 → ℂ)) (n := ⊤) (F := F) (V := (⇑f) *ᵖ V)
    exact deRhamHom_realFirstChernClass_eq_neg_of_pullback g hI f hf g'' hI''
      (Projectivization.injective_singularCohomologyMap_map_real ι hι (n := 1) (by simp)
        one_ne_zero)
      (deRhamHom_realFirstChernClass_eq_neg_projectiveLine g'' hI'')

end ProjectiveSpace

section TwistCore

open scoped LinearAlgebra.Projectivization
open Projectivization (twistCore)

variable {EB' HB' B' : Type} [NormedAddCommGroup EB'] [NormedSpace ℝ EB'] [TopologicalSpace HB']
  {IB' : ModelWithCorners ℝ EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B']
  [IsManifold IB' ∞ B'] [IB'.Boundaryless] [FiniteDimensional ℝ EB'] [T2Space B']
  [SigmaCompactSpace B']

/-- **Chern–Weil in degree two.** Let `f : B' → ℙ ℂ (Fin (N + 1) → ℂ)` be a smooth map and `g` a
smooth Hermitian metric on the pull-back `f^* 𝒪(1)` of Tau Ceti's line bundle
`Projectivization.twistCore 1`. Then the de Rham homomorphism sends the real first Chern class of
the circle bundle of unitary frames of `f^* 𝒪(1)` to minus the real image of its Euler class in
`H²(B'; ℝ)`. -/
theorem deRhamHom_realFirstChernClass_eq_neg {N : ℕ} (f : C(B', ℙ ℂ (Fin (N + 1) → ℂ)))
    (hf : ContMDiff IB' 𝓘(ℝ, Fin N → ℂ) ∞ f)
    (g : ContMDiffRiemannianMetric IB' ∞ ℂ ((⇑f) *ᵖ (twistCore (𝕜 := ℂ) (n := N) 1).Fiber))
    (hI : ∀ x v w, g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w) :
    haveI := _root_.Bundle.Pullback.contMDiffVectorBundle (F := ℂ)
      (E := (twistCore (𝕜 := ℂ) (n := N) 1).Fiber) hf
    deRhamHom IB' B' 2 (g.realFirstChernClass hI) =
      -(TopCat.of B').singularCohomologyRealImageAddMonoidHom 2
        (complexEulerClass (r := 0) ℂ ((⇑f) *ᵖ (twistCore (𝕜 := ℂ) (n := N) 1).Fiber)
          (finrank_self ℂ)) := by
  obtain ⟨g₀, hI₀⟩ := exists_contMDiffRiemannianMetric_inner_smul_I
    (IB := 𝓘(ℝ, Fin N → ℂ)) (n := ⊤) (F := ℂ) (V := (twistCore (𝕜 := ℂ) (n := N) 1).Fiber)
  exact deRhamHom_realFirstChernClass_pullback_eq_neg g₀ hI₀ f hf g hI
    (deRhamHom_realFirstChernClass_eq_neg_projectiveSpace g₀ hI₀)

end TwistCore

end Bundle

end SymplecticGeometry

end
