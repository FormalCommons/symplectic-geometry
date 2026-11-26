/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.CircleBundle
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.RealChernClass

/-!
# The real first Chern class of a Hermitian line bundle

Let `V` be a smooth complex line bundle over a finite-dimensional, boundaryless, Hausdorff,
σ-compact manifold `B`. A smooth `i`-invariant metric `g` on `V` makes it a Hermitian line bundle,
whose unitary frames form the smooth principal `Circle`-bundle
`SymplecticGeometry.Bundle.contMDiffFiberBundle_circleFiber`; it has a real first Chern class
`SymplecticGeometry.realFirstChernClass`. This file shows that this class does not depend on `g`
(`SymplecticGeometry.Bundle.realFirstChernClass_circleFiber_eq`).

For a second such metric `g'`, sending a `g`-unitary frame `φ` to the `g'`-unitary frame
`normalizedFrame (φ 1)`, whose unit vector is `φ 1 / ‖φ 1‖_{g'}`, is a smooth map of the two
circle bundles over the identity of `B` (by `SymplecticGeometry.Bundle.contMDiffOn_circleFiber_iff`
and `SymplecticGeometry.Bundle.contMDiffOn_normalizedFrame`) that commutes with the action of
`Circle` (`SymplecticGeometry.Bundle.normalizedFrame_circle_smul`). So the naturality of the real
first Chern class, `SymplecticGeometry.realFirstChernClass_map`, applies.

## Main results

* `SymplecticGeometry.Bundle.realFirstChernClass_circleFiber_eq`: the real first Chern classes of
  the unitary frame bundles of two smooth Hermitian metrics on a complex line bundle are equal.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (Chern classes of Hermitian line bundles, computed with a metric).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter II, §6 (mappings of connections).
-/

public section

noncomputable section

open Bundle MulOpposite Module TauCeti TauCeti.OrthonormalFrameBundle
open scoped Manifold ContDiff

namespace SymplecticGeometry.Bundle

variable {EB HB B F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  [IB.Boundaryless] [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [Fact (finrank ℂ F = 1)]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

attribute [local instance] finrank_real_complex_fact'

open scoped VectorBundle.ComplexToReal Module.ComplexToReal

variable [ContMDiffVectorBundle ∞ F V IB]

variable (g : ContMDiffRiemannianMetric IB ∞ F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)

/-- Let `Q` be a smooth principal `Circle`-bundle over `B` with a smooth map `σ` from its total
space to the nonzero vectors of a smooth complex line bundle `V`, over the identity of `B`, that
commutes with the actions of `Circle`. Then the real first Chern class of `Q` is that of the
unitary frame bundle of any smooth Hermitian metric `g` on `V`. -/
theorem realFirstChernClass_eq_circleFiber {Q : B → Type*}
    [TopologicalSpace (TotalSpace Circle Q)] [∀ x, TopologicalSpace (Q x)] [FiberBundle Circle Q]
    [∀ x, MulAction Circleᵐᵒᵖ (Q x)] [PrincipalBundle Circle Q]
    [ContMDiffFiberBundle ∞ Circle Q IB (𝓡 1)] (σ : ∀ x, Q x → V x)
    (hσ : ContMDiff (IB.prod (𝓡 1)) (IB.prod 𝓘(ℝ, F)) ∞ fun q : ManifoldTotalSpace Circle Q ↦
      (⟨((ManifoldTotalSpace.homeomorph _ _).symm q).proj,
        σ _ ((ManifoldTotalSpace.homeomorph _ _).symm q).snd⟩ : TotalSpace F V))
    (hσ₀ : ∀ x q, σ x q ≠ 0) (hσz : ∀ (z : Circle) x (q : Q x), σ x (op z • q) = (z : ℂ) • σ x q) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    haveI : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) IB (𝓡 1) :=
      contMDiffFiberBundle_circleFiber g hI
    realFirstChernClass IB Q = realFirstChernClass IB (Fiber ℂ F V ℂ) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) IB (𝓡 1) :=
    contMDiffFiberBundle_circleFiber g hI
  let Φ := ManifoldTotalSpace.fiberwiseMap (F := Circle)
    fun x (q : Q x) ↦ normalizedFrame (F := F) (σ x q)
  have hΦ : ContMDiff (IB.prod (𝓡 1)) (IB.prod (𝓡 1)) ∞ Φ := by
    rw [← contMDiffOn_univ]
    exact (contMDiffOn_normalizedFrame g hI isOpen_univ hσ.contMDiffOn
      fun q _ ↦ hσ₀ _ _).congr fun q _ ↦ congrFun (ManifoldTotalSpace.fiberwiseMap_eq _) q
  have hΦz (z : Circle) (q : ManifoldTotalSpace Circle Q) : Φ (op z • q) = op z • Φ q := by
    obtain ⟨p, rfl⟩ := (ManifoldTotalSpace.homeomorph Circle Q).surjective q
    simp only [Φ, ManifoldTotalSpace.smul_homeomorph, ManifoldTotalSpace.fiberwiseMap_homeomorph,
      hσz, normalizedFrame_circle_smul z (hσ₀ _ _)]
  rw [realFirstChernClass_map contMDiff_id hΦ hΦz (funext fun q ↦ by simp [Φ]),
    deRhamCohomology.map_id, LinearMap.id_apply]

/-- **The real first Chern class of a Hermitian line bundle does not depend on the metric.** For
two smooth `i`-invariant metrics `g` and `g'` on a smooth complex line bundle `V`, the real first
Chern classes of the smooth principal `Circle`-bundles of `g`-unitary and of `g'`-unitary frames
of `V` are equal. -/
theorem realFirstChernClass_circleFiber_eq (g' : ContMDiffRiemannianMetric IB ∞ F V)
    (hI' : ∀ x (v w : V x), g'.inner x (Complex.I • v) (Complex.I • w) = g'.inner x v w) :
    (letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
     letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
     letI : IsContinuousRiemannianBundle F V :=
       instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
     haveI : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) IB (𝓡 1) :=
       contMDiffFiberBundle_circleFiber g hI
     realFirstChernClass IB (Fiber ℂ F V ℂ)) =
    (letI : RiemannianBundle V := ⟨g'.toRiemannianMetric⟩
     letI : ∀ x, InnerProductSpace ℂ (V x) := g'.complexInnerProductSpace hI'
     letI : IsContinuousRiemannianBundle F V :=
       instIsContinuousRiemannianBundle g'.toContinuousRiemannianMetric
     haveI : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) IB (𝓡 1) :=
       contMDiffFiberBundle_circleFiber g' hI'
     realFirstChernClass IB (Fiber ℂ F V ℂ)) := by
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) IB (𝓡 1) :=
    contMDiffFiberBundle_circleFiber g hI
  refine realFirstChernClass_eq_circleFiber g' hI' (Q := Fiber ℂ F V ℂ) (fun _ φ ↦ φ.frame 1)
    ?_ (fun _ φ ↦ ?_) fun z _ φ ↦ ?_
  · rw [← contMDiffOn_univ]
    exact (contMDiffOn_circleFiber_iff g hI isOpen_univ _).1 (contMDiffOn_id.congr fun q _ ↦
      (ManifoldTotalSpace.homeomorph _ _).apply_symm_apply q)
  · exact φ.frame.map_ne_zero_iff.2 one_ne_zero
  · rw [Fiber.frame_op_circle_smul_apply, mul_one, ← _root_.map_smul, smul_eq_mul, mul_one]

end SymplecticGeometry.Bundle
