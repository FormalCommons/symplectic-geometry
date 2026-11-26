/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Hermitian.CircleBundle
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.CircleConnection
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.CurvatureIntegral
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.StandardTransition
import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.CoordinateDisc
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.ClutchingConnection
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.Connection.Circle

/-!
# The Chern–Weil formula for circle bundles over surfaces

Here `M` is a closed smooth surface with an orientation `o`, and `V` a smooth complex line bundle
over `M` with a smooth Hermitian metric, whose unit circle bundle `P` is the principal
`Circle`-bundle of unitary frames of `V`. Connection forms on `P` are real `1`-forms
(`SymplecticGeometry.IsCircleConnectionForm`), so their curvatures are real `2`-forms on `M`. This
file proves that the first Chern number of `V` is `-(2π)⁻¹` times the integral of the curvature
of any connection form on `P`, and that over a connected `M` every `2`-form with integral
`-2π` times the Chern number is such a curvature.

The integral of the curvature does not depend on the connection form
(`SymplecticGeometry.IsCircleConnectionForm.integralTopForm_curvature_eq`), so it suffices to
compute it for one. Take unit sections over finitely many oriented coordinate discs and off their
centres, with transitions `(z / ‖z‖) ^ k i` and `∑ i, k i` the Chern number
(`SymplecticGeometry.Bundle.exists_coordinateDisc_unitSection_eq_phase_zpow_smul`), and the
connection form that they give, flat for the outer section, whose curvature reads
`-k i d(β(‖z‖) dθ)` in the `i`-th disc
(`SymplecticGeometry.exists_isCircleConnectionForm_of_collar_eq_zpow_smul`). Each disc contributes
`-2π k i` to the integral
(`SymplecticGeometry.CoordinateDisc.integralTopForm_eq_sum_of_mpullback_ofChart_eq`). The
converse follows from the statement for one connection form and
`SymplecticGeometry.IsCircleConnectionForm.exists_curvature_eq_of_integralTopForm_eq`.

## Main results

* `SymplecticGeometry.Bundle.chernNumber_eq_integral_curvature`: the Chern number is
  `-(2π)⁻¹ ∫_M F_α` for every connection form `α`.
* `SymplecticGeometry.Bundle.exists_isCircleConnectionForm_curvature_eq`: over a connected
  surface, every `2`-form with integral `-2π` times the Chern number is a curvature.
* `SymplecticGeometry.Bundle.chernNumber_eq_integral_curvature_and_exists`: the two together.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Theorem 2.7.4.
-/

public section

noncomputable section

open Bundle Module Set TauCeti TauCeti.OrthonormalFrameBundle
open scoped Manifold ContDiff Real

namespace SymplecticGeometry

namespace Bundle

attribute [local instance] finrank_real_complex_fact'

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M] [CompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [Fact (finrank ℂ F = 1)]
  {V : M → Type} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℂ F V]

open scoped VectorBundle.ComplexToReal

variable [ContMDiffVectorBundle ∞ F V (𝓡 2)] (g : ContMDiffRiemannianMetric (𝓡 2) ∞ F V)
  (hI : ∀ x (v w : V x), g.inner x (Complex.I • v) (Complex.I • w) = g.inner x v w)

/-- **The first Chern number as the integral of a curvature.** Let `M` be a closed smooth surface
with an orientation `o`, and `V` a smooth complex line bundle over `M` with a smooth Hermitian
metric `g`. For every connection form `α` on the circle bundle of unitary frames of `V`, the
first Chern number of `V`, for the homological orientation of `o`, is `-(2π)⁻¹` times the
integral over `M` of the curvature of `α`. -/
theorem chernNumber_eq_integral_curvature (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    haveI : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) (𝓡 2) (𝓡 1) :=
      contMDiffFiberBundle_circleFiber g hI
    ∀ {α : SmoothForm ((𝓡 2).prod (𝓡 1)) (ManifoldTotalSpace Circle (Fiber ℂ F V ℂ)) ℝ 1}
      (hα : IsCircleConnectionForm α),
      (chernNumber (o.toHomologicalOrientation finrank_euclideanSpace_fin)
          finrank_euclideanSpace_fin F V : ℝ) =
        -(2 * π)⁻¹ * integralTopForm o hα.curvature.val := by
  intro α hα
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) (𝓡 2) (𝓡 1) :=
    contMDiffFiberBundle_circleFiber g hI
  obtain ⟨ι, _, e, r, hr, hc, he, φ, hφe, hatlas, hdisj, k, σ, σout, hσ, hσout, hrel, hsum⟩ :=
    exists_coordinateDisc_unitSection_eq_phase_zpow_smul g hI o
  obtain rfl : φ = fun i ↦ CoordinateDisc.ofChart (e i) (hr i) (hc i) (he i) := funext hφe
  -- a smooth cut-off `β`, `0` up to `1 / 4` and `1` from `1 / 2` on
  obtain ⟨β, hβ, -, hβa, hβb, -⟩ := TauCeti.exists_contDiff_step (by norm_num : (1 / 4 : ℝ) < 1 / 2)
  obtain ⟨α₁, hα₁, hout, hpull⟩ := exists_isCircleConnectionForm_of_collar_eq_zpow_smul
    (fun i ↦ (CoordinateDisc.contMDiff_ofChart (e i) (hr i) (hc i) (he i)
      (hatlas i)).mdifferentiable (by simp))
    (fun i ↦ CoordinateDisc.contMDiffOn_coord_ofChart (e i) (hr i) (hc i) (he i) (hatlas i))
    hdisj k hσ hσout hrel hβ (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 2 : ℝ) < 1)
    hβa hβb
  have hint : integralTopForm o hα₁.curvature.val = 2 * π * ∑ i, (-(k i : ℝ)) :=
    CoordinateDisc.integralTopForm_eq_sum_of_mpullback_ofChart_eq e hr hc he
      (fun i ↦ IsManifold.maximalAtlas_subset_of_le (by simp) (hatlas i)) hdisj
      (hβ.of_le (by simp)) (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 2 : ℝ) < 2)
      hβa hβb (hα₁.curvature.isSmoothForm.of_le (by simp)) hout hpull
  rw [hα₁.integralTopForm_curvature_eq hα o, hint, ← hsum, Finset.sum_neg_distrib]
  push_cast
  field_simp

/-- **Curvatures with a given integral.** Let `M` be a closed connected smooth surface with an
orientation `o`, and `V` a smooth complex line bundle over `M` with a smooth Hermitian metric `g`.
Every smooth `2`-form on `M` whose integral is `-2π` times the first Chern number of `V`, for the
homological orientation of `o`, is the curvature of a connection form on the circle bundle of
unitary frames of `V`. -/
theorem exists_isCircleConnectionForm_curvature_eq [ConnectedSpace M]
    (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    haveI : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) (𝓡 2) (𝓡 1) :=
      contMDiffFiberBundle_circleFiber g hI
    ∀ {σ : SmoothForm (𝓡 2) M ℝ 2},
      integralTopForm o σ.val = -2 * π * chernNumber
        (o.toHomologicalOrientation finrank_euclideanSpace_fin) finrank_euclideanSpace_fin F V →
      ∃ (α : SmoothForm ((𝓡 2).prod (𝓡 1)) (ManifoldTotalSpace Circle (Fiber ℂ F V ℂ)) ℝ 1)
        (hα : IsCircleConnectionForm α), hα.curvature = σ := by
  intro σ hσ
  let : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
  let : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
  let : IsContinuousRiemannianBundle F V :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) (𝓡 2) (𝓡 1) :=
    contMDiffFiberBundle_circleFiber g hI
  obtain ⟨α₀, hα₀⟩ := exists_isCircleConnectionForm (P := Fiber ℂ F V ℂ) (IB := 𝓡 2)
  refine hα₀.exists_curvature_eq_of_integralTopForm_eq o ?_
  rw [hσ, chernNumber_eq_integral_curvature g hI o hα₀]
  field_simp

/-- **The Chern–Weil formula for circle bundles over surfaces.** Take `M` a closed smooth
surface with an orientation `o`, and `V` a smooth complex line bundle over `M` with a smooth
Hermitian metric `g`, with circle bundle `P` of unitary frames. Write `c` for the first Chern
number of `V`, for the homological orientation of `o`.

* For every connection form `α` on `P`, `c = -(2π)⁻¹ ∫_M F_α`.
* If `M` is connected, every smooth `2`-form `σ` on `M` with `∫_M σ = -2π c` is the curvature of
  a connection form on `P`.

Connection forms and curvatures are real forms here: the curvature `F_α` is `-i` times the
`iℝ`-valued curvature, so the first statement is `c = (i / 2π) ∫_M (i F_α)`.

Milestone: *Chern–Weil formula for circle bundles over surfaces*. -/
theorem chernNumber_eq_integral_curvature_and_exists (o : Manifold.Orientation (𝓡 2) M (Fin 2)) :
    letI : RiemannianBundle V := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, InnerProductSpace ℂ (V x) := g.complexInnerProductSpace hI
    letI : IsContinuousRiemannianBundle F V :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    haveI : ContMDiffFiberBundle ∞ Circle (Fiber ℂ F V ℂ) (𝓡 2) (𝓡 1) :=
      contMDiffFiberBundle_circleFiber g hI
    (∀ {α : SmoothForm ((𝓡 2).prod (𝓡 1)) (ManifoldTotalSpace Circle (Fiber ℂ F V ℂ)) ℝ 1}
      (hα : IsCircleConnectionForm α),
      (chernNumber (o.toHomologicalOrientation finrank_euclideanSpace_fin)
          finrank_euclideanSpace_fin F V : ℝ) =
        -(2 * π)⁻¹ * integralTopForm o hα.curvature.val) ∧
    (ConnectedSpace M → ∀ {σ : SmoothForm (𝓡 2) M ℝ 2},
      integralTopForm o σ.val = -2 * π * chernNumber
        (o.toHomologicalOrientation finrank_euclideanSpace_fin) finrank_euclideanSpace_fin F V →
      ∃ (α : SmoothForm ((𝓡 2).prod (𝓡 1)) (ManifoldTotalSpace Circle (Fiber ℂ F V ℂ)) ℝ 1)
        (hα : IsCircleConnectionForm α), hα.curvature = σ) :=
  ⟨chernNumber_eq_integral_curvature g hI o,
    fun _ ↦ exists_isCircleConnectionForm_curvature_eq g hI o⟩

end Bundle

end SymplecticGeometry

end
