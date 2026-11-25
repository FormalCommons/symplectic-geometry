/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Conformal
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import SymplecticGeometry.Geometry.Manifold.Complex.Integrable
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Riemannian.Orientation.Rotation
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Analysis.InnerProductSpace.TwoDim
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import TauCeti.Analysis.Complex.Beltrami.Isothermal
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Orientation.AlmostComplex

/-!
# Smooth isothermal charts on surfaces, and integrability in dimension two

Let `J` be a smooth almost complex structure on a boundaryless manifold `M` whose model space `E`
has real dimension two. This file shows that every point of `M` lies in the source of a smooth
chart `ψ : M → ℂ`, a partial diffeomorphism onto an open subset of `ℂ`, whose derivative carries
`J` to multiplication by `i` at every point of its source: it is pseudoholomorphic there from `J`
to `ofComplexManifold ℂ ℂ`, in the sense of Tau Ceti's `TauCeti.IsPseudoholomorphicAt`
(`TauCeti.SmoothAlmostComplexStructure.exists_isothermal_partialDiffeomorph`). These charts make `J`
integrable (`TauCeti.SmoothAlmostComplexStructure.isIntegrable_of_finrank_eq_two`), by
`TauCeti.SmoothAlmostComplexStructure.isIntegrable_of_forall_exists_partialDiffeomorph`, which
accepts charts into `ℂ` in place of the model `E`.

On an oriented surface with a smooth Riemannian metric, Tau Ceti's
`TauCeti.Manifold.Orientation.rightAngleAlmostComplexStructure` turns each oriented tangent plane
by a right angle. Its isothermal charts are isothermal coordinates of the metric: their
derivatives are conformal
(`TauCeti.Manifold.Orientation.exists_isothermal_coordinates`), by the pointwise
`Orientation.isConformalMap_of_map_rightAngleRotation`.

The isothermal chart is built as follows. The extended chart of `M` at the point, followed by a
real linear isomorphism `E ≃L[ℝ] ℂ`, is a smooth partial diffeomorphism `Φ : M → ℂ`, along which
`J` pushes forward to a smooth field of operators squaring to `-1` on the target of `Φ`
(`TauCeti.SmoothAlmostComplexStructure.contDiffOn_chartPushforward`). That planar field has a
smooth isothermal chart `e` at the image of the point
(`TauCeti.Beltrami.exists_centered_smooth_isothermal_chart`), with smooth inverse, and `ψ` is
`e ∘ Φ`.

This construction adapts the proofs of Tau Ceti's private
`TauCeti.SmoothAlmostComplexStructure.exists_smooth_isIsothermalChart` and
`TauCeti.isIsothermalChart_trans_of_fderiv_comp`, in Tau Ceti's
`TauCeti/Geometry/Manifold/Complex/Isothermal.lean`: the pushforward of `J` along a chart, its
smoothness and square, the smooth planar chart on the target of the chart, and the equation from
`TauCeti.ContMDiffAlmostComplexStructure.mfderiv_comp_toEndomorphism`. Here the model space is any
real two-dimensional space with smooth charts, and the chart is a partial diffeomorphism.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.exists_isothermal_partialDiffeomorph`: smooth isothermal
  charts on a surface.
* `TauCeti.SmoothAlmostComplexStructure.isIntegrable_of_finrank_eq_two`: integrability of every
  smooth almost complex structure on a surface.
* `TauCeti.Manifold.Orientation.exists_isothermal_coordinates`: isothermal coordinates for a
  Riemannian metric on an oriented surface.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 4.2.6 and Exercise 4.2.8.
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix E.
-/

public section

open Set Bundle
open scoped ContDiff Manifold

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **Smooth isothermal charts on a surface.** Let `J` be a smooth almost complex structure on a
boundaryless manifold `M` whose model space has real dimension two. Every point `x` of `M` lies in
the source of a smooth partial diffeomorphism `ψ : M → ℂ` that is pseudoholomorphic from `J` to
multiplication by `i` at every point `y` of its source: `dψ_y (J v) = i · dψ_y v`. -/
theorem exists_isothermal_partialDiffeomorph (J : SmoothAlmostComplexStructure I M)
    (hE : Module.finrank ℝ E = 2) (x : M) :
    ∃ ψ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞, x ∈ ψ.source ∧
      ∀ y ∈ ψ.source, IsPseudoholomorphicAt J (ofComplexManifold ℂ ℂ) ψ y := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  -- The extended chart at `x`, followed by a real linear isomorphism `E ≃L[ℝ] ℂ`.
  let L : E ≃L[ℝ] ℂ :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hE, Complex.finrank_real_complex])
  let Φ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞ :=
    ((chartAt H x).toPartialDiffeomorphOfMemMaximalAtlas
      (IsManifold.chart_mem_maximalAtlas x)).trans L.toDiffeomorph.toPartialDiffeomorph
  have hx : x ∈ Φ.source := by simp [Φ]
  -- `J` pushed forward along `Φ`, a smooth field of operators squaring to `-1` on `Φ.target`.
  set A := J.chartPushforward Φ.toOpenPartialHomeomorph
  have hA (p : ℂ) (hp : p ∈ Φ.target) (w : ℂ) : A p (A p w) = -w :=
    J.chartPushforward_apply_chartPushforward_apply Φ hp w
  -- A smooth planar isothermal chart for `A` at `Φ x`.
  obtain ⟨e, hxe, -, -, hes, hesymm, hlin⟩ :=
    Beltrami.exists_centered_smooth_isothermal_chart
      (J.contDiffOn_chartPushforward Φ.contMDiffOn Φ.symm.contMDiffOn) Φ.open_target
      (Φ.map_source hx) fun p hp ↦ hA p hp
  let D : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ :=
    PartialDiffeomorph.ofOpenPartialHomeomorph e hes hesymm
  refine ⟨Φ.trans D, by simp [D, hx, hxe], fun y hy ↦
    isPseudoholomorphicAt_iff_mfderiv.2 ⟨(Φ.trans D).mdifferentiableAt hn hy, fun v ↦ ?_⟩⟩
  have hy' : y ∈ Φ.source ∧ Φ y ∈ e.source := by simpa [D] using hy
  have hc : (Φ.trans D : M → ℂ) = e ∘ Φ := by
    ext z
    simp [D]
  have hed : DifferentiableAt ℝ e (Φ y) :=
    (hes.contDiffAt (e.open_source.mem_nhds hy'.2)).differentiableAt hn
  -- The derivative of `Φ` carries `J` to `A`.
  have hJ : mfderiv I 𝓘(ℝ, ℂ) Φ y (J y v) = A (Φ y) (mfderiv I 𝓘(ℝ, ℂ) Φ y v) :=
    J.mfderiv_apply_eq_chartPushforward_apply Φ hy'.1 v
  refine Eq.trans ?_
    ((ofComplexManifold_apply (E := ℂ) _ _).trans (smul_eq_mul (α := ℂ) _ _)).symm
  rw [← mvfderiv_apply_eq_mfderiv_apply, ← mvfderiv_apply_eq_mfderiv_apply, hc,
    mvfderiv_comp_apply_of_differentiableAt hed (Φ.mdifferentiableAt hn hy'.1),
    mvfderiv_comp_apply_of_differentiableAt hed (Φ.mdifferentiableAt hn hy'.1),
    mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply, hJ]
  exact hlin _ hy'.2 _

/-- **Integrability in real dimension two.** Every smooth almost complex
structure on a boundaryless manifold whose model space has real dimension two is integrable.

Milestone: *Integrability of almost complex structures on surfaces*. -/
theorem isIntegrable_of_finrank_eq_two (J : SmoothAlmostComplexStructure I M)
    (hE : Module.finrank ℝ E = 2) : J.IsIntegrable := by
  refine J.isIntegrable_of_forall_exists_partialDiffeomorph (G := ℂ) fun x ↦ ?_
  obtain ⟨ψ, hx, hψ⟩ := J.exists_isothermal_partialDiffeomorph hE x
  exact ⟨ψ, AlmostComplexStructure.ofComplexModule ℂ, hx, fun y hy v ↦
    ((hψ y hy).mfderiv_apply_commute v).trans (ofComplexManifold_apply_eq_ofComplexModule _ _)⟩

end TauCeti.SmoothAlmostComplexStructure

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Isothermal coordinates.** On a boundaryless oriented surface with a smooth Riemannian
metric, every point `x` lies in the source of a smooth partial diffeomorphism `ψ : M → ℂ` whose
derivative is conformal at every point of its source: it multiplies the metric by a positive
factor (`isConformalMap_iff`), so that in the coordinate `ψ` the metric is a positive multiple of
the Euclidean one.

Milestone: *Integrability of almost complex structures on surfaces*. -/
theorem exists_isothermal_coordinates [I.Boundaryless] (o : Manifold.Orientation I M (Fin 2))
    (x : M) : ∃ ψ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞, x ∈ ψ.source ∧
      ∀ y ∈ ψ.source, IsConformalMap (mvfderiv I ψ y) := by
  have hE : Module.finrank ℝ E = 2 := (o.fact_finrank_tangentSpace x).out
  obtain ⟨ψ, hx, hψ⟩ :=
    o.rightAngleAlmostComplexStructure.exists_isothermal_partialDiffeomorph hE x
  refine ⟨ψ, hx, fun y hy ↦ ?_⟩
  let := o.fact_finrank_tangentSpace y
  refine (o.orientationAt y).isConformalMap_of_map_rightAngleRotation (fun v ↦ ?_) ?_
  · rw [← rightAngleAlmostComplexStructure_apply, mvfderiv_apply_eq_mfderiv_apply,
      mvfderiv_apply_eq_mfderiv_apply]
    exact ((hψ y hy).mfderiv_apply_commute v).trans
      (SmoothAlmostComplexStructure.ofComplexManifold_apply (E := ℂ) _ _)
  · -- The derivative of a partial diffeomorphism is injective, and the tangent plane is not zero.
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
    exact mvfderiv_eq_zero_iff.not.2
      (TauCeti.mfderiv_ne_zero_of_injective (ψ.isInvertible_mfderiv (by simp) hy).injective)

end TauCeti.Manifold.Orientation

end
