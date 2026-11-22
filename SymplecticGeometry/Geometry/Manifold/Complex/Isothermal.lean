/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Analysis.Complex.Beltrami.Regularity
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Smooth isothermal charts on surfaces

Let `J` be a smooth almost complex structure on a boundaryless manifold `M` whose model space `E`
has real dimension two. This file shows that every point of `M` lies in the source of a smooth
chart `ψ : M → ℂ`, a partial diffeomorphism onto an open subset of `ℂ`, whose derivative carries
`J` to multiplication by `i` at every point of its source
(`TauCeti.SmoothAlmostComplexStructure.exists_isothermal_partialDiffeomorph`).

The chart is built as follows. The extended chart of `M` at the point, followed by a real linear
isomorphism `E ≃L[ℝ] ℂ`, is a smooth partial diffeomorphism `Φ : M → ℂ`, along which `J` pushes
forward to a smooth field of complex structures on the target of `Φ`
(`TauCeti.SmoothAlmostComplexStructure.contDiffOn_chartPushforward`). That planar field has a
smooth isothermal chart `e` at the image of the point
(`TauCeti.Beltrami.exists_smooth_isothermal_chart`, which composes with complex conjugation
where the field is not tame for the standard form), and `ψ` is `e ∘ Φ`.

This construction adapts the proof of
`TauCeti.SmoothAlmostComplexStructure.exists_isIsothermalChart` on Tau Ceti's main branch, in
`TauCeti/Geometry/Manifold/Complex/Isothermal.lean` at commit 1179cf0e10, which the pinned version
of Tau Ceti does not have: the pushforward of `J` along a chart, its smoothness and square, the
planar chart, and the equation from
`TauCeti.ContMDiffAlmostComplexStructure.mfderiv_comp_toEndomorphism`. Here the model space is any
real two-dimensional space with smooth charts, and the chart is a partial diffeomorphism.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.exists_isothermal_partialDiffeomorph`: smooth isothermal
  charts on a surface.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 4.2.6.
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix E.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **Smooth isothermal charts on a surface.** Let `J` be a smooth almost complex structure on a
boundaryless manifold `M` whose model space has real dimension two. Every point `x` of `M` lies in
the source of a smooth partial diffeomorphism `ψ : M → ℂ` whose derivative carries `J` to
multiplication by `i`: `dψ_y (J v) = i · dψ_y v` at every point `y` of its source. -/
theorem exists_isothermal_partialDiffeomorph (J : SmoothAlmostComplexStructure I M)
    (hE : Module.finrank ℝ E = 2) (x : M) :
    ∃ ψ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞, x ∈ ψ.source ∧
      ∀ y ∈ ψ.source, ∀ v : TangentSpace I y,
        mvfderiv I ψ y (J y v) = Complex.I * mvfderiv I ψ y v := by
  classical
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  -- The extended chart at `x`, followed by a real linear isomorphism `E ≃L[ℝ] ℂ`.
  let L : E ≃L[ℝ] ℂ :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hE, Complex.finrank_real_complex])
  let Φ : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞ :=
    ((chartAt H x).toPartialDiffeomorphOfMemMaximalAtlas
      (IsManifold.chart_mem_maximalAtlas x)).trans L.toDiffeomorph.toPartialDiffeomorph
  have hx : x ∈ Φ.source := by simp [Φ]
  -- `J` pushed forward along `Φ`, made a field of complex structures on all of `ℂ`.
  set A := J.chartPushforward Φ.toOpenPartialHomeomorph
  have hA (p : ℂ) (hp : p ∈ Φ.target) (w : ℂ) : A p (A p w) = -w := by
    have h := (J.toContMDiff ⊤).chartPushforward_apply_chartPushforward_apply
      Φ.toOpenPartialHomeomorph hp (Φ.mdifferentiableAt hn (Φ.map_target hp))
      (Φ.symm.mdifferentiableAt hn hp) w
    rwa [toContMDiff_chartPushforward] at h
  let K : ℂ → AlmostComplexStructure ℂ := fun p ↦
    if hp : p ∈ Φ.target then ⟨(A p).toLinearMap, LinearMap.ext (hA p hp)⟩
    else AlmostComplexStructure.ofComplexModule ℂ
  have hK (p : ℂ) (hp : p ∈ Φ.target) : K p = ⟨(A p).toLinearMap, LinearMap.ext (hA p hp)⟩ := by
    simp [K, hp]
  have hKs : ContDiffOn ℝ ∞ (fun p ↦ LinearMap.toContinuousLinearMap (K p).toLinearMap)
      Φ.target :=
    (J.contDiffOn_chartPushforward Φ.contMDiffOn Φ.symm.contMDiffOn).congr fun p hp ↦ by
      rw [hK p hp]
      exact ContinuousLinearMap.coe_injective (LinearMap.coe_toContinuousLinearMap _)
  -- A smooth planar isothermal chart for `K` at `Φ x`.
  obtain ⟨e, hxe, -, hes, hinv, hlin⟩ :=
    Beltrami.exists_smooth_isothermal_chart Φ.open_target hKs (Φ.map_source hx)
  let D : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ :=
    PartialDiffeomorph.ofOpenPartialHomeomorph e hes (e.contDiffOn_symm_of_isInvertible_fderiv
      hes hinv)
  refine ⟨Φ.trans D, by simp [D, hx, hxe], fun y hy v ↦ ?_⟩
  have hy' : y ∈ Φ.source ∧ Φ y ∈ e.source := by simpa [D] using hy
  have hc : (Φ.trans D : M → ℂ) = e ∘ Φ := by
    ext z
    simp [D]
  have hed : DifferentiableAt ℝ e (Φ y) :=
    (hes.contDiffAt (e.open_source.mem_nhds hy'.2)).differentiableAt hn
  -- The derivative of `Φ` carries `J` to `K`.
  have hJ : mfderiv I 𝓘(ℝ, ℂ) Φ y (J y v) = K (Φ y) (mfderiv I 𝓘(ℝ, ℂ) Φ y v) := by
    have h := DFunLike.congr_fun ((J.toContMDiff ⊤).mfderiv_comp_toEndomorphism
      Φ.toOpenPartialHomeomorph hy'.1 (Φ.mdifferentiableAt hn hy'.1)
      (Φ.symm.mdifferentiableAt hn (Φ.map_source hy'.1))) v
    simp only [toContMDiff_chartPushforward, toContMDiff_toEndomorphism_apply,
      Φ.toFun'_toOpenPartialHomeomorph] at h
    rw [hK _ (Φ.map_source hy'.1)]
    exact h
  rw [hc, mvfderiv_comp_apply_of_differentiableAt hed (Φ.mdifferentiableAt hn hy'.1),
    mvfderiv_comp_apply_of_differentiableAt hed (Φ.mdifferentiableAt hn hy'.1),
    mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply, hJ]
  exact hlin _ hy'.2 _

end TauCeti.SmoothAlmostComplexStructure

end
