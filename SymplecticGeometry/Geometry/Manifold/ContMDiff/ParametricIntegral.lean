/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Basic
public import TauCeti.Geometry.Manifold.ModelTransport.Interior
public import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# Integrals over a compact manifold of parameters, on a boundaryless manifold

Tau Ceti's `ContMDiff.parametric_integral` says that `x ↦ ∫ a, f x a ∂μ` is `C^n` when
`(x, a) ↦ f x a` is, for a finite measure `μ` on a compact manifold `N`, and asks the model of
`M` to have no boundary (`[I.Boundaryless]`). This file proves the same for a boundaryless
manifold `M` (`[BoundarylessManifold I M]`), whose model may have boundary.

## Main results

* `ContMDiff.parametric_integral_of_boundarylessManifold`: the integral over a compact manifold
  of parameters of a `C^n` function on `M × N` is `C^n` on a boundaryless manifold `M`.

For `n = 0` the claim is continuity, which needs no hypothesis on the boundary: integration
against a finite measure on a compact space is continuous on `C(N, F)` for the uniform norm
(`TauCeti.continuous_integral_continuousMap`). For `n ≠ 0`, `M` is a `C¹` manifold, and the
function is carried along the identity diffeomorphism
`TauCeti.BoundarylessModel.interiorDiffeomorph` to the copy `TauCeti.BoundarylessModel I M`
with charts in the model vector space, where Tau Ceti's lemma applies.
-/

public section

open Function MeasureTheory TauCeti
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [MeasurableSpace N] [OpensMeasurableSpace N]
  {μ : Measure N}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [T2Space N] {n : ℕ∞} [IsManifold I n M] [IsManifold J n N]

attribute [local instance] BoundarylessModel.interiorChartedSpace in
/-- **Smoothness of an integral over a compact manifold of parameters, on a boundaryless
manifold.** Let `M` be a boundaryless manifold, whose model may have boundary, and let `μ` be a
finite measure on a compact manifold `N`. If `(x, a) ↦ f x a` is `C^n` on `M × N`, then
`x ↦ ∫ a, f x a ∂μ` is `C^n` on `M`. -/
theorem ContMDiff.parametric_integral_of_boundarylessManifold [BoundarylessManifold I M]
    [CompactSpace N] [IsFiniteMeasure μ] {f : M → N → F}
    (hf : ContMDiff (I.prod J) 𝓘(ℝ, F) n (uncurry f)) :
    ContMDiff I 𝓘(ℝ, F) n (fun x ↦ ∫ a, f x a ∂μ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [WithTop.coe_zero, contMDiff_zero_iff] at hf ⊢
    -- `x ↦ f x` is continuous into `C(N, F)` with the uniform norm.
    let φ : C(M × N, F) := ⟨uncurry f, hf⟩
    exact continuous_integral_continuousMap.comp φ.curry.continuous
  -- Otherwise `M` is a `C¹` manifold: carry `f` to the copy of `M` with charts in `E`.
  have : IsManifold I 1 M := .of_le (n := n) (by exact_mod_cast Order.one_le_iff_ne_zero.2 hn)
  let Φ := BoundarylessModel.interiorDiffeomorph I (M := M) n
  have hg : ContMDiff (𝓘(ℝ, E).prod J) 𝓘(ℝ, F) n (uncurry fun y a ↦ f (Φ.symm y) a) :=
    hf.comp (Φ.symm.contMDiff.prodMap contMDiff_id)
  have h := (ContMDiff.parametric_integral (μ := μ) hg).comp Φ.contMDiff
  simpa only [comp_def, Diffeomorph.symm_apply_apply] using h
