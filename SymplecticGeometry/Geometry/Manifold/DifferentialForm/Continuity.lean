/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Continuity of slice pullbacks in the parameter

This file extends Tau Ceti's `TauCeti.Geometry.Manifold.DifferentialForm.Continuity`. For a `C¹`
map `f : M × N → M'` and a continuous form `φ` on `M'`, the slices `x ↦ f (x, y)` pull `φ` back to
forms on `M` whose value at a fixed point on fixed tangent vectors depends continuously on the
parameter `y` (`TauCeti.IsSmoothForm.continuous_mpullback_prodMk_apply`). The differential of the
slice at `y` sends `v` to the differential of `f` on `(v, 0)`, and these vectors move continuously
in the tangent bundle of `M'` (Mathlib's `contMDiff_equivTangentBundleProd_symm`, and the
continuity of the tangent map of `f`), so Tau Ceti's `TauCeti.IsSmoothForm.tendsto_apply` applies.
No interior assumption is made on `N`: for a manifold with boundary this gives continuity of the
slices up to the boundary.

## Main results

* `TauCeti.IsSmoothForm.continuous_mpullback_prodMk_apply`: the value of the pullback of a
  continuous form along the slices of a `C¹` map is continuous in the slice parameter.
-/

public section

open Bundle
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {E'' H'' M' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I' : ModelWithCorners ℝ E'' H''} [TopologicalSpace M'] [ChartedSpace H'' M']
  [IsManifold I' 1 M'] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **Slices of a `C¹` map pull a continuous form back continuously in the parameter.** For a `C¹`
map `f : M × N → M'`, a continuous form `φ` on `M'`, a point `x` of `M` and tangent vectors `v` at
`x`, the value `(f(·, y)^* φ)_x(v)` is a continuous function of `y`. -/
theorem IsSmoothForm.continuous_mpullback_prodMk_apply {φ : RoughForm I' M' F k}
    (hφ : IsSmoothForm I' 0 φ) {f : M × N → M'} (hf : ContMDiff (I.prod J) I' 1 f) (x : M)
    (v : Fin k → TangentSpace I x) :
    Continuous fun y : N ↦ mpullback I I' (fun x' ↦ f (x', y)) φ x v := by
  have key (y : N) : mpullback I I' (fun x' ↦ f (x', y)) φ x v =
      φ (f (x, y)) (fun j ↦ mfderiv (I.prod J) I' f (x, y) (v j, 0)) := by
    rw [mpullback_apply]
    congr 1
    funext j
    have hg : MDifferentiableAt I (I.prod J) (fun x' : M ↦ (x', y)) x :=
      mdifferentiableAt_id.prodMk mdifferentiableAt_const
    rw [show (fun x' ↦ f (x', y)) = f ∘ fun x' ↦ (x', y) from rfl,
      mfderiv_comp x (hf.mdifferentiableAt one_ne_zero (x := (x, y))) hg, mfderiv_prod_left]
    -- `ContinuousLinearMap.inl_apply` does not match through the `TangentSpace` synonyms.
    rfl
  simp_rw [key]
  refine continuous_iff_continuousAt.2 fun y₀ ↦ hφ.tendsto_apply
    (hf.continuous.comp (continuous_const.prodMk continuous_id)).continuousAt fun j ↦ ?_
  have hc : Continuous fun y : N ↦ tangentMap (I.prod J) I' f
      ((equivTangentBundleProd I M J N).symm (⟨x, v j⟩, zeroSection E' (TangentSpace J) y)) :=
    (hf.continuous_tangentMap le_rfl).comp
      ((contMDiff_equivTangentBundleProd_symm (n := 1)).continuous.comp
        (continuous_const.prodMk (Trivialization.continuous_zeroSection ℝ)))
  -- The tangent map of `f` at `((x, y), (v j, 0))` is the vector `(f (x, y), df (v j, 0))`.
  exact hc.continuousAt.tendsto

end TauCeti

end
