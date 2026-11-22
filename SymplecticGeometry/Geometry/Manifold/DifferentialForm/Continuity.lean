/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family

/-!
# Continuity of slice pullbacks in the parameter

This file extends Tau Ceti's `TauCeti.Geometry.Manifold.DifferentialForm.Continuity`. For a `C¹`
map `f : M × N → M'` and a continuous form `φ` on `M'`, the slices `x ↦ f (x, y)` pull `φ` back to
forms on `M` whose value at a fixed point on fixed tangent vectors depends continuously on the
parameter `y` (`TauCeti.IsSmoothForm.continuous_mpullback_prodMk_apply`). It is the case of
continuous forms and a constant base point of Tau Ceti's `ContMDiffAt.mpullback_form_family`,
read in one fibre of the bundle of forms. No interior assumption is made on `N`: for a manifold
with boundary this gives continuity of the slices up to the boundary.

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
    Continuous fun y : N ↦ TauCeti.mpullback I I' (fun x' ↦ f (x', y)) φ x v := by
  -- The pullbacks at `x` form a continuous section over the constant map `y ↦ x`.
  have h : Continuous fun y : N ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
      (E := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Trivial M F x) x
      (TauCeti.mpullback I I' (fun x' ↦ f (x', y)) φ x) :=
    continuous_iff_continuousAt.2 fun y ↦ (ContMDiffAt.mpullback_form_family (m := 0) (n := 1)
      (f := fun y x' ↦ f (x', y)) (g := fun _ ↦ x) (hφ.contMDiff _)
      ((hf _).comp _ (contMDiffAt_snd.prodMk contMDiffAt_fst)) contMDiffAt_const
      (by simp)).continuousAt
  exact (continuous_eval_const v).comp
    ((FiberBundle.totalSpaceMk_isInducing _ _ x).continuous_iff.2 h)

end TauCeti

end
