/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic

/-!
# Fixing the first arguments of a continuous alternating map: the norm

For a continuous alternating map `f` of `r + m` arguments between normed spaces and
`u : Fin r → W`, the operator norm of `f.appendLeft u : w ↦ f (Fin.append u w)` is at most
`‖f‖ * ∏ i, ‖u i‖` (`ContinuousAlternatingMap.norm_appendLeft_le`). So `f ↦ f.appendLeft u` is a
continuous linear map (`ContinuousAlternatingMap.appendLeftCLM`), which is what a proof of
smoothness of `x ↦ (f x).appendLeft u` needs.
-/

public section

noncomputable section

namespace ContinuousAlternatingMap

variable {𝕜 W N : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [NormedAddCommGroup N] [NormedSpace 𝕜 N] {r m : ℕ}

/-- The operator norm of `f.appendLeft u` is at most `‖f‖ * ∏ i, ‖u i‖`. -/
theorem norm_appendLeft_le (f : W [⋀^Fin (r + m)]→L[𝕜] N) (u : Fin r → W) :
    ‖f.appendLeft u‖ ≤ ‖f‖ * ∏ i, ‖u i‖ := by
  refine opNorm_le_bound _ (by positivity) fun w ↦ ?_
  calc ‖f.appendLeft u w‖ ≤ ‖f‖ * ∏ p, ‖Fin.append u w p‖ := by
        rw [appendLeft_apply]
        exact f.le_opNorm _
    _ = ‖f‖ * (∏ i, ‖u i‖) * ∏ j, ‖w j‖ := by
      rw [Fin.prod_univ_add, mul_assoc]
      simp only [Fin.append_left, Fin.append_right]

variable (𝕜 N m) in
/-- `ContinuousAlternatingMap.appendLeft` with the fixed arguments `u`, as a continuous linear
map in the alternating map. -/
def appendLeftCLM (u : Fin r → W) : (W [⋀^Fin (r + m)]→L[𝕜] N) →L[𝕜] W [⋀^Fin m]→L[𝕜] N :=
  LinearMap.mkContinuous
    { toFun f := f.appendLeft u
      map_add' f g := appendLeft_add f g u
      map_smul' c f := appendLeft_smul c f u }
    (∏ i, ‖u i‖) fun f ↦ (norm_appendLeft_le f u).trans_eq (mul_comm _ _)

/-- `appendLeftCLM 𝕜 N m u` sends `f` to `f.appendLeft u`. -/
@[simp]
theorem appendLeftCLM_apply (u : Fin r → W) (f : W [⋀^Fin (r + m)]→L[𝕜] N) :
    appendLeftCLM 𝕜 N m u f = f.appendLeft u := (rfl)

end ContinuousAlternatingMap

end

end
