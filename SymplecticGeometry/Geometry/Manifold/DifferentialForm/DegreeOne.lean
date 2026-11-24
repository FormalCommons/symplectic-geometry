/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic

/-!
# One-forms: proportionality and values on smooth vector fields

If the kernel of a one-form `α` at `x` lies in that of `β`, and `α_x(v) = 1`, then
`β_x = β_x(v) α_x` (`TauCeti.RoughForm.apply_eq_smul_of_ker_le`). This holds for rough forms,
with no smoothness asked. Its proof adapts that of Tau Ceti's
`TauCeti.SmoothForm.apply_eq_smul_of_kerDistribution_le`, which is stated for smooth forms only.

The value `x ↦ α_x (X x)` of a smooth real one-form `α` on a smooth vector field `X` is a smooth
function (`TauCeti.SmoothForm.contMDiff_apply_contMDiffSection`). Through Tau Ceti's
`TauCeti.SmoothForm.degreeOneEquiv`, `α` is a smooth section of the cotangent bundle, and the
pairing of smooth sections of a dual bundle and of the bundle is smooth
(`ContMDiffAt.clm_bundle_apply_scalar`).

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- If the kernel of the one-form `α` at `x` lies in that of `β`, then `β` is proportional to `α`
at `x`: if `α_x(v) = 1`, then `β_x = β_x(v) α_x`. -/
theorem apply_eq_smul_of_ker_le {α β : RoughForm I M ℝ 1} {x : M} {v : TangentSpace I x}
    (hker : α.ker x ≤ β.ker x) (hv : α x ![v] = 1) : β x = β x ![v] • α x := by
  ext w
  -- `w - α(w) v` lies in `ker α ⊆ ker β`.
  have hw : α x ![w - α x ![w] • v] = 0 := by
    rw [← eval_apply, map_sub, map_smul, eval_apply, eval_apply, hv, smul_eq_mul, mul_one,
      sub_self]
  have h := mem_ker.1 (hker (mem_ker.2 hw))
  rw [← eval_apply, map_sub, map_smul, eval_apply, eval_apply, smul_eq_mul, sub_eq_zero] at h
  rw [ContinuousAlternatingMap.smul_apply, h, smul_eq_mul, mul_comm]

end TauCeti.RoughForm

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The value `α(X)` of a smooth one-form on a smooth vector field is a smooth function. -/
theorem contMDiff_apply_contMDiffSection (α : SmoothForm I M ℝ 1)
    (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ fun x ↦ α.val x ![X x] := fun x ↦ by
  simpa [degreeOneEquiv_apply_apply_vec] using
    ((degreeOneEquiv α).contMDiff x).clm_bundle_apply_scalar (X.contMDiff x)

end TauCeti.SmoothForm

end
