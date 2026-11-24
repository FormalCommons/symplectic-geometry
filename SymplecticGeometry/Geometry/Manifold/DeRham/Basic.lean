/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DeRham.ComplexCoefficients
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed

/-!
# Basic facts on de Rham cohomology

Small facts about Tau Ceti's de Rham cohomology with real coefficients,
`TauCeti.deRhamCohomology I M k`, and with complex coefficients,
`TauCeti.complexDeRhamCohomology I M k`, in Tau Ceti's namespaces so that they can move there.

## Main results

* `TauCeti.SmoothForm.isClosed_iff_mem_closedForms`: a smooth real form is closed, in the sense
  of `TauCeti.SmoothForm.IsClosed`, exactly when it lies in the subspace
  `TauCeti.closedForms I M k`; `TauCeti.SmoothForm.IsClosed.mem_closedForms` is the forward
  direction.
* `TauCeti.deRhamCohomology.mk_eq_mk_iff`: two closed forms have the same de Rham class exactly
  when their difference is exact. This is the analogue of Tau Ceti's
  `TauCeti.compactlySupportedDeRhamCohomology.mk_eq_mk_iff`, with the same proof.
* `TauCeti.complexDeRhamCohomology.mk_eq_mk_iff`: the same with complex coefficients.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §1.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

namespace SmoothForm

/-- A smooth real form is closed exactly when it lies in the subspace of closed forms. -/
theorem isClosed_iff_mem_closedForms {k : ℕ} (φ : SmoothForm I M ℝ k) :
    φ.IsClosed ↔ φ ∈ closedForms I M k := by
  rw [isClosed_def, mem_closedForms]

/-- A closed smooth real form lies in the subspace of closed forms. -/
theorem IsClosed.mem_closedForms {k : ℕ} {φ : SmoothForm I M ℝ k} (h : φ.IsClosed) :
    φ ∈ closedForms I M k :=
  (isClosed_iff_mem_closedForms φ).1 h

end SmoothForm

namespace deRhamCohomology

variable (I) in
/-- Two closed real forms have the same de Rham class exactly when their difference is exact. -/
theorem mk_eq_mk_iff (k : ℕ) (φ ψ : closedForms I M k) :
    mk I k φ = mk I k ψ ↔ φ.val - ψ.val ∈ exactForms I M k := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff, Submodule.coe_sub]

end deRhamCohomology

namespace complexDeRhamCohomology

variable (I) in
/-- Two closed complex-valued forms have the same complex de Rham class exactly when their
difference is exact. -/
theorem mk_eq_mk_iff (k : ℕ) (φ ψ : complexClosedForms I M k) :
    mk I k φ = mk I k ψ ↔ φ.val - ψ.val ∈ complexExactForms I M k := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff, Submodule.coe_sub]

end complexDeRhamCohomology

end TauCeti

end
