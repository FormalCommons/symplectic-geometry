/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Topology.Algebra.Support

/-!
# The restriction of a differential form to an open set, extended by zero

For a rough form `f` on `M` and a subset `U` of `M`, `U.indicator f` is `f` on `U` and `0` off
`U`. When `U` is open, `f` is a `C^n` section at the points of `U`, and `f` vanishes on `U` outside
a closed set `K ⊆ U`, the form `U.indicator f` is `C^n` on all of `M`
(`TauCeti.IsSmoothForm.indicator_of_isClosed`). Its support then lies in `K`, by the lemma
`tsupport_indicator_subset_of_eqOn` about functions. This cuts a form into the pieces it has in
finitely many disjoint open sets. Tau Ceti's `TauCeti.IsSmoothForm.indicator` gives the same
conclusion for a form that is `C^n` on all of `M` and vanishes near every point outside `U`.

The proof of smoothness follows Tau Ceti's `TauCeti.IsSmoothForm.extendByZero`, written for a set
of `M` rather than an open subset seen as a manifold.
-/

public section

open Set Bundle
open scoped Manifold

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **Restricting a form to an open set and extending by zero.** Let `U` be open and `K ⊆ U`
closed. If a form `f` is a `C^n` section at every point of `U` and vanishes on `U` outside `K`,
then `U.indicator f` is a `C^n` form on `M`. -/
theorem IsSmoothForm.indicator_of_isClosed [IsManifold I 1 M] {n : WithTop ℕ∞}
    {f : RoughForm I M F k} {U K : Set M} (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hf : ∀ x ∈ U, ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (f y)) x)
    (hf0 : ∀ x ∈ U, x ∉ K → f x = 0) :
    IsSmoothForm I n (U.indicator (M := E [⋀^Fin k]→L[ℝ] F) f) := by
  refine (isSmoothForm_def n _).2 fun x ↦ ?_
  by_cases hx : x ∈ U
  · refine (hf x hx).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx] with y hy
    exact congrArg _ (indicator_of_mem (M := E [⋀^Fin k]→L[ℝ] F) hy f)
  · refine ((IsSmoothForm.zero (I := I) (M := M) (F := F) (k := k) n).contMDiff x)
      |>.congr_of_eventuallyEq ?_
    filter_upwards [hK.isOpen_compl.mem_nhds fun h ↦ hx (hKU h)] with y hy
    exact congrArg _ (_root_.image_eq_zero_of_notMem_tsupport (α := E [⋀^Fin k]→L[ℝ] F)
      fun h ↦ hy (SymplecticGeometry.tsupport_indicator_subset_of_eqOn hK
        (fun z hz ↦ hf0 z hz.1 hz.2) h))

end TauCeti

end
