/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Extending a function by zero along a chart

Let `e` be a chart of the maximal atlas of a Hausdorff `C^n` manifold `M` modelled on `H`, and
let `ψ : H → F` be `C^n` on the target of `e`, with compact support inside that target. Then the
function on `M` that is `ψ ∘ e` on the source of `e` and zero elsewhere,
`e.source.indicator (ψ ∘ e)`, is `C^n` (`OpenPartialHomeomorph.contMDiff_indicator_comp`).

Near a point of the source the function is `ψ ∘ e`. Off the source it vanishes on the complement
of `e.symm '' tsupport ψ`, which is compact, hence closed since `M` is Hausdorff. This is the
argument of Mathlib's `SmoothBumpFunction.contMDiff`, for a function on the target of any chart
of the maximal atlas rather than a bump function in the preferred chart at a point.
-/

public section

open Set Topology
open scoped Manifold

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞}
  {e : OpenPartialHomeomorph M H} {ψ : H → F}

/-- The extension by zero along a chart `e` of the maximal atlas of a Hausdorff `C^n` manifold
of a function `ψ` that is `C^n` on the target of `e` and has compact support inside it is `C^n`.
-/
theorem contMDiff_indicator_comp [IsManifold I n M] (he : e ∈ IsManifold.maximalAtlas I n M)
    (hψ : ContMDiffOn I 𝓘(𝕜, F) n ψ e.target) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ e.target) :
    ContMDiff I 𝓘(𝕜, F) n (e.source.indicator (ψ ∘ e)) := by
  intro x
  by_cases hx : x ∈ e.source
  · refine ((hψ.contMDiffAt (e.open_target.mem_nhds (e.map_source hx))).comp x
      (contMDiffAt_of_mem_maximalAtlas he hx)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_source.mem_nhds hx] with z hz
    exact indicator_of_mem hz _
  · have hxK : x ∉ e.symm '' tsupport ψ := fun ⟨y, hy, hyx⟩ ↦ hx (hyx ▸ e.map_target (hs hy))
    refine (contMDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [(e.isClosed_image_symm_of_isCompact hc hs).isOpen_compl.mem_nhds hxK]
      with z hz
    by_cases hzs : z ∈ e.source
    · rw [indicator_of_mem hzs, Function.comp_apply]
      exact image_eq_zero_of_notMem_tsupport fun h ↦ hz ⟨e z, h, e.left_inv hzs⟩
    · exact indicator_of_notMem hzs _

end OpenPartialHomeomorph

end
