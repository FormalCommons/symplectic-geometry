/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Topology.OpenPartialHomeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Topology.Algebra.Support

/-!
# Extending a function by zero along a chart

Let `e` be an open partial homeomorphism from a Hausdorff space `M`, and `K` a compact subset of
its target. The source of `e` and the complement of `e.symm '' K` are open and cover `M`, so a
map on `M` that is `C^n` on both is `C^n`
(`OpenPartialHomeomorph.contMDiff_of_contMDiffOn_source_of_contMDiffOn_compl`). This is the step
shared by the extensions by zero of the library. It applies to sections of a vector bundle too,
such as differential forms, through their maps to the total space.

* `OpenPartialHomeomorph.contMDiff_indicator_comp`: let `e` be a chart of the maximal atlas of a
  Hausdorff `C^n` manifold `M` modelled on `H`, and let `ψ : H → F` be `C^n` on the target of `e`,
  with compact support inside that target. Then the function on `M` that is `ψ ∘ e` on the source
  of `e` and zero elsewhere, `e.source.indicator (ψ ∘ e)`, is `C^n`.
* `PartialDiffeomorph.support_indicator_comp_symm_subset`,
  `PartialDiffeomorph.tsupport_indicator_comp_symm_subset`,
  `PartialDiffeomorph.hasCompactSupport_indicator_comp_symm`,
  `PartialDiffeomorph.continuous_indicator_comp_symm` and
  `PartialDiffeomorph.contDiff_indicator_comp_symm`: in the other direction, a function `χ` on `M`
  whose support is compact and lies in the source of a partial diffeomorphism `ψ` onto an open
  subset of a normed space, read in `ψ` and extended by zero off `ψ.target`, is supported in
  `ψ '' tsupport χ`, so has compact support, and is continuous, or `C^n`, when `χ` is.

The argument for `contMDiff_indicator_comp` is that of Mathlib's `SmoothBumpFunction.contMDiff`,
for a function on the target of any chart of the maximal atlas rather than a bump function in the
preferred chart at a point.
-/

public section

open Set Topology
open scoped Manifold

namespace OpenPartialHomeomorph

section Glue

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞} {Y : Type*} [TopologicalSpace Y]

/-- On a Hausdorff space, a map that is `C^n` on the source of an open partial homeomorphism `e`
and on the complement of the image under `e.symm` of a compact subset `K` of the target of `e` is
`C^n`. -/
theorem contMDiff_of_contMDiffOn_source_of_contMDiffOn_compl (e : OpenPartialHomeomorph M Y)
    {K : Set Y} (hK : IsCompact K) (hKe : K ⊆ e.target) {f : M → N}
    (hs : ContMDiffOn I I' n f e.source) (hc : ContMDiffOn I I' n f (e.symm '' K)ᶜ) :
    ContMDiff I I' n f :=
  contMDiff_of_contMDiffOn_union_of_isOpen hs hc
    (eq_univ_of_forall fun _ ↦ or_iff_not_imp_left.2 fun hx ⟨_, hy, hyx⟩ ↦
      hx (hyx ▸ e.map_target (hKe hy)))
    e.open_source (e.isClosed_image_symm_of_isCompact hK hKe).isOpen_compl

end Glue

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
  refine e.contMDiff_of_contMDiffOn_source_of_contMDiffOn_compl hc hs
    ((hψ.comp (contMDiffOn_of_mem_maximalAtlas he) e.mapsTo).congr fun z hz ↦
      indicator_of_mem hz _) ((contMDiffOn_const (c := (0 : F))).congr fun z hz ↦ ?_)
  by_cases hzs : z ∈ e.source
  · rw [indicator_of_mem hzs, Function.comp_apply]
    exact image_eq_zero_of_notMem_tsupport fun h ↦ hz ⟨e z, h, e.left_inv hzs⟩
  · exact indicator_of_notMem hzs _

end OpenPartialHomeomorph

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {n : WithTop ℕ∞} (ψ : PartialDiffeomorph I 𝓘(𝕜, E') M E' n)

/-- A function `χ` read in the chart `ψ` and extended by `0` off `ψ.target` vanishes off the
image under `ψ` of the support of `χ`. -/
theorem support_indicator_comp_symm_subset {F : Type*} [Zero F] (χ : M → F) :
    Function.support (ψ.target.indicator fun y ↦ χ (ψ.symm y)) ⊆ ψ '' tsupport χ := fun y hy ↦ by
  by_cases hyt : y ∈ ψ.target
  · refine ⟨ψ.symm y, subset_tsupport _ fun h0 ↦ hy ?_, ψ.right_inv hyt⟩
    exact (indicator_of_mem hyt _).trans h0
  · exact absurd (indicator_of_notMem hyt _) hy

variable {ψ}

section Zero

variable {F : Type*} [Zero F] {χ : M → F}

/-- If the support of `χ` is compact and lies in the source of `ψ`, the function `χ` read in the
chart and extended by `0` off `ψ.target` is supported in the image under `ψ` of the support of
`χ`. -/
theorem tsupport_indicator_comp_symm_subset
    (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source) :
    tsupport (ψ.target.indicator fun y ↦ χ (ψ.symm y)) ⊆ ψ '' tsupport χ :=
  tsupport_indicator_subset_of_eqOn (ψ.isCompact_image_of_subset_source hK hχ).isClosed
    fun _ hy ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hy.2 ⟨_, h, ψ.right_inv hy.1⟩

/-- If the support of `χ` is compact and lies in the source of `ψ`, the function `χ` read in the
chart and extended by `0` off `ψ.target` has compact support. -/
theorem hasCompactSupport_indicator_comp_symm
    (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source) :
    HasCompactSupport (ψ.target.indicator fun y ↦ χ (ψ.symm y)) :=
  (ψ.isCompact_image_of_subset_source hK hχ).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_indicator_comp_symm_subset hK hχ)

/-- If `χ` is continuous and its support is compact and lies in the source of `ψ`, the function
`χ` read in the chart and extended by `0` off `ψ.target` is continuous. -/
theorem continuous_indicator_comp_symm [TopologicalSpace F] (hχc : Continuous χ)
    (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source) :
    Continuous (ψ.target.indicator fun y ↦ χ (ψ.symm y)) :=
  ContinuousOn.continuous_of_tsupport_subset
    ((hχc.comp_continuousOn ψ.symm.contMDiffOn.continuousOn).congr
      fun _ hy ↦ indicator_of_mem hy _) ψ.open_target
    ((tsupport_indicator_comp_symm_subset hK hχ).trans (ψ.mapsTo.mono_left hχ).image_subset)

end Zero

/-- If `χ` is `C^n` and its support is compact and lies in the source of `ψ`, the function `χ`
read in the chart and extended by `0` off `ψ.target` is `C^n`. -/
theorem contDiff_indicator_comp_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {χ : M → F} (hχc : ContMDiff I 𝓘(𝕜, F) n χ)
    (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source) :
    ContDiff 𝕜 n (ψ.target.indicator fun y ↦ χ (ψ.symm y)) := by
  refine contMDiff_iff_contDiff.1 (contMDiff_of_tsupport fun y hy ↦ ?_)
  have hyt : y ∈ ψ.target := (ψ.mapsTo.mono_left hχ).image_subset
    (tsupport_indicator_comp_symm_subset hK hχ hy)
  exact ((hχc.comp_contMDiffOn ψ.symm.contMDiffOn).congr fun y hy ↦ indicator_of_mem hy _)
    |>.contMDiffAt (ψ.open_target.mem_nhds hyt)

end PartialDiffeomorph

end
