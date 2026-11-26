/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
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

The same cover, without a chart: a function that is `C^n` on an open set `U` and vanishes on `U`
outside a closed subset `K` of `U` is `C^n` once extended by `0` off `U`
(`ContMDiffOn.contMDiff_indicator`), since `U` and the complement of `K` are open and cover `M`.

The extension by zero to `M` of a function on the model vector space read through an extended
chart is Tau Ceti's `OpenPartialHomeomorph.contMDiff_indicator_comp_extend`. This file goes the
other way:

* `PartialDiffeomorph.support_indicator_comp_symm_subset`,
  `PartialDiffeomorph.tsupport_indicator_comp_symm_subset`,
  `PartialDiffeomorph.hasCompactSupport_indicator_comp_symm`,
  `PartialDiffeomorph.continuous_indicator_comp_symm` and
  `PartialDiffeomorph.contMDiff_indicator_comp_symm`: a function `χ` on `M` whose support is
  compact and lies in the source of a partial diffeomorphism `ψ` onto an open subset of a
  Hausdorff manifold `N`, transported to `χ ∘ ψ.symm` and extended by zero off `ψ.target`, is
  supported in `ψ '' tsupport χ`, so has compact support, and is continuous, or `C^n`, when `χ`
  is. When `N` is a normed space, the last gives `PartialDiffeomorph.contDiff_indicator_comp_symm`.
* `PartialDiffeomorph.contMDiff_indicator_image_comp_symm`: the same for a function that is only
  `C^n` on an open `W ⊆ ψ.source` and vanishes on `W` outside a subset `C` whose image `ψ '' C`
  is closed, transported to `ψ '' W` and extended by zero off it. Here `N` need not be
  Hausdorff.
-/

public section

open Set Topology
open scoped Manifold

section Indicator

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A function that is `C^n` on an open set `U` and vanishes on `U` outside a closed set `K ⊆ U`,
extended by `0` off `U`, is `C^n`. -/
theorem ContMDiffOn.contMDiff_indicator {f : M → F} {U K : Set M}
    (hf : ContMDiffOn I 𝓘(𝕜, F) n f U) (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hf0 : ∀ x ∈ U, x ∉ K → f x = 0) : ContMDiff I 𝓘(𝕜, F) n (U.indicator f) :=
  contMDiff_of_contMDiffOn_union_of_isOpen (hf.congr fun _ hx ↦ indicator_of_mem hx f)
    (contMDiffOn_const.congr fun x hx ↦ by
      by_cases hxU : x ∈ U
      · rw [indicator_of_mem hxU, hf0 x hxU hx]
      · exact indicator_of_notMem hxU f)
    (eq_univ_of_forall fun x ↦ or_iff_not_imp_right.2 fun hx ↦ hKU (not_not.1 hx))
    hU hK.isOpen_compl

end Indicator

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

end OpenPartialHomeomorph

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}
  (ψ : PartialDiffeomorph I I' M N n)

/-- The function `χ ∘ ψ.symm`, extended by `0` off `ψ.target`, vanishes off the image under `ψ`
of the support of `χ`. -/
theorem support_indicator_comp_symm_subset {F : Type*} [Zero F] (χ : M → F) :
    Function.support (ψ.target.indicator fun y ↦ χ (ψ.symm y)) ⊆ ψ '' tsupport χ := fun y hy ↦ by
  by_cases hyt : y ∈ ψ.target
  · refine ⟨ψ.symm y, subset_tsupport _ fun h0 ↦ hy ?_, ψ.right_inv hyt⟩
    exact (indicator_of_mem hyt _).trans h0
  · exact absurd (indicator_of_notMem hyt _) hy

variable {ψ}

section Zero

variable [T2Space N] {F : Type*} [Zero F] {χ : M → F}

/-- If the support of `χ` is compact and lies in the source of `ψ`, the function `χ ∘ ψ.symm`,
extended by `0` off `ψ.target`, is supported in the image under `ψ` of the support of `χ`. -/
theorem tsupport_indicator_comp_symm_subset
    (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source) :
    tsupport (ψ.target.indicator fun y ↦ χ (ψ.symm y)) ⊆ ψ '' tsupport χ :=
  SymplecticGeometry.tsupport_indicator_subset_of_eqOn
    (ψ.isCompact_image_of_subset_source hK hχ).isClosed
    fun _ hy ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hy.2 ⟨_, h, ψ.right_inv hy.1⟩

/-- If the support of `χ` is compact and lies in the source of `ψ`, the function `χ ∘ ψ.symm`,
extended by `0` off `ψ.target`, has compact support. -/
theorem hasCompactSupport_indicator_comp_symm
    (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source) :
    HasCompactSupport (ψ.target.indicator fun y ↦ χ (ψ.symm y)) :=
  (ψ.isCompact_image_of_subset_source hK hχ).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_indicator_comp_symm_subset hK hχ)

/-- If `χ` is continuous and its support is compact and lies in the source of `ψ`, the function
`χ ∘ ψ.symm`, extended by `0` off `ψ.target`, is continuous. -/
theorem continuous_indicator_comp_symm [TopologicalSpace F] (hχc : Continuous χ)
    (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source) :
    Continuous (ψ.target.indicator fun y ↦ χ (ψ.symm y)) :=
  ContinuousOn.continuous_of_tsupport_subset
    ((hχc.comp_continuousOn ψ.symm.contMDiffOn.continuousOn).congr
      fun _ hy ↦ indicator_of_mem hy _) ψ.open_target
    ((tsupport_indicator_comp_symm_subset hK hχ).trans (ψ.mapsTo.mono_left hχ).image_subset)

end Zero

/-- Let `W ⊆ ψ.source` be open and `C ⊆ W` a set whose image `ψ '' C` is closed. If `χ` is `C^n`
on `W` and vanishes on `W` outside `C`, the function `χ ∘ ψ.symm` on `ψ '' W`, extended by `0`
off `ψ '' W`, is `C^n`. -/
theorem contMDiff_indicator_image_comp_symm {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {χ : M → F} {C W : Set M} (hχ : ContMDiffOn I 𝓘(𝕜, F) n χ W)
    (hC : IsClosed (ψ '' C)) (hW : IsOpen W) (hCW : C ⊆ W) (hWs : W ⊆ ψ.source)
    (hχ0 : ∀ z ∈ W, z ∉ C → χ z = 0) :
    ContMDiff I' 𝓘(𝕜, F) n ((ψ '' W).indicator fun y ↦ χ (ψ.symm y)) := by
  have hWo : IsOpen (ψ '' W) := by
    simpa using ψ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hW (by simpa using hWs)
  refine ContMDiffOn.contMDiff_indicator ?_ hWo hC (image_mono hCW) fun x hxW hx ↦ ?_
  · refine hχ.comp (ψ.symm.contMDiffOn.mono ?_) ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact ψ.map_source (hWs hz)
    · rintro _ ⟨z, hz, rfl⟩
      rw [mem_preimage, symm_toPartialEquiv, ψ.left_inv (hWs hz)]
      exact hz
  · obtain ⟨z, hz, rfl⟩ := hxW
    rw [symm_toPartialEquiv, ψ.left_inv (hWs hz)]
    exact hχ0 z hz fun hzC ↦ hx (mem_image_of_mem _ hzC)

/-- If `χ` is `C^n` and its support is compact and lies in the source of `ψ`, the function
`χ ∘ ψ.symm`, extended by `0` off `ψ.target`, is `C^n`. -/
theorem contMDiff_indicator_comp_symm [T2Space N] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {χ : M → F} (hχc : ContMDiff I 𝓘(𝕜, F) n χ)
    (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source) :
    ContMDiff I' 𝓘(𝕜, F) n (ψ.target.indicator fun y ↦ χ (ψ.symm y)) := by
  have h := contMDiff_indicator_image_comp_symm hχc.contMDiffOn
    (ψ.isCompact_image_of_subset_source hK hχ).isClosed ψ.open_source hχ subset_rfl
    fun _ _ hz ↦ image_eq_zero_of_notMem_tsupport hz
  rwa [ψ.toPartialEquiv.image_source_eq_target] at h

/-- If `χ` is `C^n` and its support is compact and lies in the source of a partial
diffeomorphism `ψ` onto an open subset of a normed space, the function `χ ∘ ψ.symm`, extended
by `0` off `ψ.target`, is `C^n`. -/
theorem contDiff_indicator_comp_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ψ : PartialDiffeomorph I 𝓘(𝕜, E') M E' n} {χ : M → F} (hχc : ContMDiff I 𝓘(𝕜, F) n χ)
    (hK : IsCompact (tsupport χ)) (hχ : tsupport χ ⊆ ψ.source) :
    ContDiff 𝕜 n (ψ.target.indicator fun y ↦ χ (ψ.symm y)) :=
  contMDiff_iff_contDiff.1 (contMDiff_indicator_comp_symm hχc hK hχ)

end PartialDiffeomorph

end
