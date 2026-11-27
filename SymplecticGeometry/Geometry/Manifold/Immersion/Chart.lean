/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.Immersion.Basic

/-!
# An immersion and its derivative in its normal-form charts

Let `f : M → N` be a `C^n` immersion at `x`. Read in its normal-form charts `φ` on `M` and `ψ` on
`N`, `f` is the inclusion `u ↦ L (u, 0)` of `E` into `E''`, through a linear equivalence
`L : E × F ≃ E''`; equivalently, `L⁻¹ (ψ (f y)) = (φ y, 0)` on the source of `φ`. For `n ≠ 0`,
differentiating this identity gives `dψ ∘ df = L (·, 0) ∘ dφ` at every point `y` of the source of
`φ`. Since the chart derivatives are invertible, a tangent vector `v` at `f y` is in the range of
`df` exactly when the `F`-component of `L⁻¹ (dψ v)` vanishes.

The proof of the derivative identity follows Tau Ceti's
`Manifold.IsSubmersionAtOfComplement.mfderiv_extend_comp_mfderiv`, in
`TauCeti/Geometry/Manifold/Submersion/Basic.lean`, its analogue for submersions.

## Main results

* `Manifold.IsImmersionAtOfComplement.equiv_symm_codChart_extend_apply`: an immersion in its
  normal-form charts.
* `Manifold.IsImmersionAtOfComplement.mfderiv_extend_comp_mfderiv`: the derivative of an
  immersion in its normal-form charts.
* `Manifold.IsImmersionAtOfComplement.snd_equiv_symm_mfderiv_extend_eq_zero_iff`: in these
  charts, the range of the derivative of an immersion is the zero set of the `F`-component.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 4 (the rank theorem).
-/

public section

open Set Function Filter Manifold
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 E'' G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : M → N} {x : M}

namespace Manifold.IsImmersionAtOfComplement

variable (h : IsImmersionAtOfComplement F I J n f x)
include h

/-- In the coordinates `E × F` of the codomain chart, read through `h.equiv`, an immersion is the
inclusion `u ↦ (u, 0)` of the coordinates of the domain chart. -/
theorem equiv_symm_codChart_extend_apply {y : M} (hy : y ∈ h.domChart.source) :
    h.equiv.symm (h.codChart.extend J (f y)) = (h.domChart.extend I y, 0) := by
  have hy' : y ∈ (h.domChart.extend I).source := by rwa [h.domChart.extend_source]
  have := (h.mem_codChart_source_and_extend_eq ((h.domChart.extend I).map_source hy')).2.1
  rw [(h.domChart.extend I).left_inv hy'] at this
  rw [this, ContinuousLinearEquiv.symm_apply_apply]

/-- An immersion in its normal-form charts: the point with coordinates `(φ y, 0)` in `E × F`, read
through `h.equiv`, is the image of `f y` in the codomain chart. -/
theorem equiv_domChart_extend_apply {y : M} (hy : y ∈ h.domChart.source) :
    h.equiv (h.domChart.extend I y, 0) = h.codChart.extend J (f y) := by
  rw [← h.equiv_symm_codChart_extend_apply hy, ContinuousLinearEquiv.apply_symm_apply]

/-- **The derivative of an immersion in its normal-form charts.** On the source of the domain
chart `φ`, the derivative of `f` followed by the derivative of the codomain chart `ψ` is the
derivative of `φ` followed by the inclusion `u ↦ L (u, 0)`, where `L = h.equiv`. -/
theorem mfderiv_extend_comp_mfderiv (hn : n ≠ 0) {y : M} (hy : y ∈ h.domChart.source) :
    (mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f y)).comp (mfderiv I J f y) =
      ((h.equiv : E × F →L[𝕜] E'').comp (ContinuousLinearMap.inl 𝕜 E F)).comp
        (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) y) := by
  have hfy : f y ∈ h.codChart.source := h.source_subset_preimage_source hy
  have hψ : MDifferentiableAt J 𝓘(𝕜, E'') (h.codChart.extend J) (f y) :=
    (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas hfy).mdifferentiableAt hn
  have hφ : MDifferentiableAt I 𝓘(𝕜, E) (h.domChart.extend I) y :=
    (h.domChart.contMDiffAt_extend h.domChart_mem_maximalAtlas hy).mdifferentiableAt hn
  have hf : MDifferentiableAt I J f y :=
    ((h.contMDiffOn y hy).contMDiffAt (h.domChart.open_source.mem_nhds hy)).mdifferentiableAt hn
  -- On the source of `φ`, `ψ ∘ f` is `L (·, 0) ∘ φ`.
  have heq : h.codChart.extend J ∘ f =ᶠ[𝓝 y]
      ((h.equiv : E × F →L[𝕜] E'').comp (ContinuousLinearMap.inl 𝕜 E F)) ∘
        h.domChart.extend I := by
    refine eventually_of_mem (h.domChart.open_source.mem_nhds hy) fun z hz ↦ ?_
    rw [comp_apply, ← h.equiv.apply_symm_apply (h.codChart.extend J (f z)),
      h.equiv_symm_codChart_extend_apply hz]
    simp
  exact hasMFDerivAt_unique (hψ.hasMFDerivAt.comp y hf.hasMFDerivAt)
    ((ContinuousLinearMap.hasMFDerivAt _).comp y hφ.hasMFDerivAt |>.congr_of_eventuallyEq_abuse
      heq)

/-- **The tangent image of an immersion in its normal-form charts.** For `n ≠ 0` and `y` in the
source of the domain chart, a tangent vector `v` at `f y` is in the range of the derivative of `f`
exactly when the `F`-component of `L⁻¹ (dψ v)` vanishes, where `ψ` is the extended codomain chart
and `L = h.equiv`. -/
theorem snd_equiv_symm_mfderiv_extend_eq_zero_iff (hn : n ≠ 0) {y : M}
    (hy : y ∈ h.domChart.source) (v : TangentSpace J (f y)) :
    (h.equiv.symm (mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f y) v)).2 = 0 ↔
      v ∈ LinearMap.range (mfderiv I J f y).toLinearMap := by
  have h1 : 1 ≤ n := ENat.one_le_iff_ne_zero_withTop.2 hn
  -- `dψ (df w) = L (dφ w, 0)` for every `w`.
  have hc (w : TangentSpace I y) :
      mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f y) (mfderiv I J f y w) =
        h.equiv (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) y w, 0) :=
    congr($(h.mfderiv_extend_comp_mfderiv hn hy) w)
  constructor
  · intro h0
    obtain ⟨Lφ, hLφ⟩ := isInvertible_mfderiv_extend
      (IsManifold.maximalAtlas_subset_of_le h1 h.domChart_mem_maximalAtlas) hy
    obtain ⟨Lψ, hLψ⟩ := isInvertible_mfderiv_extend
      (IsManifold.maximalAtlas_subset_of_le h1 h.codChart_mem_maximalAtlas)
      (h.source_subset_preimage_source hy)
    have hsurj : Surjective (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) y) := hLφ ▸ Lφ.surjective
    have hinj : Injective (mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f y)) :=
      hLψ ▸ Lψ.injective
    obtain ⟨w, hw⟩ := hsurj (h.equiv.symm (mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f y) v)).1
    refine ⟨w, hinj ?_⟩
    rw [ContinuousLinearMap.coe_coe, hc, hw, ← h0, Prod.mk.eta]
    -- `apply_symm_apply` read in `TangentSpace 𝓘(𝕜, E'') _`, which is `E''` by definition.
    exact h.equiv.apply_symm_apply _
  · rintro ⟨w, rfl⟩
    rw [ContinuousLinearMap.coe_coe, hc, ContinuousLinearEquiv.symm_apply_apply]

end Manifold.IsImmersionAtOfComplement
