/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Chart

/-!
# Local diffeomorphisms form an open set of `C^n` maps

This file proves that being a local diffeomorphism is an open condition in Tau Ceti's weak
Whitney topology on `C^n` maps out of a compact boundaryless manifold. It is the first step
towards the openness of diffeomorphisms among `C^1` maps of a compact manifold, which the
smoothing of families of diffeomorphisms uses.

* `ContMDiffMap.eventually_isInvertible_mfderiv`: the local step. If `f₀` has invertible
  manifold derivatives near `x₀`, then so does every map near `f₀`, at every point near `x₀`.
  At `x₀` an open test on the first chart derivative over a compact chart ball does it, since
  invertible linear maps form an open set; the chart derivative is read as the manifold
  derivative by `MDifferentiableAt.isInvertible_fderivWithin_extChartAt_iff`.
* `ContMDiffMap.isOpen_setOfPred_isLocalDiffeomorph`: for `1 ≤ n` and a compact boundaryless
  source modelled on a finite-dimensional space, the `C^n` local diffeomorphisms form an open set
  of `C^n⟮I, M; J, N⟯` for Tau Ceti's weak Whitney topology
  `ContMDiffMap.manifoldWeakWhitneyTopology`. Compactness of the source makes the local step
  uniform, and Tau Ceti's inverse function theorem `TauCeti.isLocalDiffeomorph_of_mfderiv_eq`
  turns invertible derivatives into a local diffeomorphism.

The argument is Hirsch's.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1 (openness of immersions
  and of local diffeomorphisms in the weak `C^1` topology).
-/

public section

open Set Filter Topology
open scoped Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

section Local

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold J n N]

/-- For `1 ≤ n`, if a `C^n` map `f₀` out of a boundaryless manifold modelled on a proper space has
invertible manifold derivative at every point near `x₀`, then every `C^n` map near `f₀` in the
weak Whitney topology has invertible manifold derivative at every point near `x₀`. -/
theorem eventually_isInvertible_mfderiv (hn : 1 ≤ n) {f₀ : C^n⟮I, M; J, N⟯} {x₀ : M}
    (hf₀ : ∀ᶠ x in 𝓝 x₀, (mfderiv I J f₀ x).IsInvertible) :
    ∀ᶠ p in 𝓝 f₀ ×ˢ 𝓝 x₀, (mfderiv I J p.1 p.2).IsInvertible := by
  have : IsManifold I 1 M := .of_le hn
  have : IsManifold J 1 N := .of_le hn
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  set φ := extChartAt I x₀
  set ψ := extChartAt J (f₀ x₀)
  -- The first chart derivatives that are invertible, as `1`-multilinear maps.
  set V : Set (E [×1]→L[𝕜] F) :=
    {A | (continuousMultilinearCurryFin1 𝕜 E F A).IsInvertible} with hV
  have hVo : IsOpen V := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
    (continuousMultilinearCurryFin1 𝕜 E F).continuous
  -- In these charts, the test on the first derivative is invertibility of the manifold derivative.
  have hkey (f : C^n⟮I, M; J, N⟯) {z : E} (hz : z ∈ φ.target) (hfz : f (φ.symm z) ∈ ψ.source) :
      iteratedFDerivWithin 𝕜 1 (ψ ∘ f ∘ φ.symm) φ.target z ∈ V ↔
        (mfderiv I J f (φ.symm z)).IsInvertible := by
    have hcurry : continuousMultilinearCurryFin1 𝕜 E F
        (iteratedFDerivWithin 𝕜 1 (ψ ∘ f ∘ φ.symm) φ.target z) =
        fderivWithin 𝕜 (ψ ∘ f ∘ φ.symm) φ.target z := by
      ext v
      exact iteratedFDerivWithin_one_apply ((uniqueDiffOn_extChartAt_target x₀) z hz) _
    rw [hV, mem_ofPred_eq, hcurry]
    exact ((f.contMDiff.mdifferentiable hn0) _).isInvertible_fderivWithin_extChartAt_iff hz hfz
  -- A closed chart ball around `x₀` on which `f₀` stays in the chart at `f₀ x₀` and has
  -- invertible derivative.
  obtain ⟨r, hr, hrs⟩ : ∃ r > 0, Metric.closedBall (φ x₀) r ⊆ φ.target ∩
      (f₀ ∘ φ.symm) ⁻¹' ψ.source ∩ φ.symm ⁻¹' {x | (mfderiv I J f₀ x).IsInvertible} := by
    have hc : ContinuousAt φ.symm (φ x₀) :=
      continuousAt_extChartAt_symm'' (mem_extChartAt_target x₀)
    have hφ : φ.symm (φ x₀) = x₀ := extChartAt_to_inv x₀
    refine Metric.nhds_basis_closedBall.mem_iff.1 (inter_mem (inter_mem
      (extChartAt_target_mem_nhds x₀) ?_) (hc.preimage_mem_nhds (by rwa [hφ])))
    exact (f₀.contMDiff.continuous.continuousAt.comp_of_eq hc hφ).preimage_mem_nhds (by
      simpa only [Function.comp_apply, hφ, ψ] using extChartAt_source_mem_nhds (I := J) (f₀ x₀))
  let K : Set φ.target := Subtype.val ⁻¹' Metric.closedBall (φ x₀) r
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.2 fun z hz ↦ (hrs hz).1.1]
    exact isCompact_closedBall _ _
  -- The chart test over `K` is a neighbourhood of `f₀`, and the open chart ball is one of `x₀`.
  have hU : chartJetSet (n := n) (J := J) x₀ (f₀ x₀) 1 K V ∈ 𝓝 f₀ := by
    refine (isOpen_chartJetSet x₀ (f₀ x₀) 1 (by exact_mod_cast hn) hK hVo).mem_nhds ?_
    rw [mem_chartJetSet]
    rintro ⟨z, hzt⟩ hz
    have hz' := hrs hz
    exact ⟨hz'.1.2, (hkey f₀ hzt hz'.1.2).2 hz'.2⟩
  have hW : φ.source ∩ φ ⁻¹' Metric.ball (φ x₀) r ∈ 𝓝 x₀ :=
    inter_mem (extChartAt_source_mem_nhds x₀)
      ((continuousAt_extChartAt x₀).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  filter_upwards [prod_mem_prod hU hW] with ⟨f, x⟩ ⟨hf, hxs, hxb⟩
  have hz := hrs (Metric.ball_subset_closedBall hxb)
  have hfx := mem_chartJetSet.1 hf ⟨_, hz.1.1⟩ (Metric.ball_subset_closedBall hxb)
  have := (hkey f hz.1.1 hfx.1).1 hfx.2
  rwa [φ.left_inv hxs] at this

end Local

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [FiniteDimensional 𝕂 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕂 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕂 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold J n N]

/-- For `1 ≤ n`, the `C^n` local diffeomorphisms from a compact boundaryless manifold modelled on
a finite-dimensional space form an open subset of `C^n⟮I, M; J, N⟯` for the weak Whitney topology.
The target may have boundary and need not be compact. -/
theorem isOpen_setOfPred_isLocalDiffeomorph (hn : 1 ≤ n) :
    IsOpen {f : C^n⟮I, M; J, N⟯ | IsLocalDiffeomorph I J n f} := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕂 E
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  refine isOpen_iff_mem_nhds.2 fun f₀ hf₀ ↦ ?_
  -- Near `f₀`, every map has invertible derivatives on all of the compact `M`.
  have h := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := f₀)
    (P := fun (f : C^n⟮I, M; J, N⟯) x ↦ (mfderiv I J f x).IsInvertible) fun x _ ↦ by
      rw [nhds_prod_eq]
      exact eventually_isInvertible_mfderiv hn
        (Eventually.of_forall fun y ↦ (hf₀ y).isInvertible_mfderiv hn0)
  filter_upwards [h] with f hf
  exact TauCeti.isLocalDiffeomorph_of_mfderiv_eq f.contMDiff hn fun x ↦ hf x (mem_univ x)

end ContMDiffMap

end
