/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Chart

/-!
# Local diffeomorphisms form an open set of `C^n` maps

This file proves that being a local diffeomorphism is an open condition in Tau Ceti's weak
Whitney topology on `C^n` maps out of a compact boundaryless manifold. It is the first step
towards the openness of diffeomorphisms among `C^1` maps of a compact manifold, which the
smoothing of families of diffeomorphisms uses.

* `ContMDiffMap.eventually_isInvertible_mfderiv`: the local step. If `f₀` has invertible
  manifold derivative at `x₀`, then so does every map near `f₀`, at every point near `x₀`.
  Tau Ceti's `TauCeti.tendsto_fderivWithin_extChartAt` makes the chart derivative continuous in
  the map and the point, invertible linear maps form an open set, and the chart derivative is
  read as the manifold derivative by `MDifferentiableAt.isInvertible_fderivWithin_extChartAt_iff`.
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
invertible manifold derivative at `x₀`, then every `C^n` map near `f₀` in the weak Whitney
topology has invertible manifold derivative at every point near `x₀`. -/
theorem eventually_isInvertible_mfderiv (hn : 1 ≤ n) {f₀ : C^n⟮I, M; J, N⟯} {x₀ : M}
    (hf₀ : (mfderiv I J f₀ x₀).IsInvertible) :
    ∀ᶠ p in 𝓝 f₀ ×ˢ 𝓝 x₀, (mfderiv I J p.1 p.2).IsInvertible := by
  have : IsManifold I 1 M := .of_le hn
  have : IsManifold J 1 N := .of_le hn
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  set φ := extChartAt I x₀
  set ψ := extChartAt J (f₀ x₀)
  have hw₀ : φ x₀ ∈ φ.target := mem_extChartAt_target x₀
  have hφo : IsOpen φ.target := isOpen_extChartAt_target x₀
  have hf₀w₀ : f₀ (φ.symm (φ x₀)) ∈ ψ.source := by
    rw [extChartAt_to_inv]
    exact mem_extChartAt_source (f₀ x₀)
  -- In these charts, invertibility of the chart derivative is that of the manifold derivative.
  have hkey (f : C^n⟮I, M; J, N⟯) {z : E} (hz : z ∈ φ.target) (hfz : f (φ.symm z) ∈ ψ.source) :=
    ((f.contMDiff.mdifferentiable hn0) _).isInvertible_fderivWithin_extChartAt_iff hz hfz
  -- Near `(f₀, φ x₀)`, maps stay in the target chart and have invertible chart derivatives.
  have hev : ∀ᶠ p : C^n⟮I, M; J, N⟯ × E in 𝓝 f₀ ×ˢ 𝓝 (φ x₀),
      p.2 ∈ φ.target ∧ p.1 (φ.symm p.2) ∈ ψ.source ∧
        (fderivWithin 𝕜 (ψ ∘ p.1 ∘ φ.symm) φ.target p.2).IsInvertible := by
    rw [← hφo.nhdsWithin_eq hw₀]
    have hinv := (hkey f₀ hw₀ hf₀w₀).2 (by rwa [extChartAt_to_inv])
    filter_upwards [prod_mem_prod univ_mem self_mem_nhdsWithin,
      ContMDiffMap.eventually_mem_extChartAt_source hw₀ hf₀w₀,
      (TauCeti.tendsto_fderivWithin_extChartAt hn hw₀ hf₀w₀).eventually
        (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hinv)] with p h₁ h₂ h₃
    exact ⟨h₁.2, h₂, h₃⟩
  have hφ : Tendsto (fun p : C^n⟮I, M; J, N⟯ × M ↦ (p.1, φ p.2)) (𝓝 f₀ ×ˢ 𝓝 x₀)
      (𝓝 f₀ ×ˢ 𝓝 (φ x₀)) :=
    tendsto_fst.prodMk ((continuousAt_extChartAt x₀).tendsto.comp tendsto_snd)
  filter_upwards [hφ.eventually hev,
    prod_mem_prod univ_mem (extChartAt_source_mem_nhds (I := I) x₀)]
    with ⟨f, x⟩ ⟨hz, hfz, hinv⟩ ⟨_, hx⟩
  have h := (hkey f hz hfz).1 hinv
  rwa [φ.left_inv hx] at h

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
      exact eventually_isInvertible_mfderiv hn ((hf₀ x).isInvertible_mfderiv hn0)
  filter_upwards [h] with f hf
  exact TauCeti.isLocalDiffeomorph_of_mfderiv_eq f.contMDiff hn fun x ↦ hf x (mem_univ x)

end ContMDiffMap

end
