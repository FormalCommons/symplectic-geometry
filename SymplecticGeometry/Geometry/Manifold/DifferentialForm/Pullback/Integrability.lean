/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Geometry.Manifold.ContMDiff.Defs

/-!
# Integrability of the density of a two-form along a `C¹` map

Let `u : E' → M` be a map from a normed space into a manifold and `φ` a continuous two-form on
`M`. The density `z ↦ φ (u z) (du_z a, du_z b)` of `φ` along `u`, for fixed vectors `a` and `b`,
is continuous where `u` is `C¹` (Tau Ceti's `TauCeti.IsSmoothForm.continuousOn_apply_mfderiv`),
since the points where `u` is `C¹` form an open set (`TauCeti.isOpen_setOfPred_contMDiffAt`). So
it is integrable, for any measure finite on compact sets, over a compact set at each point of
which `u` is `C¹` (`TauCeti.IsSmoothForm.integrableOn_apply_mfderiv`), and, in a proper space,
over a bounded set at each point of whose closure `u` is `C¹`
(`TauCeti.SmoothForm.integrableOn_eval₂_mfderiv_of_isBounded`, for smooth forms and in the
notation `eval₂`).

Tau Ceti's `TauCeti.SmoothTwoForm.integrableOn_eval₂_mfderiv` states the compact case for maps of
the plane `ℝ × ℝ` that are `C¹` on an open set; the proof here is the same argument.

## Main results

* `TauCeti.IsSmoothForm.integrableOn_apply_mfderiv`: the density of a continuous two-form along
  a map that is `C¹` at each point of a compact set is integrable on that set.
* `TauCeti.SmoothForm.integrableOn_eval₂_mfderiv_of_isBounded`: the density of a smooth two-form
  along a map that is `C¹` at each point of the closure of a bounded set is integrable on that
  set.
-/

public section

open MeasureTheory
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [MeasurableSpace E'] [OpensMeasurableSpace E']
  {μ : Measure E'} [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {u : E' → M}

/-- **The density of a continuous two-form along a `C¹` map is integrable on compact sets.** If
`u : E' → M` is `C¹` at each point of a compact set `K`, then for a continuous two-form `φ` and
vectors `a` and `b`, the function `z ↦ φ (u z) (du_z a, du_z b)` is integrable on `K` for every
measure that is finite on compact sets. -/
theorem IsSmoothForm.integrableOn_apply_mfderiv {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) {K : Set E'} (hK : IsCompact K)
    (hu : ∀ z ∈ K, ContMDiffAt 𝓘(ℝ, E') I 1 u z) (a b : E') :
    IntegrableOn (fun z ↦ φ (u z) ![mfderiv 𝓘(ℝ, E') I u z a, mfderiv 𝓘(ℝ, E') I u z b]) K μ := by
  exact ((hφ.continuousOn_apply_mfderiv (isOpen_setOfPred_contMDiffAt (by simp))
    (fun _ hz ↦ hz.contMDiffWithinAt) a b).mono hu).integrableOn_compact hK

/-- **The density of a smooth two-form along a `C¹` map is integrable on bounded sets.** In a
proper space `E'`, if `u : E' → M` is `C¹` at each point of the closure of a bounded set `Ω`,
then for a smooth two-form `φ` and vectors `a` and `b`, the function
`z ↦ φ_{u z} (du_z a, du_z b)` is integrable on `Ω` for every measure that is finite on compact
sets. -/
theorem SmoothForm.integrableOn_eval₂_mfderiv_of_isBounded [ProperSpace E']
    (φ : SmoothForm I M F 2) {Ω : Set E'} (hΩ : Bornology.IsBounded Ω)
    (hu : ∀ z ∈ closure Ω, ContMDiffAt 𝓘(ℝ, E') I 1 u z) (a b : E') :
    IntegrableOn (fun z ↦ φ.eval₂ (u z) (mfderiv 𝓘(ℝ, E') I u z a)
      (mfderiv 𝓘(ℝ, E') I u z b)) Ω μ := by
  have h := (φ.isSmoothForm.of_le (by simp)).integrableOn_apply_mfderiv (μ := μ)
    hΩ.isCompact_closure hu a b
  simp only [← SmoothBundleForm.eval₂_apply] at h
  exact h.mono_set subset_closure

end TauCeti
