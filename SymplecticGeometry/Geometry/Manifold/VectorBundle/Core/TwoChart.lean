/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import SymplecticGeometry.Topology.VectorBundle.Core.TwoChart
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import SymplecticGeometry.Algebra.GroupWithZero.Units.Lemmas

/-!
# Smoothness of vector bundle cores with two charts

The core `SymplecticGeometry.Bundle.twoChartCore U₁ U₂ ρ g`, glued from two charts over `U₁` and
`U₂` along `x ↦ ρ (g x)`, is a `C^n` vector bundle core as soon as `x ↦ ρ (g x)` is `C^n` on
`U₁ ∩ U₂` (`SymplecticGeometry.Bundle.isContMDiff_twoChartCore`). The coordinate change from the
first chart to the second is `ρ (g x)⁻¹ = Ring.inverse (ρ (g x))`, which is `C^n` because
`Ring.inverse` is analytic at the units of the complete normed algebra `F →L[𝕜] F`
(`ContDiffAt.inverse`).
-/

public section

open Set
open scoped Manifold

namespace SymplecticGeometry

namespace Bundle

variable {𝕜 B F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] [Group G] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {n : WithTop ℕ∞}

/-- If `x ↦ ρ (g x)` is `C^n` on `U₁ ∩ U₂`, then the coordinate change `x ↦ ρ (g x ^ (j - i))` of
the two charts is `C^n` where both charts are defined. -/
theorem contMDiffOn_twoChartCocycle {U₁ U₂ : Set B} (ρ : G →* (F →L[𝕜] F)) {g : B → G}
    (hg : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x ↦ ρ (g x)) (U₁ ∩ U₂)) (i j : Bool) :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x ↦ ρ (twoChartCocycle g i j x))
      ((bif i then U₁ else U₂) ∩ (bif j then U₁ else U₂)) := by
  cases i <;> cases j
  · simpa using contMDiffOn_const
  · simpa [inter_comm] using hg
  · simp only [twoChartCocycle_true_false, map_inv_eq_ringInverse]
    refine fun x hx ↦ ContMDiffAt.comp_contMDiffWithinAt (g := Ring.inverse) x ?_ (hg x hx)
    exact (contDiffAt_id.inverse ((Group.isUnit (g x)).map ρ)).contMDiffAt
  · simpa using contMDiffOn_const

/-- **Smoothness of the bundle of two charts.** If `x ↦ ρ (g x)` is `C^n` on `U₁ ∩ U₂`, then the
core `twoChartCore U₁ U₂ ρ g` is `C^n`. -/
theorem isContMDiff_twoChartCore {U₁ U₂ : Set B} (ρ : G →* (F →L[𝕜] F)) {g : B → G}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : U₁ ∪ U₂ = univ)
    (hg : ContinuousOn (fun x ↦ ρ (g x)) (U₁ ∩ U₂))
    (hg' : ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x ↦ ρ (g x)) (U₁ ∩ U₂)) :
    (twoChartCore U₁ U₂ ρ g hU₁ hU₂ hU hg).IsContMDiff IB n where
  contMDiffOn_coordChange i j := by
    rw [baseSet_twoChartCore, baseSet_twoChartCore]
    exact (contMDiffOn_twoChartCocycle ρ hg' i j).congr fun x _ ↦
      coordChange_twoChartCore U₁ U₂ ρ g hU₁ hU₂ hU hg i j x

end Bundle

end SymplecticGeometry

end
