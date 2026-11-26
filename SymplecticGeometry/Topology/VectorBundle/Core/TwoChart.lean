/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Topology.VectorBundle.Basic
import SymplecticGeometry.Algebra.GroupWithZero.Units.Lemmas
import SymplecticGeometry.Topology.VectorBundle.Core.Basic
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# Vector bundle cores with two charts

Let `U₁` and `U₂` be open sets that cover a topological space `B`, `G` a group,
`ρ : G →* (F →L[𝕜] F)` a representation of `G` on a complete normed space `F`, and `g : B → G` a
map such that `x ↦ ρ (g x)` is continuous on `U₁ ∩ U₂`. This file glues the trivial bundles
`U₁ × F` and `U₂ × F` along `ρ ∘ g`: the vector `v` over `x` in the chart of `U₂` is the vector
`ρ (g x) v` in the chart of `U₁`. Such bundles arise by clutching, for instance over a surface
cut along a circle.

The charts are indexed by `Bool`, `true` for `U₁` and `false` for `U₂`, and the coordinate change
from the chart `i` to the chart `j` is `ρ (g x ^ (j - i))` (`twoChartCocycle`), which is defined at
every point, not only on `U₁ ∩ U₂`. Its continuity for `true → false` comes from that of
`Ring.inverse` at the units of the complete normed ring `F →L[𝕜] F`
(`ContinuousAt.ringInverse`), since `ρ (g x)⁻¹ = Ring.inverse (ρ (g x))`
(`map_inv_eq_ringInverse`).

## Main definitions

* `SymplecticGeometry.Bundle.twoChartCocycle g i j x`: the element `g x ^ (j - i)` of `G`.
* `SymplecticGeometry.Bundle.twoChartCore U₁ U₂ ρ g`: the vector bundle core with fibre `F`, two
  charts over `U₁` and `U₂`, and coordinate change `ρ (g x)` from the second to the first.

The identification of its fibres with `F` is `VectorBundleCore.fiberEquiv`, under which the
inverse of the chart `i` at `x` is the coordinate change `ρ (g x ^ (indexAt x - i))`
(`VectorBundleCore.fiberEquiv_localTriv_symm`).
-/

public section

noncomputable section

open Set

namespace SymplecticGeometry

namespace Bundle

/-! ### The cocycle -/

section Cocycle

variable {X G : Type*} [Group G] (g : X → G)

/-- The cocycle of two charts glued along `g`: from the chart `i` to the chart `j` at `x`, the
element `g x ^ (j - i)`, where `true` counts as `1` and `false` as `0`. -/
def twoChartCocycle (i j : Bool) (x : X) : G :=
  g x ^ ((j.toNat : ℤ) - i.toNat)

theorem twoChartCocycle_def (i j : Bool) (x : X) :
    twoChartCocycle g i j x = g x ^ ((j.toNat : ℤ) - i.toNat) :=
  (rfl)

@[simp]
theorem twoChartCocycle_self (i : Bool) (x : X) : twoChartCocycle g i i x = 1 := by
  simp [twoChartCocycle_def]

/-- From the chart `false` to the chart `true`, the cocycle is `g`. -/
@[simp]
theorem twoChartCocycle_false_true (x : X) : twoChartCocycle g false true x = g x := by
  simp [twoChartCocycle_def]

/-- From the chart `true` to the chart `false`, the cocycle is `g⁻¹`. -/
@[simp]
theorem twoChartCocycle_true_false (x : X) : twoChartCocycle g true false x = (g x)⁻¹ := by
  simp [twoChartCocycle_def]

/-- The cocycle condition: from `i` to `j`, then from `j` to `l`, is from `i` to `l`. -/
theorem twoChartCocycle_mul (i j l : Bool) (x : X) :
    twoChartCocycle g j l x * twoChartCocycle g i j x = twoChartCocycle g i l x := by
  rw [twoChartCocycle_def, twoChartCocycle_def, twoChartCocycle_def, ← zpow_add]
  congr 1
  ring

end Cocycle

/-! ### The core -/

section Core

variable {𝕜 B F G : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [Group G]

/-- If `x ↦ ρ (g x)` is continuous on `U₁ ∩ U₂`, then the coordinate change
`x ↦ ρ (g x ^ (j - i))` of the two charts is continuous where both charts are defined. -/
theorem continuousOn_twoChartCocycle {U₁ U₂ : Set B} (ρ : G →* (F →L[𝕜] F)) {g : B → G}
    (hg : ContinuousOn (fun x ↦ ρ (g x)) (U₁ ∩ U₂)) (i j : Bool) :
    ContinuousOn (fun x ↦ ρ (twoChartCocycle g i j x))
      ((bif i then U₁ else U₂) ∩ (bif j then U₁ else U₂)) := by
  cases i <;> cases j
  · simpa using continuousOn_const
  · simpa [inter_comm] using hg
  · simp only [twoChartCocycle_true_false, map_inv_eq_ringInverse]
    refine fun x hx ↦ ContinuousAt.comp_continuousWithinAt (g := Ring.inverse) ?_ (hg x hx)
    exact continuousAt_id.ringInverse ((Group.isUnit (g x)).map ρ)
  · simpa using continuousOn_const

variable (U₁ U₂ : Set B) (ρ : G →* (F →L[𝕜] F)) (g : B → G) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
  (hU : U₁ ∪ U₂ = univ) (hg : ContinuousOn (fun x ↦ ρ (g x)) (U₁ ∩ U₂))

open scoped Classical in
/-- **The bundle of two charts glued along `ρ ∘ g`.** Over open sets `U₁` and `U₂` covering `B`,
the vector bundle core with fibre `F` and two charts, `true` over `U₁` and `false` over `U₂`,
whose coordinate change from the chart `i` to the chart `j` is `ρ (g x ^ (j - i))`; from the
second chart to the first, it is `ρ (g x)`. The preferred chart at `x` is the first one when
`x ∈ U₁`. -/
def twoChartCore : VectorBundleCore 𝕜 B F Bool where
  baseSet b := bif b then U₁ else U₂
  isOpen_baseSet b := by cases b <;> assumption
  indexAt x := decide (x ∈ U₁)
  mem_baseSet_at x := by
    by_cases hx : x ∈ U₁
    · simp [hx]
    · simpa [hx] using (hU.symm ▸ mem_univ x : x ∈ U₁ ∪ U₂).resolve_left hx
  coordChange i j x := ρ (twoChartCocycle g i j x)
  coordChange_self i x _ v := by simp
  continuousOn_coordChange i j := continuousOn_twoChartCocycle ρ hg i j
  coordChange_comp i j l x _ v := by
    rw [← mul_apply_eq_comp, ← map_mul, twoChartCocycle_mul]

/-- The base set of the chart `b` is `U₁` for `b = true` and `U₂` for `b = false`. -/
theorem baseSet_twoChartCore (b : Bool) :
    (twoChartCore U₁ U₂ ρ g hU₁ hU₂ hU hg).baseSet b = bif b then U₁ else U₂ :=
  (rfl)

/-- The base set of the first chart is `U₁`. -/
theorem baseSet_twoChartCore_true : (twoChartCore U₁ U₂ ρ g hU₁ hU₂ hU hg).baseSet true = U₁ :=
  (rfl)

/-- The base set of the second chart is `U₂`. -/
theorem baseSet_twoChartCore_false : (twoChartCore U₁ U₂ ρ g hU₁ hU₂ hU hg).baseSet false = U₂ :=
  (rfl)

/-- The first chart lies over `U₁`. -/
@[simp]
theorem baseSet_localTriv_twoChartCore_true :
    ((twoChartCore U₁ U₂ ρ g hU₁ hU₂ hU hg).localTriv true).baseSet = U₁ :=
  (rfl)

/-- The second chart lies over `U₂`. -/
@[simp]
theorem baseSet_localTriv_twoChartCore_false :
    ((twoChartCore U₁ U₂ ρ g hU₁ hU₂ hU hg).localTriv false).baseSet = U₂ :=
  (rfl)

open scoped Classical in
/-- The preferred chart at `x` is the first one exactly when `x ∈ U₁`. -/
@[simp]
theorem indexAt_twoChartCore (x : B) :
    (twoChartCore U₁ U₂ ρ g hU₁ hU₂ hU hg).indexAt x = decide (x ∈ U₁) :=
  (rfl)

/-- The coordinate change from the chart `i` to the chart `j` is `ρ (g x ^ (j - i))`. -/
@[simp]
theorem coordChange_twoChartCore (i j : Bool) (x : B) :
    (twoChartCore U₁ U₂ ρ g hU₁ hU₂ hU hg).coordChange i j x = ρ (twoChartCocycle g i j x) :=
  (rfl)

end Core

end Bundle

end SymplecticGeometry

end

end
