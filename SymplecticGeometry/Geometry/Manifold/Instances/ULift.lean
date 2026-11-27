/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import SymplecticGeometry.Topology.Constructions.ULift

/-!
# The universe lift of a manifold

For a space `M` charted on `H`, the lift `ULift M` to a higher universe is charted on `H` by the
charts of `M` precomposed with the homeomorphism `Homeomorph.ulift : ULift M ≃ₜ M`: this is the
structure that Tau Ceti's `Homeomorph.pullbackChartedSpace` pulls back along a homeomorphism. A
`C^n` manifold over `I` lifts to a `C^n` manifold over `I`, and for every model `I` on `H` the map
`ULift.down` is a `C^n` diffeomorphism. This lets a manifold in `Type` be a piece of a
construction, such as a gluing, whose pieces share a universe.

## Main definitions

* `ULift.instChartedSpace`, `ULift.instIsManifold`: the charted space and manifold structures of
  `ULift M`, with `ULift.chartAt_eq` giving its charts.
* `Diffeomorph.ulift`: `ULift.down`, as a `C^n` diffeomorphism `ULift M ≃ₘ^n⟮I, I⟯ M`
  (Tau Ceti's `Homeomorph.pullbackDiffeomorph`).
-/

public section

noncomputable section

open scoped Manifold ContDiff

universe u v

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

namespace ULift

/-- The charts of `ULift M`: those of `M`, precomposed with `Homeomorph.ulift`. -/
instance instChartedSpace : ChartedSpace H (ULift.{v} M) :=
  Homeomorph.ulift.pullbackChartedSpace

/-- The chart of `ULift M` at `x` is the chart of `M` at `x.down`, precomposed with
`Homeomorph.ulift`. -/
theorem chartAt_eq (x : ULift.{v} M) :
    chartAt H x = Homeomorph.ulift.transOpenPartialHomeomorph (chartAt H x.down) :=
  (rfl)

/-- The universe lift of a `C^n` manifold is a `C^n` manifold over the same model. -/
instance instIsManifold [IsManifold I n M] : IsManifold I n (ULift.{v} M) :=
  Homeomorph.ulift.pullback_isManifold I n

end ULift

namespace Diffeomorph

variable (I n M) in
/-- `ULift.down`, as a `C^n` diffeomorphism from the universe lift `ULift M` of a space charted
on `H` onto `M`, for any model `I` on `H`. -/
def ulift : ULift.{v} M ≃ₘ^n⟮I, I⟯ M :=
  Homeomorph.ulift.pullbackDiffeomorph I n

@[simp]
theorem coe_ulift : ⇑(ulift I n M : ULift.{v} M ≃ₘ^n⟮I, I⟯ M) = ULift.down :=
  Homeomorph.ulift.coe_pullbackDiffeomorph I n

@[simp]
theorem coe_ulift_symm : ⇑(ulift I n M : ULift.{v} M ≃ₘ^n⟮I, I⟯ M).symm = ULift.up :=
  Homeomorph.ulift.coe_pullbackDiffeomorph_symm I n

@[simp]
theorem toHomeomorph_ulift :
    (ulift I n M : ULift.{v} M ≃ₘ^n⟮I, I⟯ M).toHomeomorph = Homeomorph.ulift :=
  Homeomorph.ulift.pullbackDiffeomorph_toHomeomorph I n

end Diffeomorph

end
