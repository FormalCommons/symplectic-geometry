/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Lebesgue measure on a Euclidean space indexed by a sum

The continuous linear equivalence `EuclideanSpace.sumEquivProd` between `EuclideanSpace ℝ (ι ⊕ κ)`
and the product `EuclideanSpace ℝ ι × EuclideanSpace ℝ κ` carries Lebesgue measure to Lebesgue
measure (`EuclideanSpace.volume_preserving_sumEquivProd`). It is the composite of the isometry
`PiLp.sumPiLpEquivProdLpPiLp` onto the `L²` product, which preserves volume as every linear
isometry does, and of `WithLp.ofLp`, which preserves volume by `WithLp.volume_preserving_ofLp`.
-/

public section

open MeasureTheory

/-- The identification `EuclideanSpace.sumEquivProd` of `EuclideanSpace ℝ (ι ⊕ κ)` with
`EuclideanSpace ℝ ι × EuclideanSpace ℝ κ` preserves Lebesgue measure. -/
theorem EuclideanSpace.volume_preserving_sumEquivProd (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := ι) (κ := κ)) :=
  (WithLp.volume_preserving_ofLp _ _).comp
    (PiLp.sumPiLpEquivProdLpPiLp 2 fun _ : ι ⊕ κ ↦ ℝ).measurePreserving

end
