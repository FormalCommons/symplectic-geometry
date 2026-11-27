/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart.Deriv

/-!
# Sobolev sections of order `k + 1` regarded as sections of order one

Let `C : TauCeti.SectionChartData E F S` be chart data. A Sobolev section of order `k + 1`,
an element of `C.sobolevSections μ p (k + 1)`, is also one of order one, by forgetting its `k`
highest weak derivatives (`TauCeti.SectionChartData.toOrderOne`). This does not change its chart
data (`TauCeti.SectionChartData.chartValueL_toOrderOne`), and the order-one weak derivative
`TauCeti.SectionChartData.chartDerivL` of the section regarded as one of order one is, almost
everywhere, the function assembled from the order-`k` components
`TauCeti.SectionChartData.chartDerivDataL` of its weak derivative
(`TauCeti.SectionChartData.sum_value_chartDerivDataL_ae_eq_chartDerivL_toOrderOne`). This lets a
statement about the weak derivative at order one, such as its transformation on chart overlaps,
be used at every order.

The definition and the first lemma generalize the private `toOrderOne` and
`chartValueL_toOrderOne` of Tau Ceti's
`Geometry/Manifold/VectorBundle/Sobolev/CauchyRiemann/HigherOrder/Basic.lean` from the Sobolev
sections of a finite bundle atlas to those of any chart data. The last lemma is the order-`k`
counterpart of `TauCeti.SectionChartData.sum_value_chartDerivDataL_zero_ae_eq_chartDerivL`, and is
proved in the same way, by uniqueness of weak derivatives.

## Main definitions

* `TauCeti.SectionChartData.toOrderOne`: a Sobolev section of order `k + 1` regarded as one of
  order one.

## Main results

* `TauCeti.SectionChartData.chartValueL_toOrderOne`: the chart data are unchanged.
* `TauCeti.SectionChartData.sum_value_chartDerivDataL_ae_eq_chartDerivL_toOrderOne`: the
  order-one weak derivative is assembled from the order-`k` components `chartDerivDataL`.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ENNReal

universe u

namespace TauCeti

namespace SectionChartData

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : Type*} [AddCommGroup S] [Module ℝ S] (C : SectionChartData E F S)
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- A Sobolev section of order `k + 1` regarded as one of order one, by forgetting its `k`
highest weak derivatives. -/
def toOrderOne (w : C.sobolevSections μ p (k + 1)) : C.sobolevSections μ p 1 :=
  C.lowerOrdersL μ p 1 k ((Nat.add_comm k 1) ▸ w)

theorem toOrderOne_def (w : C.sobolevSections μ p (k + 1)) :
    C.toOrderOne μ p k w = C.lowerOrdersL μ p 1 k ((Nat.add_comm k 1) ▸ w) :=
  (rfl)

/-- Regarding a Sobolev section of order `k + 1` as one of order one does not change its reading
in any chart. -/
@[simp]
theorem chartValueL_toOrderOne (w : C.sobolevSections μ p (k + 1)) (i : Fin C.n) :
    C.chartValueL μ p 1 i (C.toOrderOne μ p k w) = C.chartValueL μ p (k + 1) i w := by
  rw [toOrderOne_def, chartValueL_lowerOrdersL, chartValueL_eqRec]

/-- `toOrderOne` as a continuous linear map, built by lowering the order one step at a time
(`TauCeti.SectionChartData.toOrderOneL_apply`). -/
def toOrderOneL : (k : ℕ) → C.sobolevSections μ p (k + 1) →L[ℝ] C.sobolevSections μ p 1
  | 0 => ContinuousLinearMap.id ℝ _
  | k + 1 => (toOrderOneL k).comp (C.lowerOrderL μ p (k + 1))

/-- `toOrderOneL` does not change the chart data. -/
theorem chartValuesL_toOrderOneL (w : C.sobolevSections μ p (k + 1)) :
    C.chartValuesL μ p 1 (C.toOrderOneL μ p k w) = C.chartValuesL μ p (k + 1) w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [toOrderOneL, ContinuousLinearMap.comp_apply, ih, chartValuesL_lowerOrderL]

/-- `toOrderOneL` is `toOrderOne`. -/
@[simp]
theorem toOrderOneL_apply (w : C.sobolevSections μ p (k + 1)) :
    C.toOrderOneL μ p k w = C.toOrderOne μ p k w :=
  C.chartValuesL_injective μ p 1 <| funext fun i ↦ by
    rw [chartValuesL_toOrderOneL, chartValuesL_apply, chartValuesL_apply, chartValueL_toOrderOne]

/-- Almost everywhere on the image of chart `i`, the function assembled from the order-`k`
components `chartDerivDataL` of the weak derivative of a Sobolev section `w` of order `k + 1` is
the order-one weak derivative `chartDerivL` of `w` regarded as a section of order one. -/
theorem sum_value_chartDerivDataL_ae_eq_chartDerivL_toOrderOne (i : Fin C.n)
    (w : C.sobolevSections μ p (k + 1)) :
    (fun y ↦ ∑ a, Wkp.value k (C.chartDerivDataL μ p k i w a) y • finBasis ℝ (E →L[ℝ] F) a)
      =ᵐ[μ.restrict (C.image i)] C.chartDerivL μ p i (C.toOrderOne μ p k w) := by
  have hDu := C.hasWeakFDerivOn_chartValueL_chartDerivDataL μ p k i w
  rw [← chartValueL_toOrderOne] at hDu
  exact hDu.ae_eq (C.hasWeakFDerivOn_chartValueL μ p i (C.toOrderOne μ p k w))

end SectionChartData

end TauCeti

end
