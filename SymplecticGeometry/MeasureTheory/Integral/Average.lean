/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Set averages through lower averages of `ofReal (K - u)`

* `MeasureTheory.setAverage_le_of_ae_le`: if a real function `u` is integrable on a set `s` of
  finite positive measure and `u ≤ K` almost everywhere on `s`, then `⨍ x in s, u x ∂μ ≤ K`,
  by Tau Ceti's `TauCeti.average_mono_ae`.
* `MeasureTheory.setLAverage_ofReal_sub_eq`: if a real function `u` is integrable on a set `s`
  of finite positive measure and `u ≤ K` almost everywhere on `s`, then
  `⨍⁻ x in s, ofReal (K - u x) ∂μ = ofReal (K - ⨍ x in s, u x ∂μ)`.
* `MeasureTheory.sub_setAverage_le_of_setLAverage_ofReal_sub_le`: if a real function `u` is
  integrable on a set `s` of finite positive measure, then a bound
  `⨍⁻ x in s, ofReal (K - u x) ∂μ ≤ ofReal L`, with `0 ≤ L`, gives `K - ⨍ x in s, u x ∂μ ≤ L`.

The last two lemmas pass from the lower average of `ofReal (K - u)` over `s`, an extended
nonnegative quantity, to the Bochner average of `u` over `s`. When `u ≤ K` almost everywhere on
`s`, the `ofReal` loses nothing, and the identity computes the lower average from the average of
`u`.
When only a bound on the lower average is known, as a sub-mean value inequality gives, the
inequality turns it into a lower bound on the average of `u`.
-/

public section

namespace MeasureTheory

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- If `u` is integrable on a set `s` with `0 < μ s < ∞` and `u ≤ K` almost everywhere on `s`,
then the average of `u` over `s` is at most `K`. -/
theorem setAverage_le_of_ae_le {μ : Measure α} {s : Set α} {u : α → ℝ} {K : ℝ}
    (h0 : μ s ≠ 0) (hfin : μ s ≠ ∞) (hu : IntegrableOn u s μ)
    (hK : ∀ᵐ x ∂μ.restrict s, u x ≤ K) :
    ⨍ x in s, u x ∂μ ≤ K :=
  (TauCeti.average_mono_ae hu (integrableOn_const hfin) hK).trans_eq (setAverage_const h0 hfin K)

/-- If `u` is integrable on a set `s` with `0 < μ s < ∞` and `u ≤ K` almost everywhere on `s`,
then the lower average of `ofReal (K - u)` over `s` is `ofReal (K - ⨍ x in s, u x ∂μ)`. -/
theorem setLAverage_ofReal_sub_eq {μ : Measure α} {s : Set α} {u : α → ℝ} {K : ℝ}
    (h0 : μ s ≠ 0) (hfin : μ s ≠ ∞) (hu : IntegrableOn u s μ)
    (hK : ∀ᵐ x ∂μ.restrict s, u x ≤ K) :
    ⨍⁻ x in s, ENNReal.ofReal (K - u x) ∂μ = ENNReal.ofReal (K - ⨍ x in s, u x ∂μ) := by
  rw [setLAverage_eq, ← ofReal_setAverage (f := fun x => K - u x)
    ((integrableOn_const hfin).sub hu) (hK.mono fun _ => sub_nonneg.2),
    setAverage_fun_sub (integrableOn_const hfin) hu, setAverage_const h0 hfin]

/-- If `u` is integrable on a set `s` with `0 < μ s < ∞`, and `0 ≤ L`, then
`⨍⁻ x in s, ofReal (K - u x) ∂μ ≤ ofReal L` gives `K - ⨍ x in s, u x ∂μ ≤ L`. -/
theorem sub_setAverage_le_of_setLAverage_ofReal_sub_le
    {μ : Measure α} {s : Set α} {u : α → ℝ} {K L : ℝ}
    (h0 : μ s ≠ 0) (hfin : μ s ≠ ∞) (hu : IntegrableOn u s μ) (hL : 0 ≤ L)
    (h : ⨍⁻ x in s, ENNReal.ofReal (K - u x) ∂μ ≤ ENNReal.ofReal L) :
    K - ⨍ x in s, u x ∂μ ≤ L := by
  rw [← setAverage_const h0 hfin K, ← setAverage_fun_sub (integrableOn_const hfin) hu,
    setAverage_eq']
  rw [setLAverage_eq'] at h
  exact (ENNReal.ofReal_le_ofReal_iff hL).1
    (TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal.trans h)

end MeasureTheory

end
