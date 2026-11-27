/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Module.Basic
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Asymptotics.TruncatedPowerSeries

/-!
# Polynomials that are little-o of their top power

A polynomial `∑_{i ≤ j} hⁱ • cᵢ` with vector coefficients that is `o(hʲ)` as `h → 0`, `h ≠ 0`,
has all its coefficients zero. This is the little-o companion of Tau Ceti's
`TauCeti.eq_zero_of_isBigO_sum_pow_smul`, which it uses for the coefficients of order `< j`.
The top term `hʲ • cⱼ` is then `o(hʲ)`, so `cⱼ = 0` by Tau Ceti's
`Asymptotics.isLittleO_smul_const_self_iff`.

## Main results

* `SymplecticGeometry.eq_zero_of_isLittleO_sum_pow_smul`: the coefficients of a polynomial of
  degree at most `j` that is `o(hʲ)` at `0` vanish.
-/

public section

open Asymptotics Filter Finset
open scoped Topology

namespace SymplecticGeometry

/-- If the polynomial `∑_{i ≤ j} hⁱ • cᵢ` is `o(hʲ)` as `h → 0`, `h ≠ 0`, then all its
coefficients `cᵢ`, `i ≤ j`, vanish. -/
theorem eq_zero_of_isLittleO_sum_pow_smul {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {j : ℕ} {c : ℕ → E}
    (hc : (fun h : 𝕜 ↦ ∑ i ∈ range (j + 1), h ^ i • c i) =o[𝓝[≠] 0] fun h ↦ h ^ j) :
    ∀ i ≤ j, c i = 0 := by
  have hlow : ∀ i < j, c i = 0 := TauCeti.eq_zero_of_isBigO_sum_pow_smul
    ((hc.isBigO.sub (isBigO_smul_const_self _ (c j) (norm_smul_le · (c j)))).congr_left
      fun h ↦ by simp [sum_range_succ])
  have htop : (fun h : 𝕜 ↦ h ^ j • c j) =o[𝓝[≠] 0] fun h ↦ h ^ j := by
    refine hc.congr_left fun h ↦ ?_
    rw [sum_range_succ, sum_eq_zero fun i hi ↦ by simp [hlow i (mem_range.1 hi)], zero_add]
  intro i hi
  rcases hi.lt_or_eq with hi | rfl
  · exact hlow i hi
  · exact (isLittleO_smul_const_self_iff (.of_forall fun _ ↦ norm_nonneg _)
      (eventually_mem_nhdsWithin.mono fun h (hh : h ≠ 0) ↦
        norm_ne_zero_iff.2 (pow_ne_zero _ hh)).frequently (norm_smul · _)).1 htop

end SymplecticGeometry

end
