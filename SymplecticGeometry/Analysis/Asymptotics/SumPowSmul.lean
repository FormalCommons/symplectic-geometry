/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Asymptotics.TruncatedPowerSeries

/-!
# Polynomials that are little-o of their top power

A polynomial `∑_{i ≤ j} hⁱ • cᵢ` with vector coefficients that is `o(hʲ)` as `h → 0`, `h ≠ 0`,
has all its coefficients zero. This is the little-o companion of Tau Ceti's
`TauCeti.eq_zero_of_isBigO_sum_pow_smul`, which it uses for the coefficients of order `< j`.
The last coefficient is then a constant that is `o(1)`, hence zero.

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
  have hconst : (fun _ : 𝕜 ↦ c j) =o[𝓝[≠] 0] fun _ ↦ (1 : 𝕜) := by
    refine ((isBigO_refl (fun h : 𝕜 ↦ (h ^ j)⁻¹) _).smul_isLittleO htop).congr' ?_ ?_ <;>
      filter_upwards [self_mem_nhdsWithin] with h (hh : h ≠ 0)
    · rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero j hh), one_smul]
    · rw [smul_eq_mul, inv_mul_cancel₀ (pow_ne_zero j hh)]
  intro i hi
  rcases hi.lt_or_eq with hi | rfl
  · exact hlow i hi
  · exact isLittleO_const_const_iff.1 hconst

end SymplecticGeometry

end
