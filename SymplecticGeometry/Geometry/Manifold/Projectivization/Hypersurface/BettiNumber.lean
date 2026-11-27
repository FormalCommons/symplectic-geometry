/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.EulerCharacteristic
public import TauCeti.AlgebraicTopology.Singular.BettiNumber

import SymplecticGeometry.AlgebraicTopology.Cellular.ComplexProjective.BettiNumber
import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.PoincareDuality
import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Lefschetz
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Manifold
import TauCeti.Geometry.Manifold.Morse.BettiNumber
import TauCeti.Topology.ComplexProjectiveSpace.Projectivization

/-!
# The Betti numbers of a smooth projective hypersurface

Let `X ⊆ ℂℙⁿ⁺¹` be a smooth projective hypersurface of degree `d ≠ 0`, of real dimension `2n`,
and write `b_k` for its rational Betti numbers. Away from the middle degree they are those of
`ℂℙⁿ`: `b_k = 1` for even `k ≤ 2n` with `k ≠ n`, and `b_k = 0` for the other `k ≠ n`. The middle
one is determined by the Euler characteristic: `(-1)ⁿ b_n = χ(X) - (n + 1) + [n even]`, where
`χ(X)` is given by `SmoothProjectiveHypersurface.eulerChar_eq`.

* Below the middle degree, `k < n`, the inclusion `X → ℂℙⁿ⁺¹` is an isomorphism on `H_k`
  (`SmoothProjectiveHypersurface.isIso_homologyMap_subtypeVal`, the Lefschetz hyperplane
  theorem), and the Betti numbers of `ℂℙⁿ⁺¹` are `TauCeti.bettiNumber_complexProjectiveSpace`.
* For `n < k ≤ 2n`, rational Poincaré duality for `X`, oriented by its complex structure
  (`SymplecticGeometry.complexManifoldHomologicalOrientation`), gives `b_k = b_{2n-k}`
  (`TauCeti.HomologicalOrientation.bettiNumber_eq_bettiNumber`).
* Above `2n` the Betti numbers of a compact manifold vanish
  (`TauCeti.bettiNumber_eq_zero_of_finrank_lt`).
* The Euler characteristic is the alternating sum of the Betti numbers up to the dimension
  (`TauCeti.eulerChar_eq_sum_range_finrank_singularHomology`), and the terms other than `b_n`
  contribute `n + 1 - [n even]` (`Finset.sum_range_ite_even`).

For `d = 0` the hypersurface is empty and both formulas fail when `n ≠ 0`. For `n = 0` they hold,
`X` being `d` points.

## Main results

The following are in the namespace `SymplecticGeometry.SmoothProjectiveHypersurface`.

* `bettiNumber_of_lt`: `b_k = [k even]` for `k < n`, over any ring with the strong rank condition.
* `bettiNumber_of_ne`: `b_k = [k even and k ≤ 2n]` for `k ≠ n`.
* `bettiNumber_middle`: `(-1)ⁿ b_n = χ(X) - (n + 1) + [n even]`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Examples 4.4.3 and 4.4.4 and Exercise 4.4.6.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton (1963), §7.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 2.44 and
  Section 3.3.
-/

public section

open CategoryTheory Module TauCeti
open scoped Manifold TauCeti.ComplexManifold

namespace SymplecticGeometry

namespace SmoothProjectiveHypersurface

variable {n d : ℕ} (X : SmoothProjectiveHypersurface n d)

/-- **The Betti numbers of a hypersurface below the middle degree.** For `d ≠ 0` and `k < n`, the
`k`-th Betti number, with coefficients in a ring `R` with the strong rank condition, of a smooth
hypersurface `X ⊆ ℂℙⁿ⁺¹` is `1` if `k` is even and `0` if `k` is odd. -/
theorem bettiNumber_of_lt (R : Type) [Ring R] [StrongRankCondition R] (hd : d ≠ 0) {k : ℕ}
    (hk : k < n) : bettiNumber R X k = if Even k then 1 else 0 := by
  have : IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) k).obj
      (ModuleCat.of R R)).map (TopCat.ofHom (ContinuousMap.subtypeVal X.carrier))) := by
    rw [TauCeti.singularHomologyFunctor_obj_map]
    exact X.isIso_homologyMap_subtypeVal hd _ hk
  rw [bettiNumber_def, (asIso (((AlgebraicTopology.singularHomologyFunctor _ k).obj
      (ModuleCat.of R R)).map (TopCat.ofHom (ContinuousMap.subtypeVal X.carrier)))
      ).toLinearEquiv.finrank_eq, ← bettiNumber_def,
    ← (ComplexProjectiveSpace.homeomorphProjectivization (n + 1)).toHomotopyEquiv.bettiNumber_eq,
    bettiNumber_complexProjectiveSpace]
  grind

/-- **The Betti numbers of a hypersurface outside the middle degree.** For `d ≠ 0` and `k ≠ n`,
the `k`-th rational Betti number of a smooth hypersurface `X ⊆ ℂℙⁿ⁺¹` is `1` if `k` is even with
`k ≤ 2n`, and `0` otherwise, as for `ℂℙⁿ`. -/
theorem bettiNumber_of_ne (hd : d ≠ 0) {k : ℕ} (hk : k ≠ n) :
    bettiNumber ℚ X k = if Even k ∧ k ≤ 2 * n then 1 else 0 := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · rw [X.bettiNumber_of_lt ℚ hd hk]
    grind
  by_cases hk' : k ≤ 2 * n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : n ≠ 0)
    have hE : finrank ℝ (Fin (m + 1) → ℂ) =
        2 * m + 1 + 1 :=
      finrank_real_of_finrank_complex_eq_add_one (Module.finrank_fin_fun ℂ)
    rw [(complexManifoldHomologicalOrientation (Fin (m + 1) → ℂ) X
        (Module.finrank_fin_fun ℂ)).bettiNumber_eq_bettiNumber hE ℚ
        (p := 2 * (m + 1) - k) (by omega),
      X.bettiNumber_of_lt ℚ hd (by omega)]
    simp [hk', Nat.even_sub hk']
  · rw [ite_eq_right_iff.2 fun h ↦ absurd h.2 hk']
    exact bettiNumber_eq_zero_of_finrank_lt X
      (𝓘(ℂ, Fin n → ℂ).restrictScalars ℝ) ℚ
      (by rw [finrank_real_of_complex, Module.finrank_fin_fun]; omega)

/-- **The middle Betti number of a hypersurface.** For `d ≠ 0`, the `n`-th rational Betti number
of a smooth hypersurface `X ⊆ ℂℙⁿ⁺¹` satisfies `(-1)ⁿ b_n = χ(X) - (n + 1) + [n even]`, where
`[n even]` is `1` for even `n` and `0` for odd `n`. -/
theorem bettiNumber_middle (hd : d ≠ 0) :
    (-1 : ℤ) ^ n * bettiNumber ℚ X n = eulerChar X - (n + 1) + if Even n then 1 else 0 := by
  have h := eulerChar_eq_sum_range_finrank_singularHomology
    (E := Fin n → ℂ) X ℚ
  simp only [← bettiNumber_def, finrank_real_of_complex, Module.finrank_fin_fun] at h
  have hn : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.2 (by omega)
  have hterm : ∀ i ∈ (Finset.range (2 * n + 1)).erase n,
      (-1 : ℤ) ^ i * bettiNumber ℚ X i = if Even i then 1 else 0 := by
    intro i hi
    have := Finset.mem_range.1 (Finset.mem_of_mem_erase hi)
    rw [X.bettiNumber_of_ne hd (Finset.ne_of_mem_erase hi)]
    split_ifs <;> simp_all
  rw [h, ← Finset.add_sum_erase _ _ hn, Finset.sum_congr rfl hterm, Finset.sum_erase_eq_sub hn,
    Finset.sum_range_ite_even (fun _ ↦ (1 : ℤ)), show (2 * n + 1 + 1) / 2 = n + 1 by omega]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  ring

end SmoothProjectiveHypersurface

end SymplecticGeometry

end
