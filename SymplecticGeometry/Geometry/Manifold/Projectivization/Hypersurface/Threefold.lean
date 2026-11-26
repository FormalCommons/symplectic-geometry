/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module


import SymplecticGeometry.AlgebraicTopology.Cohomology.Empty
import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.BettiNumber
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.ChernClass
public import Mathlib.Geometry.Manifold.VectorField.Pullback

/-!
# Smooth threefolds in `ℂℙ⁴`

Let `Z ⊆ ℂℙ⁴` be a smooth threefold of degree `d`, with inclusion `ι`, and let `h` be the
hyperplane class. This file specializes the general results on hypersurfaces to `Z`: its first
Chern class is `c₁(TZ) = (5 - d) ι^* h`
(`SmoothProjectiveHypersurface.chernClass_one_tangentSpace`),
and for `d ≠ 0` its Betti numbers in degrees `2` and `4` are those of `ℂℙ³`
(`SmoothProjectiveHypersurface.bettiNumber_of_ne`, from the Lefschetz theorem and Poincaré
duality), while the middle one is `b₃ = 4 - χ(Z) = d⁴ - 5d³ + 10d² - 10d + 4`
(`SmoothProjectiveHypersurface.bettiNumber_middle` and `SmoothProjectiveHypersurface.eulerChar_eq`,
which gives `χ(Z) = d (10 - 10d + 5d² - d³)`).

The formulas for the Betti numbers fail for `d = 0`, where `Z` is empty.

## Main results

The following are in the namespace `SymplecticGeometry.SmoothProjectiveHypersurface`.

* `chernClass_one_tangentSpace_threefold`: `c₁(TZ) = (5 - d) ι^* h`.
* `bettiNumber_two_threefold`, `bettiNumber_four_threefold`: `b₂ = b₄ = 1` for `d ≠ 0`.
* `bettiNumber_three_threefold`: `b₃ = d⁴ - 5d³ + 10d² - 10d + 4` for `d ≠ 0`.
* `bettiNumber_two_fermat_zero_threefold`, `bettiNumber_three_fermat_zero_threefold`: the
  empty threefold of degree `0` shows that these need `d ≠ 0`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Example 4.4.4 and Exercise 4.4.6.
-/

public section

open Module SymplecticGeometry.Bundle TauCeti
open scoped Manifold

namespace SymplecticGeometry

namespace SmoothProjectiveHypersurface

variable {d : ℕ} (Z : SmoothProjectiveHypersurface 3 d)

/-- **The first Chern class of a threefold in `ℂℙ⁴`.** A smooth threefold `Z ⊆ ℂℙ⁴` of degree `d`
has `c₁(TZ) = (5 - d) ι^* h`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem chernClass_one_tangentSpace_threefold :
    chernClass (Fin 3 → ℂ)
        (TangentSpace 𝓘(ℂ, Fin 3 → ℂ) : Z → Type) 1 =
      (5 - d : ℤ) • Z.hyperplaneClass := by
  rw [chernClass_one_tangentSpace]
  norm_num

/-- **The second Betti number of a threefold in `ℂℙ⁴`.** For `d ≠ 0`, a smooth threefold
`Z ⊆ ℂℙ⁴` of degree `d` has `b₂ = 1`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem bettiNumber_two_threefold (hd : d ≠ 0) : bettiNumber ℚ Z 2 = 1 := by
  rw [Z.bettiNumber_of_ne hd (by decide)]
  decide

/-- **The fourth Betti number of a threefold in `ℂℙ⁴`.** For `d ≠ 0`, a smooth threefold
`Z ⊆ ℂℙ⁴` of degree `d` has `b₄ = 1`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem bettiNumber_four_threefold (hd : d ≠ 0) : bettiNumber ℚ Z 4 = 1 := by
  rw [Z.bettiNumber_of_ne hd (by decide)]
  decide

/-- `bettiNumber_two_threefold` and `bettiNumber_four_threefold` need `d ≠ 0`: the Fermat
threefold of degree `0` is empty, so its second Betti number is `0`. -/
theorem bettiNumber_two_fermat_zero_threefold : bettiNumber ℚ (fermat 3 0) 2 = 0 :=
  bettiNumber_eq_zero_of_isEmpty ℚ _ 2

/-- **The third Betti number of a threefold in `ℂℙ⁴`.** For `d ≠ 0`, a smooth threefold
`Z ⊆ ℂℙ⁴` of degree `d` has `b₃ = d⁴ - 5d³ + 10d² - 10d + 4`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem bettiNumber_three_threefold (hd : d ≠ 0) :
    (bettiNumber ℚ Z 3 : ℤ) = (d : ℤ) ^ 4 - 5 * d ^ 3 + 10 * d ^ 2 - 10 * d + 4 := by
  have h := Z.bettiNumber_middle hd
  rw [Z.eulerChar_eq] at h
  simp [Finset.sum_range_succ, Nat.choose, show ¬Even 3 by decide] at h
  linear_combination -h

/-- `bettiNumber_three_threefold` needs `d ≠ 0`: the Fermat threefold of degree `0` is empty, so
its third Betti number is `0`, while `d⁴ - 5d³ + 10d² - 10d + 4 = 4` for `d = 0`. -/
theorem bettiNumber_three_fermat_zero_threefold : bettiNumber ℚ (fermat 3 0) 3 = 0 :=
  bettiNumber_eq_zero_of_isEmpty ℚ _ 3

end SmoothProjectiveHypersurface

end SymplecticGeometry

end
