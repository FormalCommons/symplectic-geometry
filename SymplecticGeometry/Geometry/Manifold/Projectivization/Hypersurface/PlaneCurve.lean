/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.EulerCharacteristic
public import TauCeti.AlgebraicTopology.Singular.SurfaceGenus

import SymplecticGeometry.AlgebraicTopology.Cohomology.Empty
import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.Lefschetz
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus

/-!
# The genus of a smooth plane curve

A smooth curve `X ⊆ ℂℙ²` of degree `d ≠ 0` has genus `(d - 1)(d - 2) / 2`. Its Euler
characteristic is `χ(X) = d (3 - d)` (`SmoothProjectiveHypersurface.eulerChar_planeCurve`, from
`SmoothProjectiveHypersurface.eulerChar_eq`), which is even
and at most `2`, so `χ(X) = 2 - 2g` for the genus `g = TauCeti.RiemannSurface.genus X` read off
the Euler characteristic (`TauCeti.RiemannSurface.eulerChar_eq_two_sub_two_mul_genus_iff`). The
curve is connected (`SmoothProjectiveHypersurface.connectedSpace`, from the Lefschetz theorem) and
oriented by its complex structure, so that genus is `TauCeti.surfaceGenus X`, half the first
rational Betti number (`TauCeti.HomologicalOrientation.genus_eq_surfaceGenus`).

For `d = 0` the curve is empty and has genus `0`, while `(d - 1)(d - 2) / 2 = 1`.

## Main results

* `SymplecticGeometry.SmoothProjectiveHypersurface.eulerChar_planeCurve`: `χ(X) = d (3 - d)`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.two_mul_surfaceGenus`:
  `2 g = (d - 1)(d - 2)` for `d ≠ 0`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Example 4.4.5.
-/

public section

open Module TauCeti
open scoped Manifold

namespace SymplecticGeometry

namespace SmoothProjectiveHypersurface

variable {d : ℕ}

/-- **The Euler characteristic of a plane curve.** A smooth curve `X ⊆ ℂℙ²` of degree `d` has
`χ(X) = d (3 - d)`. -/
theorem eulerChar_planeCurve (X : SmoothProjectiveHypersurface 1 d) :
    eulerChar X = d * (3 - d) := by
  rw [X.eulerChar_eq]
  simp [Finset.sum_range_succ, -mul_eq_mul_left_iff]
  ring

/-- **The genus of a smooth plane curve.** For `d ≠ 0`, a smooth curve `X ⊆ ℂℙ²` of degree `d`
has genus `g = TauCeti.surfaceGenus X` with `2g = (d - 1)(d - 2)`.

Milestone: *Adjunction formula*. -/
theorem two_mul_surfaceGenus (X : SmoothProjectiveHypersurface 1 d) (hd : d ≠ 0) :
    2 * (surfaceGenus X : ℤ) = ((d : ℤ) - 1) * (d - 2) := by
  have := X.connectedSpace hd one_ne_zero
  have hχ := X.eulerChar_planeCurve
  have hle : eulerChar X ≤ 2 := by
    rw [hχ]
    rcases le_or_gt (d : ℤ) 1 with h | h <;> nlinarith
  have hev : Even (eulerChar X) := by
    rw [hχ, show (d : ℤ) * (3 - d) = d * (d + 1) + 2 * (d * (1 - d)) by ring]
    exact (Int.even_mul_succ_self _).add (even_two_mul _)
  have hg := RiemannSurface.eulerChar_eq_two_sub_two_mul_genus_iff.2 ⟨hle, hev⟩
  rw [(complexManifoldHomologicalOrientation (Fin 1 → ℂ) X
    (Module.finrank_fin_fun ℂ)).genus_eq_surfaceGenus
      (finrank_real_of_finrank_complex_eq_add_one (Module.finrank_fin_fun ℂ)),
    hχ] at hg
  linarith

/-- `two_mul_surfaceGenus` needs `d ≠ 0`: the Fermat curve of degree `0` is empty, so its genus
is `0`, while `(d - 1)(d - 2) = 2` for `d = 0`. -/
theorem surfaceGenus_fermat_zero : surfaceGenus (fermat 1 0) = 0 :=
  surfaceGenus_eq_zero_of_isEmpty _

end SmoothProjectiveHypersurface

end SymplecticGeometry

end
