/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Grassmannian.ForgetLast
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph

/-!
# Homotopy groups of the space of unit vectors over `ℝ` or `ℂ`

For any `RCLike 𝕜`, an orthonormal one-frame of `𝕜^N` is a unit vector, so the space
`finiteOrthonormalFrame 𝕜 1 N` is the unit sphere of `𝕜^N`, a real sphere of dimension
`dim_ℝ 𝕜 * N - 1`. Its homotopy groups therefore vanish below that degree. For `r = 1` this
extends Tau Ceti's real `TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup` to every
`RCLike 𝕜`; over `ℂ` it is the input for the stable range of the unitary groups.

The space of one-frames is the whole fibre of `finiteOrthonormalFrame.forgetLast` over the unique
`0`-frame, and `TauCeti.finiteOrthonormalFrame.forgetLastFiberSphere` identifies that fibre with
the unit sphere of `EuclideanSpace 𝕜 (Fin N)`. This is the unit sphere of a finite-dimensional
real normed space, so `TauCeti.subsingleton_homotopyGroup_sphere_of_lt` applies directly, with
no comparison of `𝕜^N` with a real coordinate space.

## Main results

* `TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup_unitVector`: `π_k` of the space of
  unit vectors of `𝕜^N` is trivial for `k + 1 < dim_ℝ 𝕜 * N`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  §2.2 (the fibrations of unitary groups over spheres).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Corollary 4.9 and
  Example 4.53.
-/

public section

open Metric

namespace TauCeti.finiteOrthonormalFrame

variable {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}

/-- **The unit sphere of `𝕜^N` is `(dim_ℝ 𝕜 * N - 2)`-connected.** For any `RCLike 𝕜`, the
homotopy group of the space `finiteOrthonormalFrame 𝕜 1 N` of unit vectors of `𝕜^N`, indexed by a
type of `k` cube directions, is trivial whenever `k + 1 < dim_ℝ 𝕜 * N`, where `k` is
`Nat.card M`; the index type need not be finite. -/
theorem subsingleton_homotopyGroup_unitVector {M : Type*}
    (h : Nat.card M + 1 < Module.finrank ℝ 𝕜 * N) (x : finiteOrthonormalFrame 𝕜 1 N) :
    Subsingleton (HomotopyGroup M (finiteOrthonormalFrame 𝕜 1 N) x) := by
  -- the one-frames are the whole fibre of `forgetLast` over the unique `0`-frame
  let φ : finiteOrthonormalFrame 𝕜 1 N ≃ₜ sphere (0 : EuclideanSpace 𝕜 (Fin (N - 0))) 1 :=
    ((Homeomorph.Set.univ _).symm.trans ((Homeomorph.refl _).subtype fun g ↦ by
      simp [Subsingleton.elim (forgetLast g) (forgetLast x)])).trans
      (forgetLastFiberSphere (forgetLast x))
  have hE : Module.finrank ℝ (EuclideanSpace 𝕜 (Fin (N - 0))) =
      Module.finrank ℝ 𝕜 * N - 1 + 1 := by
    rw [← Module.finrank_mul_finrank ℝ 𝕜, finrank_euclideanSpace_fin, Nat.sub_zero]
    omega
  have := subsingleton_homotopyGroup_sphere_of_lt hE (N := M) (by omega) (φ x)
  exact (HomotopyGroup.homeomorphEquiv φ x).subsingleton

end TauCeti.finiteOrthonormalFrame

end
