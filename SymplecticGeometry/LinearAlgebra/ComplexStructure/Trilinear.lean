/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Abel

/-!
# Trilinear forms with vanishing cyclic sum and a complex structure

Let `j` be an endomorphism of a module `V` with `j ∘ j = -1`, and let `α` be a trilinear map on
`V` with values in an additive group without torsion. Suppose that `j` moves freely between the
last two arguments of `α`, `α(u, j v, w) = α(u, v, j w)`, and that the cyclic sum of `α`
vanishes, `α(u, v, w) + α(v, w, u) + α(w, u, v) = 0`. Then `j` also moves from the first argument
to the last: `α(j v, w, z) = α(v, w, j z)`.

Applied to `α(u, v, w) = ⟪(∇_u J) v, w⟫`, where `∇` is the Levi-Civita connection of the metric
`ω(·, J ·)` of a closed two-form `ω` and a `J` compatible with it, this gives
`∇_{J v} J = -J ∘ ∇_v J`.

## Main results

* `LinearMap.apply_left_eq_apply_right_of_cyclic`: the statement above.

## Implementation notes

The proof follows the coordinate-free proof of [McDuffSalamon2017], Lemma 4.1.14: the defect
`D(v, w, z) = α(j v, w, z) - α(v, w, j z)` is invariant under cyclic permutations and satisfies
`D(a, b, j c) = D(a, j b, c) = -D(j a, b, c)`; going once round the cycle shows
`D(j v, w, z) = -D(j v, w, z)`. Unlike the book's setting, the form need not be skew in its last
two arguments.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  proof of Lemma 4.1.14, equation (4.1.12).
* [V. Apostolov and T. Drăghici, *The curvature and the integrability of almost-Kähler manifolds:
  a survey*][ApostolovDraghici2003], §3.3, equation (7).
-/

public section

namespace LinearMap

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W]
  [Module R W] [IsAddTorsionFree W]

/-- Let `j ∘ j = -1` on `V`, and let `α` be a trilinear map on `V` with
`α(u, j v, w) = α(u, v, j w)` and vanishing cyclic sum. Then `α(j v, w, z) = α(v, w, j z)`. -/
theorem apply_left_eq_apply_right_of_cyclic {j : V →ₗ[R] V} (hj : j ∘ₗ j = -LinearMap.id)
    {α : V →ₗ[R] V →ₗ[R] V →ₗ[R] W} (hα : ∀ u v w, α u (j v) w = α u v (j w))
    (hcyc : ∀ u v w, α u v w + α v w u + α w u v = 0) (v w z : V) :
    α (j v) w z = α v w (j z) := by
  have hjj (a : V) : j (j a) = -a := by simpa using congr($hj a)
  -- The defect `D(a, b, c) = α(j a, b, c) - α(a, b, j c)`.
  set D : V → V → V → W := fun a b c ↦ α (j a) b c - α a b (j c) with hD
  have hcycD (a b c : V) : D b c a = D a b c := by
    have h := (hcyc (j b) c a).trans (hcyc b c (j a)).symm
    rw [hα c a b, hα a b c] at h
    simp only [hD]
    rw [← sub_eq_zero, ← sub_eq_zero.2 h]
    abel
  have hright (a b c : V) : D a b (j c) = D a (j b) c := by
    simp only [hD, hα, hjj, map_neg]
  have hleft (a b c : V) : D (j a) b c = -D a (j b) c := by
    simp only [hD, hα, hjj, map_neg, LinearMap.neg_apply]
    abel
  -- Going once round the cycle changes the sign of `D (j a) w z`, so it vanishes.
  have hzero (a : V) : D (j a) w z = 0 := by
    have h2 : D (j a) w z = -D (j a) w z :=
      calc D (j a) w z = -D a (j w) z := hleft _ _ _
        _ = -D a w (j z) := by rw [hright]
        _ = -D (j z) a w := by rw [hcycD (j z) a w]
        _ = D z (j a) w := by rw [hleft, neg_neg]
        _ = D z a (j w) := by rw [hright]
        _ = D (j w) z a := by rw [hcycD (j w) z a]
        _ = -D w (j z) a := hleft _ _ _
        _ = -D w z (j a) := by rw [hright]
        _ = -D (j a) w z := by rw [hcycD (j a) w z]
    have h : (2 : ℕ) • D (j a) w z = 0 := by
      rw [two_nsmul]
      nth_rw 2 [h2]
      exact add_neg_cancel _
    simpa using h
  -- `v = j (-j v)`.
  have h := hzero (-j v)
  rw [map_neg, hjj, neg_neg] at h
  exact sub_eq_zero.1 h

end LinearMap

end
