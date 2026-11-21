/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Volume

/-!
# The symplectic orientation of a negated two-form

Let `σ` be a fiberwise nondegenerate smooth two-form on a manifold modelled on a real vector space
of dimension `2 * n`. Then `-σ` is nondegenerate too, and its volume form `(-σ)ⁿ / n!` is
`(-1)ⁿ` times the volume form `σⁿ / n!` of `σ`. So when `n` is odd, the symplectic orientation of
`-σ` is the opposite of that of `σ`. (When `n` is even the two orientations agree.)

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_neg`: for odd `n`, the symplectic
  orientation of `-σ` is the negative of that of `σ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, Berlin, 2001][CannasdaSilva2001Lectures]
-/

public section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {n : ℕ}

/-- **The symplectic orientation of a negated two-form.** On a manifold modelled on a space of
dimension `2 * n` with `n` odd, the symplectic orientation of `-σ` is the opposite of the
symplectic orientation of a fiberwise nondegenerate two-form `σ`. -/
theorem IsNondegenerate.volumeOrientation_neg (h : σ.IsNondegenerate) (hodd : Odd n)
    (hn : finrank ℝ E = 2 * n) :
    h.neg.volumeOrientation hn = -h.volumeOrientation hn := by
  ext x
  rw [Manifold.Orientation.orientationAt_neg]
  have : Nonempty (Fin (2 * n)) := ⟨⟨0, by have := hodd.pos; omega⟩⟩
  -- A basis of the tangent space (the model space `E`) that is positive for the symplectic
  -- orientation of `σ`.
  let b := (Module.finBasisOfFinrankEq ℝ (TangentSpace I x) (by exact hn)).adjustToOrientation
    (Manifold.Orientation.orientationAt (h.volumeOrientation hn) x)
  have hb : b.orientation = Manifold.Orientation.orientationAt (h.volumeOrientation hn) x :=
    Basis.orientation_adjustToOrientation _ _
  have hpos : 0 < (σ.volumeForm n).val x b :=
    (h.orientation_eq_orientationAt_volumeOrientation_iff hn b).1 hb
  -- The volume form of `-σ` is negative on it.
  have hneg : ¬ 0 < ((-σ).volumeForm n).val x b := by
    rw [← neg_one_smul ℝ σ, volumeForm_smul, hodd.neg_one_pow, Submodule.coe_smul,
      Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    linarith
  rw [← hb, ← b.orientation_ne_iff_eq_neg]
  exact fun h' ↦ hneg ((h.neg.orientation_eq_orientationAt_volumeOrientation_iff hn b).1 h'.symm)

end SmoothTwoForm

end TauCeti

end
