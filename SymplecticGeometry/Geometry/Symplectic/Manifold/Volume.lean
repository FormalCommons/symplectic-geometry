/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Volume
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Wedge.TwoForm

/-!
# The symplectic orientation of a negated two-form, and of a two-form on a surface

Let `σ` be a fiberwise nondegenerate smooth two-form on a manifold modelled on a real vector space
of dimension `2 * n`. Then `-σ` is nondegenerate too, and its volume form `(-σ)ⁿ / n!` is
`(-1)ⁿ` times the volume form `σⁿ / n!` of `σ`. So when `n` is odd, the symplectic orientation of
`-σ` is the opposite of that of `σ`. (When `n` is even the two orientations agree.)

On a surface (`n = 1`) the volume form `σ¹ / 1!` is `σ` itself, so the symplectic orientation of a
nondegenerate two-form `σ` is the orientation `TauCeti.Manifold.Orientation.ofTopForm` on which
`σ` is positive.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_neg`: for odd `n`, the symplectic
  orientation of `-σ` is the negative of that of `σ`.
* `TauCeti.SmoothTwoForm.volumeForm_one`: the volume form `σ¹ / 1!` is `σ`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_eq_ofTopForm`: on a surface, the
  symplectic orientation of `σ` is the orientation defined by `σ` as a top form.

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

omit [FiniteDimensional ℝ E] in
/-- The volume form `σ¹ / 1!` of a two-form `σ` is `σ` itself. -/
@[simp]
theorem volumeForm_one (σ : SmoothTwoForm I M) : σ.volumeForm 1 = σ :=
  Subtype.ext (funext fun x ↦ by
    rw [volumeForm_apply, ContinuousAlternatingMap.wedgePow_one, Nat.factorial_one, Nat.cast_one,
      inv_one, one_smul])

/-- **The symplectic orientation of a surface.** On a manifold modelled on a plane, the symplectic
orientation of a fiberwise nondegenerate two-form `σ` is the orientation on which `σ`, as a
nowhere-vanishing top form, is positive. -/
theorem IsNondegenerate.volumeOrientation_eq_ofTopForm (h : σ.IsNondegenerate)
    (hE : finrank ℝ E = 2) :
    h.volumeOrientation (n := 1) hE = Manifold.Orientation.ofTopForm hE σ.val
      (σ.isSmoothForm.of_le zero_le)
      (fun x ↦ by simpa using h.volumeForm_apply_ne_zero (n := 1) hE x) := by
  ext x
  have : Nonempty (Fin 2) := ⟨0⟩
  -- A basis of the tangent space (the model space `E`) that is positive for the orientation of
  -- `σ` as a top form; `σ` and `σ¹ / 1!` are positive on it.
  let b := (Module.finBasisOfFinrankEq ℝ (TangentSpace I x) (by exact hE)).adjustToOrientation
    (Manifold.Orientation.orientationAt (Manifold.Orientation.ofTopForm hE σ.val
      (σ.isSmoothForm.of_le zero_le)
      (fun x ↦ by simpa using h.volumeForm_apply_ne_zero (n := 1) hE x)) x)
  have hb : b.orientation = _ := Basis.orientation_adjustToOrientation _ _
  rw [← hb]
  refine ((h.orientation_eq_orientationAt_volumeOrientation_iff (n := 1) hE b).2 ?_).symm
  rw [volumeForm_one]
  exact (Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff hE _ _ b).1 hb

end SmoothTwoForm

end TauCeti

end
