/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Symplectic.Manifold.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.Volume
import SymplecticGeometry.Geometry.Manifold.Orientation.Sphere
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Wedge.TwoForm
import TauCeti.Geometry.Symplectic.Manifold.Surface

/-!
# The symplectic orientation of a negated two-form, and of a two-form on a surface

Let `σ` be a fiberwise nondegenerate smooth two-form on a manifold modelled on a real vector space
of dimension `2 * n`. Then `-σ` is nondegenerate too, and its volume form `(-σ)ⁿ / n!` is
`(-1)ⁿ` times the volume form `σⁿ / n!` of `σ`. So when `n` is odd, the symplectic orientation of
`-σ` is the opposite of that of `σ`. (When `n` is even the two orientations agree.)

On a surface (`n = 1`) the volume form `σ¹ / 1!` is `σ` itself (Tau Ceti's
`TauCeti.SmoothTwoForm.volumeForm_one`), so the symplectic orientation of a nondegenerate
two-form `σ` is the orientation `TauCeti.Manifold.Orientation.ofTopForm` on which
`σ` is positive. For the volume form of the unit sphere of an oriented three-dimensional space,
this is the outward-normal orientation.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_neg`: for odd `n`, the symplectic
  orientation of `-σ` is the negative of that of `σ`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_eq_orientation`: in every dimension,
  the orientation `volumeOrientation` of `σ` is Tau Ceti's other symplectic orientation
  `IsNondegenerate.orientation`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_eq_ofTopForm`: on a surface, the
  symplectic orientation of `σ` is the orientation defined by `σ` as a top form. This is Tau
  Ceti's `TauCeti.SmoothTwoForm.IsNondegenerate.orientation_eq_ofTopForm`, stated for
  `volumeOrientation`, which equals Tau Ceti's `IsNondegenerate.orientation` by
  `volumeOrientation_eq_orientation`.
* `Orientation.volumeOrientation_sphereVolumeForm`: the symplectic orientation of the volume form
  of the unit two-sphere is its outward-normal orientation.

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

/-- Tau Ceti's two symplectic orientations of a fiberwise nondegenerate two-form `σ` agree:
`IsNondegenerate.volumeOrientation`, on which the volume form `σⁿ / n!` is positive, is
`IsNondegenerate.orientation`, the linear symplectic orientation of each tangent space. -/
theorem IsNondegenerate.volumeOrientation_eq_orientation (h : σ.IsNondegenerate)
    (hn : finrank ℝ E = 2 * n) : h.volumeOrientation hn = h.orientation hn :=
  Manifold.Orientation.ext fun x ↦ by simp

/-- **The symplectic orientation of a surface.** On a manifold modelled on a plane, the symplectic
orientation of a fiberwise nondegenerate two-form `σ` is the orientation on which `σ`, as a
nowhere-vanishing top form, is positive. -/
theorem IsNondegenerate.volumeOrientation_eq_ofTopForm (h : σ.IsNondegenerate)
    (hE : finrank ℝ E = 2) :
    h.volumeOrientation (n := 1) hE = Manifold.Orientation.ofTopForm hE σ.val
      (σ.isSmoothForm.of_le zero_le)
      (fun x ↦ by simpa using h.volumeForm_apply_ne_zero (n := 1) hE x) :=
  (h.volumeOrientation_eq_orientation hE).trans (h.orientation_eq_ofTopForm hE)

end SmoothTwoForm

end TauCeti

namespace Orientation

/-- **The symplectic orientation of the two-sphere.** On the unit sphere of an oriented
three-dimensional real inner product space, the symplectic orientation of the volume form
`o.sphereVolumeForm`, a nondegenerate two-form, is the outward-normal orientation
`o.sphereOrientation`. -/
theorem volumeOrientation_sphereVolumeForm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2 + 1)] (o : Orientation ℝ E (Fin (2 + 1)))
    (h : TauCeti.SmoothTwoForm.IsNondegenerate o.sphereVolumeForm) :
    h.volumeOrientation (n := 1) finrank_euclideanSpace_fin = o.sphereOrientation := by
  rw [TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_eq_ofTopForm,
    o.sphereOrientation_eq_ofTopForm]

end Orientation

end
