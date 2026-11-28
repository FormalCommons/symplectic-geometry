/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Symplectic.Manifold.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.Volume
public import SymplecticGeometry.Geometry.Manifold.Orientation.PositiveForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
import SymplecticGeometry.Geometry.Manifold.Orientation.Sphere
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Wedge.TwoForm
import TauCeti.Geometry.Symplectic.Manifold.Surface
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ZeroDim

/-!
# The symplectic orientation and volume: negated forms, surfaces, and symplectomorphisms

Let `σ` be a fiberwise nondegenerate smooth two-form on a manifold modelled on a real vector space
of dimension `2 * n`. The volume form `σⁿ / n!` is positive for the symplectic orientation, so on
a nonempty compact manifold its integral, the symplectic volume, is positive: by Tau Ceti's
`TauCeti.integralTopForm_pos` when `n > 0`, and by summing over the finitely many points
(`TauCeti.integralTopForm_finite_zeroDim`) when `n = 0`.

The form `-σ` is nondegenerate too, and its volume form `(-σ)ⁿ / n!` is
`(-1)ⁿ` times the volume form `σⁿ / n!` of `σ`. So when `n` is odd, the symplectic orientation of
`-σ` is the opposite of that of `σ`. (When `n` is even the two orientations agree.)

On a surface (`n = 1`) the volume form `σ¹ / 1!` is `σ` itself (Tau Ceti's
`TauCeti.SmoothTwoForm.volumeForm_one`), so the symplectic orientation of a nondegenerate
two-form `σ` is the orientation `TauCeti.Manifold.Orientation.ofTopForm` on which
`σ` is positive. For the volume form of the unit sphere of an oriented three-dimensional space,
this is the outward-normal orientation.

Finally, every diffeomorphism that preserves `σ` preserves its symplectic orientation, so a
fibre bundle atlas whose coordinate changes are symplectic is oriented for it.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.isPositive_volumeForm`: the volume form `σⁿ / n!` is
  positive for the symplectic orientation of `σ`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.integralTopForm_volumeForm_pos`: on a nonempty compact
  manifold, the integral of `σⁿ / n!` against the symplectic orientation is positive.
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
* `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_eq_of_isPositive`: on a surface, an
  orientation for which `σ` is positive is the symplectic orientation of `σ`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation_eq_iff_isPositive`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.orientation_eq_iff_isPositive`: on a surface, an
  orientation is the symplectic orientation of `σ` exactly when `σ` is positive for it.
* `TauCeti.SmoothForm.diffeomorphStabilizer_le_orientationPreservingSubgroup`: a diffeomorphism
  preserving `σ` preserves the symplectic orientation of `σ`, from Tau Ceti's
  `TauCeti.SmoothTwoForm.IsNondegenerate.isOrientationPreservingAt_orientation` and
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

/-- The volume form `σⁿ / n!` of a fiberwise nondegenerate two-form `σ`, on a manifold modelled
on a space of dimension `2 * n > 0`, is positive for the symplectic orientation of `σ`. -/
theorem IsNondegenerate.isPositive_volumeForm [NeZero (2 * n)] (h : σ.IsNondegenerate)
    (hn : finrank ℝ E = 2 * n) :
    (h.volumeOrientation hn).IsPositive (σ.volumeForm n).val :=
  Manifold.Orientation.isPositive_iff_forall_apply_pos.2 fun _ c hc ↦
    (h.orientation_eq_orientationAt_volumeOrientation_iff hn c).1 hc

/-- **The symplectic volume is positive.** On a nonempty compact manifold modelled on a space of
dimension `2 * n`, the integral of the volume form `σⁿ / n!` of a fiberwise nondegenerate
two-form `σ` against its symplectic orientation is positive. This includes `n = 0`, where the
manifold is a nonempty finite set of points. -/
theorem IsNondegenerate.integralTopForm_volumeForm_pos [CompactSpace M] [Nonempty M]
    (h : σ.IsNondegenerate) (hn : finrank ℝ E = 2 * n) :
    0 < integralTopForm (h.volumeOrientation hn) (σ.volumeForm n).val := by
  rcases n with - | n
  · have hcard : finrank ℝ E = 0 := hn
    have : Subsingleton E := finrank_zero_iff.mp hcard
    have : DiscreteTopology M := I.discreteTopology M
    have : Finite M := finite_of_compact_of_discrete
    let : Fintype M := Fintype.ofFinite M
    let b := finBasisOfFinrankEq ℝ E hcard
    rw [integralTopForm_finite_zeroDim _ b]
    refine Finset.sum_pos (fun x _ ↦ ?_) Finset.univ_nonempty
    have hv (v) : (σ.volumeForm 0).val x v = 1 := by
      simp [volumeForm_apply, ContinuousAlternatingMap.wedgePow_zero_apply]
    have hb : b.orientation = (h.volumeOrientation hn).orientationAt x := by
      refine (h.orientation_eq_orientationAt_volumeOrientation_iff hn b).2 ?_
      rw [hv]
      exact one_pos
    rw [← hb, hv, mul_one]
    have hs : ((b.orientation.signBasis b : ℤ) : ℝ) = 1 := by
      rw [Orientation.signBasis_orientation, Units.val_one, Int.cast_one]
    convert zero_lt_one (α := ℝ)
    -- The goal and `hs` agree up to unfolding `Fin (2 * 0)` to `Fin 0` and `TangentSpace I x`
    -- to `E`.
    exact hs
  · have : NeZero (2 * (n + 1)) := ⟨by omega⟩
    exact (h.isPositive_volumeForm hn).integralTopForm_pos
      ((σ.volumeForm _).isSmoothForm.of_le bot_le) (isClosed_tsupport _).isCompact

/-- **The symplectic orientation of a negated two-form.** On a manifold modelled on a space of
dimension `2 * n` with `n` odd, the symplectic orientation of `-σ` is the opposite of the
symplectic orientation of a fiberwise nondegenerate two-form `σ`. -/
theorem IsNondegenerate.volumeOrientation_neg (h : σ.IsNondegenerate) (hodd : Odd n)
    (hn : finrank ℝ E = 2 * n) :
    h.neg.volumeOrientation hn = -h.volumeOrientation hn := by
  have : NeZero (2 * n) := ⟨by have := hodd.pos; omega⟩
  -- The volume form of `-σ` is `(-1)ⁿ = -1` times that of `σ`, so it is positive for both
  -- orientations.
  have hvol : ((-σ).volumeForm n).val = -(σ.volumeForm n).val := by
    rw [← neg_one_smul ℝ σ, volumeForm_smul, hodd.neg_one_pow, Submodule.coe_smul,
      neg_one_smul]
  refine (h.neg.isPositive_volumeForm hn).eq ?_
  rw [hvol]
  exact (h.isPositive_volumeForm hn).neg

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

/-- On a manifold modelled on a plane, if a fiberwise nondegenerate two-form `σ` is positive for
an orientation `o`, then `o` is the symplectic orientation of `σ`. -/
theorem IsNondegenerate.volumeOrientation_eq_of_isPositive (h : σ.IsNondegenerate)
    (hE : finrank ℝ E = 2) {o : Manifold.Orientation I M (Fin 2)} (ho : o.IsPositive σ.val) :
    h.volumeOrientation (n := 1) hE = o := by
  have hv := h.isPositive_volumeForm (n := 1) hE
  rw [volumeForm_one] at hv
  exact hv.eq ho

/-- On a manifold modelled on a plane, an orientation `o` is the symplectic orientation of a
fiberwise nondegenerate two-form `σ` if and only if `σ` is positive for `o`. -/
theorem IsNondegenerate.volumeOrientation_eq_iff_isPositive (h : σ.IsNondegenerate)
    (hE : finrank ℝ E = 2) {o : Manifold.Orientation I M (Fin 2)} :
    h.volumeOrientation (n := 1) hE = o ↔ o.IsPositive σ.val := by
  refine ⟨?_, h.volumeOrientation_eq_of_isPositive hE⟩
  rintro rfl
  have hv := h.isPositive_volumeForm (n := 1) hE
  rwa [volumeForm_one] at hv

/-- On a manifold modelled on a plane, an orientation `o` is Tau Ceti's symplectic orientation
`IsNondegenerate.orientation` of a fiberwise nondegenerate two-form `σ` if and only if `σ` is
positive for `o`. -/
theorem IsNondegenerate.orientation_eq_iff_isPositive (h : σ.IsNondegenerate)
    (hE : finrank ℝ E = 2) {o : Manifold.Orientation I M (Fin 2)} :
    h.orientation hE = o ↔ o.IsPositive σ.val := by
  -- After the rewrites the two sides differ only in the index `2 * 1` against `2` of
  -- `Fin`, which `rw` closes by `rfl`.
  rw [← h.volumeOrientation_eq_iff_isPositive hE, h.volumeOrientation_eq_orientation (n := 1) hE]

/-- On a manifold modelled on a plane, if a fiberwise nondegenerate two-form `σ` is positive for
an orientation `o`, then `o` is Tau Ceti's symplectic orientation `IsNondegenerate.orientation`
of `σ`. -/
theorem IsNondegenerate.orientation_eq_of_isPositive (h : σ.IsNondegenerate)
    (hE : finrank ℝ E = 2) {o : Manifold.Orientation I M (Fin 2)} (ho : o.IsPositive σ.val) :
    h.orientation hE = o :=
  (h.orientation_eq_iff_isPositive hE).2 ho

end SmoothTwoForm

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {n : ℕ}

/-- **Symplectomorphisms preserve the symplectic orientation.** Every smooth diffeomorphism that
pulls a fiberwise nondegenerate two-form `σ` back to itself preserves the symplectic orientation
`volumeOrientation` of `σ` at every point. This holds in every dimension `2 * n`, `n = 0`
included. -/
theorem diffeomorphStabilizer_le_orientationPreservingSubgroup (h : σ.IsNondegenerate)
    (hn : finrank ℝ E = 2 * n) :
    diffeomorphStabilizer σ ≤
      Diffeomorph.orientationPreservingSubgroup (n := ∞) (by simp) (h.volumeOrientation hn) :=
  fun φ hφ ↦ Diffeomorph.mem_orientationPreservingSubgroup_iff.2 fun x ↦ by
    rw [SmoothTwoForm.IsNondegenerate.volumeOrientation_eq_orientation]
    exact h.isOrientationPreservingAt_orientation hn h hn φ.contMDiff
      (mem_diffeomorphStabilizer.1 hφ) x

end SmoothForm

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
