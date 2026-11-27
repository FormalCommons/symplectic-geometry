/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.ConnectedSum.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Orientation
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import TauCeti.Analysis.InnerProductSpace.Calculus

/-!
# The radial rescaling of the model blowup preserves the complex orientation

For `ε > 0`, the radial rescaling `BlowupModel.radialRescale ε`, `(ℓ, z) ↦ (ℓ, ε z / √(1 + |z|²))`,
is a local diffeomorphism of the real manifold `BlowupModel n`, but it is not holomorphic. This
file shows that it still preserves the complex orientation of the model blowup at every point.

The model blowup is path-connected, being the image of the complement of a point in projective
space under `projectiveBlowupModelDiffeomorph n`, so it is enough to check one point, as in the
proof of `SymplecticGeometry.isOrientationReversing_projectiveBlowupModelDiffeomorph`. At the
point `(blowupModelChart i).symm 0` of the exceptional divisor, the rescaling reads, in the chart
`blowupModelChart i` on both sides, as `w ↦ update w i (ρ (w i • update w i 1)) i`, with
`ρ = univBall 0 ε` on the Hermitian space. Since `ρ` has derivative `ε • id` at `0`, the real
derivative of this map at `0` is `ε` times the identity on the coordinate `i` and the identity on
the others, which has positive determinant.

## Main results

* `SymplecticGeometry.BlowupModel.instPathConnectedSpace`: the model blowup is path-connected;
* `SymplecticGeometry.BlowupModel.isOrientationPreservingAt_radialRescale`: for `0 < ε`, the
  radial rescaling preserves the complex orientation at every point.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Section 7.1.
-/

public section

noncomputable section

open Set Function OpenPartialHomeomorph TauCeti Manifold.Orientation
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry

namespace BlowupModel

variable {n : ℕ}

/-- The model blowup `BlowupModel n` is path-connected: it is the image of the path-connected
complement of a point in `ℙ ℂ (Fin (n + 2) → ℂ)` under `projectiveBlowupModelDiffeomorph n`. -/
instance instPathConnectedSpace : PathConnectedSpace (BlowupModel n) :=
  (projectiveBlowupModelDiffeomorph n).surjective.pathConnectedSpace
    (projectiveBlowupModelDiffeomorph n).continuous

variable {ε : ℝ}

/-- The radial rescaling read in the chart `blowupModelChart i` on both sides. -/
private theorem blowupModelChart_radialRescale_blowupModelChart_symm (i : Fin (n + 1))
    (w : Fin (n + 1) → ℂ) :
    blowupModelChart i (radialRescale ε ((blowupModelChart i).symm w)) =
      update w i (EuclideanSpace.equiv (Fin (n + 1)) ℂ (univBall 0 ε
        ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm (w i • update w i 1))) i) := by
  have hw := (blowupModelChart i).right_inv (by rw [blowupModelChart_target]; exact mem_univ w)
  rw [blowupModelChart_apply] at hw
  conv_rhs => arg 1; rw [← hw]
  rw [blowupModelChart_apply, Fin.update_insertNth, pr_radialRescale, blowdown_radialRescale,
    blowdown_blowupModelChart_symm_apply]

/-- At `0`, the map of the previous lemma has the real derivative that multiplies the
coordinate `i` by `ε` and fixes the others. -/
private theorem hasFDerivAt_update_univBall_zero (hε : 0 < ε) (i : Fin (n + 1)) :
    HasFDerivAt (𝕜 := ℝ) (fun w : Fin (n + 1) → ℂ ↦ update w i
        (EuclideanSpace.equiv (Fin (n + 1)) ℂ (univBall 0 ε
          ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm (w i • update w i 1))) i))
      (LinearMap.toContinuousLinearMap (LinearMap.pi fun j ↦
        (if j = i then ε • LinearMap.id else LinearMap.id).comp (LinearMap.proj j))) 0 := by
  set L := EuclideanSpace.equiv (Fin (n + 1)) ℂ
  have hm := (hasFDerivAt_apply (𝕜 := ℝ) i (0 : Fin (n + 1) → ℂ)).smul
    ((hasFDerivAt_const (1 : ℂ) (0 : Fin (n + 1) → ℂ)).update_self i)
  have hρ := hasFDerivAt_univBall hε 0 (L.symm ((0 : Fin (n + 1) → ℂ) i •
    update (0 : Fin (n + 1) → ℂ) i 1))
  have hl := (L.symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp _ hm
  have hh := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) ↦ ℂ) i).comp
    (L.toContinuousLinearMap.restrictScalars ℝ)).hasFDerivAt.comp (0 : Fin (n + 1) → ℂ)
      (hρ.comp (0 : Fin (n + 1) → ℂ) hl)
  refine (hh.update_self i).congr_fderiv ?_
  ext δ j
  by_cases hj : j = i
  · subst hj
    simp [L]
  · simp [hj, L]

/-- The radial rescaling preserves the complex orientation at the point
`(blowupModelChart i).symm 0` of the exceptional divisor. -/
private theorem isOrientationPreservingAt_radialRescale_blowupModelChart_symm_zero (hε : 0 < ε)
    (i : Fin (n + 1)) :
    IsOrientationPreservingAt (complexManifoldOrientation (Fin (n + 1) → ℂ) (BlowupModel n))
      (complexManifoldOrientation (Fin (n + 1) → ℂ) (BlowupModel n)) (radialRescale ε)
      ((blowupModelChart i).symm 0) := by
  set eB := blowupModelChart (n := n) i
  have h0 : (0 : Fin (n + 1) → ℂ) ∈ eB.target := by
    rw [blowupModelChart_target]
    exact mem_univ _
  have hp : eB.symm 0 ∈ eB.source := eB.map_target h0
  have hRp : radialRescale ε (eB.symm 0) ∈ eB.source := by
    rw [blowupModelChart_source] at hp ⊢
    rwa [mem_preimage, pr_radialRescale]
  -- Read in the chart `i` on both sides, the rescaling has positive Jacobian determinant at `0`.
  have hF := orientationSign_complexManifoldOrientation_eq_comp_chart
    (((contMDiff_radialRescale ε).mdifferentiable (by simp)) (eB.symm 0))
    (blowupModelChart_mem_maximalAtlas 1 i) hp (blowupModelChart_mem_maximalAtlas 1 i) hRp
  rw [eB.right_inv h0,
    show ⇑eB ∘ radialRescale ε ∘ eB.symm = _ from
      funext (blowupModelChart_radialRescale_blowupModelChart_symm i)] at hF
  rw [← orientationSign_eq_one_iff, hF, orientationSign_eq_one_iff]
  refine isOrientationPreservingAt_of_det_fderiv_pos _ ?_
  rw [(hasFDerivAt_update_univBall_zero hε i).fderiv, ContinuousLinearMap.det,
    LinearMap.coe_toContinuousLinearMap, LinearMap.det_pi]
  refine Finset.prod_pos fun j _ ↦ ?_
  split_ifs
  · simpa using pow_pos hε _
  · simp

/-- For `0 < ε`, the radial rescaling `radialRescale ε` of the model blowup preserves orientation
at every point, for the complex orientation of `BlowupModel n` on both sides, indexed by
`Fin (2 * n + 1 + 1)`. -/
theorem isOrientationPreservingAt_radialRescale (hε : 0 < ε) (p : BlowupModel n) :
    (complexManifoldOrientationOfFinrank (Fin (n + 1) → ℂ) (BlowupModel n) (r := n)
        (by simp)).IsOrientationPreservingAt
      (complexManifoldOrientationOfFinrank (Fin (n + 1) → ℂ) (BlowupModel n) (r := n) (by simp))
      (radialRescale ε) p := by
  rw [complexManifoldOrientationOfFinrank_def]
  refine IsOrientationPreservingAt.reindex ?_ _
  have hR := isLocalDiffeomorph_radialRescale (n := n) hε
  exact (isPreconnected_univ.isOrientationPreservingAt_iff
    (fun y _ ↦ ((contMDiff_radialRescale ε).of_le (by simp)).contMDiffAt)
    (fun y _ ↦ ⟨_, (hR y).mfderivToContinuousLinearEquiv_coe (by simp)⟩)
    _ _ (mem_univ _) (mem_univ _)).1
    (isOrientationPreservingAt_radialRescale_blowupModelChart_symm_zero hε 0)

end BlowupModel

end SymplecticGeometry

end
