/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.ConnectedSum.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Orientation
public import SymplecticGeometry.Geometry.Manifold.ConnectedSum.OrientationPreserving
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
import Mathlib.LinearAlgebra.Complex.Determinant
import SymplecticGeometry.Geometry.Manifold.Orientation.OpenSubset
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import TauCeti.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# The blowup as an oriented connected sum

This file shows how the maps of `ConnectedSum/Basic.lean` act on the complex orientations, read
with `SymplecticGeometry.complexManifoldOrientationOfFinrank`.

The diffeomorphism `projectiveBlowupModelDiffeomorph n`, from the complement of `[0 : ⋯ : 0 : 1]`
in `ℙ ℂ (Fin (n + 2) → ℂ)` onto the model blowup, reverses the complex orientations at every
point. In the chart `blowupModelChart (Fin.last n)` of the model blowup and the affine chart at
the coordinate `Fin.castSucc (Fin.last n)` of projective space, its inverse reads
`(ζ, w) ↦ (ζ, w̄ |(ζ, 1)|²)`, whose real derivative at the origin is complex conjugation on the
coordinate `w`. The complement of the point is path-connected (an instance of
`PathConnectedSpace`, by Tau Ceti's `TauCeti.isPathConnected_compl_of_finite_of_one_lt_rank`),
so the sign is the same everywhere.

For `ε > 0`, the radial rescaling `BlowupModel.radialRescale ε`, `(ℓ, z) ↦ (ℓ, ε z / √(1 + |z|²))`,
is a local diffeomorphism of the real manifold `BlowupModel n`, but it is not holomorphic. It
still preserves the complex orientation of the model blowup at every point.

The model blowup is path-connected, being the image of the complement of a point in projective
space under `projectiveBlowupModelDiffeomorph n`, so it is enough to check one point, as for
`projectiveBlowupModelDiffeomorph n`. At the point `(blowupModelChart i).symm 0` of the exceptional
divisor, the rescaling reads, in the chart `blowupModelChart i` on both sides, as
`w ↦ update w i (ρ (w i • update w i 1) i)`, with `ρ = univBall 0 ε` on the Hermitian space.
Since `ρ` has derivative `ε • id` at `0`, the real derivative of this map at `0` is `ε` times the
identity on the coordinate `i` and the identity on the others, which has positive determinant.

The file then orients the two pieces `Blowup.connectedSumInl c` and `Blowup.connectedSumInr c`
through which the connected sum of `M` and the projective space maps onto the blowup. The first,
from the punctured `M`, is holomorphic: a re-modelling, the inclusion of an open set and
`GluedAlong.inl`. So it preserves the complex orientations, by
`IsLocalDiffeomorphAt.isOrientationPreservingAt_complexManifoldOrientationOfFinrank`, the complex
orientation of an open subset being the restriction of that of the manifold. The second, from the
punctured projective space, is the re-modelling into `projectiveBlowupOpens n`, which is
holomorphic, then `projectiveBlowupModelDiffeomorph n`, which reverses the complex orientations,
then the radial rescaling, which preserves them, and finally `GluedAlong.inr` and a re-modelling,
which are holomorphic. It therefore reverses the complex orientations, and preserves orientation
from the opposite of the complex orientation of the projective space. These are the orientations
of the summands of the connected sum `M # \overline{ℂP}^{n+1}`.

With `TauCeti.ConnectedSum.isOrientationPreservingAt_of_comp_inl_of_comp_inr`, from this
library's `ConnectedSum/OrientationPreserving.lean`, the two pieces show that
`Blowup.connectedSumDiffeomorph c` carries `TauCeti.ConnectedSum.orientation` of these summands to
the complex orientation of the blowup. Composed with the inverse of the orientation-preserving
diffeomorphism of
`TauCeti.OrientedConnectedSum.exists_diffeomorph_connectedSum_isOrientationPreservingAt`, also
from that file, going from the oriented connected sum onto the connected sum along these balls, it
identifies the blowup with
Tau Ceti's oriented connected sum `TauCeti.OrientedConnectedSum` of `M` and the reversed
projective space, preserving orientation.

## Main results

* `SymplecticGeometry.instPathConnectedSpaceProjectiveBlowupOpens`: the complement of
  `[0 : ⋯ : 0 : 1]` in `ℙ ℂ (Fin (n + 2) → ℂ)` is path-connected;
* `SymplecticGeometry.isOrientationReversingAt_projectiveBlowupModelDiffeomorph`: the
  diffeomorphism `projectiveBlowupModelDiffeomorph n` reverses the complex orientations at every
  point;
* `SymplecticGeometry.BlowupModel.instPathConnectedSpace`: the model blowup is path-connected;
* `SymplecticGeometry.BlowupModel.isOrientationPreservingAt_radialRescale`: for `0 < ε`, the
  radial rescaling preserves the complex orientation at every point;
* `SymplecticGeometry.Blowup.isOrientationPreservingAt_connectedSumInl`: the punctured `M` maps
  into the blowup preserving the complex orientations;
* `SymplecticGeometry.Blowup.isOrientationPreservingAt_connectedSumInr`: the punctured projective
  space maps into the blowup preserving orientation from the opposite of its complex orientation
  to the complex orientation of the blowup;
* `SymplecticGeometry.Blowup.isOrientationPreservingAt_connectedSumDiffeomorph`: the
  diffeomorphism `Blowup.connectedSumDiffeomorph c` preserves orientation, from
  `TauCeti.ConnectedSum.orientation` to the complex orientation of the blowup;
* `SymplecticGeometry.Blowup.nonempty_orientationPreserving_diffeomorph_connectedSum`: the
  blowup is diffeomorphic to the oriented connected sum of `M` and the reversed projective space
  by a diffeomorphism that preserves orientation at every point.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Section 7.1.
-/

public section

noncomputable section

open Set Function OpenPartialHomeomorph TauCeti Manifold.Orientation
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry

section ProjectiveBlowupModel

open Projectivization BlowupModel
open scoped LinearAlgebra.Projectivization ComplexConjugate

variable {n : ℕ}

/-- The complement of `[0 : ⋯ : 0 : 1]` is path-connected: removing a point from the connected
manifold `ℙ ℂ (Fin (n + 2) → ℂ)`, of real dimension `2 n + 2 > 1`, leaves it path-connected. -/
instance instPathConnectedSpaceProjectiveBlowupOpens :
    PathConnectedSpace (projectiveBlowupOpens n) := by
  have h := isPathConnected_compl_of_finite_of_one_lt_rank (E := Fin (n + 1) → ℂ)
    (X := ℙ ℂ (Fin (n + 2) → ℂ)) (by
      rw [rank_fun_eq_lift_mul, Complex.rank_real_complex]
      norm_num
      exact_mod_cast (show 1 < (n + 1) * 2 by omega))
    (finite_singleton (mk ℂ (Pi.single (Fin.last (n + 1)) (1 : ℂ)) (by simp)))
  rw [← coe_projectiveBlowupOpens] at h
  exact isPathConnected_iff_pathConnectedSpace.1 h

/-- The inverse diffeomorphism read in the chart `blowupModelChart (Fin.last n)` of the blowup and
the affine chart at the coordinate `Fin.castSucc (Fin.last n)` of projective space:
`w ↦ update w ℓ (w̄_ℓ |z|²)`, for `ℓ = Fin.last n` and `z = update w ℓ 1`. -/
private theorem affineChart_projectiveBlowupModelDiffeomorph_symm_blowupModelChart_symm
    (w : Fin (n + 1) → ℂ) :
    affineChart (K := ℂ) (Fin.castSucc (Fin.last n))
      (((projectiveBlowupModelDiffeomorph n).symm ((blowupModelChart (Fin.last n)).symm w) :
        ℙ ℂ (Fin (n + 2) → ℂ))) =
      update w (Fin.last n) (conj (w (Fin.last n)) *
        ((∑ j, ‖update w (Fin.last n) 1 j‖ ^ 2 : ℝ) : ℂ)) := by
  rw [blowupModelChart_symm_apply, projectiveBlowupModelDiffeomorph_symm_apply, affineChart_mk]
  funext k
  induction k using Fin.lastCases with
  | last => simp [Fin.succAbove_of_le_castSucc]
  | cast k =>
    have : (Fin.castSucc k : Fin (n + 1)) ≠ Fin.last n := Fin.castSucc_ne_last k
    simp [Fin.succAbove_of_castSucc_lt, this]

/-- At `0`, the map of the previous lemma has the real derivative that conjugates the coordinate
`Fin.last n` and fixes the others. -/
private theorem hasFDerivAt_update_conj_mul_zero :
    HasFDerivAt (𝕜 := ℝ) (fun w : Fin (n + 1) → ℂ ↦ update w (Fin.last n)
        (conj (w (Fin.last n)) * ((∑ j, ‖update w (Fin.last n) 1 j‖ ^ 2 : ℝ) : ℂ)))
      (LinearMap.toContinuousLinearMap (LinearMap.pi fun j ↦
        (if j = Fin.last n then Complex.conjAe.toLinearEquiv.toLinearMap
          else LinearMap.id).comp (LinearMap.proj j))) 0 := by
  set ℓ := Fin.last n
  have hS : DifferentiableAt ℝ (fun w : Fin (n + 1) → ℂ ↦
      ((∑ j, ‖update w ℓ 1 j‖ ^ 2 : ℝ) : ℂ)) 0 := by
    have h : DifferentiableAt ℝ (fun w : Fin (n + 1) → ℂ ↦ ∑ j, ‖update w ℓ 1 j‖ ^ 2) 0 := by
      refine DifferentiableAt.fun_sum fun j _ ↦ ?_
      simp only [update_apply]
      split_ifs
      · exact differentiableAt_const _
      · exact (differentiableAt_apply j _).norm_sq ℝ
    exact Complex.ofRealCLM.differentiableAt.comp (0 : Fin (n + 1) → ℂ) h
  have hc : HasFDerivAt (𝕜 := ℝ) (fun w : Fin (n + 1) → ℂ ↦ conj (w ℓ))
      (Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj (R := ℝ) ℓ)) 0 :=
    Complex.conjCLE.hasFDerivAt.comp _ (hasFDerivAt_apply ℓ _)
  have h1 : ∑ x, (‖update (0 : Fin (n + 1) → ℂ) ℓ 1 x‖ : ℂ) ^ 2 = 1 := by
    simp [update_apply, apply_ite]
  refine ((hc.fun_mul hS.hasFDerivAt).update_self ℓ).congr_fderiv ?_
  ext δ j
  by_cases hj : j = ℓ
  · subst hj
    simp [h1]
  · simp [hj]

/-- The diffeomorphism reverses the complex orientations at the point `[e_ℓ : 0]`, the image under
its inverse of the origin of the chart `blowupModelChart (Fin.last n)`. -/
private theorem isOrientationReversingAt_projectiveBlowupModelDiffeomorph_symm_chart :
    IsOrientationReversingAt
      (complexManifoldOrientation (Fin (n + 1) → ℂ) (projectiveBlowupOpens n))
      (complexManifoldOrientation (Fin (n + 1) → ℂ) (BlowupModel n))
      (projectiveBlowupModelDiffeomorph n)
      ((projectiveBlowupModelDiffeomorph n).symm ((blowupModelChart (Fin.last n)).symm 0)) := by
  set E := Fin (n + 1) → ℂ
  set Φ := projectiveBlowupModelDiffeomorph n
  set ℓ := Fin.last n
  set oU := complexManifoldOrientation E (projectiveBlowupOpens n)
  set oB := complexManifoldOrientation E (BlowupModel n)
  set oP := complexManifoldOrientation E (ℙ ℂ (Fin (n + 2) → ℂ))
  set oE := complexManifoldOrientation E E
  set eB := blowupModelChart (n := n) ℓ
  set eP := affineOpenPartialHomeomorph (K := ℂ) (Fin.castSucc ℓ)
  set p₀ := eB.symm 0
  set F : BlowupModel n → ℙ ℂ (Fin (n + 2) → ℂ) := Subtype.val ∘ Φ.symm
  have hFp₀ : F p₀ ∈ eP.source := by
    rw [affineOpenPartialHomeomorph_toPartialEquiv, affineChart_source]
    simp only [F, p₀, comp_apply, eB, blowupModelChart_symm_apply]
    rw [projectiveBlowupModelDiffeomorph_symm_apply, mk_mem_affineOpen_iff]
    simp [ℓ]
  -- In the two charts, the map has negative Jacobian determinant at `0`.
  have hsg : orientationSign oE oE (⇑eP ∘ F ∘ eB.symm) 0 = -1 := by
    have hg : ⇑eP ∘ F ∘ eB.symm = fun w : E ↦ update w ℓ (conj (w ℓ) *
        ((∑ j, ‖update w ℓ 1 j‖ ^ 2 : ℝ) : ℂ)) :=
      funext fun w ↦ by
        rw [comp_apply, comp_apply, coe_affineOpenPartialHomeomorph]
        exact affineChart_projectiveBlowupModelDiffeomorph_symm_blowupModelChart_symm w
    rw [hg, orientationSign_eq_neg_one_iff]
    refine isOrientationReversingAt_of_det_fderiv_neg oE ?_
    rw [hasFDerivAt_update_conj_mul_zero.fderiv, ContinuousLinearMap.det,
      LinearMap.coe_toContinuousLinearMap, LinearMap.det_pi]
    simp [apply_ite LinearMap.det, Complex.det_conjAe]
  -- Read in these charts, `F` has the same sign, and so has `Φ.symm`, followed by the inclusion
  -- of the open set, which preserves the complex orientations.
  have hp₀ : eB p₀ = 0 := eB.right_inv (by simp [eB, blowupModelChart_target])
  have hF := orientationSign_complexManifoldOrientation_eq_comp_chart
    (((isLocalDiffeomorph_subtype_val (n := 1) _).mdifferentiableAt one_ne_zero).comp p₀
      (Φ.symm.mdifferentiable (by simp) p₀))
    (blowupModelChart_mem_maximalAtlas 1 ℓ) (eB.map_target (by simp [eB, blowupModelChart_target]))
    (affineOpenPartialHomeomorph_mem_maximalAtlas _) hFp₀
  rw [hp₀, hsg] at hF
  have h3 := Φ.symm.orientationSign_comp_diffeomorph (by simp) oB oU oP Subtype.val p₀
  rw [orientationSign_of_isOrientationPreservingAt
    (isOrientationPreservingAt_subtype_val_complexManifoldOrientation _), one_mul] at h3
  have h4 := Φ.symm.orientationSign_comp_diffeomorph (by simp) oB oU oB Φ p₀
  rw [show ⇑Φ ∘ ⇑Φ.symm = id from funext Φ.apply_symm_apply, orientationSign_id,
    ← h3, hF] at h4
  rw [← orientationSign_eq_neg_one_iff]
  omega

/-- The diffeomorphism `projectiveBlowupModelDiffeomorph n` reverses orientation at every point,
for the complex orientation of the open subset `projectiveBlowupOpens n` of
`ℙ ℂ (Fin (n + 2) → ℂ)` and the complex orientation of the model blowup `BlowupModel n`, both
indexed by `Fin (2 * n + 1 + 1)`. -/
theorem isOrientationReversingAt_projectiveBlowupModelDiffeomorph (x : projectiveBlowupOpens n) :
    (complexManifoldOrientationOfFinrank (Fin (n + 1) → ℂ) (projectiveBlowupOpens n) (r := n)
        (by simp)).IsOrientationReversingAt
      (complexManifoldOrientationOfFinrank (Fin (n + 1) → ℂ) (BlowupModel n) (r := n) (by simp))
      (projectiveBlowupModelDiffeomorph n) x := by
  rw [complexManifoldOrientationOfFinrank_def, complexManifoldOrientationOfFinrank_def]
  refine IsOrientationReversingAt.reindex ?_ _
  set Φ := projectiveBlowupModelDiffeomorph n
  have h₀ := isOrientationReversingAt_projectiveBlowupModelDiffeomorph_symm_chart (n := n)
  rw [← isOrientationPreservingAt_neg_right] at h₀ ⊢
  exact (Φ.isLocalDiffeomorph.isOrientationPreservingAt_iff (by simp) _ _ _ _).1 h₀

end ProjectiveBlowupModel

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
  exact (hR.isOrientationPreservingAt_iff (by simp) _ _ _ _).1
    (isOrientationPreservingAt_radialRescale_blowupModelChart_symm_zero hε 0)

end BlowupModel

/-! ## The orientations of the two pieces of the connected sum -/

namespace Blowup

open ConnectedSum (puncture)
open scoped LinearAlgebra.Projectivization

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M] {p₀ : M}
  (c : BlowupChart (n := n) M p₀) [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

/-- For a holomorphic chart `c`, the map `connectedSumInl c` of the punctured `M` into the
blowup, both re-modelled on `EuclideanSpace ℂ (Fin (n + 1))`, preserves orientation at every
point, from the restriction of the complex orientation of `M` to the complex orientation of the
blowup. -/
theorem isOrientationPreservingAt_connectedSumInl [T2Space M] (x : puncture c.connectedSumBall) :
    ((complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
        (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M) (r := n)
          (by simp)).restrict (puncture c.connectedSumBall)).IsOrientationPreservingAt
      (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
        (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm (Blowup c)) (r := n)
          (by simp))
      (connectedSumInl c) x := by
  rw [← complexManifoldOrientationOfFinrank_opens_eq_restrict]
  exact (isLocalDiffeomorph_connectedSumInl_complex c x
    ).isOrientationPreservingAt_complexManifoldOrientationOfFinrank _ _ ∞

/-- For a holomorphic chart `c`, the map `connectedSumInr c` of the punctured projective space into
the blowup, both re-modelled on `EuclideanSpace ℂ (Fin (n + 1))`, preserves orientation at every
point, from the restriction of the opposite of the complex orientation of the projective space to
the complex orientation of the blowup. -/
theorem isOrientationPreservingAt_connectedSumInr
    (y : puncture (EuclideanComplexProjectiveSpace.connectedSumBall n)) :
    ((-EuclideanComplexProjectiveSpace.orientation n).restrict
        (puncture (EuclideanComplexProjectiveSpace.connectedSumBall n))).IsOrientationPreservingAt
      (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
        (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm (Blowup c)) (r := n)
          (by simp))
      (connectedSumInr c) y := by
  -- The composite of `GluedAlong.inr` and the re-modelling is holomorphic.
  have hl : (complexManifoldOrientationOfFinrank (Fin (n + 1) → ℂ) (modelOpens c) (r := n)
      (by simp)).IsOrientationPreservingAt
      (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
        (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm (Blowup c)) (r := n)
          (by simp)) (remodelHomeomorph _ _ ∘ GluedAlong.inr (gluingHomeomorph c))
      (connectedSumInrModel c y) := by
    rw [← coe_remodelDiffeomorph (n := ∞)]
    exact (((isLocalDiffeomorph_inr c _).of_le le_top).comp
      (hg := (remodelDiffeomorph _ _).isLocalDiffeomorph _)
      ).isOrientationPreservingAt_complexManifoldOrientationOfFinrank _ _ ∞
  have hg : (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
      (puncture (EuclideanComplexProjectiveSpace.connectedSumBall n)) (r := n)
      (by simp)).IsOrientationReversingAt
      (complexManifoldOrientationOfFinrank (Fin (n + 1) → ℂ) (modelOpens c) (r := n)
        (by simp)) (connectedSumInrModel c) y := by
    rw [complexManifoldOrientationOfFinrank_opens_eq_restrict (M := BlowupModel n),
      ← Manifold.Orientation.isOrientationPreservingAt_neg_right,
      ← Manifold.Orientation.restrict_neg,
      Manifold.Orientation.isOrientationPreservingAt_restrict_iff,
      Manifold.Orientation.isOrientationPreservingAt_neg_right, val_comp_connectedSumInrModel]
    exact (BlowupModel.isOrientationPreservingAt_radialRescale c.ballRadius_pos _).comp_reversing
      ((isOrientationReversingAt_projectiveBlowupModelDiffeomorph _).comp_preserving
        ((isLocalDiffeomorph_connectedSumInrOpens y
          ).isOrientationPreservingAt_complexManifoldOrientationOfFinrank _ _ ∞))
  rw [Manifold.Orientation.restrict_neg, Manifold.Orientation.isOrientationPreservingAt_neg_left,
    EuclideanComplexProjectiveSpace.orientation_def,
    ← complexManifoldOrientationOfFinrank_opens_eq_restrict, connectedSumInr_eq_comp]
  exact hl.comp_reversing hg

variable [T2Space M]

/-- For a holomorphic chart `c`, the diffeomorphism `Blowup.connectedSumDiffeomorph c` preserves
orientation at every point, from the orientation `TauCeti.ConnectedSum.orientation` of the
connected sum of `M`, with its complex orientation, and the projective space, with the opposite
of its complex orientation, to the complex orientation of the blowup. -/
theorem isOrientationPreservingAt_connectedSumDiffeomorph :
    letI := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1)))
      c.isOpenEmbedding_connectedSumBall
      (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
    haveI := TauCeti.ConnectedSum.isManifold (n := 1) c.isOpenEmbedding_connectedSumBall
      (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
      (IsLocalDiffeomorph.of_le (c.isLocalDiffeomorph_connectedSumBall Fact.out)
        ENat.LEInfty.out)
      (IsLocalDiffeomorph.of_le
        (EuclideanComplexProjectiveSpace.isLocalDiffeomorph_connectedSumBall n) ENat.LEInfty.out)
    ∀ p, IsOrientationPreservingAt
      (TauCeti.ConnectedSum.orientation c.isOpenEmbedding_connectedSumBall
        (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
        (IsLocalDiffeomorph.of_le (c.isLocalDiffeomorph_connectedSumBall Fact.out)
          ENat.LEInfty.out)
        (IsLocalDiffeomorph.of_le
          (EuclideanComplexProjectiveSpace.isLocalDiffeomorph_connectedSumBall n)
          ENat.LEInfty.out)
        (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
          (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M) (r := n)
            (by simp))
        (-EuclideanComplexProjectiveSpace.orientation n)
        (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
          (EuclideanSpace ℂ (Fin (n + 1))) (r := n) (by simp))
        (fun v _ ↦ c.isOrientationPreservingAt_connectedSumBall Fact.out v)
        (fun u _ ↦ EuclideanComplexProjectiveSpace.isOrientationReversingAt_connectedSumBall n u))
      (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
        (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm (Blowup c)) (r := n)
          (by simp))
      (connectedSumDiffeomorph c) p := by
  let := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1)))
    c.isOpenEmbedding_connectedSumBall
    (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
  refine TauCeti.ConnectedSum.isOrientationPreservingAt_of_comp_inl_of_comp_inr
    ((connectedSumDiffeomorph c).isLocalDiffeomorph.of_le (by simp)) _ 0 (fun x ↦ ?_)
    (fun y _ ↦ ?_)
  · rw [show ⇑(connectedSumDiffeomorph c) ∘ ConnectedSum.inl _ _ = connectedSumInl c from
      funext (connectedSumDiffeomorph_inl c)]
    exact isOrientationPreservingAt_connectedSumInl c x
  · rw [show ⇑(connectedSumDiffeomorph c) ∘ ConnectedSum.inr _ _ = connectedSumInr c from
      funext (connectedSumDiffeomorph_inr c)]
    exact isOrientationPreservingAt_connectedSumInr c y

/-- **The blowup as an oriented connected sum.** Let `M` be a connected Hausdorff complex manifold
of complex dimension `n + 1`, and `c` a holomorphic chart of `M` centred at `p₀`. Re-model `M`, the
blowup `Blowup c` and the projective space `EuclideanComplexProjectiveSpace n` on
`EuclideanSpace ℂ (Fin (n + 1))`, and give each its complex orientation. Then there is a
diffeomorphism from the blowup onto Tau Ceti's oriented connected sum of `M` and the projective
space with the opposite orientation, `M # \overline{ℂP}^{n+1}`, which preserves orientation at
every point, for the orientation `TauCeti.OrientedConnectedSum.orientation` of the connected sum.

Milestone: *Blowup as a connected sum with the reversed projective space*. -/
theorem nonempty_orientationPreserving_diffeomorph_connectedSum [ConnectedSpace M] :
    Nonempty {Φ : Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm (Blowup c)
        ≃ₘ^∞⟮𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))), 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1)))⟯
        OrientedConnectedSum
          (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
            (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M) (r := n)
              (by simp))
          (-EuclideanComplexProjectiveSpace.orientation n) //
      ∀ p, IsOrientationPreservingAt
        (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
          (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm (Blowup c)) (r := n)
            (by simp))
        (OrientedConnectedSum.orientation _ _) Φ p} := by
  let := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1)))
    c.isOpenEmbedding_connectedSumBall
    (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
  have := TauCeti.ConnectedSum.isManifold c.isOpenEmbedding_connectedSumBall
    (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
    (c.isLocalDiffeomorph_connectedSumBall Fact.out)
    (EuclideanComplexProjectiveSpace.isLocalDiffeomorph_connectedSumBall n)
  obtain ⟨Ψ, hΨ⟩ := OrientedConnectedSum.exists_diffeomorph_connectedSum_isOrientationPreservingAt
    _ _ c.isOpenEmbedding_connectedSumBall
    (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
    (c.isLocalDiffeomorph_connectedSumBall Fact.out)
    (EuclideanComplexProjectiveSpace.isLocalDiffeomorph_connectedSumBall n) _
    (c.isOrientationPreservingAt_connectedSumBall Fact.out)
    (EuclideanComplexProjectiveSpace.isOrientationReversingAt_connectedSumBall n)
  refine ⟨⟨(connectedSumDiffeomorph c).symm.trans Ψ.symm, fun p ↦ ?_⟩⟩
  rw [Diffeomorph.coe_trans]
  exact ((hΨ _).diffeomorph_symm (by simp)).comp
    ((isOrientationPreservingAt_connectedSumDiffeomorph c _).diffeomorph_symm (by simp))

end Blowup

end SymplecticGeometry

end
