/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Model
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Euclidean
public import TauCeti.Algebra.Group.Fin.Tuple
public import TauCeti.Geometry.Manifold.ConnectedSum.Basic
public import TauCeti.Geometry.Manifold.ConnectedSum.Smooth
public import TauCeti.LinearAlgebra.Projectivization.Basic
import SymplecticGeometry.Analysis.Normed.Module.Ball.Homeomorph
import SymplecticGeometry.Geometry.Manifold.Complex.Orientation
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.RestrictScalars
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving
import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.UnivBall
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Projectivization.Map
import TauCeti.Topology.Algebra.Projectivization

/-!
# The blowup as a connected sum: the gluing balls and the model

Blowing up a complex manifold `M` of complex dimension `n + 1` at a point `p₀` gives, as a smooth
oriented manifold, the connected sum of `M` with the complex projective space of dimension
`n + 1` with its orientation reversed. Tau Ceti's connected sum `TauCeti.ConnectedSum e₁ e₂` glues
two manifolds modelled on one real inner product space along coordinate balls `e₁` and `e₂`,
and its diffeomorphism type depends only on how these act on orientations at `0`
(`TauCeti.ConnectedSum.nonempty_diffeomorph_of_isOrientationReversingAt`). This file builds the
two balls, on the Hermitian space `EuclideanSpace ℂ (Fin (n + 1))`, and proves that they satisfy
the hypotheses of that theorem.

* The first summand is `M`, charted on `Fin (n + 1) → ℂ` and re-modelled on the Hermitian space
  with `SymplecticGeometry.Remodel`, as `SymplecticGeometry.EuclideanComplexProjectiveSpace` is.
  For a chart `c : BlowupChart M p₀`, `BlowupChart.euclideanChart c` is `c` read on the Hermitian
  space, and `BlowupChart.connectedSumBall c` sends `v` to `c.symm (ρ v)`, where
  `ρ = OpenPartialHomeomorph.univBall 0 ε` is Mathlib's map `v ↦ ε (1 + |v|²)^(-1/2) v` onto the
  ball of radius `ε`, for an `ε > 0` (`BlowupChart.ballRadius c`) whose closed ball lies in the
  target of the chart. When `c` is holomorphic, the ball preserves the complex orientations at
  `0`: there `ρ` has derivative `ε • id`, and `c.symm` is a local biholomorphism. Being a local
  diffeomorphism of a connected space, it then preserves them at every point.
* The second summand is `EuclideanComplexProjectiveSpace n` with the opposite of its complex
  orientation, and `EuclideanComplexProjectiveSpace.connectedSumBall n` is `u ↦ [u : 1]`, the
  inverse of the affine chart at the last coordinate. Being holomorphic, it preserves the complex
  orientations, and so reverses the opposite one.

In both cases the orientation of the model is its complex orientation as a complex manifold over
itself, `SymplecticGeometry.complexManifoldOrientationOfFinrank`.

The file also identifies the projective space minus a point with the model
blowup. For `E := Fin (n + 1) → ℂ`, write a point of `ℙ ℂ (Fin (n + 2) → ℂ)` as `[z : w]`
with `z ∈ E` and `w ∈ ℂ` (`Fin.snoc z w`). Off the point `[0 : ⋯ : 0 : 1]` the vector `z` is
nonzero, and
$$[z : w] \longmapsto \bigl([z],\ \bar w\, z / \lvert z\rvert^2\bigr)$$
is a well-defined map onto the model blowup `BlowupModel n`, where `|z|² = ∑ i, ‖z i‖ ^ 2` is the
Hermitian norm. Its inverse sends `(ℓ, t • z)`, for `z` spanning `ℓ`, to `[z : t̄ |z|²]`. This is
the identification of the complement of the point with the total space of the dual of the
tautological line bundle, followed by the conjugate-linear identification of that dual with the
tautological bundle by the Hermitian metric, as in McDuff–Salamon, §7.1. The map is not
holomorphic, so it is a diffeomorphism of the underlying real manifolds. How it acts on the complex
orientations is shown in `ConnectedSum/Orientation.lean`.

Finally, for `ε > 0`, the radial rescaling `(ℓ, z) ↦ (ℓ, ε z / √(1 + |z|²))` of the model blowup
keeps the line and applies Mathlib's map `univBall 0 ε` of the Hermitian space to the blowdown. It
is injective, its range is the set of points whose blowdown has Hermitian norm less than `ε`, and
it is a smooth local diffeomorphism of the real manifold `BlowupModel n`, with inverse on its range
given by `(univBall 0 ε).symm` on the blowdown. For `ε = c.ballRadius` it lands in
`Blowup.modelOpens c`. This is the map `S` with which the connected sum is identified with the
blowup on the side of the projective space.

A section maps the two punctured summands of the connected sum into the blowup, both
re-modelled on the Hermitian space. The punctured `M` goes in by `GluedAlong.inl`, as the
complement of the exceptional divisor; the punctured projective space goes in by
`GluedAlong.inr` after `projectiveBlowupModelDiffeomorph n` and the rescaling `S` for
`ε = c.ballRadius`. Both maps are injective smooth local diffeomorphisms, their images cover the
blowup, and they meet exactly at the points that the connected sum glues: for `v ≠ 0`, the
point `c.symm (ρ v)` of `M` and the point `[u : 1]`, with `u` the inversion of `v` in the unit
sphere, both go to the point of the blowup over `c.symm (ρ v)`, since the blowdown of
`projectiveBlowupModelDiffeomorph n [u : 1]` is the inversion of `u`, that is `v`. Glued with
Tau Ceti's `TauCeti.ConnectedSum.lift`, they give a bijection from the connected sum onto the
blowup which is a local diffeomorphism, since the inclusions of the punctured summands into the
connected sum are local diffeomorphisms
(`TauCeti.ConnectedSum.isLocalDiffeomorph_of_comp_inl_of_comp_inr`); it is therefore a
diffeomorphism,
`SymplecticGeometry.Blowup.connectedSumDiffeomorph c`. This last step follows the proof of Tau
Ceti's `TauCeti.ConnectedSum.assocDiffeomorph`, which builds a diffeomorphism out of a connected
sum in the same way with `IsLocalDiffeomorph.diffeomorphOfBijective`.

## Main definitions

* `SymplecticGeometry.BlowupChart.connectedSumBall c`: the ball `e₁` of `M`.
* `SymplecticGeometry.EuclideanComplexProjectiveSpace.connectedSumBall n`: the ball `e₂` of the
  projective space.
* `SymplecticGeometry.projectiveBlowupOpens n`: the complement of `[0 : ⋯ : 0 : 1]` in
  `ℙ ℂ (Fin (n + 2) → ℂ)`, as an open set: Tau Ceti's `Projectivization.linearProjectionDomain`
  of `Fin.init`. By `SymplecticGeometry.mk_mem_projectiveBlowupOpens`, the line of `v` lies in it
  exactly when `Fin.init v ≠ 0`, and `SymplecticGeometry.coe_projectiveBlowupOpens` says that it
  is the complement of the point.
* `SymplecticGeometry.projectiveBlowupModelDiffeomorph n`: the smooth diffeomorphism above, for
  the real manifold structures modelled on `𝓘(ℝ, Fin (n + 1) → ℂ)`, with
  `projectiveBlowupModelDiffeomorph_apply` and `projectiveBlowupModelDiffeomorph_symm_apply` on
  representatives.
* `SymplecticGeometry.BlowupModel.radialRescale ε`: the radial rescaling above, with
  `SymplecticGeometry.BlowupModel.pr_radialRescale`,
  `SymplecticGeometry.BlowupModel.blowdown_radialRescale` and
  `SymplecticGeometry.BlowupModel.blowdown_radialRescale_of_pos`.
* `SymplecticGeometry.Blowup.connectedSumInl c`, `SymplecticGeometry.Blowup.connectedSumInr c`:
  the maps of the punctured `M` and of the punctured projective space into the blowup. They
  factor (`connectedSumInl_eq_comp`, `connectedSumInr_eq_comp`) through
  `SymplecticGeometry.Blowup.connectedSumInlOpens c`, into `puncturedOpens c`, and
  `SymplecticGeometry.Blowup.connectedSumInrModel c`, into `modelOpens c`, which is
  `SymplecticGeometry.Blowup.connectedSumInrOpens`, into `projectiveBlowupOpens n`, followed by
  `projectiveBlowupModelDiffeomorph n` and the radial rescaling. Their values are given by
  `coe_connectedSumInlOpens`, `coe_connectedSumInrOpens` and `coe_connectedSumInrModel`.
* `SymplecticGeometry.Blowup.connectedSumDiffeomorph c`: the diffeomorphism from the connected sum
  of `M` and the projective space along the two balls onto the blowup, as real manifolds modelled
  on the Hermitian space, with `SymplecticGeometry.Blowup.coe_connectedSumDiffeomorph`,
  `SymplecticGeometry.Blowup.connectedSumDiffeomorph_inl` and
  `SymplecticGeometry.Blowup.connectedSumDiffeomorph_inr`: it is `connectedSumInl c` on the
  punctured `M` and `connectedSumInr c` on the punctured projective space.

## Main results

* `SymplecticGeometry.BlowupChart.isOpenEmbedding_connectedSumBall`,
  `SymplecticGeometry.BlowupChart.isLocalDiffeomorph_connectedSumBall`,
  `SymplecticGeometry.BlowupChart.isOrientationPreservingAt_connectedSumBall`;
* `SymplecticGeometry.EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall`,
  `SymplecticGeometry.EuclideanComplexProjectiveSpace.isLocalDiffeomorph_connectedSumBall`,
  `SymplecticGeometry.EuclideanComplexProjectiveSpace.isOrientationPreservingAt_connectedSumBall`,
  `SymplecticGeometry.EuclideanComplexProjectiveSpace.isOrientationReversingAt_connectedSumBall`:
  at every point, the ball preserves the complex orientations and reverses the opposite one;
* `SymplecticGeometry.projectiveBlowupModelDiffeomorph_apply_snoc_one`: the diffeomorphism sends
  `[u : 1]` to `([u], u / |u|²)`, and
  `SymplecticGeometry.blowdown_projectiveBlowupModelDiffeomorph_snoc_one`:
  read on `EuclideanSpace ℂ (Fin (n + 1))`, its blowdown there is the inversion
  `EuclideanGeometry.inversion 0 1 u` in the unit sphere;
* `SymplecticGeometry.BlowupModel.radialRescale_injective`,
  `SymplecticGeometry.BlowupModel.range_radialRescale`,
  `SymplecticGeometry.BlowupModel.radialRescale_ballRadius_mem_modelOpens`,
  `SymplecticGeometry.BlowupModel.contMDiff_radialRescale` and
  `SymplecticGeometry.BlowupModel.isLocalDiffeomorph_radialRescale`.
* `SymplecticGeometry.Blowup.connectedSumInl_injective`,
  `SymplecticGeometry.Blowup.connectedSumInr_injective`,
  `SymplecticGeometry.Blowup.isLocalDiffeomorph_connectedSumInl_complex`,
  `SymplecticGeometry.Blowup.isLocalDiffeomorph_connectedSumInl`,
  `SymplecticGeometry.Blowup.isLocalDiffeomorph_connectedSumInr`: both maps are injective local
  diffeomorphisms, and the first is even a local biholomorphism;
* `SymplecticGeometry.Blowup.connectedSumInl_eq_connectedSumInr_iff`: they agree exactly at glued
  points, and `SymplecticGeometry.Blowup.range_connectedSumInl_union_range_connectedSumInr`: their
  ranges cover the blowup.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Section 7.1.
* [A. Kosinski, *Differential Manifolds*][Kosinski1993], Chapter VI, Section 1.
-/

public section

noncomputable section

open Set Metric TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

open OpenPartialHomeomorph

variable {n : ℕ}

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M] {p₀ : M}

namespace BlowupChart

variable (c : BlowupChart (n := n) M p₀)

/-- The chart `c` of `M`, read on `M` re-modelled on the Hermitian space
`EuclideanSpace ℂ (Fin (n + 1))`: `c` followed by the identification of `Fin (n + 1) → ℂ` with
that space. -/
def euclideanChart :
    OpenPartialHomeomorph (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M)
      (EuclideanSpace ℂ (Fin (n + 1))) :=
  remodelChart _ c.toOpenPartialHomeomorph

theorem euclideanChart_def :
    c.euclideanChart =
      remodelChart (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm
        c.toOpenPartialHomeomorph :=
  (rfl)

@[simp]
theorem euclideanChart_symm_apply (v : EuclideanSpace ℂ (Fin (n + 1))) :
    c.euclideanChart.symm v =
      remodelHomeomorph _ M (c.symm (EuclideanSpace.equiv (Fin (n + 1)) ℂ v)) := by
  simp [euclideanChart_def]

theorem zero_mem_euclideanChart_target : 0 ∈ c.euclideanChart.target := by
  simpa [euclideanChart_def] using c.zero_mem_target

/-- When `c` is a holomorphic chart of `M`, `c.euclideanChart` is a holomorphic chart of `M`
re-modelled on `EuclideanSpace ℂ (Fin (n + 1))`. -/
theorem euclideanChart_mem_maximalAtlas [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
    (hc : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M) :
    c.euclideanChart ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin (n + 1))) ∞
      (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M) :=
  remodelChart_mem_maximalAtlas
    (IsManifold.maximalAtlas_eq_of_ne_zero (I := 𝓘(ℂ, Fin (n + 1) → ℂ)) (M := M) (m := ω) (n := ∞)
      (by simp) (by simp) ▸ hc)

theorem exists_closedBall_subset_euclideanChart_target :
    ∃ ε : ℝ, 0 < ε ∧ closedBall 0 ε ⊆ c.euclideanChart.target :=
  nhds_basis_closedBall.mem_iff.1
    (c.euclideanChart.open_target.mem_nhds c.zero_mem_euclideanChart_target)

/-- A radius `ε > 0` such that the closed ball of radius `ε` about `0`, in the Hermitian norm,
lies in the target of `c.euclideanChart`. -/
def ballRadius : ℝ := c.exists_closedBall_subset_euclideanChart_target.choose

theorem ballRadius_pos : 0 < c.ballRadius :=
  c.exists_closedBall_subset_euclideanChart_target.choose_spec.1

theorem closedBall_ballRadius_subset : closedBall 0 c.ballRadius ⊆ c.euclideanChart.target :=
  c.exists_closedBall_subset_euclideanChart_target.choose_spec.2

/-- The coordinate ball of `M` along which the blowup at `p₀` is a connected sum:
`v ↦ c.symm (ρ v)`, for Mathlib's map `ρ = univBall 0 ε` of the Hermitian space
`EuclideanSpace ℂ (Fin (n + 1))` onto the ball of radius `ε = c.ballRadius`, read in
`Fin (n + 1) → ℂ`. -/
def connectedSumBall :
    EuclideanSpace ℂ (Fin (n + 1)) →
      Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M :=
  c.euclideanChart.symm ∘ univBall 0 c.ballRadius

theorem connectedSumBall_def :
    c.connectedSumBall = c.euclideanChart.symm ∘ univBall 0 c.ballRadius :=
  (rfl)

theorem connectedSumBall_apply (v : EuclideanSpace ℂ (Fin (n + 1))) :
    c.connectedSumBall v =
      remodelHomeomorph _ M
        (c.symm (EuclideanSpace.equiv (Fin (n + 1)) ℂ (univBall 0 c.ballRadius v))) := by
  rw [connectedSumBall_def, Function.comp_apply, euclideanChart_symm_apply]

@[simp]
theorem connectedSumBall_zero : c.connectedSumBall 0 = remodelHomeomorph _ M p₀ := by
  rw [connectedSumBall_apply, univBall_apply_zero, map_zero, symm_zero]

/-- The point `ρ v` of the ball of radius `c.ballRadius`, read on `Fin (n + 1) → ℂ`, lies in the
target of `c`. -/
theorem equiv_univBall_mem_target (v : EuclideanSpace ℂ (Fin (n + 1))) :
    EuclideanSpace.equiv (Fin (n + 1)) ℂ (univBall 0 c.ballRadius v) ∈ c.target := by
  have h := (univBall (0 : EuclideanSpace ℂ (Fin (n + 1))) c.ballRadius).map_source
    (x := v) (by simp)
  rw [univBall_target 0 c.ballRadius_pos] at h
  have h' := c.closedBall_ballRadius_subset (ball_subset_closedBall h)
  rw [euclideanChart_def, remodelChart_target] at h'
  -- `exact`: the inverse of the identification of the models is `EuclideanSpace.equiv`.
  exact h'

theorem isOpenEmbedding_connectedSumBall : Topology.IsOpenEmbedding c.connectedSumBall :=
  isOpenEmbedding_symm_comp_univBall c.ballRadius_pos
    (ball_subset_closedBall.trans c.closedBall_ballRadius_subset)

variable [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]

theorem isLocalDiffeomorph_connectedSumBall
    (hc : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M) :
    IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1)))
      ∞ c.connectedSumBall :=
  isLocalDiffeomorph_symm_comp_univBall le_rfl
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero ∞ (by simp)
      (c.euclideanChart_mem_maximalAtlas hc))
    c.ballRadius_pos (ball_subset_closedBall.trans c.closedBall_ballRadius_subset)

/-- For a holomorphic chart `c`, the ball `c.connectedSumBall` preserves at every point the
complex orientations of `EuclideanSpace ℂ (Fin (n + 1))` and of `M`, re-modelled on it. -/
theorem isOrientationPreservingAt_connectedSumBall
    (hc : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)
    (v : EuclideanSpace ℂ (Fin (n + 1))) :
    (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
        (EuclideanSpace ℂ (Fin (n + 1))) (r := n) (by simp)).IsOrientationPreservingAt
      (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
        (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M) (r := n) (by simp))
      c.connectedSumBall v := by
  -- The ball is a local diffeomorphism of the connected space `EuclideanSpace ℂ (Fin (n + 1))`,
  -- so it is enough to check the point `0`, where `univBall` has derivative `ε • id`.
  have hd := c.isLocalDiffeomorph_connectedSumBall hc
  refine (hd.isOrientationPreservingAt_iff (by simp) _ _ 0 v).1 ?_
  have hφ := (c.euclideanChart.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
    (c.euclideanChart_mem_maximalAtlas hc)
    c.zero_mem_euclideanChart_target).isOrientationPreservingAt_complexManifoldOrientation ∞
  rw [complexManifoldOrientationOfFinrank_def, complexManifoldOrientationOfFinrank_def,
    connectedSumBall_def]
  exact ((univBall_apply_zero (0 : EuclideanSpace ℂ (Fin (n + 1))) c.ballRadius ▸
    hφ.reindex _).comp (isOrientationPreservingAt_univBall c.ballRadius_pos _))

end BlowupChart

namespace EuclideanComplexProjectiveSpace

variable (n)

/-- The affine chart of `ℙ ℂ (Fin (n + 2) → ℂ)` at the last homogeneous coordinate, read on
`EuclideanComplexProjectiveSpace n`: Tau Ceti's `affineOpenPartialHomeomorph (Fin.last (n + 1))`
followed by the identification of `Fin (n + 1) → ℂ` with `EuclideanSpace ℂ (Fin (n + 1))`. -/
def lastAffineChart :
    OpenPartialHomeomorph (EuclideanComplexProjectiveSpace n) (EuclideanSpace ℂ (Fin (n + 1))) :=
  remodelChart _ (Projectivization.affineOpenPartialHomeomorph (K := ℂ) (Fin.last (n + 1)))

theorem lastAffineChart_def :
    lastAffineChart n =
      remodelChart (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm
        (Projectivization.affineOpenPartialHomeomorph (K := ℂ) (Fin.last (n + 1))) :=
  (rfl)

theorem lastAffineChart_symm_apply (u : EuclideanSpace ℂ (Fin (n + 1))) :
    (lastAffineChart n).symm u = remodelHomeomorph _ _
      ((Projectivization.affineChart (Fin.last (n + 1))).symm (EuclideanSpace.equiv _ ℂ u)) := by
  simp [lastAffineChart_def]

@[simp]
theorem lastAffineChart_target : (lastAffineChart n).target = univ := by
  simp [lastAffineChart_def]

theorem lastAffineChart_mem_maximalAtlas :
    lastAffineChart n ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin (n + 1))) ∞
      (EuclideanComplexProjectiveSpace n) :=
  remodelChart_mem_maximalAtlas
    (Projectivization.affineOpenPartialHomeomorph_mem_maximalAtlas (Fin.last (n + 1)))

/-- The coordinate ball of the projective space along which the blowup is a connected sum:
`u ↦ [u : 1]`, the inverse of the affine chart at the last homogeneous coordinate. -/
def connectedSumBall : EuclideanSpace ℂ (Fin (n + 1)) → EuclideanComplexProjectiveSpace n :=
  (lastAffineChart n).symm

theorem connectedSumBall_def : connectedSumBall n = (lastAffineChart n).symm :=
  (rfl)

theorem connectedSumBall_apply (u : EuclideanSpace ℂ (Fin (n + 1))) :
    connectedSumBall n u = remodelHomeomorph _ _
      (Projectivization.mk ℂ
        (Fin.insertNth (α := fun _ ↦ ℂ) (Fin.last (n + 1)) 1 (EuclideanSpace.equiv _ ℂ u))
        (Fin.insertNth_one_ne_zero _ _)) := by
  rw [connectedSumBall_def, lastAffineChart_symm_apply, Projectivization.affineChart_symm_apply]

/-- The centre of the ball `connectedSumBall n` is the point `[0 : ⋯ : 0 : 1]`. -/
@[simp]
theorem connectedSumBall_zero :
    connectedSumBall n 0 = remodelHomeomorph _ _
      (Projectivization.mk ℂ (Pi.single (Fin.last (n + 1)) 1 : Fin (n + 2) → ℂ) (by simp)) := by
  rw [connectedSumBall_def, lastAffineChart_symm_apply, map_zero,
    Projectivization.affineChart_symm_zero]

theorem isOpenEmbedding_connectedSumBall : Topology.IsOpenEmbedding (connectedSumBall n) :=
  (lastAffineChart n).symm.isOpenEmbedding (by simp)

theorem isLocalDiffeomorph_connectedSumBall :
    IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1)))
      ∞ (connectedSumBall n) := fun u ↦
  (lastAffineChart n).isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
    (IsManifold.maximalAtlas_subset_restrictScalars_of_ne_zero ∞ (by simp)
      (lastAffineChart_mem_maximalAtlas n)) (by simp)

/-- The ball `connectedSumBall n` preserves the complex orientations of
`EuclideanSpace ℂ (Fin (n + 1))` and of the projective space at every point. -/
theorem isOrientationPreservingAt_connectedSumBall (u : EuclideanSpace ℂ (Fin (n + 1))) :
    (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
        (EuclideanSpace ℂ (Fin (n + 1))) (r := n) (by simp)).IsOrientationPreservingAt
      (orientation n) (connectedSumBall n) u := by
  rw [complexManifoldOrientationOfFinrank_def, orientation_def,
    complexManifoldOrientationOfFinrank_def]
  exact (((lastAffineChart n).isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
    (lastAffineChart_mem_maximalAtlas n) (by simp)
    ).isOrientationPreservingAt_complexManifoldOrientation ∞).reindex _

/-- The ball `connectedSumBall n` reverses orientation at every point, from the complex
orientation of `EuclideanSpace ℂ (Fin (n + 1))` to the opposite of the complex orientation of the
projective space. -/
theorem isOrientationReversingAt_connectedSumBall (u : EuclideanSpace ℂ (Fin (n + 1))) :
    (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
        (EuclideanSpace ℂ (Fin (n + 1))) (r := n) (by simp)).IsOrientationReversingAt
      (-orientation n) (connectedSumBall n) u := by
  rw [Manifold.Orientation.isOrientationReversingAt_neg_right]
  exact isOrientationPreservingAt_connectedSumBall n u

end EuclideanComplexProjectiveSpace

/-! ## Projective space minus a point as the model blowup -/

section ProjectiveBlowupModel

open Function Filter Projectivization
open scoped LinearAlgebra.Projectivization Topology ComplexConjugate

/-! ### The complement of the point `[0 : ⋯ : 0 : 1]` -/

/-- `Fin.init`, read as the linear map `LinearMap.funLeft ℂ ℂ Fin.castSucc`. -/
private theorem funLeft_castSucc_apply (v : Fin (n + 2) → ℂ) :
    LinearMap.funLeft ℂ ℂ Fin.castSucc v = Fin.init v :=
  (rfl)

variable (n) in
/-- The complement in `ℙ ℂ (Fin (n + 2) → ℂ)` of the point `[0 : ⋯ : 0 : 1]`, the line of the last
basis vector, as an open set: the domain of the projection `[v] ↦ [Fin.init v]`. -/
noncomputable def projectiveBlowupOpens : TopologicalSpace.Opens (ℙ ℂ (Fin (n + 2) → ℂ)) :=
  ⟨linearProjectionDomain (LinearMap.funLeft ℂ ℂ Fin.castSucc),
    isOpen_linearProjectionDomain (LinearMap.continuous_on_pi _)⟩

theorem projectiveBlowupOpens_def :
    (projectiveBlowupOpens n : Set (ℙ ℂ (Fin (n + 2) → ℂ))) =
      linearProjectionDomain (LinearMap.funLeft ℂ ℂ Fin.castSucc) :=
  (rfl)

/-- The line of a nonzero vector `v` lies off `[0 : ⋯ : 0 : 1]` exactly when the first `n + 1`
coordinates `Fin.init v` of `v` are not all zero. -/
@[simp]
theorem mk_mem_projectiveBlowupOpens {v : Fin (n + 2) → ℂ} (hv : v ≠ 0) :
    mk ℂ v hv ∈ projectiveBlowupOpens n ↔ Fin.init v ≠ 0 := by
  rw [← SetLike.mem_coe, projectiveBlowupOpens_def, mk_mem_linearProjectionDomain_iff,
    funLeft_castSucc_apply]

/-- `projectiveBlowupOpens n` is the complement of the point `[0 : ⋯ : 0 : 1]`. -/
theorem coe_projectiveBlowupOpens :
    (projectiveBlowupOpens n : Set (ℙ ℂ (Fin (n + 2) → ℂ))) =
      {mk ℂ (Pi.single (Fin.last (n + 1)) 1) (by simp)}ᶜ := by
  ext x
  induction x using Projectivization.ind with
  | h v hv =>
    rw [SetLike.mem_coe, mk_mem_projectiveBlowupOpens, mem_compl_singleton_iff, Ne, Ne,
      not_iff_not, mk_eq_mk_iff']
    constructor
    · intro h
      refine ⟨v (Fin.last _), funext fun j => ?_⟩
      induction j using Fin.lastCases with
      | last => simp
      | cast j => simpa [Fin.castSucc_ne_last, Fin.init] using (congrFun h j).symm
    · rintro ⟨a, rfl⟩
      funext j
      simp [Fin.init, Fin.castSucc_ne_last]

/-! ### Homogeneous coordinates -/

/-- The squared Hermitian norm of a scalar multiple. -/
private theorem sum_norm_smul_sq (a : ℂ) (z : Fin (n + 1) → ℂ) :
    ∑ i, ‖(a • z) i‖ ^ 2 = ‖a‖ ^ 2 * ∑ i, ‖z i‖ ^ 2 := by
  simp [mul_pow, Finset.mul_sum]

private theorem sum_norm_sq_ne_zero {z : Fin (n + 1) → ℂ} (hz : z ≠ 0) :
    ∑ i, ‖z i‖ ^ 2 ≠ 0 := by
  rw [Ne, Finset.sum_eq_zero_iff_of_nonneg fun i _ => by positivity]
  exact fun h => hz (funext fun i => by simpa using h i (Finset.mem_univ i))

/-- The blowdown coordinate `w̄ z / |z|²` of the point `[z : w]`, for `z = Fin.init v` and
`w = v (Fin.last _)`. -/
private noncomputable def blowdownCoord (v : Fin (n + 2) → ℂ) : Fin (n + 1) → ℂ :=
  (∑ i, ‖Fin.init v i‖ ^ 2)⁻¹ • conj (v (Fin.last _)) • Fin.init v

private theorem blowdownCoord_eq (v : Fin (n + 2) → ℂ) :
    blowdownCoord v =
      (((∑ i, ‖Fin.init v i‖ ^ 2 : ℝ) : ℂ)⁻¹ * conj (v (Fin.last _))) • Fin.init v := by
  rw [blowdownCoord, ← Complex.coe_smul, smul_smul, Complex.ofReal_inv]

private theorem blowdownCoord_smul {a : ℂ} (ha : a ≠ 0) {v : Fin (n + 2) → ℂ}
    (hz : Fin.init v ≠ 0) : blowdownCoord (a • v) = blowdownCoord v := by
  have hS : ((∑ i, ‖Fin.init v i‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sum_norm_sq_ne_zero hz
  have ha' : conj a ≠ 0 := (map_ne_zero _).2 ha
  rw [blowdownCoord_eq, blowdownCoord_eq, ← funLeft_castSucc_apply (a • v), map_smul,
    funLeft_castSucc_apply, sum_norm_smul_sq, Pi.smul_apply,
    smul_eq_mul, map_mul, smul_smul, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.conj_mul' a]
  congr 1
  field_simp

private theorem mem_blowupModel_blowdownCoord {v : Fin (n + 2) → ℂ} (hz : Fin.init v ≠ 0) :
    (mk ℂ (Fin.init v) hz, blowdownCoord v) ∈ blowupModel n := by
  rw [mem_blowupModel_iff, submodule_mk, blowdownCoord_eq]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- The point `[z : c]` lies off `[0 : ⋯ : 0 : 1]` when `z ≠ 0`. -/
theorem mk_snoc_mem_projectiveBlowupOpens {z : Fin (n + 1) → ℂ} (hz : z ≠ 0) (c : ℂ) :
    mk ℂ (Fin.snoc z c : Fin (n + 2) → ℂ) (Fin.snoc_ne_zero_iff.2 (Or.inl hz)) ∈
      projectiveBlowupOpens n := by
  rw [mk_mem_projectiveBlowupOpens, Fin.init_snoc]
  exact hz

private theorem init_rep_ne_zero (x : projectiveBlowupOpens n) : Fin.init x.val.rep ≠ 0 := by
  rw [← funLeft_castSucc_apply, ← mem_linearProjectionDomain_iff, ← projectiveBlowupOpens_def]
  exact x.property

/-! ### The map and its inverse -/

/-- The map `[z : w] ↦ ([z], w̄ z / |z|²)`, computed on the representative `rep`. -/
private noncomputable def toFun (x : projectiveBlowupOpens n) : BlowupModel n :=
  ⟨(mk ℂ (Fin.init x.val.rep) (init_rep_ne_zero x), blowdownCoord x.val.rep),
    mem_blowupModel_blowdownCoord _⟩

private theorem toFun_val (x : projectiveBlowupOpens n) :
    (toFun x : ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) =
      (mk ℂ (Fin.init x.val.rep) (init_rep_ne_zero x), blowdownCoord x.val.rep) :=
  (rfl)

private theorem toFun_eq {x : projectiveBlowupOpens n} {v : Fin (n + 2) → ℂ} (hv : v ≠ 0)
    (hx : x.val = mk ℂ v hv) (hz : Fin.init v ≠ 0) :
    (toFun x : ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) =
      (mk ℂ (Fin.init v) hz, blowdownCoord v) := by
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a • v = x.val.rep :=
    (mk_eq_mk_iff' ℂ _ _ x.val.rep_ne_zero hv).1 (by rw [mk_rep]; exact hx)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact x.val.rep_ne_zero (by rw [← ha, zero_smul])
  rw [toFun_val, Prod.mk.injEq]
  refine ⟨(mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨a, by
    rw [← ha, ← funLeft_castSucc_apply (a • v), map_smul, funLeft_castSucc_apply]⟩, ?_⟩
  rw [← ha, blowdownCoord_smul ha0 hz]

/-- The coefficient of the blowdown of `p` along the representative of its line. -/
private theorem exists_smul_rep (p : BlowupModel n) : ∃ t : ℂ, t • p.pr.rep = p.blowdown :=
  Submodule.mem_span_singleton.1 (by rw [← submodule_eq]; exact p.blowdown_mem_submodule)

/-- The inverse `(ℓ, t • z) ↦ [z : t̄ |z|²]`, computed on the representative `rep` of `ℓ`. -/
private noncomputable def invFun (p : BlowupModel n) : projectiveBlowupOpens n :=
  ⟨mk ℂ (Fin.snoc p.pr.rep (conj (exists_smul_rep p).choose *
      ((∑ i, ‖p.pr.rep i‖ ^ 2 : ℝ) : ℂ)) : Fin (n + 2) → ℂ)
      (Fin.snoc_ne_zero_iff.2 (Or.inl p.pr.rep_ne_zero)),
    mk_snoc_mem_projectiveBlowupOpens p.pr.rep_ne_zero _⟩

private theorem invFun_val (p : BlowupModel n) :
    (invFun p : ℙ ℂ (Fin (n + 2) → ℂ)) = mk ℂ (Fin.snoc p.pr.rep (conj (exists_smul_rep p).choose *
      ((∑ i, ‖p.pr.rep i‖ ^ 2 : ℝ) : ℂ)) : Fin (n + 2) → ℂ)
      (Fin.snoc_ne_zero_iff.2 (Or.inl p.pr.rep_ne_zero)) :=
  (rfl)

private theorem invFun_eq {p : BlowupModel n} {z : Fin (n + 1) → ℂ} (hz : z ≠ 0)
    (hpr : p.pr = mk ℂ z hz) {c : ℂ} (hbl : p.blowdown = c • z) :
    (invFun p : ℙ ℂ (Fin (n + 2) → ℂ)) =
      mk ℂ (Fin.snoc z (conj c * ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ)) : Fin (n + 2) → ℂ)
        (Fin.snoc_ne_zero_iff.2 (Or.inl hz)) := by
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a • z = p.pr.rep :=
    (mk_eq_mk_iff' ℂ _ _ p.pr.rep_ne_zero hz).1 (by rw [mk_rep]; exact hpr)
  set t := (exists_smul_rep p).choose
  have ht : t • p.pr.rep = p.blowdown := (exists_smul_rep p).choose_spec
  have hc : t * a = c := by
    have h : (t * a) • z = c • z := by rw [mul_smul, ha, ht, hbl]
    exact smul_left_injective ℂ hz h
  have hS : ∑ i, ‖p.pr.rep i‖ ^ 2 = ‖a‖ ^ 2 * ∑ i, ‖z i‖ ^ 2 := by
    rw [← ha, sum_norm_smul_sq]
  refine (mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨a, funext fun j => ?_⟩
  induction j using Fin.lastCases with
  | last =>
    simp only [Pi.smul_apply, Fin.snoc_last, smul_eq_mul, hS, ← hc, map_mul]
    push_cast
    rw [← Complex.conj_mul' a]
    ring
  | cast j => simp [← ha]

private theorem invFun_toFun (x : projectiveBlowupOpens n) : invFun (toFun x) = x := by
  have hz := init_rep_ne_zero x
  have hS : ((∑ i, ‖Fin.init x.val.rep i‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sum_norm_sq_ne_zero hz
  refine Subtype.ext ?_
  rw [invFun_eq hz (by rw [BlowupModel.pr_def, toFun_val])
    (by rw [BlowupModel.blowdown_def, toFun_val, blowdownCoord_eq])]
  conv_rhs => rw [← mk_rep x.val]
  congr 1
  conv_rhs => rw [← Fin.snoc_init_self x.val.rep]
  congr 1
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
  field_simp

private theorem toFun_invFun (p : BlowupModel n) : toFun (invFun p) = p := by
  have hz := p.pr.rep_ne_zero
  have hS : ((∑ i, ‖p.pr.rep i‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sum_norm_sq_ne_zero hz
  have h := toFun_eq (x := invFun p) _ (invFun_val p)
    (by rw [Fin.init_snoc]; exact hz)
  refine BlowupModel.ext ?_ ?_
  · rw [BlowupModel.pr_def, h]
    simp only [Fin.init_snoc, mk_rep]
  · rw [BlowupModel.blowdown_def, h, blowdownCoord_eq]
    simp only [Fin.init_snoc, Fin.snoc_last, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    refine Eq.trans ?_ (exists_smul_rep p).choose_spec
    congr 1
    field_simp

/-! ### Smoothness -/

private theorem contDiffAt_blowdownCoord {v : Fin (n + 2) → ℂ} (hz : Fin.init v ≠ 0) :
    ContDiffAt ℝ ∞ blowdownCoord v := by
  have hinit : ContDiff ℝ ∞ fun v : Fin (n + 2) → ℂ => Fin.init v :=
    (LinearMap.funLeft ℝ ℂ Fin.castSucc).toContinuousLinearMap.contDiff
  have hS : ContDiff ℝ ∞ fun v : Fin (n + 2) → ℂ => ∑ i, ‖Fin.init v i‖ ^ 2 :=
    ContDiff.sum fun i _ =>
      (contDiff_norm_sq ℝ).comp ((contDiff_apply ℝ (fun _ => ℂ) i).comp hinit)
  have hw : ContDiff ℝ ∞ fun v : Fin (n + 2) → ℂ => conj (v (Fin.last _)) :=
    Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) _)
  exact (hS.contDiffAt.inv (sum_norm_sq_ne_zero hz)).smul (hw.contDiffAt.smul hinit.contDiffAt)

/-- The first component of the map is the projection `[v] ↦ [Fin.init v]`. -/
private theorem pr_toFun (x : projectiveBlowupOpens n) :
    (toFun x).pr = linearProjection (LinearMap.funLeft ℂ ℂ Fin.castSucc) x.val := by
  conv_rhs => rw [← mk_rep x.val]
  rw [BlowupModel.pr_def, toFun_val,
    linearProjection_mk _ _ (by rw [funLeft_castSucc_apply]; exact init_rep_ne_zero x)]
  simp only [funLeft_castSucc_apply]

private theorem contMDiff_toFun :
    ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (toFun (n := n)) := by
  intro x
  have hval := contMDiff_subtypeVal (I := 𝓘(ℂ, Fin (n + 1) → ℂ)) (n := ∞)
    (U := projectiveBlowupOpens n)
  refine BlowupModel.contMDiffAt_real_iff_contMDiffAt_pr_comp_and_blowdown_comp.2 ⟨?_, ?_⟩
  · have hpr := ((contMDiffOn_linearProjection (LinearMap.funLeft ℂ ℂ Fin.castSucc) ∞).contMDiffAt
      (((projectiveBlowupOpens n).isOpen).mem_nhds x.property)).comp x hval.contMDiffAt
    simpa only [comp_def, pr_toFun] using hpr.restrictScalars' ℝ
  · obtain ⟨F, hF, hFx⟩ := exists_contMDiffAt_eventually_eq_mk (r := ∞) hval.contMDiffAt (x := x)
    have hev : ∀ᶠ y in 𝓝 x, ∃ (_ : F y ≠ 0) (hz : Fin.init (F y) ≠ 0),
        (toFun y : ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) =
          (mk ℂ (Fin.init (F y)) hz, blowdownCoord (F y)) := by
      filter_upwards [hFx] with y ⟨hy, hyF⟩
      have hz : Fin.init (F y) ≠ 0 := (mk_mem_projectiveBlowupOpens hy).1 (hyF ▸ y.property)
      exact ⟨hy, hz, toFun_eq hy hyF hz⟩
    obtain ⟨-, hzx, -⟩ := hev.self_of_nhds
    refine ((contDiffAt_blowdownCoord hzx).comp_contMDiffAt (hF.restrictScalars' ℝ))
      |>.congr_of_eventuallyEq ?_
    filter_upwards [hev] with y ⟨_, _, hy⟩
    exact (BlowupModel.blowdown_def _).trans (congrArg Prod.snd hy)

/-- The inverse read in the chart `i` of the blowup, in homogeneous coordinates. -/
private noncomputable def invCoord (i : Fin (n + 1)) (w : Fin (n + 1) → ℂ) : Fin (n + 2) → ℂ :=
  Fin.snoc (update w i 1) (conj (w i) * ((∑ j, ‖update w i 1 j‖ ^ 2 : ℝ) : ℂ))

private theorem contDiff_invCoord (i : Fin (n + 1)) : ContDiff ℝ ∞ (invCoord (n := n) i) := by
  have hv : ContDiff ℝ ∞ fun w : Fin (n + 1) → ℂ => update w i 1 :=
    ContDiff.update_self i contDiff_const
  have hS : ContDiff ℝ ∞ fun w : Fin (n + 1) → ℂ => ∑ j, ‖update w i 1 j‖ ^ 2 :=
    ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp ((contDiff_apply ℝ (fun _ => ℂ) j).comp hv)
  have hc : ContDiff ℝ ∞ fun w : Fin (n + 1) → ℂ =>
      conj (w i) * ((∑ j, ‖update w i 1 j‖ ^ 2 : ℝ) : ℂ) :=
    (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) i)).mul
      (Complex.ofRealCLM.contDiff.comp hS)
  refine contDiff_pi.2 fun j => ?_
  induction j using Fin.lastCases with
  | last => simpa [invCoord] using hc
  | cast j => simpa [invCoord, comp_def] using (contDiff_apply ℝ (fun _ => ℂ) j).comp hv

private theorem invFun_blowupModelChart_symm (i : Fin (n + 1)) (w : Fin (n + 1) → ℂ) :
    (invFun ((BlowupModel.blowupModelChart i).symm w) : ℙ ℂ (Fin (n + 2) → ℂ)) =
      mk ℂ (invCoord i w) (Fin.snoc_ne_zero_iff.2 (Or.inl (update_ne_zero w i one_ne_zero))) :=
  invFun_eq _ (BlowupModel.pr_blowupModelChart_symm_apply i w)
    (BlowupModel.blowdown_blowupModelChart_symm_apply i w)

private theorem contMDiff_invFun :
    ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (invFun (n := n)) := by
  refine (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1 fun p => ?_
  obtain ⟨i, hi⟩ := exists_mem_affineOpen p.pr
  have hsrc : p ∈ (BlowupModel.blowupModelChart i).source := by
    rw [BlowupModel.blowupModelChart_source]
    exact hi
  have hopen := (BlowupModel.blowupModelChart (n := n) i).open_source
  -- In the chart `i`, the inverse is `w ↦ [invCoord i w]`.
  have hG := (contMDiff_mkNonzero ℂ (n + 1) ∞).comp
    ((TauCeti.ContMDiff.subtypeVal_comp_iff (TauCeti.puncturedSpace _) (fun w => ⟨invCoord i w,
        TauCeti.mem_puncturedSpace.2
          (Fin.snoc_ne_zero_iff.2 (Or.inl (update_ne_zero w i one_ne_zero)))⟩)).1
      (contDiff_invCoord i).contMDiff)
  have hc := ((BlowupModel.contMDiffOn_blowupModelChart i ∞).restrictScalars' ℝ).contMDiffAt
    (hopen.mem_nhds hsrc)
  refine ((hG.contMDiffAt).comp p hc).congr_of_eventuallyEq ?_
  filter_upwards [hopen.mem_nhds hsrc] with q hq
  rw [comp_apply, comp_apply, comp_apply, mkNonzero_apply, ← invFun_blowupModelChart_symm,
    (BlowupModel.blowupModelChart i).left_inv hq]

/-! ### The diffeomorphism -/

variable (n) in
/-- The diffeomorphism `[z : w] ↦ ([z], w̄ z / |z|²)` from the complement of `[0 : ⋯ : 0 : 1]` in
`ℙ ℂ (Fin (n + 2) → ℂ)` onto the model blowup `BlowupModel n`, for the real smooth structures.
Here `z = Fin.init v` and `w = v (Fin.last _)` for homogeneous coordinates `v`, and
`|z|² = ∑ i, ‖z i‖ ^ 2`.
Its inverse sends `(ℓ, t • z)`, for `z` spanning `ℓ`, to `[z : t̄ |z|²]`. -/
noncomputable def projectiveBlowupModelDiffeomorph :
    projectiveBlowupOpens n ≃ₘ^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), 𝓘(ℝ, Fin (n + 1) → ℂ)⟯ BlowupModel n where
  toFun := toFun
  invFun := invFun
  left_inv := invFun_toFun
  right_inv := toFun_invFun
  contMDiff_toFun := contMDiff_toFun
  contMDiff_invFun := contMDiff_invFun

private theorem coe_projectiveBlowupModelDiffeomorph :
    ⇑(projectiveBlowupModelDiffeomorph n) = toFun :=
  (rfl)

private theorem coe_projectiveBlowupModelDiffeomorph_symm :
    ⇑(projectiveBlowupModelDiffeomorph n).symm = invFun :=
  (rfl)

/-- The point `([z], w̄ z / |z|²)` of the blowup, for `z = Fin.init v ≠ 0` and `w = v (Fin.last _)`,
is the image of `[v]`. -/
theorem projectiveBlowupModelDiffeomorph_apply {v : Fin (n + 2) → ℂ} (hv : v ≠ 0)
    (h : mk ℂ v hv ∈ projectiveBlowupOpens n) :
    (projectiveBlowupModelDiffeomorph n ⟨mk ℂ v hv, h⟩ :
        ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) =
      (mk ℂ (Fin.init v) ((mk_mem_projectiveBlowupOpens hv).1 h),
        (∑ i, ‖Fin.init v i‖ ^ 2)⁻¹ • conj (v (Fin.last _)) • Fin.init v) := by
  rw [coe_projectiveBlowupModelDiffeomorph]
  exact toFun_eq hv rfl _

/-- The inverse sends `(ℓ, t • z)`, for a nonzero `z` spanning `ℓ`, to `[z : t̄ |z|²]`. -/
theorem projectiveBlowupModelDiffeomorph_symm_apply {z : Fin (n + 1) → ℂ} (hz : z ≠ 0) (t : ℂ)
    (h : (mk ℂ z hz, t • z) ∈ blowupModel n) :
    ((projectiveBlowupModelDiffeomorph n).symm ⟨(mk ℂ z hz, t • z), h⟩ :
        ℙ ℂ (Fin (n + 2) → ℂ)) =
      mk ℂ (Fin.snoc z (conj t * ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ)) : Fin (n + 2) → ℂ)
        (Fin.snoc_ne_zero_iff.2 (Or.inl hz)) := by
  rw [coe_projectiveBlowupModelDiffeomorph_symm]
  exact invFun_eq hz (BlowupModel.pr_mk _ _ h) (BlowupModel.blowdown_mk _ _ h)

/-- The point `[u : 1]`, for `u ≠ 0`, goes to `([u], u / |u|²)`. -/
theorem projectiveBlowupModelDiffeomorph_apply_snoc_one {u : Fin (n + 1) → ℂ} (hu : u ≠ 0) :
    (projectiveBlowupModelDiffeomorph n ⟨mk ℂ (Fin.snoc u 1 : Fin (n + 2) → ℂ)
        (Fin.snoc_ne_zero_iff.2 (Or.inl hu)), mk_snoc_mem_projectiveBlowupOpens hu 1⟩ :
        ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) =
      (mk ℂ u hu, (∑ i, ‖u i‖ ^ 2)⁻¹ • u) := by
  rw [projectiveBlowupModelDiffeomorph_apply]
  simp only [Fin.init_snoc, Fin.snoc_last, map_one, one_smul]

/-- Read on `EuclideanSpace ℂ (Fin (n + 1))`, the blowdown of the image of `[u : 1]` is the
inversion of `u ≠ 0` in the unit sphere. -/
theorem blowdown_projectiveBlowupModelDiffeomorph_snoc_one {u : EuclideanSpace ℂ (Fin (n + 1))}
    (hu : u ≠ 0) :
    (projectiveBlowupModelDiffeomorph n ⟨mk ℂ (Fin.snoc u.ofLp 1 : Fin (n + 2) → ℂ)
        (Fin.snoc_ne_zero_iff.2 (Or.inl (by rwa [Ne, WithLp.ofLp_eq_zero]))),
        mk_snoc_mem_projectiveBlowupOpens (by rwa [Ne, WithLp.ofLp_eq_zero]) 1⟩).blowdown =
      (EuclideanGeometry.inversion 0 1 u).ofLp := by
  rw [BlowupModel.blowdown_def,
    projectiveBlowupModelDiffeomorph_apply_snoc_one (by rwa [Ne, WithLp.ofLp_eq_zero])]
  simp only [EuclideanGeometry.inversion, dist_zero_right, vsub_eq_sub, sub_zero, vadd_eq_add,
    add_zero, one_div, inv_pow, EuclideanSpace.norm_sq_eq, WithLp.ofLp_smul]

/-- A point of the projective space other than the centre of the ball
`EuclideanComplexProjectiveSpace.connectedSumBall n` lies off `[0 : ⋯ : 0 : 1]`. -/
theorem EuclideanComplexProjectiveSpace.symm_coe_mem_projectiveBlowupOpens
    (y : ConnectedSum.puncture (EuclideanComplexProjectiveSpace.connectedSumBall n)) :
    (remodelHomeomorph _ _).symm y.val ∈ projectiveBlowupOpens n := by
  rw [← SetLike.mem_coe, coe_projectiveBlowupOpens, mem_compl_singleton_iff, Ne,
    Homeomorph.symm_apply_eq, ← EuclideanComplexProjectiveSpace.connectedSumBall_zero]
  exact ConnectedSum.mem_puncture.1 y.property

end ProjectiveBlowupModel

/-! ## The radial rescaling of the model blowup -/

namespace BlowupModel

section RadialRescale

variable (ε : ℝ)

/-- Mathlib's map `univBall 0 ε` of the Hermitian space, read on `Fin (n + 1) → ℂ`. -/
private def rescaleCoord (z : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  EuclideanSpace.equiv (Fin (n + 1)) ℂ
    (univBall 0 ε ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm z))

/-- The inverse of `univBall 0 ε`, read on `Fin (n + 1) → ℂ`. -/
private def rescaleCoordInv (z : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  EuclideanSpace.equiv (Fin (n + 1)) ℂ
    ((univBall 0 ε).symm ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm z))

private theorem mem_blowupModel_rescaleCoord (p : BlowupModel n) :
    (p.pr, rescaleCoord ε p.blowdown) ∈ blowupModel n := by
  obtain ⟨a, ha⟩ := exists_univBall_zero_apply_eq_smul ε
    ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm p.blowdown)
  rw [mem_blowupModel_iff, rescaleCoord, ha, LinearMapClass.map_smul_of_tower,
    ContinuousLinearEquiv.apply_symm_apply]
  exact Submodule.smul_of_tower_mem _ a p.blowdown_mem_submodule

private theorem mem_blowupModel_rescaleCoordInv (p : BlowupModel n) :
    (p.pr, rescaleCoordInv ε p.blowdown) ∈ blowupModel n := by
  obtain ⟨a, ha⟩ := exists_univBall_zero_symm_apply_eq_smul ε
    ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm p.blowdown)
  rw [mem_blowupModel_iff, rescaleCoordInv, ha, LinearMapClass.map_smul_of_tower,
    ContinuousLinearEquiv.apply_symm_apply]
  exact Submodule.smul_of_tower_mem _ a p.blowdown_mem_submodule

/-- The radial rescaling `(ℓ, z) ↦ (ℓ, ε z / √(1 + |z|²))` of the model blowup, for `ε > 0`, where
`|z|` is the Hermitian norm: it keeps the line, and on blowdowns it is Mathlib's map
`univBall 0 ε` of the Hermitian space `EuclideanSpace ℂ (Fin (n + 1))` onto the ball of radius
`ε`, read on `Fin (n + 1) → ℂ`. For `ε ≤ 0` it is the identity, as `univBall 0 ε` is. -/
def radialRescale (p : BlowupModel n) : BlowupModel n :=
  ⟨(p.pr, rescaleCoord ε p.blowdown), mem_blowupModel_rescaleCoord ε p⟩

/-- The inverse of `radialRescale ε` on its range. -/
private def radialRescaleInv (p : BlowupModel n) : BlowupModel n :=
  ⟨(p.pr, rescaleCoordInv ε p.blowdown), mem_blowupModel_rescaleCoordInv ε p⟩

@[simp]
theorem pr_radialRescale (p : BlowupModel n) : (radialRescale ε p).pr = p.pr :=
  pr_mk _ _ _

@[simp]
theorem blowdown_radialRescale (p : BlowupModel n) :
    (radialRescale ε p).blowdown =
      EuclideanSpace.equiv (Fin (n + 1)) ℂ
        (univBall 0 ε ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm p.blowdown)) :=
  blowdown_mk _ _ _

private theorem radialRescaleInv_radialRescale (p : BlowupModel n) :
    radialRescaleInv ε (radialRescale ε p) = p := by
  refine ext (by rw [radialRescaleInv, pr_mk, pr_radialRescale]) ?_
  rw [radialRescaleInv, blowdown_mk, rescaleCoordInv, blowdown_radialRescale,
    ContinuousLinearEquiv.symm_apply_apply, (univBall 0 ε).left_inv (by simp),
    ContinuousLinearEquiv.apply_symm_apply]

variable {ε}

private theorem radialRescale_radialRescaleInv (hε : 0 < ε) {p : BlowupModel n}
    (hp : p ∈ openNbhd n ε) :
    radialRescale ε (radialRescaleInv ε p) = p := by
  refine ext (by rw [pr_radialRescale, radialRescaleInv, pr_mk]) ?_
  rw [blowdown_radialRescale, radialRescaleInv, blowdown_mk, rescaleCoordInv,
    ContinuousLinearEquiv.symm_apply_apply,
    (univBall 0 ε).right_inv
      (by rw [univBall_target 0 hε]; exact mem_openNbhd_iff_mem_ball.1 hp),
    ContinuousLinearEquiv.apply_symm_apply]

/-- For `ε > 0`, the blowdown of the rescaled point is `ε z / √(1 + |z|²)`, for the blowdown `z`
of the point and its Hermitian norm `|z|`. -/
theorem blowdown_radialRescale_of_pos (hε : 0 < ε) (p : BlowupModel n) :
    (radialRescale ε p).blowdown =
      (ε / √(1 + ‖(EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm p.blowdown‖ ^ 2)) • p.blowdown := by
  rw [blowdown_radialRescale, univBall_apply hε, vadd_eq_add, add_zero,
    LinearMapClass.map_smul_of_tower,
    ContinuousLinearEquiv.apply_symm_apply]

/-- For `ε > 0`, a rescaled point lies in `openNbhd n ε`: its blowdown has Euclidean norm less
than `ε`. -/
theorem radialRescale_mem_openNbhd (hε : 0 < ε) (p : BlowupModel n) :
    radialRescale ε p ∈ openNbhd n ε := by
  rw [mem_openNbhd_iff_mem_ball, blowdown_radialRescale,
    ContinuousLinearEquiv.symm_apply_apply, ← univBall_target 0 hε]
  exact (univBall 0 ε).map_source (by simp)

variable (ε) in
/-- The radial rescaling is injective. -/
theorem radialRescale_injective : Function.Injective (radialRescale (n := n) ε) :=
  Function.LeftInverse.injective (radialRescaleInv_radialRescale ε)

/-- For `ε > 0`, the radial rescaling maps the model blowup onto `openNbhd n ε`, the points whose
blowdown has Euclidean norm less than `ε`. -/
theorem range_radialRescale (hε : 0 < ε) :
    Set.range (radialRescale (n := n) ε) = openNbhd n ε :=
  Set.Subset.antisymm (Set.range_subset_iff.2 (radialRescale_mem_openNbhd hε))
    fun _ hp => ⟨_, radialRescale_radialRescaleInv hε hp⟩

/-- For a chart `c : BlowupChart M p₀`, the radial rescaling with `ε = c.ballRadius` lands in
`Blowup.modelOpens c`, the points whose blowdown lies in the target of `c`. -/
theorem radialRescale_ballRadius_mem_modelOpens (c : BlowupChart (n := n) M p₀)
    (p : BlowupModel n) : radialRescale c.ballRadius p ∈ Blowup.modelOpens c := by
  have hp := mem_openNbhd_iff_mem_ball.1 (radialRescale_mem_openNbhd c.ballRadius_pos p)
  have h := c.closedBall_ballRadius_subset (ball_subset_closedBall hp)
  rw [BlowupChart.euclideanChart_def, remodelChart_target] at h
  exact (Blowup.mem_modelOpens c).2 h

variable (ε) in
/-- The radial rescaling is smooth for the real structure of the model blowup. -/
theorem contMDiff_radialRescale :
    ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (radialRescale (n := n) ε) := by
  intro p
  refine contMDiffAt_real_iff_contMDiffAt_pr_comp_and_blowdown_comp.2
    ⟨by simpa only [pr_radialRescale] using ((contMDiff_pr ∞).restrictScalars' ℝ).contMDiffAt, ?_⟩
  have hc : ContDiff ℝ ∞ fun z : Fin (n + 1) → ℂ => EuclideanSpace.equiv (Fin (n + 1)) ℂ
      (univBall 0 ε ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm z)) :=
    ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).contDiff.restrict_scalars ℝ).comp
      ((contDiff_univBall (n := ⊤)).comp
        ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm.contDiff.restrict_scalars ℝ))
  exact (hc.contMDiff.contMDiffAt.comp p
    ((contMDiff_blowdown ∞).restrictScalars' ℝ).contMDiffAt).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => blowdown_radialRescale ε y)

/-- The inverse of the radial rescaling is smooth on `openNbhd n ε`. -/
private theorem contMDiffOn_radialRescaleInv :
    ContMDiffOn 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (radialRescaleInv (n := n) ε)
      (openNbhd n ε) := by
  have hc : ContDiffOn ℝ ∞ (fun z : Fin (n + 1) → ℂ => EuclideanSpace.equiv (Fin (n + 1)) ℂ
      ((univBall 0 ε).symm ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm z)))
      ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm ⁻¹' ball 0 ε) :=
    ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).contDiff.restrict_scalars ℝ).comp_contDiffOn
      ((contDiffOn_univBall_symm (n := ⊤)).comp
        ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm.contDiff.restrict_scalars ℝ).contDiffOn
        fun _ hz => hz)
  have hopen : IsOpen ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm ⁻¹' ball 0 ε) :=
    isOpen_ball.preimage (EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm.continuous
  intro p hp
  rw [mem_openNbhd_iff_mem_ball] at hp
  refine (contMDiffAt_real_iff_contMDiffAt_pr_comp_and_blowdown_comp.2 ⟨?_, ?_⟩).contMDiffWithinAt
  · simpa only [radialRescaleInv, pr_mk] using ((contMDiff_pr ∞).restrictScalars' ℝ).contMDiffAt
  · exact (((hc.contDiffAt (hopen.mem_nhds hp)).contMDiffAt).comp p
      ((contMDiff_blowdown ∞).restrictScalars' ℝ).contMDiffAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => blowdown_mk _ _ _)

/-- For `ε > 0`, the radial rescaling as a partial diffeomorphism of the model blowup, from all of
it onto `openNbhd n ε`. -/
private def radialRescalePartialDiffeomorph (hε : 0 < ε) :
    PartialDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n)
      (BlowupModel n) ∞ where
  toFun := radialRescale ε
  invFun := radialRescaleInv ε
  source := univ
  target := openNbhd n ε
  map_source' p _ := radialRescale_mem_openNbhd hε p
  map_target' _ _ := mem_univ _
  left_inv' p _ := radialRescaleInv_radialRescale ε p
  right_inv' _ hp := radialRescale_radialRescaleInv hε hp
  open_source := isOpen_univ
  open_target := isOpen_openNbhd ε
  contMDiffOn_toFun := (contMDiff_radialRescale ε).contMDiffOn
  contMDiffOn_invFun := contMDiffOn_radialRescaleInv

/-- For `ε > 0`, the radial rescaling is a smooth local diffeomorphism of the model blowup, for its
real structure. -/
theorem isLocalDiffeomorph_radialRescale (hε : 0 < ε) :
    IsLocalDiffeomorph 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (radialRescale (n := n) ε) :=
  fun p => (radialRescalePartialDiffeomorph hε).isLocalDiffeomorphAt _ _ _ (mem_univ p)

end RadialRescale

end BlowupModel

/-! ## The punctured summands as open pieces of the blowup -/

namespace Blowup

open GluedAlong (inl inr)
open ConnectedSum (puncture mem_puncture)
open EuclideanGeometry (inversion)
open scoped LinearAlgebra.Projectivization

variable (c : BlowupChart (n := n) M p₀)

/-- The punctured projective space, the second summand of the connected sum, as an open piece of
the blowup, both re-modelled on the Hermitian space: a point `y ≠ [0 : ⋯ : 0 : 1]` goes to the
point `GluedAlong.inr` of the blowup at `S (projectiveBlowupModelDiffeomorph n y)`, where `S` is
the radial rescaling `BlowupModel.radialRescale c.ballRadius` of the model blowup. -/
def connectedSumInr (y : puncture (EuclideanComplexProjectiveSpace.connectedSumBall n)) :
    Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm (Blowup c) :=
  remodelHomeomorph _ _ (inr (gluingHomeomorph c)
    ⟨BlowupModel.radialRescale c.ballRadius (projectiveBlowupModelDiffeomorph n
      ⟨_, EuclideanComplexProjectiveSpace.symm_coe_mem_projectiveBlowupOpens y⟩),
      BlowupModel.radialRescale_ballRadius_mem_modelOpens c _⟩)

theorem connectedSumInr_apply (y : puncture (EuclideanComplexProjectiveSpace.connectedSumBall n)) :
    connectedSumInr c y =
      remodelHomeomorph _ _ (inr (gluingHomeomorph c)
        ⟨BlowupModel.radialRescale c.ballRadius (projectiveBlowupModelDiffeomorph n
          ⟨_, EuclideanComplexProjectiveSpace.symm_coe_mem_projectiveBlowupOpens y⟩),
          BlowupModel.radialRescale_ballRadius_mem_modelOpens c _⟩) :=
  (rfl)

/-- The punctured projective space is mapped injectively into the blowup. -/
theorem connectedSumInr_injective : Function.Injective (connectedSumInr c) := by
  intro y y' h
  have h' := (projectiveBlowupModelDiffeomorph n).injective <|
    BlowupModel.radialRescale_injective _ <| congrArg Subtype.val <|
      GluedAlong.inr_injective _ <| (remodelHomeomorph _ _).injective h
  exact Subtype.ext ((remodelHomeomorph _ _).symm.injective (congrArg Subtype.val h' :))

/-- The first step of `connectedSumInr c`: a point of the punctured projective space, re-modelled
on `Fin (n + 1) → ℂ`, as a point of the complement `projectiveBlowupOpens n` of `[0 : 1]`. -/
def connectedSumInrOpens (y : puncture (EuclideanComplexProjectiveSpace.connectedSumBall n)) :
    projectiveBlowupOpens n :=
  ⟨_, EuclideanComplexProjectiveSpace.symm_coe_mem_projectiveBlowupOpens y⟩

@[simp]
theorem coe_connectedSumInrOpens
    (y : puncture (EuclideanComplexProjectiveSpace.connectedSumBall n)) :
    (connectedSumInrOpens y : ℙ ℂ (Fin (n + 2) → ℂ)) = (remodelHomeomorph _ _).symm y.val :=
  (rfl)

/-- The punctured projective space mapped into the open set `modelOpens c` of the model blowup:
`connectedSumInrOpens`, then `projectiveBlowupModelDiffeomorph n`, then the radial rescaling. -/
def connectedSumInrModel (y : puncture (EuclideanComplexProjectiveSpace.connectedSumBall n)) :
    modelOpens c :=
  ⟨BlowupModel.radialRescale c.ballRadius (projectiveBlowupModelDiffeomorph n
    (connectedSumInrOpens y)), BlowupModel.radialRescale_ballRadius_mem_modelOpens c _⟩

@[simp]
theorem coe_connectedSumInrModel
    (y : puncture (EuclideanComplexProjectiveSpace.connectedSumBall n)) :
    (connectedSumInrModel c y : BlowupModel n) = BlowupModel.radialRescale c.ballRadius
      (projectiveBlowupModelDiffeomorph n (connectedSumInrOpens y)) :=
  (rfl)

theorem val_comp_connectedSumInrModel :
    Subtype.val ∘ connectedSumInrModel c = BlowupModel.radialRescale c.ballRadius ∘
      projectiveBlowupModelDiffeomorph n ∘ connectedSumInrOpens :=
  (rfl)

theorem connectedSumInr_eq_comp :
    connectedSumInr c = remodelHomeomorph _ _ ∘ inr (gluingHomeomorph c) ∘ connectedSumInrModel c :=
  (rfl)

variable [T2Space M]

/-- A point of `M` other than the centre `p₀` of the ball `c.connectedSumBall` lies in the first
piece `M \ {p₀}` of the blowup. -/
theorem symm_coe_mem_puncturedOpens (x : puncture c.connectedSumBall) :
    (remodelHomeomorph _ M).symm x.val ∈ puncturedOpens c := by
  rw [mem_puncturedOpens, Ne, Homeomorph.symm_apply_eq, ← c.connectedSumBall_zero]
  exact mem_puncture.1 x.property

/-- The punctured `M`, the first summand of the connected sum, as an open piece of the blowup,
both re-modelled on the Hermitian space: a point `x ≠ p₀` goes to the point `GluedAlong.inl x` of
the blowup, off the exceptional divisor. -/
def connectedSumInl (x : puncture c.connectedSumBall) :
    Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm (Blowup c) :=
  remodelHomeomorph _ _ (inl (gluingHomeomorph c) ⟨_, symm_coe_mem_puncturedOpens c x⟩)

theorem connectedSumInl_apply (x : puncture c.connectedSumBall) :
    connectedSumInl c x =
      remodelHomeomorph _ _ (inl (gluingHomeomorph c) ⟨_, symm_coe_mem_puncturedOpens c x⟩) :=
  (rfl)

/-- The punctured `M` is mapped injectively into the blowup. -/
theorem connectedSumInl_injective : Function.Injective (connectedSumInl c) := by
  intro x x' h
  rw [connectedSumInl_apply, connectedSumInl_apply, (remodelHomeomorph _ _).injective.eq_iff,
    GluedAlong.inl_inj, Subtype.mk.injEq, (remodelHomeomorph _ M).symm.injective.eq_iff] at h
  exact Subtype.ext h

/-- The first step of `connectedSumInl c`: a point `x ≠ p₀` of `M`, re-modelled on the Hermitian
space, as a point of the open set `puncturedOpens c` of `M`. -/
def connectedSumInlOpens (x : puncture c.connectedSumBall) : puncturedOpens c :=
  ⟨_, symm_coe_mem_puncturedOpens c x⟩

@[simp]
theorem coe_connectedSumInlOpens (x : puncture c.connectedSumBall) :
    (connectedSumInlOpens c x : M) = (remodelHomeomorph _ M).symm x.val :=
  (rfl)

theorem connectedSumInl_eq_comp :
    connectedSumInl c = remodelHomeomorph _ _ ∘ inl (gluingHomeomorph c) ∘ connectedSumInlOpens c :=
  (rfl)

section LocalDiffeomorph

open scoped TauCeti.ComplexManifold

/-- The map `connectedSumInlOpens c` is a local biholomorphism. -/
theorem isLocalDiffeomorph_connectedSumInlOpens :
    IsLocalDiffeomorph 𝓘(ℂ, EuclideanSpace ℂ (Fin (n + 1))) 𝓘(ℂ, Fin (n + 1) → ℂ) ∞
      (connectedSumInlOpens c) := by
  let R := remodelDiffeomorph (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M (n := ∞)
  have hmaps : MapsTo R.symm (puncture c.connectedSumBall) (puncturedOpens c) :=
    fun x hx ↦ by simpa [R] using symm_coe_mem_puncturedOpens c ⟨x, hx⟩
  have hF : connectedSumInlOpens c = hmaps.restrict _ _ _ :=
    funext fun x ↦ Subtype.ext (by simp [R])
  exact hF ▸ (R.symm.isLocalDiffeomorph.isLocalDiffeomorphOn _).mapsToRestrict hmaps

omit [T2Space M] in
/-- The map `connectedSumInrOpens` is a local biholomorphism. -/
theorem isLocalDiffeomorph_connectedSumInrOpens :
    IsLocalDiffeomorph 𝓘(ℂ, EuclideanSpace ℂ (Fin (n + 1))) 𝓘(ℂ, Fin (n + 1) → ℂ) ∞
      (connectedSumInrOpens (n := n)) := by
  let R := remodelDiffeomorph (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm
    (ℙ ℂ (Fin (n + 2) → ℂ)) (n := ∞)
  have hmaps : MapsTo R.symm (puncture (EuclideanComplexProjectiveSpace.connectedSumBall n))
      (projectiveBlowupOpens n) := fun y hy ↦ by
    simpa [R] using EuclideanComplexProjectiveSpace.symm_coe_mem_projectiveBlowupOpens ⟨y, hy⟩
  have hF : connectedSumInrOpens = hmaps.restrict _ _ _ :=
    funext fun y ↦ Subtype.ext (by simp [R])
  exact hF ▸ (R.symm.isLocalDiffeomorph.isLocalDiffeomorphOn _).mapsToRestrict hmaps

omit [T2Space M] in
/-- The map `connectedSumInrModel c` is a smooth local diffeomorphism of the underlying real
manifolds. -/
theorem isLocalDiffeomorph_connectedSumInrModel :
    IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞
      (connectedSumInrModel c) :=
  TauCeti.isLocalDiffeomorph_subtypeVal_comp_iff.1 <| val_comp_connectedSumInrModel c ▸ fun y ↦
    (((isLocalDiffeomorph_connectedSumInrOpens y).restrictScalars ℝ).comp
      (hg := (projectiveBlowupModelDiffeomorph n).isLocalDiffeomorph _)).comp
      (hg := BlowupModel.isLocalDiffeomorph_radialRescale c.ballRadius_pos _)

variable [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

/-- For a holomorphic chart `c`, the punctured `M` is mapped into the blowup by a local
biholomorphism. -/
theorem isLocalDiffeomorph_connectedSumInl_complex :
    IsLocalDiffeomorph 𝓘(ℂ, EuclideanSpace ℂ (Fin (n + 1))) 𝓘(ℂ, EuclideanSpace ℂ (Fin (n + 1)))
      ∞ (connectedSumInl c) := by
  rw [connectedSumInl_eq_comp, ← coe_remodelDiffeomorph (n := ∞)]
  exact fun x ↦ ((isLocalDiffeomorph_connectedSumInlOpens c x).comp
    (hg := (isLocalDiffeomorph_inl c _).of_le le_top)).comp
    (hg := (remodelDiffeomorph _ _).isLocalDiffeomorph _)

/-- For a holomorphic chart `c`, the punctured `M` is mapped into the blowup by a smooth local
diffeomorphism of the underlying real manifolds. -/
theorem isLocalDiffeomorph_connectedSumInl :
    IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1)))
      ∞ (connectedSumInl c) :=
  fun x ↦ (isLocalDiffeomorph_connectedSumInl_complex c x).restrictScalars ℝ

omit [T2Space M] in
/-- For a holomorphic chart `c`, the punctured projective space is mapped into the blowup by a
smooth local diffeomorphism of the underlying real manifolds. -/
theorem isLocalDiffeomorph_connectedSumInr :
    IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1)))
      ∞ (connectedSumInr c) := by
  rw [connectedSumInr_eq_comp, ← coe_remodelDiffeomorph (n := ∞)]
  exact fun y ↦ ((isLocalDiffeomorph_connectedSumInrModel c y).comp
    (hg := isLocalDiffeomorph_inr_real c _)).comp
    (hg := ((remodelDiffeomorph _ _).isLocalDiffeomorph _).restrictScalars ℝ)

end LocalDiffeomorph

/-- The two pieces agree on glued points: for `v ≠ 0`, the point `c.connectedSumBall v` of the
punctured `M` and the point `EuclideanComplexProjectiveSpace.connectedSumBall n (inversion 0 1 v)`
of the punctured projective space, which the connected sum identifies, go to the same point of the
blowup. -/
theorem connectedSumInl_eq_connectedSumInr (v : EuclideanSpace ℂ (Fin (n + 1)))
    (hx : c.connectedSumBall v ∈ puncture c.connectedSumBall)
    (hy : EuclideanComplexProjectiveSpace.connectedSumBall n (inversion 0 1 v) ∈
      puncture (EuclideanComplexProjectiveSpace.connectedSumBall n)) :
    connectedSumInl c ⟨_, hx⟩ = connectedSumInr c ⟨_, hy⟩ := by
  have hv : v ≠ 0 := TauCeti.ConnectedSum.ne_zero_of_apply_mem_puncture hx
  have hv' : inversion 0 1 v ≠ 0 := by
    simpa [EuclideanGeometry.inversion_eq_center one_ne_zero] using hv
  have hb (h : (remodelHomeomorph _ _).symm
      (EuclideanComplexProjectiveSpace.connectedSumBall n (inversion 0 1 v)) ∈
        projectiveBlowupOpens n) :
      (projectiveBlowupModelDiffeomorph n ⟨_, h⟩).blowdown =
        (inversion 0 1 (inversion 0 1 v)).ofLp := by
    rw [← blowdown_projectiveBlowupModelDiffeomorph_snoc_one hv']
    congr 3
    rw [EuclideanComplexProjectiveSpace.connectedSumBall_apply, Homeomorph.symm_apply_apply]
    congr 1
    rw [Fin.insertNth_last', EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
  rw [connectedSumInl_apply, connectedSumInr_apply, (remodelHomeomorph _ _).injective.eq_iff,
    inl_eq_inr_iff]
  simp only [BlowupChart.connectedSumBall_apply, Homeomorph.symm_apply_apply]
  refine ⟨c.map_target (c.equiv_univBall_mem_target v), ?_⟩
  rw [c.right_inv (c.equiv_univBall_mem_target v), BlowupModel.blowdown_radialRescale, hb,
    EuclideanGeometry.inversion_inversion _ one_ne_zero]
  simp

/-- **The two pieces meet only at glued points.** A point `x` of the punctured `M` and a point `y`
of the punctured projective space go to the same point of the blowup exactly when the connected
sum identifies them: `x = c.connectedSumBall v` and
`y = EuclideanComplexProjectiveSpace.connectedSumBall n (inversion 0 1 v)` for some `v ≠ 0`. -/
theorem connectedSumInl_eq_connectedSumInr_iff {x : puncture c.connectedSumBall}
    {y : puncture (EuclideanComplexProjectiveSpace.connectedSumBall n)} :
    connectedSumInl c x = connectedSumInr c y ↔
      ∃ v ≠ 0, c.connectedSumBall v = x ∧
        EuclideanComplexProjectiveSpace.connectedSumBall n (inversion 0 1 v) = y := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h' := h
    rw [connectedSumInl_apply, connectedSumInr_apply, (remodelHomeomorph _ _).injective.eq_iff,
      inl_eq_inr_iff, BlowupModel.blowdown_radialRescale] at h'
    obtain ⟨hsrc, heq⟩ := h'
    set a := (EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm (projectiveBlowupModelDiffeomorph n
      ⟨_, EuclideanComplexProjectiveSpace.symm_coe_mem_projectiveBlowupOpens y⟩).blowdown
    have hxa : c.connectedSumBall a = x := by
      rw [BlowupChart.connectedSumBall_apply, ← heq, c.left_inv hsrc,
        Homeomorph.apply_symm_apply]
    have ha : a ≠ 0 := by
      rintro ha
      exact mem_puncture.1 x.property (by rw [← hxa, ha])
    have hy' := TauCeti.ConnectedSum.apply_inversion_mem_puncture
      (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n).injective ha
    have hF : connectedSumInr c ⟨_, hy'⟩ = connectedSumInr c y := by
      rw [← h, ← connectedSumInl_eq_connectedSumInr c a (hxa ▸ x.property) hy']
      congr 1
      exact Subtype.ext hxa
    exact ⟨a, ha, hxa, congrArg Subtype.val (connectedSumInr_injective c hF)⟩
  · rintro ⟨v, -, hx, hy⟩
    obtain ⟨x, hx'⟩ := x
    obtain ⟨y, hy'⟩ := y
    subst hx hy
    exact connectedSumInl_eq_connectedSumInr c v hx' hy'

/-- The two pieces cover the blowup. -/
theorem range_connectedSumInl_union_range_connectedSumInr :
    range (connectedSumInl c) ∪ range (connectedSumInr c) = univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  by_cases hz : (remodelHomeomorph _ _).symm z ∈ exceptionalDivisor c
  · right
    obtain ⟨q, hb, hq⟩ := (mem_exceptionalDivisor_iff c).1 hz
    obtain ⟨q', hq'⟩ : (q : BlowupModel n) ∈ range (BlowupModel.radialRescale c.ballRadius) := by
      rw [BlowupModel.range_radialRescale c.ballRadius_pos]
      exact BlowupModel.exceptionalDivisor_subset_openNbhd c.ballRadius_pos
        (BlowupModel.mem_exceptionalDivisor_iff.2 hb)
    set w := (projectiveBlowupModelDiffeomorph n).symm q'
    have hw : remodelHomeomorph _ _ (w : ℙ ℂ (Fin (n + 2) → ℂ)) ∈
        puncture (EuclideanComplexProjectiveSpace.connectedSumBall n) := by
      have := w.property
      rw [← SetLike.mem_coe, coe_projectiveBlowupOpens, mem_compl_singleton_iff] at this
      rwa [mem_puncture, EuclideanComplexProjectiveSpace.connectedSumBall_zero,
        (remodelHomeomorph _ _).injective.ne_iff]
    refine ⟨⟨_, hw⟩, ?_⟩
    rw [connectedSumInr_apply, ← (remodelHomeomorph _ _).apply_symm_apply z, ← hq]
    congr 2
    refine Subtype.ext ?_
    simp only [Homeomorph.symm_apply_apply, Subtype.coe_eta, w,
      Diffeomorph.apply_symm_apply, hq']
  · left
    obtain ⟨x, hx⟩ : (remodelHomeomorph _ _).symm z ∈ range (inl (gluingHomeomorph c)) := by
      rwa [range_inl]
    refine ⟨⟨remodelHomeomorph _ M x, mem_puncture.2 ?_⟩, ?_⟩
    · rw [c.connectedSumBall_zero, (remodelHomeomorph _ M).injective.ne_iff]
      exact (mem_puncturedOpens c).1 x.property
    · rw [connectedSumInl_apply, ← (remodelHomeomorph _ _).apply_symm_apply z, ← hx]
      congr 2
      exact Subtype.ext (Homeomorph.symm_apply_apply _ _)

/-! ## The connected sum as the blowup -/

section Diffeomorph

open TauCeti.ConnectedSum (mk_surjective mk_inl mk_inr)

/-- The map glued from the two pieces is a bijection from the connected sum onto the blowup. -/
private theorem bijective_lift_connectedSumInl_connectedSumInr :
    Function.Bijective (ConnectedSum.lift (connectedSumInl c) (connectedSumInr c)
      fun v _ hx hy ↦ connectedSumInl_eq_connectedSumInr c v hx hy) := by
  have h₁ := c.isOpenEmbedding_connectedSumBall.injective
  refine ⟨fun p q h ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨x | y, rfl⟩ := mk_surjective _ _ p <;> obtain ⟨x' | y', rfl⟩ := mk_surjective _ _ q <;>
      simp only [mk_inl, mk_inr, ConnectedSum.lift_inl, ConnectedSum.lift_inr] at h ⊢
    · rw [connectedSumInl_injective c h]
    · exact (TauCeti.ConnectedSum.inl_eq_inr_iff h₁).2
        ((connectedSumInl_eq_connectedSumInr_iff c).1 h)
    · exact ((TauCeti.ConnectedSum.inl_eq_inr_iff h₁).2
        ((connectedSumInl_eq_connectedSumInr_iff c).1 h.symm)).symm
    · rw [connectedSumInr_injective c h]
  · obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ :=
      (range_connectedSumInl_union_range_connectedSumInr c).symm ▸ mem_univ z
    exacts [⟨_, ConnectedSum.lift_inl _ _ _ x⟩, ⟨_, ConnectedSum.lift_inr _ _ _ y⟩]

open scoped TauCeti.ComplexManifold

variable [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

/-- For a holomorphic chart `c`, the map glued from the two pieces is a smooth local
diffeomorphism from the connected sum, with the charts of Tau Ceti's
`TauCeti.ConnectedSum.chartedSpace`. -/
private theorem isLocalDiffeomorph_lift_connectedSumInl_connectedSumInr :
    letI := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1)))
      c.isOpenEmbedding_connectedSumBall
      (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
    IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1)))
      ∞ (ConnectedSum.lift (connectedSumInl c) (connectedSumInr c)
        fun v _ hx hy ↦ connectedSumInl_eq_connectedSumInr c v hx hy) := by
  have h₁ := c.isOpenEmbedding_connectedSumBall
  have h₂ := EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n
  let := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1))) h₁ h₂
  refine TauCeti.ConnectedSum.isLocalDiffeomorph_of_comp_inl_of_comp_inr h₁ h₂
    (c.isLocalDiffeomorph_connectedSumBall Fact.out)
    (EuclideanComplexProjectiveSpace.isLocalDiffeomorph_connectedSumBall n) ?_ ?_
  · rw [show _ ∘ ConnectedSum.inl _ _ = connectedSumInl c from
      funext (ConnectedSum.lift_inl _ _ _)]
    exact isLocalDiffeomorph_connectedSumInl c
  · rw [show _ ∘ ConnectedSum.inr _ _ = connectedSumInr c from
      funext (ConnectedSum.lift_inr _ _ _)]
    exact isLocalDiffeomorph_connectedSumInr c

/-- **The blowup as a connected sum.** For a holomorphic chart `c` of `M` centred at `p₀`, the
connected sum of `M` and the complex projective space of dimension `n + 1` along the balls
`c.connectedSumBall` and `EuclideanComplexProjectiveSpace.connectedSumBall n`, with the charts of
`TauCeti.ConnectedSum.chartedSpace`, is diffeomorphic to the blowup `Blowup c`, both as smooth real
manifolds modelled on `EuclideanSpace ℂ (Fin (n + 1))`. The diffeomorphism is
`Blowup.connectedSumInl c` on the punctured `M`, which it sends off the exceptional divisor, and
`Blowup.connectedSumInr c` on the punctured projective space. -/
def connectedSumDiffeomorph :
    letI := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1)))
      c.isOpenEmbedding_connectedSumBall
      (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
    TauCeti.ConnectedSum c.connectedSumBall (EuclideanComplexProjectiveSpace.connectedSumBall n)
      ≃ₘ^∞⟮𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))), 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1)))⟯
      Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm (Blowup c) :=
  letI := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1)))
    c.isOpenEmbedding_connectedSumBall
    (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
  (isLocalDiffeomorph_lift_connectedSumInl_connectedSumInr c).diffeomorphOfBijective
    (bijective_lift_connectedSumInl_connectedSumInr c)

/-- The diffeomorphism `Blowup.connectedSumDiffeomorph c` is the map out of the connected sum
glued from `Blowup.connectedSumInl c` and `Blowup.connectedSumInr c`. -/
theorem coe_connectedSumDiffeomorph :
    letI := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1)))
      c.isOpenEmbedding_connectedSumBall
      (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
    ⇑(connectedSumDiffeomorph c) = ConnectedSum.lift (connectedSumInl c) (connectedSumInr c)
      fun v _ hx hy ↦ connectedSumInl_eq_connectedSumInr c v hx hy :=
  letI := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1)))
    c.isOpenEmbedding_connectedSumBall
    (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
  IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

/-- On the punctured `M`, the diffeomorphism `Blowup.connectedSumDiffeomorph c` is
`Blowup.connectedSumInl c`. -/
@[simp]
theorem connectedSumDiffeomorph_inl (x : puncture c.connectedSumBall) :
    letI := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1)))
      c.isOpenEmbedding_connectedSumBall
      (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
    connectedSumDiffeomorph c (ConnectedSum.inl _ _ x) = connectedSumInl c x := by
  let := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1)))
    c.isOpenEmbedding_connectedSumBall
    (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
  rw [coe_connectedSumDiffeomorph, ConnectedSum.lift_inl]

/-- On the punctured projective space, the diffeomorphism `Blowup.connectedSumDiffeomorph c` is
`Blowup.connectedSumInr c`. -/
@[simp]
theorem connectedSumDiffeomorph_inr
    (y : puncture (EuclideanComplexProjectiveSpace.connectedSumBall n)) :
    letI := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1)))
      c.isOpenEmbedding_connectedSumBall
      (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
    connectedSumDiffeomorph c (ConnectedSum.inr _ _ y) = connectedSumInr c y := by
  let := TauCeti.ConnectedSum.chartedSpace (H := EuclideanSpace ℂ (Fin (n + 1)))
    c.isOpenEmbedding_connectedSumBall
    (EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall n)
  rw [coe_connectedSumDiffeomorph, ConnectedSum.lift_inr]

end Diffeomorph

end Blowup

end SymplecticGeometry

end
