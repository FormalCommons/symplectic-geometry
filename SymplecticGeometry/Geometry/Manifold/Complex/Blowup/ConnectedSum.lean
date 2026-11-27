/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Euclidean
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.UnivBall
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# The balls along which the blowup is a connected sum

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
  `0`: there `ρ` has derivative `ε • id`, and `c.symm` is a local biholomorphism.
* The second summand is `EuclideanComplexProjectiveSpace n` with the opposite of its complex
  orientation, and `EuclideanComplexProjectiveSpace.connectedSumBall n` is `u ↦ [u : 1]`, the
  inverse of the affine chart at the last coordinate. Being holomorphic, it preserves the complex
  orientations, and so reverses the opposite one.

In both cases the orientation of the model is its complex orientation as a complex manifold over
itself, `SymplecticGeometry.complexManifoldOrientationOfFinrank`.

## Main definitions

* `SymplecticGeometry.BlowupChart.connectedSumBall c`: the ball `e₁` of `M`.
* `SymplecticGeometry.EuclideanComplexProjectiveSpace.connectedSumBall n`: the ball `e₂` of the
  projective space.

## Main results

* `SymplecticGeometry.BlowupChart.isOpenEmbedding_connectedSumBall`,
  `SymplecticGeometry.BlowupChart.isLocalDiffeomorph_connectedSumBall`,
  `SymplecticGeometry.BlowupChart.isOrientationPreservingAt_connectedSumBall`;
* `SymplecticGeometry.EuclideanComplexProjectiveSpace.isOpenEmbedding_connectedSumBall`,
  `SymplecticGeometry.EuclideanComplexProjectiveSpace.isLocalDiffeomorph_connectedSumBall`,
  `SymplecticGeometry.EuclideanComplexProjectiveSpace.isOrientationReversingAt_connectedSumBall`.

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

/-- A complex manifold charted on `Fin (n + 1) → ℂ`, re-modelled on the Hermitian space
`EuclideanSpace ℂ (Fin (n + 1))`, is a smooth real manifold, the one underlying its complex
structure. -/
instance (M : Type*) [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M]
    [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M] :
    IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) ∞
      (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M) :=
  (inferInstance : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin (n + 1))) ∞
    (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M)).restrictScalars ℝ

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M] {p₀ : M}

namespace BlowupChart

variable (c : BlowupChart (n := n) M p₀)

/-- The chart `c` of `M`, read on `M` re-modelled on the Hermitian space
`EuclideanSpace ℂ (Fin (n + 1))`: `c` followed by the identification of `Fin (n + 1) → ℂ` with
that space. -/
def euclideanChart :
    OpenPartialHomeomorph (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M)
      (EuclideanSpace ℂ (Fin (n + 1))) :=
  c.toOpenPartialHomeomorph.trans
    (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm.toHomeomorph.toOpenPartialHomeomorph

theorem euclideanChart_def :
    c.euclideanChart = c.toOpenPartialHomeomorph.trans
      ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm.toHomeomorph
        |>.toOpenPartialHomeomorph) :=
  (rfl)

theorem center_mem_euclideanChart_source : p₀ ∈ c.euclideanChart.source := by
  rw [euclideanChart_def, OpenPartialHomeomorph.trans_source]
  exact ⟨c.mem_source, trivial⟩

theorem euclideanChart_apply (x : M) :
    c.euclideanChart x = (EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm (c x) :=
  (rfl)

@[simp]
theorem euclideanChart_symm_apply (v : EuclideanSpace ℂ (Fin (n + 1))) :
    c.euclideanChart.symm v = c.symm (EuclideanSpace.equiv (Fin (n + 1)) ℂ v) :=
  (rfl)

theorem euclideanChart_center : c.euclideanChart p₀ = 0 := by
  rw [euclideanChart_apply, c.map_center, map_zero]

theorem zero_mem_euclideanChart_target : 0 ∈ c.euclideanChart.target :=
  c.euclideanChart_center ▸ c.euclideanChart.map_source c.center_mem_euclideanChart_source

/-- When `c` is a holomorphic chart of `M`, `c.euclideanChart` is a holomorphic chart of `M`
re-modelled on `EuclideanSpace ℂ (Fin (n + 1))`. -/
theorem euclideanChart_mem_maximalAtlas [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]
    (hc : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M) :
    c.euclideanChart ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin (n + 1))) ∞
      (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M) :=
  trans_mem_maximalAtlas_remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M
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
      c.symm (EuclideanSpace.equiv (Fin (n + 1)) ℂ (univBall 0 c.ballRadius v)) := by
  rw [connectedSumBall_def, Function.comp_apply, euclideanChart_symm_apply]

@[simp]
theorem connectedSumBall_zero : c.connectedSumBall 0 = p₀ := by
  rw [connectedSumBall_def, Function.comp_apply, univBall_apply_zero, ← c.euclideanChart_center]
  exact c.euclideanChart.left_inv c.center_mem_euclideanChart_source

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

/-- For a holomorphic chart `c`, the ball `c.connectedSumBall` preserves at `0` the complex
orientations of `EuclideanSpace ℂ (Fin (n + 1))` and of `M`, re-modelled on it. -/
theorem isOrientationPreservingAt_connectedSumBall
    (hc : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M) :
    (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
        (EuclideanSpace ℂ (Fin (n + 1))) (r := n) (by simp)).IsOrientationPreservingAt
      (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
        (Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm M) (r := n) (by simp))
      c.connectedSumBall 0 := by
  have hφ := (c.euclideanChart.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
    (c.euclideanChart_mem_maximalAtlas hc)
    c.zero_mem_euclideanChart_target).isOrientationPreservingAt_complexManifoldOrientation ∞
  rw [complexManifoldOrientationOfFinrank_def, complexManifoldOrientationOfFinrank_def,
    connectedSumBall_def]
  exact ((univBall_apply_zero (0 : EuclideanSpace ℂ (Fin (n + 1))) c.ballRadius ▸
    hφ.reindex _).comp (isOrientationPreservingAt_univBall_zero c.ballRadius_pos _))

end BlowupChart

namespace EuclideanComplexProjectiveSpace

variable (n)

/-- The affine chart of `ℙ ℂ (Fin (n + 2) → ℂ)` at the last homogeneous coordinate, read on
`EuclideanComplexProjectiveSpace n`: Tau Ceti's `affineOpenPartialHomeomorph (Fin.last (n + 1))`
followed by the identification of `Fin (n + 1) → ℂ` with `EuclideanSpace ℂ (Fin (n + 1))`. -/
def lastAffineChart :
    OpenPartialHomeomorph (EuclideanComplexProjectiveSpace n) (EuclideanSpace ℂ (Fin (n + 1))) :=
  (Projectivization.affineOpenPartialHomeomorph (K := ℂ) (Fin.last (n + 1))).trans
    (EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm.toHomeomorph.toOpenPartialHomeomorph

theorem lastAffineChart_def :
    lastAffineChart n =
      (Projectivization.affineOpenPartialHomeomorph (K := ℂ) (Fin.last (n + 1))).trans
        ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm.toHomeomorph
          |>.toOpenPartialHomeomorph) :=
  (rfl)

theorem lastAffineChart_symm_apply (u : EuclideanSpace ℂ (Fin (n + 1))) :
    (lastAffineChart n).symm u =
      (Projectivization.affineChart (Fin.last (n + 1))).symm (EuclideanSpace.equiv _ ℂ u) := by
  -- The same statement on `ℙ ℂ (Fin (n + 2) → ℂ)`, whose type synonym is
  -- `EuclideanComplexProjectiveSpace n`, where the lemmas on `trans` apply.
  have h : ((Projectivization.affineOpenPartialHomeomorph (K := ℂ) (Fin.last (n + 1))).trans
      ((EuclideanSpace.equiv (Fin (n + 1)) ℂ).toDiffeomorph.symm.toHomeomorph
        |>.toOpenPartialHomeomorph)).symm
        u =
      (Projectivization.affineChart (Fin.last (n + 1))).symm (EuclideanSpace.equiv _ ℂ u) := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans,
      Function.comp_apply, Projectivization.coe_affineOpenPartialHomeomorph_symm]
    simp
  exact h

@[simp]
theorem lastAffineChart_target : (lastAffineChart n).target = univ := by
  simp [lastAffineChart_def]

theorem lastAffineChart_mem_maximalAtlas :
    lastAffineChart n ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin (n + 1))) ∞
      (EuclideanComplexProjectiveSpace n) :=
  trans_mem_maximalAtlas_remodel _ _
    (Projectivization.affineOpenPartialHomeomorph_mem_maximalAtlas (Fin.last (n + 1)))

/-- The coordinate ball of the projective space along which the blowup is a connected sum:
`u ↦ [u : 1]`, the inverse of the affine chart at the last homogeneous coordinate. -/
def connectedSumBall : EuclideanSpace ℂ (Fin (n + 1)) → EuclideanComplexProjectiveSpace n :=
  (lastAffineChart n).symm

theorem connectedSumBall_def : connectedSumBall n = (lastAffineChart n).symm :=
  (rfl)

theorem connectedSumBall_apply (u : EuclideanSpace ℂ (Fin (n + 1))) :
    connectedSumBall n u =
      Projectivization.mk ℂ
        (Fin.insertNth (α := fun _ ↦ ℂ) (Fin.last (n + 1)) 1 (EuclideanSpace.equiv _ ℂ u))
        (Fin.insertNth_one_ne_zero _ _) := by
  rw [connectedSumBall_def, lastAffineChart_symm_apply, Projectivization.affineChart_symm_apply]

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

/-- The ball `connectedSumBall n` reverses at `0` the complex orientation of
`EuclideanSpace ℂ (Fin (n + 1))` and the opposite of the complex orientation of the projective
space. -/
theorem isOrientationReversingAt_connectedSumBall :
    (complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
        (EuclideanSpace ℂ (Fin (n + 1))) (r := n) (by simp)).IsOrientationReversingAt
      (-orientation n) (connectedSumBall n) 0 := by
  rw [Manifold.Orientation.isOrientationReversingAt_neg_right]
  exact isOrientationPreservingAt_connectedSumBall n 0

end EuclideanComplexProjectiveSpace

end SymplecticGeometry

end
