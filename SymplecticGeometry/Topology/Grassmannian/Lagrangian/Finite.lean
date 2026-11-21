/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Basic
public import TauCeti.Topology.Grassmannian.Orthonormal
public import TauCeti.Topology.Grassmannian.Plucker
public import TauCeti.Topology.Grassmannian.Tautological

/-!
# The Lagrangian Grassmannian inside Tau Ceti's finite Grassmannian

Write `ℒ(n)` for `LagrangianGrassmannian (stdForm (Fin n))`, the space of Lagrangian subspaces of
the standard model `(StdSpace (Fin n), ω₀)`, with the topology of orthogonal projections. The
coordinates of `StdSpace (Fin n) = EuclideanSpace ℝ (Fin n ⊕ Fin n)` are relabelled by
`finSumFinEquiv`, which gives the linear isometry
`LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv` onto `EuclideanSpace ℝ (Fin (n + n))`,
and then `WithLp.linearEquiv` forgets the inner product. The image of a Lagrangian under this
identification is an `n`-dimensional subspace of `Fin (n + n) → ℝ`, a point of
`TauCeti.finiteGrassmannian ℝ n (n + n)`.

This file shows that the resulting map is a topological embedding, whose image consists of the
subspaces that pull back to Lagrangian subspaces. So the topology of `ℒ(n)` is the subspace
topology of the finite Grassmannian.

The proof compares orthogonal projections. The isometry conjugates the projection onto a
Lagrangian into the projection onto its image (`Submodule.starProjection_map_apply`), and on the
finite Grassmannian, which is compact and Hausdorff, Tau Ceti's continuous and injective map
`V ↦ V.toEuclidean.starProjection` is a closed embedding.

## Main definitions and results

* `SymplecticGeometry.LagrangianGrassmannian.toFiniteGrassmannian`: a Lagrangian of
  `StdSpace (Fin n)` as a point of `TauCeti.finiteGrassmannian ℝ n (n + n)`.
* `SymplecticGeometry.LagrangianGrassmannian.isEmbedding_toFiniteGrassmannian`: this map is a
  topological embedding.
* `SymplecticGeometry.LagrangianGrassmannian.range_toFiniteGrassmannian`: its image is the set
  of subspaces whose pull-back to `StdSpace (Fin n)` is Lagrangian.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

open TauCeti StdSpace Topology

namespace LagrangianGrassmannian

variable {n : ℕ}

/-- A Lagrangian subspace of `StdSpace (Fin n)`, viewed as an `n`-dimensional subspace of
`Fin (n + n) → ℝ`, a point of Tau Ceti's finite Grassmannian, through the relabelling of
coordinates along `finSumFinEquiv`. -/
noncomputable def toFiniteGrassmannian (Λ : LagrangianGrassmannian (stdForm (Fin n))) :
    finiteGrassmannian ℝ n (n + n) :=
  ⟨((Λ : Submodule ℝ (StdSpace (Fin n))).map
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv).toLinearEquiv.toLinearMap).map
        (WithLp.linearEquiv 2 ℝ (Fin (n + n) → ℝ)).toLinearMap, by
    rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]
    have h := Λ.isLagrangian.two_mul_finrank
    rw [finrank_stdSpace, Fintype.card_fin] at h
    exact Nat.eq_of_mul_eq_mul_left two_pos h⟩

@[simp]
theorem coe_toFiniteGrassmannian (Λ : LagrangianGrassmannian (stdForm (Fin n))) :
    ((toFiniteGrassmannian Λ : finiteGrassmannian ℝ n (n + n)) :
        Submodule ℝ (Fin (n + n) → ℝ)) =
      ((Λ : Submodule ℝ (StdSpace (Fin n))).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv).toLinearEquiv.toLinearMap).map
          (WithLp.linearEquiv 2 ℝ (Fin (n + n) → ℝ)).toLinearMap :=
  (rfl)

/-- Read in `EuclideanSpace ℝ (Fin (n + n))`, the image of a Lagrangian is its image under the
coordinate isometry. -/
@[simp]
theorem toEuclidean_toFiniteGrassmannian (Λ : LagrangianGrassmannian (stdForm (Fin n))) :
    (toFiniteGrassmannian Λ).toEuclidean =
      (Λ : Submodule ℝ (StdSpace (Fin n))).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv).toLinearEquiv.toLinearMap :=
  SetLike.ext fun x ↦ by
    rw [finiteGrassmannian.mem_toEuclidean, coe_toFiniteGrassmannian, Submodule.mem_map_equiv]
    simp

/-- The orthogonal projection onto the image of a Lagrangian is the projection onto the
Lagrangian, conjugated by the coordinate isometry. -/
theorem starProjection_toEuclidean_toFiniteGrassmannian
    (Λ : LagrangianGrassmannian (stdForm (Fin n))) :
    (toFiniteGrassmannian Λ).toEuclidean.starProjection =
      ContinuousLinearEquiv.arrowCongr
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv).toContinuousLinearEquiv
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv).toContinuousLinearEquiv
        (Λ : Submodule ℝ (StdSpace (Fin n))).starProjection := by
  ext1 x
  rw [toEuclidean_toFiniteGrassmannian, Submodule.starProjection_map_apply]
  rfl

theorem toFiniteGrassmannian_injective :
    Function.Injective (toFiniteGrassmannian (n := n)) := fun Λ Λ' h ↦ by
  have h' := congrArg finiteGrassmannian.toEuclidean h
  rw [toEuclidean_toFiniteGrassmannian, toEuclidean_toFiniteGrassmannian] at h'
  exact toSubmodule_injective
    (Submodule.map_injective_of_injective (LinearIsometryEquiv.injective _) h')

@[simp]
theorem toFiniteGrassmannian_inj {Λ Λ' : LagrangianGrassmannian (stdForm (Fin n))} :
    toFiniteGrassmannian Λ = toFiniteGrassmannian Λ' ↔ Λ = Λ' :=
  toFiniteGrassmannian_injective.eq_iff

/-- On Tau Ceti's finite Grassmannian, the orthogonal projection onto a point is a closed
embedding into the operators of `EuclideanSpace ℝ (Fin (n + n))`: it is continuous and
injective, and the Grassmannian is compact and Hausdorff. -/
private theorem isClosedEmbedding_starProjection_toEuclidean :
    IsClosedEmbedding fun V : finiteGrassmannian ℝ n (n + n) ↦ V.toEuclidean.starProjection :=
  finiteGrassmannian.continuous_starProjection_toEuclidean.isClosedEmbedding
    fun (_ _ : finiteGrassmannian ℝ n (n + n)) h ↦
      finiteGrassmannian.toEuclidean_injective (Submodule.starProjection_inj.mp h)

/-- The map from the Lagrangians of `StdSpace (Fin n)` to Tau Ceti's finite Grassmannian of
`n`-planes in `Fin (n + n) → ℝ` is a topological embedding. -/
theorem isEmbedding_toFiniteGrassmannian : IsEmbedding (toFiniteGrassmannian (n := n)) := by
  rw [← isClosedEmbedding_starProjection_toEuclidean.isEmbedding.of_comp_iff]
  have : (fun V : finiteGrassmannian ℝ n (n + n) ↦ V.toEuclidean.starProjection) ∘
      toFiniteGrassmannian =
        ContinuousLinearEquiv.arrowCongr
          (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv).toContinuousLinearEquiv
          (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv).toContinuousLinearEquiv ∘
          fun Λ : LagrangianGrassmannian (stdForm (Fin n)) ↦
            (Λ : Submodule ℝ (StdSpace (Fin n))).starProjection :=
    funext starProjection_toEuclidean_toFiniteGrassmannian
  rw [this]
  exact (ContinuousLinearEquiv.arrowCongr _ _).toHomeomorph.isEmbedding.comp
    (isEmbedding_starProjection (ω := stdForm (Fin n)))

@[fun_prop]
theorem continuous_toFiniteGrassmannian : Continuous (toFiniteGrassmannian (n := n)) :=
  isEmbedding_toFiniteGrassmannian.continuous

/-- The image of the Lagrangians of `StdSpace (Fin n)` in Tau Ceti's finite Grassmannian
consists of the `n`-planes of `Fin (n + n) → ℝ` whose pull-back to `StdSpace (Fin n)`, along the
coordinate isometry, is Lagrangian. -/
theorem range_toFiniteGrassmannian :
    Set.range (toFiniteGrassmannian (n := n)) =
      {V | (stdForm (Fin n)).IsLagrangian (V.toEuclidean.comap
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          finSumFinEquiv).toLinearEquiv.toLinearMap)} := by
  ext V
  constructor
  · rintro ⟨Λ, rfl⟩
    rw [Set.mem_ofPred_eq, toEuclidean_toFiniteGrassmannian,
      Submodule.comap_map_eq_of_injective (LinearIsometryEquiv.injective _)]
    exact Λ.isLagrangian
  · intro hV
    refine ⟨⟨_, hV⟩, finiteGrassmannian.toEuclidean_injective ?_⟩
    rw [toEuclidean_toFiniteGrassmannian, coe_mk]
    exact Submodule.map_comap_eq_of_surjective (LinearIsometryEquiv.surjective _) _

end LagrangianGrassmannian

end SymplecticGeometry

end
