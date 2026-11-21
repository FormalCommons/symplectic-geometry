/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Basic

/-!
# The topology of the Lagrangian Grassmannian

Let `V` be a finite-dimensional real inner product space and `ω` a symplectic form on `V`. This
file puts a topology on `SymplecticGeometry.LagrangianGrassmannian ω`: a Lagrangian subspace `Λ`
is identified with its orthogonal projection `Λ.starProjection : V →L[ℝ] V`, and the topology is
the one induced from the space of continuous linear endomorphisms of `V`. Since `V` is finite
dimensional, that space carries its unique Hausdorff vector space topology. This is the
topology of McDuff–Salamon's `𝓛(V, ω)`.

The symplectic form only selects which subspaces are points; the inner product is an auxiliary
choice that fixes the projections.

## Main definitions and results

* `SymplecticGeometry.LagrangianGrassmannian.instTopologicalSpace`: the topology induced by
  `Λ ↦ Λ.starProjection`.
* `SymplecticGeometry.LagrangianGrassmannian.isEmbedding_starProjection`: the map
  `Λ ↦ Λ.starProjection` is a topological embedding, since a subspace is determined by its
  orthogonal projection.
* `SymplecticGeometry.LagrangianGrassmannian.continuous_iff_continuous_starProjection`: a map into
  the Lagrangian Grassmannian is continuous exactly when its orthogonal projections depend
  continuously on the parameter.
* The Lagrangian Grassmannian is Hausdorff.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

namespace LagrangianGrassmannian

open Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : TauCeti.SymplecticForm V}

/-- The topology on the Lagrangian Grassmannian of a finite-dimensional real inner product space:
the coarsest one for which the orthogonal projection `Λ ↦ Λ.starProjection` onto the subspace is
continuous, as a map to `V →L[ℝ] V`. -/
noncomputable instance instTopologicalSpace : TopologicalSpace (LagrangianGrassmannian ω) :=
  .induced (fun Λ ↦ (Λ : Submodule ℝ V).starProjection) inferInstance

/-- The topology of the Lagrangian Grassmannian is induced by the orthogonal projections. -/
theorem instTopologicalSpace_def :
    (instTopologicalSpace : TopologicalSpace (LagrangianGrassmannian ω)) =
      .induced (fun Λ ↦ (Λ : Submodule ℝ V).starProjection) inferInstance :=
  rfl

/-- A Lagrangian subspace is determined by its orthogonal projection. -/
theorem starProjection_injective :
    Function.Injective fun Λ : LagrangianGrassmannian ω ↦ (Λ : Submodule ℝ V).starProjection :=
  fun _ _ h ↦ toSubmodule_injective (Submodule.starProjection_inj.mp h)

@[simp]
theorem starProjection_inj {Λ Λ' : LagrangianGrassmannian ω} :
    (Λ : Submodule ℝ V).starProjection = (Λ' : Submodule ℝ V).starProjection ↔ Λ = Λ' :=
  starProjection_injective.eq_iff

theorem isInducing_starProjection :
    IsInducing fun Λ : LagrangianGrassmannian ω ↦ (Λ : Submodule ℝ V).starProjection :=
  ⟨rfl⟩

/-- The map sending a Lagrangian subspace to its orthogonal projection is a topological
embedding into `V →L[ℝ] V`. -/
theorem isEmbedding_starProjection :
    IsEmbedding fun Λ : LagrangianGrassmannian ω ↦ (Λ : Submodule ℝ V).starProjection :=
  ⟨isInducing_starProjection, starProjection_injective⟩

/-- The orthogonal projection onto a Lagrangian subspace depends continuously on the subspace. -/
@[continuity, fun_prop]
theorem continuous_starProjection :
    Continuous fun Λ : LagrangianGrassmannian ω ↦ (Λ : Submodule ℝ V).starProjection :=
  isInducing_starProjection.continuous

/-- A map into the Lagrangian Grassmannian is continuous if and only if the orthogonal
projections onto its values depend continuously on the parameter. -/
theorem continuous_iff_continuous_starProjection {X : Type*} [TopologicalSpace X]
    {f : X → LagrangianGrassmannian ω} :
    Continuous f ↔ Continuous fun x ↦ (f x : Submodule ℝ V).starProjection :=
  isInducing_starProjection.continuous_iff

/-- The Lagrangian Grassmannian is Hausdorff. -/
instance instT2Space : T2Space (LagrangianGrassmannian ω) :=
  isEmbedding_starProjection.t2Space

end LagrangianGrassmannian

end SymplecticGeometry

end
