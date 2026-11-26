/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace

/-!
# The Lagrangian Grassmannian

For a symplectic form `ω` on a real vector space `V`, this file defines
`SymplecticGeometry.LagrangianGrassmannian ω`, the type of Lagrangian subspaces of `(V, ω)`:
the subspaces `L` with `L^ω = L` (Tau Ceti's `TauCeti.SymplecticForm.IsLagrangian`). It is
McDuff–Salamon's `𝓛(V, ω)`, and for the standard form on `ℝ²ⁿ` it is `𝓛(n)`.

Following Mathlib's `Module.Grassmannian`, it is a structure extending `Submodule ℝ V` with the
proof that the subspace is Lagrangian. This file has no topology.

## Main definitions and results

* `SymplecticGeometry.LagrangianGrassmannian ω`: the Lagrangian subspaces of `(V, ω)`, with a
  `SetLike` instance and closure classes, extensionality, the basic API relating it to
  `Submodule ℝ V`, and `orthogonal_eq`, the equation `Λ^ω = Λ` that defines a point.
* `SymplecticGeometry.LagrangianGrassmannian.instNonempty`: every symplectic vector space has a
  Lagrangian subspace (Lagrangian extension of the zero subspace).
* `SymplecticGeometry.LagrangianGrassmannian.isCompl_iff_disjoint`: in finite dimension, two
  Lagrangian subspaces are complementary exactly when they meet only in `0`, since each has half
  the dimension of `V`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

open Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The Lagrangian Grassmannian of a symplectic vector space `(V, ω)`: the type of subspaces
`L ⊆ V` that are Lagrangian for `ω`, that is, equal to their symplectic complement `L^ω`. -/
structure LagrangianGrassmannian (ω : TauCeti.SymplecticForm V) extends Submodule ℝ V where
  /-- The subspace is Lagrangian. Use `LagrangianGrassmannian.isLagrangian` instead. -/
  isLagrangian' : ω.IsLagrangian toSubmodule

namespace LagrangianGrassmannian

variable {ω : TauCeti.SymplecticForm V}

instance : SetLike (LagrangianGrassmannian ω) V where
  coe Λ := Λ.carrier
  coe_injective := fun ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ h => by congr

instance : AddSubgroupClass (LagrangianGrassmannian ω) V where
  zero_mem Λ := Λ.toSubmodule.zero_mem
  add_mem {Λ} _ _ := Λ.toSubmodule.add_mem
  neg_mem {Λ} _ := Λ.toSubmodule.neg_mem

instance : SMulMemClass (LagrangianGrassmannian ω) ℝ V where
  smul_mem {Λ} _ _ := Λ.toSubmodule.smul_mem _

instance : CoeOut (LagrangianGrassmannian ω) (Submodule ℝ V) :=
  ⟨toSubmodule⟩

/-- A vector lies in the carrier set of `Λ` exactly when it lies in `Λ`. -/
theorem mem_carrier {Λ : LagrangianGrassmannian ω} {x : V} : x ∈ Λ.carrier ↔ x ∈ Λ :=
  Iff.rfl

@[simp]
theorem coe_toSubmodule (Λ : LagrangianGrassmannian ω) :
    ((Λ : Submodule ℝ V) : Set V) = Λ :=
  rfl

@[simp]
theorem mem_toSubmodule {Λ : LagrangianGrassmannian ω} {x : V} :
    x ∈ (Λ : Submodule ℝ V) ↔ x ∈ Λ :=
  Iff.rfl

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : LagrangianGrassmannian ω → Submodule ℝ V) :=
  fun _ _ h => SetLike.coe_injective (congrArg (fun L : Submodule ℝ V => (L : Set V)) h)

@[simp]
theorem toSubmodule_inj {Λ Λ' : LagrangianGrassmannian ω} :
    (Λ : Submodule ℝ V) = Λ' ↔ Λ = Λ' :=
  toSubmodule_injective.eq_iff

/-- Two Lagrangian subspaces are equal when they have the same elements. -/
@[ext]
theorem ext {Λ Λ' : LagrangianGrassmannian ω} (h : ∀ x, x ∈ Λ ↔ x ∈ Λ') : Λ = Λ' :=
  SetLike.ext h

/-- A point of the Lagrangian Grassmannian is a Lagrangian subspace. -/
theorem isLagrangian (Λ : LagrangianGrassmannian ω) : ω.IsLagrangian Λ :=
  Λ.isLagrangian'

/-- A point of the Lagrangian Grassmannian is its own symplectic complement. -/
@[simp]
theorem orthogonal_eq (Λ : LagrangianGrassmannian ω) : ω.orthogonal Λ = Λ :=
  Λ.isLagrangian.orthogonal_eq

@[simp]
theorem coe_mk (L : Submodule ℝ V) (h : ω.IsLagrangian L) :
    ((⟨L, h⟩ : LagrangianGrassmannian ω) : Submodule ℝ V) = L :=
  rfl

@[simp]
theorem coe_set_mk (L : Submodule ℝ V) (h : ω.IsLagrangian L) :
    ((⟨L, h⟩ : LagrangianGrassmannian ω) : Set V) = L :=
  rfl

@[simp]
theorem mem_mk {L : Submodule ℝ V} {h : ω.IsLagrangian L} {x : V} :
    x ∈ (⟨L, h⟩ : LagrangianGrassmannian ω) ↔ x ∈ L :=
  Iff.rfl

@[simp]
theorem mk_toSubmodule (Λ : LagrangianGrassmannian ω) :
    (⟨Λ, Λ.isLagrangian⟩ : LagrangianGrassmannian ω) = Λ :=
  rfl

/-- Every symplectic vector space has a Lagrangian subspace, in any dimension. -/
instance instNonempty : Nonempty (LagrangianGrassmannian ω) :=
  let ⟨L, _, hL⟩ := (TauCeti.SymplecticForm.isIsotropic_bot (ω := ω)).exists_le_isLagrangian
  ⟨⟨L, hL⟩⟩

/-- In finite dimension, two Lagrangian subspaces are complementary exactly when they meet only
in `0`: each has half the dimension of `V`. -/
theorem isCompl_iff_disjoint [FiniteDimensional ℝ V] (Λ Λ' : LagrangianGrassmannian ω) :
    IsCompl (Λ : Submodule ℝ V) Λ' ↔ Disjoint (Λ : Submodule ℝ V) Λ' :=
  Submodule.isCompl_iff_disjoint _ _ <| by
    have h := Λ.isLagrangian.two_mul_finrank
    have h' := Λ'.isLagrangian.two_mul_finrank
    omega

end LagrangianGrassmannian

end SymplecticGeometry

end
