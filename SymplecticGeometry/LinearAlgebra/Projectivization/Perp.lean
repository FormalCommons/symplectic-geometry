/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Topology.Algebra.Projectivization

/-!
# The quarter turn `(s, t) ↦ (t, -s)` of a plane and the line map it induces

On the plane `Fin 2 → R` over a ring `R`, the map `(s, t) ↦ (t, -s)` is a linear
automorphism. Over a field `K`, a nonzero vector `w` and its image span the two lines that pair
under the dot product: the vectors `z` with `w ⬝ᵥ z = 0` are exactly the multiples of
`(w₁, -w₀)`. On the projective line this gives the involution `[s : t] ↦ [t : -s]`, which sends
the point `ℓ` to the line of the vectors orthogonal to `ℓ` for the dot product.

## Main definitions

* `SymplecticGeometry.perpLinearEquiv R`: the linear automorphism `(s, t) ↦ (t, -s)` of
  `Fin 2 → R`, with inverse `(s, t) ↦ (-t, s)`.
* `SymplecticGeometry.perpLine ℓ`: the image of `ℓ ∈ ℙ K (Fin 2 → K)` under
  `perpLinearEquiv K`, through `Projectivization.map`, that is `[s : t] ↦ [t : -s]`.

## Main results

* `SymplecticGeometry.dotProduct_perpLinearEquiv_self`: over a commutative ring, `w` is
  orthogonal to `(w₁, -w₀)` for the dot product.
* `SymplecticGeometry.perpLine_perpLine`, `SymplecticGeometry.continuous_perpLine`: `perpLine`
  is an involution, and it is continuous when negation on `K` is.
* `SymplecticGeometry.mem_span_singleton_perpLinearEquiv_iff`: for `w ≠ 0`, a vector `z` is a
  multiple of `(w₁, -w₀)` exactly when `w ⬝ᵥ z = 0`.
* `SymplecticGeometry.mem_submodule_perpLine_mk_iff`,
  `SymplecticGeometry.mem_submodule_perpLine_iff`: the same for the line `perpLine ℓ`.
-/

public section

open Projectivization Module
open scoped LinearAlgebra.Projectivization Matrix

namespace SymplecticGeometry

/-! ### The linear automorphism `(s, t) ↦ (t, -s)` -/

section Ring

variable (R : Type*) [Ring R]

/-- The linear automorphism `(s, t) ↦ (t, -s)` of the plane `Fin 2 → R`; its inverse is
`(s, t) ↦ (-t, s)`. -/
def perpLinearEquiv : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R) where
  toFun w := ![w 1, -w 0]
  invFun w := ![-w 1, w 0]
  map_add' v w := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' a w := by ext i; fin_cases i <;> simp
  left_inv w := by ext i; fin_cases i <;> simp
  right_inv w := by ext i; fin_cases i <;> simp

variable {R}

theorem perpLinearEquiv_apply (w : Fin 2 → R) : perpLinearEquiv R w = ![w 1, -w 0] :=
  (rfl)

theorem perpLinearEquiv_symm_apply (w : Fin 2 → R) :
    (perpLinearEquiv R).symm w = ![-w 1, w 0] :=
  (rfl)

@[simp]
theorem perpLinearEquiv_apply_zero (w : Fin 2 → R) : perpLinearEquiv R w 0 = w 1 :=
  (rfl)

@[simp]
theorem perpLinearEquiv_apply_one (w : Fin 2 → R) : perpLinearEquiv R w 1 = -w 0 :=
  (rfl)

@[simp]
theorem perpLinearEquiv_perpLinearEquiv (w : Fin 2 → R) :
    perpLinearEquiv R (perpLinearEquiv R w) = -w := by
  ext i; fin_cases i <;> simp

@[fun_prop, continuity]
theorem continuous_perpLinearEquiv [TopologicalSpace R] [ContinuousNeg R] :
    Continuous (perpLinearEquiv R) := by
  rw [show ⇑(perpLinearEquiv R) = fun w ↦ ![w 1, -w 0] from funext perpLinearEquiv_apply]
  fun_prop

end Ring

/-- A vector `w` of the plane is orthogonal to its image `(w₁, -w₀)` for the dot product. -/
theorem dotProduct_perpLinearEquiv_self {R : Type*} [CommRing R] (w : Fin 2 → R) :
    w ⬝ᵥ perpLinearEquiv R w = 0 := by
  simp [Matrix.vec2_dotProduct]; ring

/-! ### The orthogonal line -/

section Field

variable {K : Type*} [Field K]

/-- For `w ≠ 0`, the vectors `z` with `w ⬝ᵥ z = 0` are the multiples of `(w₁, -w₀)`. -/
theorem mem_span_singleton_perpLinearEquiv_iff {w : Fin 2 → K} (hw : w ≠ 0) (z : Fin 2 → K) :
    z ∈ K ∙ perpLinearEquiv K w ↔ w ⬝ᵥ z = 0 := by
  set f : Dual K (Fin 2 → K) := dotProductEquiv K (Fin 2) w
  have hf : f ≠ 0 := by simpa [f] using hw
  have hk : LinearMap.ker f = K ∙ perpLinearEquiv K w :=
    eq_span_singleton_of_mem_of_finrank_eq_one
      (by have := f.finrank_ker_add_one_of_ne_zero hf; simp at this; omega)
      (by simpa [f] using dotProduct_perpLinearEquiv_self w) (by simpa using hw)
  simp [← hk, f]

/-- The line map `[s : t] ↦ [t : -s]` of `ℙ K (Fin 2 → K)`, induced by `perpLinearEquiv K`. -/
noncomputable def perpLine (ℓ : ℙ K (Fin 2 → K)) : ℙ K (Fin 2 → K) :=
  map (perpLinearEquiv K).toLinearMap (perpLinearEquiv K).injective ℓ

@[simp]
theorem perpLine_mk (w : Fin 2 → K) (hw : w ≠ 0) :
    perpLine (mk K w hw) =
      mk K (perpLinearEquiv K w) ((LinearEquiv.map_ne_zero_iff _).2 hw) :=
  map_mk _ _ _ _

@[simp]
theorem perpLine_perpLine (ℓ : ℙ K (Fin 2 → K)) : perpLine (perpLine ℓ) = ℓ := by
  induction ℓ using ind with
  | h w hw =>
    rw [perpLine_mk, perpLine_mk, mk_eq_mk_iff']
    exact ⟨-1, by simp⟩

theorem perpLine_involutive : Function.Involutive (perpLine (K := K)) :=
  perpLine_perpLine

@[fun_prop, continuity]
theorem continuous_perpLine [TopologicalSpace K] [ContinuousNeg K] :
    Continuous (perpLine (K := K)) :=
  continuous_map (perpLinearEquiv K).injective continuous_perpLinearEquiv

/-- A vector `z` lies on the line `perpLine (mk K w hw)` exactly when `w ⬝ᵥ z = 0`. -/
theorem mem_submodule_perpLine_mk_iff {w : Fin 2 → K} (hw : w ≠ 0) (z : Fin 2 → K) :
    z ∈ (perpLine (mk K w hw)).submodule ↔ w ⬝ᵥ z = 0 := by
  rw [perpLine_mk, submodule_mk, mem_span_singleton_perpLinearEquiv_iff hw]

/-- A vector `z` lies on the line `perpLine ℓ` exactly when `ℓ.rep ⬝ᵥ z = 0`. -/
theorem mem_submodule_perpLine_iff (ℓ : ℙ K (Fin 2 → K)) (z : Fin 2 → K) :
    z ∈ (perpLine ℓ).submodule ↔ ℓ.rep ⬝ᵥ z = 0 := by
  conv_lhs => rw [← mk_rep ℓ]
  exact mem_submodule_perpLine_mk_iff ℓ.rep_ne_zero z

end Field

end SymplecticGeometry

end
