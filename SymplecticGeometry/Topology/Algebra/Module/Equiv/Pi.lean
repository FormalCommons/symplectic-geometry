/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Splitting off the `none` coordinate of a product over `Option ι`

`ContinuousLinearEquiv.piOptionEquivProd` is Mathlib's `LinearEquiv.piOptionEquivProd`, the
identification of `Π i : Option ι, M i` with `M none × Π i : ι, M (some i)`, as a continuous
linear equivalence for the product topologies.
-/

public section

namespace ContinuousLinearEquiv

variable (R : Type*) [Semiring R] {ι : Type*} (M : Option ι → Type*) [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)]

/-- `Equiv.piOptionEquivProd` as a continuous linear equivalence: a family indexed by `Option ι`
is its `none` coordinate together with the family of its `some` coordinates. -/
def piOptionEquivProd : ((i : Option ι) → M i) ≃L[R] M none × ((i : ι) → M (some i)) where
  __ := LinearEquiv.piOptionEquivProd (R := R) (M := M)
  continuous_toFun :=
    (continuous_apply none).prodMk (continuous_pi fun i ↦ continuous_apply (some i))
  continuous_invFun := continuous_pi fun i ↦ by
    cases i with
    | none => exact continuous_fst
    | some i => exact (continuous_apply i).comp continuous_snd

variable {R M}

@[simp]
theorem piOptionEquivProd_apply (f : (i : Option ι) → M i) :
    piOptionEquivProd R M f = (f none, fun i ↦ f (some i)) :=
  (rfl)

@[simp]
theorem piOptionEquivProd_symm_apply_none (p : M none × ((i : ι) → M (some i))) :
    (piOptionEquivProd R M).symm p none = p.1 :=
  (rfl)

@[simp]
theorem piOptionEquivProd_symm_apply_some (p : M none × ((i : ι) → M (some i))) (i : ι) :
    (piOptionEquivProd R M).symm p (some i) = p.2 i :=
  (rfl)

end ContinuousLinearEquiv

end
