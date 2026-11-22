/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Pi
public import TauCeti.Topology.PiCurry

/-!
# Splitting off the `none` coordinate of a product over `Option ι`

`ContinuousLinearEquiv.piOptionEquivProd` is Mathlib's `LinearEquiv.piOptionEquivProd`, the
identification of `Π i : Option ι, M i` with `M none × Π i : ι, M (some i)`, as a continuous
linear equivalence for the product topologies. Its topological part is Tau Ceti's homeomorphism
`TauCeti.piOptionEquivProdHomeomorph`, put together with the linear part as Mathlib does for
`ContinuousLinearEquiv.sumPiEquivProdPi`.
-/

public section

namespace ContinuousLinearEquiv

variable (R : Type*) [Semiring R] {ι : Type*} (M : Option ι → Type*) [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)]

/-- The continuous linear equivalence that sends `f : Π i : Option ι, M i` to the pair of its
value at `none` and the function `i ↦ f (some i)` on `ι`. -/
def piOptionEquivProd : ((i : Option ι) → M i) ≃L[R] M none × ((i : ι) → M (some i)) where
  __ := LinearEquiv.piOptionEquivProd (R := R) (M := M)
  -- The body of Tau Ceti's homeomorphism is not exposed, so its continuity is transported
  -- along its apply lemmas. Mathlib states no apply lemma for the inverse of
  -- `LinearEquiv.piOptionEquivProd`, so its coordinates are computed by `rfl`.
  continuous_toFun := (TauCeti.piOptionEquivProdHomeomorph M).continuous.congr
    (TauCeti.piOptionEquivProdHomeomorph_apply M)
  continuous_invFun := (TauCeti.piOptionEquivProdHomeomorph M).symm.continuous.congr
    fun p ↦ funext fun i ↦ by
      cases i <;> simp only [TauCeti.piOptionEquivProdHomeomorph_symm_apply_none,
        TauCeti.piOptionEquivProdHomeomorph_symm_apply_some] <;> rfl

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
