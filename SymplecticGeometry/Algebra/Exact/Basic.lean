/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# Splittings of exact sequences

Complements to Mathlib's `Mathlib/Algebra/Exact/Basic.lean`.

## Main results

* `Function.Exact.splitSurjectiveEquiv_symm_apply`: for an exact sequence `0 → M → N → P` with
  maps `f` and `g`, and a section `l` of `g`, the isomorphism `M × P ≃ N` that
  `Function.Exact.splitSurjectiveEquiv` attaches to `l` sends `(x, p)` to `f x + l p`.
-/

public section

namespace Function.Exact

variable {R M N P : Type*} [Semiring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}

/-- The splitting `M × P ≃ N` of an exact sequence `0 → M → N → P` given by a section `l` of `g`
sends `(x, p)` to `f x + l p`. -/
@[simp]
theorem splitSurjectiveEquiv_symm_apply (h : Function.Exact f g) (hf : Function.Injective f)
    (l : { l : P →ₗ[R] N // g ∘ₗ l = .id }) (x : M × P) :
    (h.splitSurjectiveEquiv hf l).val.symm x = f x.1 + l.val x.2 :=
  (rfl)

end Function.Exact

end
