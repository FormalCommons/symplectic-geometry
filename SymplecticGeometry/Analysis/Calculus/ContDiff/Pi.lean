/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of `Function.update` in the family and the new value

For a finite index type `ι`, the map `x ↦ Function.update (f x) i (g x)` is `C^n` as soon as
both `f : E → ∀ i, F' i` and `g : E → F' i` are. Mathlib's `contDiff_update` covers only the
dependence on the new value with the family fixed, and Tau Ceti's `ContDiff.update_self` only
the case where `f` is the identity. The proofs go coordinatewise through `contDiffWithinAt_pi`,
as those of `contDiff_update` and `ContDiff.update_self` do.

## Main results

* `ContDiffWithinAt.update`, `ContDiffAt.update`, `ContDiffOn.update`, `ContDiff.update`: the
  update of a `C^n` family at one index by a `C^n` value is `C^n`.
-/

public section

open Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {ι : Type*} [Fintype ι] [DecidableEq ι] {F' : ι → Type*}
  [∀ i, NormedAddCommGroup (F' i)] [∀ i, NormedSpace 𝕜 (F' i)] {n : WithTop ℕ∞}
  {f : E → ∀ i, F' i} {s : Set E} {x : E}

/-- Updating a family that is `C^n` within `s` at `x`, at one index, by a value that is `C^n`
within `s` at `x`, gives a map that is `C^n` within `s` at `x`. -/
@[fun_prop]
theorem ContDiffWithinAt.update (hf : ContDiffWithinAt 𝕜 n f s x) (i : ι) {g : E → F' i}
    (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun y ↦ update (f y) i (g y)) s x := by
  refine contDiffWithinAt_pi.2 fun j ↦ ?_
  rcases eq_or_ne j i with rfl | h
  · simpa using hg
  · simpa [update_of_ne h] using contDiffWithinAt_pi.1 hf j

/-- Updating a family that is `C^n` at `x`, at one index, by a value that is `C^n` at `x`,
gives a map that is `C^n` at `x`. -/
@[fun_prop]
theorem ContDiffAt.update (hf : ContDiffAt 𝕜 n f x) (i : ι) {g : E → F' i}
    (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun y ↦ update (f y) i (g y)) x :=
  ContDiffWithinAt.update hf i hg

/-- Updating a family that is `C^n` on `s`, at one index, by a value that is `C^n` on `s`,
gives a map that is `C^n` on `s`. -/
@[fun_prop]
theorem ContDiffOn.update (hf : ContDiffOn 𝕜 n f s) (i : ι) {g : E → F' i}
    (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun y ↦ update (f y) i (g y)) s :=
  fun y hy ↦ (hf y hy).update i (hg y hy)

/-- Updating a `C^n` family, at one index, by a `C^n` value gives a `C^n` map. -/
@[fun_prop]
theorem ContDiff.update (hf : ContDiff 𝕜 n f) (i : ι) {g : E → F' i} (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun y ↦ update (f y) i (g y) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ hf.contDiffAt.update i hg.contDiffAt

end
