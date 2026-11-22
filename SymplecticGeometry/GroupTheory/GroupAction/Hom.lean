/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Equivariant maps out of the acting monoid

A map `f : R → M` that commutes with the action of `R`, with `R` acting on itself by left
multiplication, is determined by its value at `1`: `f r = r • f 1` (`map_eq_smul_map_one`). This
covers linear maps, linear equivalences and linear isometries out of the scalar ring, such as a
complex-linear map out of `ℂ`.

## Main results

* `map_eq_smul_map_one`: an equivariant map `f` out of `R` sends `r` to `r • f 1`.
-/

public section

/-- A map `f` out of `R` that commutes with the action of `R` on itself by left multiplication is
the action on its value at `1`: `f r = r • f 1`. -/
theorem map_eq_smul_map_one {R M F : Type*} [MulOneClass R] [SMul R M] [FunLike F R M]
    [MulActionHomClass F R R M] (f : F) (r : R) : f r = r • f 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]

end
