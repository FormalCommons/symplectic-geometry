/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Dimension of a subspace after restricting scalars

For a tower of scalars `F → K → V` and a `K`-subspace `W` of `V`, the `F`-dimension of `W`,
seen as an `F`-subspace, is the `F`-dimension of `K` times the `K`-dimension of `W`
(`Submodule.finrank_restrictScalars`). This is the tower law `Module.finrank_mul_finrank`
transported along `Submodule.restrictScalarsEquiv`.
-/

public section

namespace Submodule

/-- **Tower law for a subspace.** A `K`-subspace `W` of `V`, seen as an `F`-subspace, has
`F`-dimension `finrank F K * finrank K W`. -/
theorem finrank_restrictScalars {F K V : Type*} [DivisionRing F] [DivisionRing K] [Module F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V] (W : Submodule K V) :
    Module.finrank F (W.restrictScalars F) = Module.finrank F K * Module.finrank K W :=
  ((restrictScalarsEquiv F K V W).restrictScalars F).finrank_eq.trans
    (Module.finrank_mul_finrank F K W).symm

end Submodule

end
