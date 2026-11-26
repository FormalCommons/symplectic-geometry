/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import SymplecticGeometry.Topology.ComplexProjectiveSpace.Homeomorph
import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact

/-!
# Complex projective spaces are simply connected

Tau Ceti proves that its sphere-quotient model `ComplexProjectiveSpace m` of `ℂℙᵐ` is simply
connected (`TauCeti.ComplexProjectiveSpace.instSimplyConnectedSpace`). This file carries that
along the homeomorphism `Projectivization.complexProjectiveSpaceHomeomorph` to the
projectivization `ℙ ℂ V` of every nonzero finite-dimensional Hausdorff complex topological vector
space `V`, as an instance.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

/-- The projectivization `ℙ ℂ V` of a nonzero finite-dimensional Hausdorff complex topological
vector space `V` is simply connected. -/
instance instSimplyConnectedSpaceComplex {V : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V]
    [FiniteDimensional ℂ V] [Nontrivial V] : SimplyConnectedSpace (ℙ ℂ V) := by
  obtain ⟨m, hV⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℂ) (M := V)).ne'
  exact (complexProjectiveSpaceHomeomorph hV).toHomotopyEquiv.simplyConnectedSpace_iff.1
    inferInstance

end Projectivization

end
