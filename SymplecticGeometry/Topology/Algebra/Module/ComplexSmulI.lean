/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# Multiplication by `i` and the almost complex structure of a complex module

On a complex module with a compatible real structure, Tau Ceti gives multiplication by `i` in two
forms: as a continuous real-linear equivalence, `Complex.smulIEquiv X`, and as the endomorphism of
the almost complex structure `TauCeti.AlmostComplexStructure.ofComplexModule X`. This file shows
that the two have the same underlying real-linear map
(`Complex.coe_smulIEquiv_eq_ofComplexModule`), so that results stated for one apply to the other,
and that `Complex.smulIEquiv X` squares to `-1` (`Complex.smulIEquiv_comp_smulIEquiv`).
-/

public section

/-- As a real-linear map, multiplication by `i` as a continuous real-linear equivalence,
`Complex.smulIEquiv X`, is the endomorphism of Tau Ceti's almost complex structure
`TauCeti.AlmostComplexStructure.ofComplexModule X`. -/
theorem Complex.coe_smulIEquiv_eq_ofComplexModule (X : Type*) [AddCommGroup X]
    [TopologicalSpace X] [Module ℝ X] [Module ℂ X] [IsScalarTower ℝ ℂ X] [ContinuousConstSMul ℂ X] :
    ((Complex.smulIEquiv X : X →L[ℝ] X) : X →ₗ[ℝ] X) =
      (TauCeti.AlmostComplexStructure.ofComplexModule X).toLinearMap := by
  ext x
  simp [TauCeti.AlmostComplexStructure.ofComplexModule_apply]

/-- Multiplication by `i`, as a continuous real-linear map `Complex.smulIEquiv X`, squares to
`-1`. -/
theorem Complex.smulIEquiv_comp_smulIEquiv (X : Type*) [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [Module ℝ X] [Module ℂ X] [IsScalarTower ℝ ℂ X]
    [ContinuousConstSMul ℂ X] :
    (Complex.smulIEquiv X : X →L[ℝ] X) ∘L (Complex.smulIEquiv X : X →L[ℝ] X) = -1 := by
  ext x
  simp [smul_smul]

end
