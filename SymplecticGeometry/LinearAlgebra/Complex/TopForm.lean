/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Top forms on a real plane with a complex structure

Let `W` be a real vector space of dimension two with a complex structure `j`. For `e ≠ 0` the
pair `(e, j e)` is a basis of `W` (`TauCeti.AlmostComplexStructure.exists_basis_coe_eq`). So an
alternating form of degree two on `W` is determined by its value on `(e, j e)`
(`TauCeti.AlmostComplexStructure.alternatingMap_ext`), and the ratio of two such forms takes the
same value on every such pair (`TauCeti.AlmostComplexStructure.alternatingMap_apply_div_apply_eq`).
Neither statement needs an orientation of `W`.

The proofs follow those of Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.apply_basis_nonneg_of_forall_nonneg`: a top form is its
value on a basis times the determinant of that basis (`AlternatingMap.eq_smul_basis_det`).

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  §2.2.
-/

public section

open Module

noncomputable section

namespace TauCeti

namespace AlmostComplexStructure

variable {W : Type*} [AddCommGroup W] [Module ℝ W] (j : AlmostComplexStructure W)

/-- On a real plane, every pair `(e, j e)` with `e ≠ 0` is a basis. -/
theorem exists_basis_coe_eq (h2 : finrank ℝ W = 2) {e : W} (he : e ≠ 0) :
    ∃ b : Basis (Fin 2) ℝ W, ⇑b = ![e, j e] :=
  ⟨basisOfLinearIndependentOfCardEqFinrank (j.linearIndependent_pair he) (by simp [h2]),
    coe_basisOfLinearIndependentOfCardEqFinrank _ _⟩

/-- On a real plane, two alternating forms of degree two that agree on one pair `(e, j e)` with
`e ≠ 0` are equal. -/
theorem alternatingMap_ext (h2 : finrank ℝ W = 2) {e : W} (he : e ≠ 0)
    {η μ : W [⋀^Fin 2]→ₗ[ℝ] ℝ} (h : η ![e, j e] = μ ![e, j e]) : η = μ := by
  obtain ⟨b, hb⟩ := j.exists_basis_coe_eq h2 he
  rw [η.eq_smul_basis_det b, μ.eq_smul_basis_det b, hb, h]

/-- On a real plane, the ratio of two alternating forms of degree two takes the same value on all
pairs `(e, j e)` with `e ≠ 0`. -/
theorem alternatingMap_apply_div_apply_eq (h2 : finrank ℝ W = 2) {e e' : W} (he : e ≠ 0)
    (he' : e' ≠ 0) (η μ : W [⋀^Fin 2]→ₗ[ℝ] ℝ) :
    η ![e', j e'] / μ ![e', j e'] = η ![e, j e] / μ ![e, j e] := by
  obtain ⟨b, hb⟩ := j.exists_basis_coe_eq h2 he
  obtain ⟨b', hb'⟩ := j.exists_basis_coe_eq h2 he'
  rw [← hb, ← hb', η.eq_smul_basis_det b, μ.eq_smul_basis_det b]
  simp only [smul_apply, smul_eq_mul, Basis.det_self, mul_one]
  exact mul_div_mul_right _ _ (b.isUnit_det b').ne_zero

end AlmostComplexStructure

end TauCeti
