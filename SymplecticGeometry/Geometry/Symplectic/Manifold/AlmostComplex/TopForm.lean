/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Top forms on the tangent planes of an almost complex surface

Let `j` be an almost complex structure on a manifold `C` modelled on a real vector space of
dimension two. For a nonzero tangent vector `e`, the pair `(e, j e)` is a basis of the tangent
plane, so a top form on that plane is determined by its value on `(e, j e)`
(`TauCeti.SmoothAlmostComplexStructure.topForm_ext`), and the ratio of two top forms takes the
same value on every such pair
(`TauCeti.SmoothAlmostComplexStructure.topForm_apply_div_apply_eq`). Neither statement needs an
orientation of `C`.

The proofs follow those of Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.apply_basis_nonneg_of_forall_nonneg`, with the basis
`(e, j e)` built from the dimension of the model in place of Tau Ceti's `complexFrame`, which
takes it from an orientation.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  §2.2.
-/

public section

open Module
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

/-- The tangent spaces of a manifold modelled on a vector space of positive dimension are
nontrivial. -/
theorem nontrivial_tangentSpace_of_finrank_pos {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (h : 0 < finrank 𝕜 E) (x : M) : Nontrivial (TangentSpace I x) :=
  Module.nontrivial_of_finrank_pos (R := 𝕜) (by rwa [finrank_tangentSpace])

namespace SmoothAlmostComplexStructure

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  (j : SmoothAlmostComplexStructure I C) {c : C}

/-- On a surface, every pair `(e, j e)` with `e ≠ 0` is a basis of the tangent plane. -/
theorem exists_basis_coe_eq (h2 : finrank ℝ E = 2) {e : TangentSpace I c} (he : e ≠ 0) :
    ∃ b : Basis (Fin 2) ℝ (TangentSpace I c), ⇑b = ![e, j c e] :=
  ⟨basisOfLinearIndependentOfCardEqFinrank
      ((j.almostComplexStructureAt c).linearIndependent_pair he) (by simp [h2]),
    by rw [coe_basisOfLinearIndependentOfCardEqFinrank, almostComplexStructureAt_apply]⟩

/-- On a surface, two top forms on a tangent plane that agree on one pair `(e, j e)` with
`e ≠ 0` are equal. -/
theorem topForm_ext (h2 : finrank ℝ E = 2) {e : TangentSpace I c} (he : e ≠ 0)
    {η μ : TangentSpace I c [⋀^Fin 2]→L[ℝ] ℝ} (h : η ![e, j c e] = μ ![e, j c e]) : η = μ := by
  obtain ⟨b, hb⟩ := j.exists_basis_coe_eq h2 he
  rw [← sub_eq_zero, ← (η - μ).map_basis_eq_zero_iff b, hb, ContinuousAlternatingMap.sub_apply, h,
    sub_self]

/-- On a surface, the ratio of two top forms on a tangent plane takes the same value on all pairs
`(e, j e)` with `e ≠ 0`. -/
theorem topForm_apply_div_apply_eq (h2 : finrank ℝ E = 2) {e e' : TangentSpace I c} (he : e ≠ 0)
    (he' : e' ≠ 0) (η μ : TangentSpace I c [⋀^Fin 2]→L[ℝ] ℝ) :
    η ![e', j c e'] / μ ![e', j c e'] = η ![e, j c e] / μ ![e, j c e] := by
  obtain ⟨b, hb⟩ := j.exists_basis_coe_eq h2 he
  obtain ⟨b', hb'⟩ := j.exists_basis_coe_eq h2 he'
  rw [← hb, ← hb', η.apply_eq_det_mul b, μ.apply_eq_det_mul b]
  exact mul_div_mul_left _ _ (b.isUnit_det b').ne_zero

end SmoothAlmostComplexStructure

end TauCeti
