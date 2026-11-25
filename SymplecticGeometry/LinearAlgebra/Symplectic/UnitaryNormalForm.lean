/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Compatible
public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology

/-!
# Unitary normal forms with uniform bounds

Let `V` be a real normed space of dimension `2 n` with a symplectic form `ω`. For each complex
structure `J` compatible with `ω`, some linear isomorphism `Ψ : ℝ²ⁿ ≃ V` from the standard model
has `Ψ^* ω = ω₀` and `Ψ J₀ = J Ψ`
(`SymplecticGeometry.compatible_iff_exists_isSymplectomorphism_stdForm`). This file bounds the
norms of `Ψ` and `Ψ⁻¹` uniformly along a family of such structures.

Such a `Ψ` is an isometry from the Euclidean norm to the metric `g_J = ω(·, J ·)`
(`SymplecticGeometry.associatedBilinForm_apply_apply_eq_inner`), so constants `a > 0` and `b`
with `a ‖v‖² ≤ g_J(v, v) ≤ b ‖v‖²` give `‖Ψ‖ ≤ 1 / √a` and `‖Ψ⁻¹‖ ≤ √b`. For a family `J x`
that is continuous in the operator norm on a compact set, Tau Ceti's
`TauCeti.SymplecticForm.exists_pos_forall_mul_norm_sq_le_associatedBilinForm` gives such
constants uniformly in `x`.

## Main results

* `SymplecticGeometry.norm_le_of_mul_norm_sq_le_associatedBilinForm` and
  `SymplecticGeometry.norm_symm_le_of_associatedBilinForm_le_mul_norm_sq`: the bounds on `‖Ψ‖`
  and `‖Ψ⁻¹‖` for one structure.
* `SymplecticGeometry.exists_forall_isSymplectomorphism_stdForm_norm_le`: for a continuous family
  of compatible structures on a compact set, one constant `C` bounds `‖Ψ‖` and `‖Ψ⁻¹‖` for a
  choice of `Ψ` at every point.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.5.
-/

public section

namespace SymplecticGeometry

open TauCeti TauCeti.SymplecticForm Module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ω : SymplecticForm V}
  {J : AlmostComplexStructure V} {ι : Type*} [Fintype ι]

/-- Let `Ψ : ℝ²ⁿ ≃ V` have `Ψ^* ω = ω₀` and `Ψ J₀ = J Ψ`. If `a ‖v‖² ≤ ω(v, J v)` for all `v`,
with `a > 0`, then `‖Ψ‖ ≤ 1 / √a`. -/
theorem norm_le_of_mul_norm_sq_le_associatedBilinForm {Ψ : StdSpace ι ≃L[ℝ] V}
    (hΨ : IsSymplectomorphism (stdForm ι) ω Ψ.toLinearEquiv)
    (hJ : IsComplexLinearMap (stdComplexStructure ι) J Ψ.toLinearMap) {a : ℝ} (ha : 0 < a)
    (h : ∀ v, a * ‖v‖ ^ 2 ≤ ω.associatedBilinForm J v v) :
    ‖(Ψ : StdSpace ι →L[ℝ] V)‖ ≤ (√a)⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  have hu := h (Ψ u)
  rw [← Ψ.coe_toLinearEquiv, associatedBilinForm_apply_apply_eq_inner hΨ hJ,
    real_inner_self_eq_norm_sq, ← Real.sq_sqrt ha.le, ← mul_pow] at hu
  rw [ContinuousLinearEquiv.coe_coe, inv_mul_eq_div, le_div_iff₀' (Real.sqrt_pos.2 ha)]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg u) two_ne_zero).1 hu

/-- Let `Ψ : ℝ²ⁿ ≃ V` have `Ψ^* ω = ω₀` and `Ψ J₀ = J Ψ`. If `ω(v, J v) ≤ b ‖v‖²` for all `v`,
then `‖Ψ⁻¹‖ ≤ √b`. -/
theorem norm_symm_le_of_associatedBilinForm_le_mul_norm_sq {Ψ : StdSpace ι ≃L[ℝ] V}
    (hΨ : IsSymplectomorphism (stdForm ι) ω Ψ.toLinearEquiv)
    (hJ : IsComplexLinearMap (stdComplexStructure ι) J Ψ.toLinearMap) {b : ℝ}
    (h : ∀ v, ω.associatedBilinForm J v v ≤ b * ‖v‖ ^ 2) :
    ‖(Ψ.symm : V →L[ℝ] StdSpace ι)‖ ≤ √b := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg b) fun v ↦ ?_
  have hv := h v
  rw [← Ψ.apply_symm_apply v, ← Ψ.coe_toLinearEquiv, associatedBilinForm_apply_apply_eq_inner hΨ hJ,
    real_inner_self_eq_norm_sq, Ψ.coe_toLinearEquiv, Ψ.apply_symm_apply] at hv
  rw [ContinuousLinearEquiv.coe_coe, ← Real.sqrt_sq (norm_nonneg v),
    ← Real.sqrt_mul' b (sq_nonneg _),
    ← Real.sqrt_sq (norm_nonneg (Ψ.symm v))]
  exact Real.sqrt_le_sqrt hv

/-- **Uniform unitary normal form.** Let `V` have dimension `2 n`, with `n` the cardinality of
`ι`, and let `J x` be complex structures on `V` compatible with `ω`, for `x` in a compact set `K`,
that depend continuously on `x` in the operator norm. Then one constant `C` works for all
`x ∈ K`: some linear isomorphism `Ψ : ℝ²ⁿ ≃ V` has `Ψ^* ω = ω₀`, `Ψ J₀ = J x Ψ`, `‖Ψ‖ ≤ C` and
`‖Ψ⁻¹‖ ≤ C`. -/
theorem exists_forall_isSymplectomorphism_stdForm_norm_le [FiniteDimensional ℝ V]
    (hι : finrank ℝ V = 2 * Fintype.card ι) {X : Type*} [TopologicalSpace X]
    {J : X → AlmostComplexStructure V} {K : Set X} (hK : IsCompact K)
    (hJ : ContinuousOn (fun x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap) K)
    (hJc : ∀ x ∈ K, ω.Compatible (J x)) :
    ∃ C, ∀ x ∈ K, ∃ Ψ : StdSpace ι ≃L[ℝ] V,
      IsSymplectomorphism (stdForm ι) ω Ψ.toLinearEquiv ∧
      IsComplexLinearMap (stdComplexStructure ι) (J x) Ψ.toLinearMap ∧
      ‖(Ψ : StdSpace ι →L[ℝ] V)‖ ≤ C ∧ ‖(Ψ.symm : V →L[ℝ] StdSpace ι)‖ ≤ C := by
  obtain ⟨a, ha, b, -, hab⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm hK hJ
    fun x hx ↦ (hJc x hx).tames
  refine ⟨max (√a)⁻¹ √b, fun x hx ↦ ?_⟩
  obtain ⟨Ψ, hΨ, hΨJ⟩ := (compatible_iff_exists_isSymplectomorphism_stdForm hι).1 (hJc x hx)
  refine ⟨Ψ.toContinuousLinearEquiv, hΨ, hΨJ, ?_, ?_⟩
  · exact (norm_le_of_mul_norm_sq_le_associatedBilinForm hΨ hΨJ ha
      fun v ↦ (hab x hx v).1).trans (le_max_left _ _)
  · exact (norm_symm_le_of_associatedBilinForm_le_mul_norm_sq hΨ hΨJ
      fun v ↦ (hab x hx v).2).trans (le_max_right _ _)

end SymplecticGeometry

end
