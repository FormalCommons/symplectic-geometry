/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import SymplecticGeometry.Analysis.CStarAlgebra.Matrix
import SymplecticGeometry.Analysis.Matrix.SymplecticGroup.Connected
import SymplecticGeometry.Geometry.Symplectic.LinearMoser
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix

/-!
# Smooth paths of symplectic frames

A `Cⁿ⁺¹` path `t ↦ ω t` of nondegenerate skew forms on `StdSpace ι` that starts at the standard
form `ω₀ = stdForm ι` is trivialized by a `Cⁿ⁺¹` path of frames `P t`, that is,
`ω t (P t v) (P t w) = ω₀ v w`, which starts at the identity and ends at any prescribed frame `B`
of `ω 1`.

* `SymplecticGeometry.exists_contDiff_path_apply_eq_stdForm`: such a path `P` exists, of class
  `Cⁿ⁺¹`, with `P 0 = 1` and `P 1 = B`.

The linear Moser lemma `exists_contDiff_isUnit_apply_eq` gives a `Cⁿ⁺¹` path `Ψ` with
`Ψ 0 = 1` and `(Ψ t)^* (ω t) = ω₀`. The map `(Ψ 1)⁻¹ B` preserves `ω₀`, so its matrix is symplectic
(`mem_symplecticGroup_iff_forall_stdForm`), and `Matrix.exists_contDiff_path_symplecticGroup`
joins `1` to it by a smooth path `S` of symplectic matrices. Then `P t = Ψ t ∘ S t`. This is the
linear algebra of the frames along a path of centres, for the case of radius zero of
McDuff–Salamon, Theorem 3.3.1.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace SymplecticGeometry

variable {ι : Type*} [Fintype ι]

open scoped Matrix.Norms.Elementwise in
/-- **Smooth symplectic frames along a path of forms.** A `Cⁿ⁺¹` path `t ↦ ω t` of nondegenerate
skew forms on `StdSpace ι` with `ω 0 = ω₀` is trivialized by a `Cⁿ⁺¹` path `P` of linear maps,
`ω t (P t v) (P t w) = ω₀ v w`, that starts at `P 0 = 1` and ends at any given `B` with
`B^* (ω 1) = ω₀`. The smooth case is `n = ⊤`. -/
theorem exists_contDiff_path_apply_eq_stdForm {n : ℕ∞}
    {ω : ℝ → StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] ℝ} (hω : ContDiff ℝ (n + 1) ω)
    (hskew : ∀ t v w, ω t v w = -ω t w v) (hnd : ∀ t, (ω t).toBilinForm.Nondegenerate)
    (h₀ : ∀ v w, ω 0 v w = stdForm ι v w)
    {B : StdSpace ι →L[ℝ] StdSpace ι} (hB : ∀ v w, ω 1 (B v) (B w) = stdForm ι v w) :
    ∃ P : ℝ → StdSpace ι →L[ℝ] StdSpace ι, ContDiff ℝ (n + 1) P ∧ P 0 = 1 ∧ P 1 = B ∧
      ∀ t v w, ω t (P t v) (P t w) = stdForm ι v w := by
  classical
  obtain ⟨Ψ, hΨ, hΨ0, hΨu, hΨω⟩ := exists_contDiff_isUnit_apply_eq hω hskew hnd
  obtain ⟨u, hu⟩ := hΨu 1
  set L : StdSpace ι →L[ℝ] StdSpace ι := ↑u⁻¹ * B
  have hΨL (v : StdSpace ι) : Ψ 1 (L v) = B v := by
    rw [← hu, ← mul_apply_eq_comp, ← mul_assoc, Units.mul_inv, one_mul]
  have hL : Matrix.toEuclideanLin.symm L.toLinearMap ∈ Matrix.symplecticGroup ι ℝ := by
    rw [mem_symplecticGroup_iff_forall_stdForm, LinearEquiv.apply_symm_apply]
    intro v w
    calc stdForm ι (L v) (L w) = ω 1 (Ψ 1 (L v)) (Ψ 1 (L w)) := by rw [hΨω, h₀]
      _ = stdForm ι v w := by rw [hΨL, hΨL, hB]
  obtain ⟨γ, hγ, hγs, hγ0, hγ1⟩ :=
    Matrix.exists_contDiff_path_symplecticGroup (one_mem _) hL
  have hS : ContDiff ℝ (⊤ : ℕ∞) fun t ↦ Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (γ t) := by
    rw [← Matrix.coe_toEuclideanCLMContinuousLinearEquiv]
    exact Matrix.toEuclideanCLMContinuousLinearEquiv.contDiff.comp hγ
  refine ⟨fun t ↦ Ψ t * Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (γ t),
    hΨ.mul (hS.of_le (mod_cast le_top)), ?_, ?_, fun t v w ↦ ?_⟩
  · dsimp only
    rw [hΨ0, hγ0, map_one, one_mul]
  · ext1 v
    rw [mul_apply_eq_comp, hγ1, Matrix.toEuclideanCLM_apply, LinearEquiv.apply_symm_apply,
      ContinuousLinearMap.coe_coe, hΨL]
  · rw [mul_apply_eq_comp, mul_apply_eq_comp, hΨω, h₀]
    exact mem_symplecticGroup_iff_forall_stdForm_toEuclideanCLM.1 (hγs t) v w

end SymplecticGeometry

end
