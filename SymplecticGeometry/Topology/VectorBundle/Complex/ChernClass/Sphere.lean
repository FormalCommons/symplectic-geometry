/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Basic
import SymplecticGeometry.AlgebraicTopology.Cohomology.Sphere.Basic
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Whitney

/-!
# Chern classes of complex vector bundles over spheres

Let `E` be a real normed space of dimension `n + 1`. A complex vector bundle over the unit sphere
`S^n` of `E` can have a nonzero Chern class `c_k` only for `k = 0` or `2 k = n`, since the integral
cohomology of `S^n` vanishes in the other degrees (`TopCat.isZero_integralCohomology_sphere_of_ne`).
This is `SymplecticGeometry.Bundle.chernClass_sphere_eq_zero`. On an even sphere `S^{2m}`, `m ≠ 0`,
the Whitney sum formula in degree `2 m` therefore reduces to
`c_m(E₁ ⊕ E₂) = c_m(E₁) + c_m(E₂)` (`SymplecticGeometry.Bundle.chernClass_prod_sphere`), the
products of classes of intermediate degrees being zero.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.2 (the cohomology of
  spheres).
-/

public section

open Bundle Module Metric

namespace SymplecticGeometry.Bundle

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  (G : Type) [NormedAddCommGroup G] [NormedSpace ℂ G]
  (V : sphere (0 : E) 1 → Type) [∀ b, AddCommGroup (V b)] [∀ b, Module ℂ (V b)]
  [∀ b, Module ℝ (V b)] [∀ b, IsScalarTower ℝ ℂ (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace G V)] [FiberBundle G V] [VectorBundle ℂ G V]

/-- **The Chern classes of a bundle over a sphere vanish away from degrees `0` and `n`.** For a
real normed space `E` of dimension `n + 1` and a complex vector bundle `V` over the unit sphere
`S^n` of `E`, `c_k(V) = 0` whenever `k ≠ 0` and `2 k ≠ n`. -/
theorem chernClass_sphere_eq_zero (hE : finrank ℝ E = n + 1) {k : ℕ} (hk₀ : k ≠ 0)
    (hk : 2 * k ≠ n) : chernClass G V k = 0 :=
  have := ModuleCat.subsingleton_of_isZero
    (TopCat.isZero_integralCohomology_sphere_of_ne hE (q := 2 * k) (by omega) hk)
  Subsingleton.elim _ _

section Prod

variable {G₁ : Type} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
  {E₁ : sphere (0 : E) 1 → Type} [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℂ (E₁ b)]
  [∀ b, Module ℝ (E₁ b)] [∀ b, IsScalarTower ℝ ℂ (E₁ b)] [∀ b, TopologicalSpace (E₁ b)]
  [TopologicalSpace (TotalSpace G₁ E₁)] [FiberBundle G₁ E₁] [VectorBundle ℂ G₁ E₁]
  {G₂ : Type} [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
  {E₂ : sphere (0 : E) 1 → Type} [∀ b, AddCommGroup (E₂ b)] [∀ b, Module ℂ (E₂ b)]
  [∀ b, Module ℝ (E₂ b)] [∀ b, IsScalarTower ℝ ℂ (E₂ b)] [∀ b, TopologicalSpace (E₂ b)]
  [TopologicalSpace (TotalSpace G₂ E₂)] [FiberBundle G₂ E₂] [VectorBundle ℂ G₂ E₂]

/-- **The Whitney sum formula in the top degree of an even sphere.** For a real normed space `E`
of dimension `2 m + 1` with `m ≠ 0`, and complex vector bundles `E₁`, `E₂` of finite rank over the
unit sphere `S^{2m}` of `E`, `c_m(E₁ ⊕ E₂) = c_m(E₁) + c_m(E₂)`: the products of classes of
intermediate degrees vanish. -/
theorem chernClass_prod_sphere {m : ℕ} (hE : finrank ℝ E = 2 * m + 1) (hm : m ≠ 0) :
    chernClass (G₁ × G₂) (E₁ ×ᵇ E₂) m = chernClass G₁ E₁ m + chernClass G₂ E₂ m := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have h := congrArg (PowerSeries.coeff (r + 1))
    (mk_evenIntegralCohomologyOf_chernClass_prod (G₁ := G₁) (E₁ := E₁) (G₂ := G₂) (E₂ := E₂))
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
    Finset.sum_eq_single (r, 0) (fun p hp hne ↦ ?_) (by simp)] at h
  · simp only [PowerSeries.coeff_mk, chernClass_zero, TopCat.evenIntegralCohomologyOf_one,
      one_mul, mul_one, ← map_add] at h
    exact (DirectSum.of_injective
      (β := fun k ↦ (TopCat.of (sphere (0 : E) 1)).integralCohomology (2 * k)) (r + 1) h).trans
      (add_comm _ _)
  · -- The products of classes of intermediate degrees vanish with the cohomology there.
    rw [Finset.mem_antidiagonal] at hp
    have hp₁ : p.1 < r := by
      rcases p with ⟨a, b⟩
      simp only [ne_eq, Prod.mk.injEq, not_and] at hne hp ⊢
      omega
    rw [PowerSeries.coeff_mk, chernClass_sphere_eq_zero G₁ E₁ hE (k := p.1 + 1) (by omega)
      (by omega), map_zero, zero_mul]

end Prod

end SymplecticGeometry.Bundle

end
