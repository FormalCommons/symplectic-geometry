/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Sphere.Basic
public import SymplecticGeometry.Analysis.Normed.Module.Conjugate
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Sphere
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.EulerCharacteristic
public import SymplecticGeometry.Topology.VectorBundle.Complexification.Basic
public import SymplecticGeometry.Topology.VectorBundle.Complexification.ComplexStructure
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
public import TauCeti.Topology.VectorBundle.Orientation.Complex.Conjugate

/-!
# Complex structures on the tangent bundles of spheres

Let `E` be a real inner product space of dimension `n + 1`, so that the unit sphere `S^n` of `E`
is a smooth manifold modelled on `EuclideanSpace ℝ (Fin n)`, and `J` a continuous complex
structure on its tangent bundle (Tau Ceti's `TauCeti.Bundle.ContinuousComplexStructure`). The
theorems assume that `n = 2 r + 2` is even and positive; `J` then orients the sphere
(`TauCeti.Bundle.ContinuousComplexStructure.tangentOrientation`).

* `TauCeti.Bundle.ContinuousComplexStructure.evalFundamentalClass_chernClass_sphere`: the top
  Chern class `c_{r+1}` of the complex tangent bundle `J.Fiber`, evaluated on the fundamental
  class of the orientation given by `J`, is `2`, the Euler characteristic of `S^{2r+2}`. This
  is the closed-manifold statement
  `TauCeti.Bundle.ContinuousComplexStructure.evalFundamentalClass_chernClass_eq_eulerChar` with
  Tau Ceti's `TauCeti.eulerChar_sphere`.
* `TauCeti.Bundle.ContinuousComplexStructure.two_nsmul_chernClass_sphere_eq_zero`: if `n = 2 j`
  with `j ≠ 0` even, then `2 c_j(J.Fiber) = 0`. The complexification `ℂ ⊗ TS^n` has total Chern
  class `1`, since `TS^n` plus a trivial line is trivial (`sphereTangentProdHomeomorph`,
  `Bundle.totalChernClass_complexification_eq_one`), and it is the sum of `J.Fiber` and of its
  conjugate (`TauCeti.Bundle.ContinuousComplexStructure.complexificationEquiv`). In degree `2 j`
  the Whitney formula keeps only `c_j(J.Fiber) + c_j(conj J.Fiber)`, because the cohomology of
  the sphere vanishes in the degrees between `0` and `n`
  (`TopCat.isZero_integralCohomology_sphere_of_ne`). Both classes are Euler classes, and
  `e(conj J.Fiber) = (-1)^j e(J.Fiber) = e(J.Fiber)` (`TauCeti.complexEulerClass_conjugateBundle`).
* `SymplecticGeometry.isEmpty_continuousComplexStructure_sphere_four_mul`: for `k ≠ 0`, the
  tangent bundle of `S^{4k}` has no continuous complex structure, since evaluating
  `2 c_{2k}(J.Fiber) = 0` on the fundamental class would give `4 = 0`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Exercise 4.1.9.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11, §14 and §15.
-/

public section

open Bundle Module Metric
open scoped Manifold ContDiff VectorBundle.ComplexToReal TauCeti.Complexification

namespace TauCeti.Bundle.ContinuousComplexStructure

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * finrank ℂ G)]

/-- **The top Chern number of a complex structure on the tangent bundle of a sphere is `2`.** Let
`J` be a continuous complex structure on the tangent bundle of the unit sphere `S^n` of `E`, with
`finrank ℝ E = n + 1` and `n = 2 r + 2`, and complex model `G`. Orient the sphere by `J`
(`J.tangentOrientation hn`). Then the top Chern class `c_{r+1}` of the complex bundle `J.Fiber`,
evaluated on the fundamental class of the sphere, is `2`.

The sphere `S^0`, two points, is left out: the fundamental class is defined here only in
positive dimension. -/
theorem evalFundamentalClass_chernClass_sphere
    (J : ContinuousComplexStructure (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type)) {r : ℕ}
    (hn : finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * r + 2) :
    ((J.tangentOrientation hn).toHomologicalOrientation hn).evalFundamentalClass hn
      (ModuleCat.of ℤ ℤ) (ContinuousMap.id _)
      (SymplecticGeometry.Bundle.chernClass G J.Fiber (r + 1)) = 2 := by
  rw [J.evalFundamentalClass_chernClass_eq_eulerChar (G := G) hn,
    eulerChar_sphere (Fact.out : finrank ℝ E = n + 1)]
  obtain rfl : n = 2 * r + 2 := by simpa using hn
  rw [Even.neg_one_pow ⟨r + 1, by ring⟩]
  norm_num

open SymplecticGeometry SymplecticGeometry.Bundle in
/-- **Twice the top Chern class of a complex structure on `TS^{2j}` vanishes for even `j`.** Let
`J` be a continuous complex structure on the tangent bundle of the unit sphere `S^n` of `E`, with
`finrank ℝ E = n + 1` and `n = 2 j` for an even `j ≠ 0`, and complex model `G`. Then
`2 c_j(J.Fiber) = 0` in `H^{2j}(S^n; ℤ)`. -/
theorem two_nsmul_chernClass_sphere_eq_zero
    (J : ContinuousComplexStructure (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type)) {j : ℕ} (hj₀ : j ≠ 0) (hj : Even j)
    (hn : n = 2 * j) :
    2 • SymplecticGeometry.Bundle.chernClass G J.Fiber j = 0 := by
  have hE : finrank ℝ E = n + 1 := Fact.out
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj₀
  have hG : finrank ℂ G = r + 1 := by
    have : finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * finrank ℂ G := Fact.out
    simp only [finrank_euclideanSpace_fin] at this
    omega
  have hG' : finrank ℂ (Conjugate G) = r + 1 := Conjugate.finrank_complex.trans hG
  -- The complexification of the tangent bundle has total Chern class `1`.
  have h₁ := totalChernClass_complexification_eq_one (sphereTangentProdEquiv n)
    ((sphereTangentProdHomeomorph E n).continuous.congr fun v ↦ by
      ext <;> simp)
  -- It is the sum of `J.Fiber` and of its conjugate.
  have := fun b ↦ FiberBundle.t2Space (G × Conjugate G) (J.Fiber ×ᵇ ConjugateBundle J.Fiber) b
  have := VectorBundle.isTopologicalAddGroup ℂ (G × Conjugate G)
    (J.Fiber ×ᵇ ConjugateBundle J.Fiber)
  have := VectorBundle.continuousSMul ℂ (G × Conjugate G) (J.Fiber ×ᵇ ConjugateBundle J.Fiber)
  have h₂ : ∀ k ≠ 0, chernClass (G × Conjugate G) (J.Fiber ×ᵇ ConjugateBundle J.Fiber) k = 0 :=
    fun k hk ↦ by
      rw [← chernClass_congr (fun b ↦ (J.complexificationEquiv b).toContinuousLinearEquiv)
        (J.continuous_complexificationEquiv G) k, ← totalChernClass_apply, h₁,
        ← TopCat.evenIntegralCohomologyOf_one]
      exact DirectSum.of_eq_of_ne _ _ _ hk
  -- The Whitney formula in degree `2 (r + 1)`: only the two top classes survive.
  have h₃ := congrArg (PowerSeries.coeff (r + 1))
    (mk_evenIntegralCohomologyOf_chernClass_prod (G₁ := G) (E₁ := J.Fiber) (G₂ := Conjugate G)
      (E₂ := ConjugateBundle J.Fiber))
  rw [PowerSeries.coeff_mk, h₂ (r + 1) (by omega), map_zero, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_succ,
    Finset.sum_eq_single (r, 0) (fun p hp hne ↦ ?_) (by simp)] at h₃
  · simp only [PowerSeries.coeff_mk, chernClass_zero, TopCat.evenIntegralCohomologyOf_one,
      one_mul, mul_one, ← map_add] at h₃
    have h₄ := DirectSum.of_injective
      (β := fun k ↦ (TopCat.of (sphere (0 : E) 1)).integralCohomology (2 * k)) (r + 1)
      (h₃.symm.trans (map_zero _).symm)
    -- Both top classes are Euler classes, and they agree since `r + 1` is even.
    have h₅ := complexEulerClass_conjugateBundle (E := J.Fiber) hG'
    rw [hj.neg_one_pow, one_smul] at h₅
    rw [chernClass_finrank_eq_complexEulerClass hG,
      chernClass_finrank_eq_complexEulerClass hG'] at h₄
    rw [chernClass_finrank_eq_complexEulerClass hG, two_nsmul]
    convert h₄ using 3
    -- `h₅` gives `Conjugate G` Tau Ceti's real structure, and `h₄` Mathlib's `complexToReal`.
    convert h₅.symm
    exact Conjugate.complexToReal_eq_instNormedSpaceReal G
  · -- The middle terms vanish, since so does the cohomology of the sphere in their degrees.
    rw [Finset.mem_antidiagonal] at hp
    have hp₁ : p.1 < r := by
      rcases p with ⟨a, b⟩
      simp only [ne_eq, Prod.mk.injEq, not_and] at hne hp ⊢
      omega
    have := ModuleCat.subsingleton_of_isZero (TopCat.isZero_integralCohomology_sphere_of_ne hE
      (q := 2 * (p.1 + 1)) (by omega) (by omega))
    rw [PowerSeries.coeff_mk, Subsingleton.elim (chernClass G J.Fiber (p.1 + 1)) 0, map_zero,
      zero_mul]

end TauCeti.Bundle.ContinuousComplexStructure

namespace SymplecticGeometry

open TauCeti TauCeti.Bundle

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The sphere `S^{4k}` has no almost complex structure.** For `k ≠ 0` and a real inner product
space `E` of dimension `4 k + 1`, the tangent bundle of the unit sphere `S^{4k}` of `E` carries no
continuous complex structure. -/
theorem isEmpty_continuousComplexStructure_sphere_four_mul {k : ℕ} (hk : k ≠ 0)
    [Fact (finrank ℝ E = 4 * k + 1)] :
    IsEmpty (ContinuousComplexStructure (EuclideanSpace ℝ (Fin (4 * k)))
      (TangentSpace (𝓡 (4 * k)) : sphere (0 : E) 1 → Type)) := by
  refine ⟨fun J ↦ ?_⟩
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (4 * k))) =
      2 * finrank ℂ (EuclideanSpace ℂ (Fin (2 * k)))) := ⟨by simp; ring⟩
  obtain ⟨r, hr⟩ : ∃ r, 2 * k = r + 1 := ⟨2 * k - 1, by omega⟩
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin (4 * k))) = 2 * r + 2 := by simp; omega
  -- The top Chern number is `2`, but twice the top Chern class vanishes.
  have h := congrArg (((J.tangentOrientation hn).toHomologicalOrientation hn).evalFundamentalClass
      hn (ModuleCat.of ℤ ℤ) (ContinuousMap.id _))
    (J.two_nsmul_chernClass_sphere_eq_zero (G := EuclideanSpace ℂ (Fin (2 * k))) (j := r + 1)
      (by omega) (hr ▸ even_two_mul k) (by omega))
  rw [map_nsmul, J.evalFundamentalClass_chernClass_sphere hn, map_zero] at h
  norm_num at h

end SymplecticGeometry

end
