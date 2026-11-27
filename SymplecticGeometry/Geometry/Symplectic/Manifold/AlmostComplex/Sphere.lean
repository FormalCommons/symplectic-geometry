/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
public import TauCeti.Topology.VectorBundle.Orientation.Complex.Conjugate
public import SymplecticGeometry.Geometry.Manifold.Orientation.ComplexStructure
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Basic
public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
import SymplecticGeometry.Analysis.Normed.Module.Conjugate
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Sphere
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.EulerCharacteristic
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Sphere.Basic
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Sphere.Integrality
import SymplecticGeometry.Topology.VectorBundle.Complexification.Basic
import SymplecticGeometry.Topology.VectorBundle.Complexification.ComplexStructure
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.EulerClass
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Naturality
import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars

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
  (`SymplecticGeometry.Bundle.chernClass_prod_sphere`). Both classes are Euler classes, and
  `e(conj J.Fiber) = (-1)^j e(J.Fiber) = e(J.Fiber)` (`TauCeti.complexEulerClass_conjugateBundle`).
* `TauCeti.Bundle.ContinuousComplexStructure.odd_of_sphere`: if `n = 2 j` with `j ≠ 0`, then `j`
  is odd, since for even `j` evaluating `2 c_j(J.Fiber) = 0` on the fundamental class would give
  `4 = 0`.
* `TauCeti.Bundle.ContinuousComplexStructure.factorial_dvd_two_of_sphere`: if `n = 2 r + 2`, then
  `r!` divides `2`, since the top Chern number `2` is a multiple of `r!` by Bott's integrality
  theorem (`SymplecticGeometry.Bundle.factorial_dvd_evalFundamentalClass_chernClass_sphere`).
* `TauCeti.Bundle.ContinuousComplexStructure.eq_one_or_eq_three_of_sphere`: if `n = 2 j` with
  `j ≠ 0`, then `j = 1` or `j = 3`: `j = 2 k + 1` is odd, and `(2k)!` divides `2`, so
  `2 k ≤ 2`.
* `SymplecticGeometry.isEmpty_continuousComplexStructure_sphere_four_mul`: for `k ≠ 0`, the
  tangent bundle of `S^{4k}` has no continuous complex structure.
* `SymplecticGeometry.isEmpty_continuousComplexStructure_sphere_four_mul_add_two`: the same for
  `S^{4k+2}` with `k ≥ 2`, since `(2k)!` does not divide `2`.
* `SymplecticGeometry.isEmpty_continuousComplexStructure_sphere`: the tangent bundle of `S^{2n}`
  has no continuous complex structure for `n ∉ {0, 1, 3}`, and
  `SymplecticGeometry.isEmpty_smoothAlmostComplexStructure_sphere`: hence `S^{2n}` has no smooth
  almost complex structure, through Tau Ceti's
  `TauCeti.ContMDiffAlmostComplexStructure.toContinuousComplexStructure`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Exercise 4.1.9.
* [A. Hatcher, *Vector Bundles and K-Theory*, version 2.2 (2017)][Hatcher2017], Chapter 4
  (Bott's integrality theorem and the almost complex spheres).
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
  have h₂ : chernClass (G × Conjugate G) (J.Fiber ×ᵇ ConjugateBundle J.Fiber) (r + 1) = 0 := by
    rw [← chernClass_congr (fun b ↦ (J.complexificationEquiv b).toContinuousLinearEquiv)
      (J.continuous_complexificationEquiv G)]
    exact chernClass_eq_zero_of_totalChernClass_eq_one _ _ h₁ hj₀
  -- The Whitney formula in degree `2 (r + 1)`: only the two top classes survive.
  have h₃ := (chernClass_prod_sphere (E₁ := J.Fiber) (G₂ := Conjugate G)
    (E₂ := ConjugateBundle J.Fiber) (hn ▸ hE) hj₀).symm.trans h₂
  -- Both top classes are Euler classes, and they agree since `r + 1` is even.
  have h₄ := complexEulerClass_conjugateBundle (E := J.Fiber) hG'
  rw [hj.neg_one_pow, one_smul] at h₄
  rw [chernClass_finrank_eq_complexEulerClass hG,
    chernClass_finrank_eq_complexEulerClass hG'] at h₃
  rw [chernClass_finrank_eq_complexEulerClass hG, two_nsmul]
  convert h₃ using 3
  -- `h₄` gives `Conjugate G` Tau Ceti's real structure, and `h₃` Mathlib's `complexToReal`.
  convert h₄.symm
  exact Conjugate.complexToReal_eq_instNormedSpaceReal G

/-- **On `TS^{2j}`, a complex structure forces `j` to be odd.** Let `J` be a continuous complex
structure on the tangent bundle of the unit sphere `S^n` of `E`, with `finrank ℝ E = n + 1` and
`n = 2 j`, `j ≠ 0`. Then `j` is odd. -/
theorem odd_of_sphere
    (J : ContinuousComplexStructure (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type)) {j : ℕ} (hj₀ : j ≠ 0) (hn : n = 2 * j) :
    Odd j := by
  rw [← Nat.not_even_iff_odd]
  intro hj
  obtain ⟨r, hr⟩ : ∃ r, j = r + 1 := ⟨j - 1, by omega⟩
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      2 * finrank ℂ (EuclideanSpace ℂ (Fin (r + 1)))) := ⟨by simp; omega⟩
  have hn' : finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * r + 2 := by simp; omega
  subst hr
  -- The top Chern number is `2`, but twice the top Chern class vanishes.
  have h₂ := J.two_nsmul_chernClass_sphere_eq_zero (G := EuclideanSpace ℂ (Fin (r + 1))) hj₀ hj hn
  have h := congrArg (((J.tangentOrientation hn').toHomologicalOrientation hn').evalFundamentalClass
      hn' (ModuleCat.of ℤ ℤ) (ContinuousMap.id _)) h₂
  rw [map_nsmul, J.evalFundamentalClass_chernClass_sphere hn', map_zero] at h
  norm_num at h

/-- **Bott integrality bounds the dimension of an almost complex sphere.** Let `J` be a
continuous complex structure on the tangent bundle of the unit sphere `S^n` of `E`, with
`finrank ℝ E = n + 1` and `n = 2 r + 2`. Then `r!` divides `2`. -/
theorem factorial_dvd_two_of_sphere
    (J : ContinuousComplexStructure (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type)) {r : ℕ}
    (hn : finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * r + 2) :
    r.factorial ∣ 2 := by
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      2 * finrank ℂ (EuclideanSpace ℂ (Fin (r + 1)))) := ⟨by simp [hn]; ring⟩
  have h := SymplecticGeometry.Bundle.factorial_dvd_evalFundamentalClass_chernClass_sphere
    (EuclideanSpace ℂ (Fin (r + 1))) J.Fiber hn (J.tangentOrientation hn)
  rw [J.evalFundamentalClass_chernClass_sphere hn] at h
  exact Int.natCast_dvd_natCast.1 h

/-- **On `TS^{2j}`, a complex structure forces `j = 1` or `j = 3`.** Let `J` be a continuous
complex structure on the tangent bundle of the unit sphere `S^n` of `E`, with
`finrank ℝ E = n + 1` and `n = 2 j`, `j ≠ 0`. Then `j = 1` or `j = 3`. -/
theorem eq_one_or_eq_three_of_sphere
    (J : ContinuousComplexStructure (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type)) {j : ℕ} (hj₀ : j ≠ 0) (hn : n = 2 * j) :
    j = 1 ∨ j = 3 := by
  obtain ⟨k, hk⟩ := J.odd_of_sphere hj₀ hn
  have h := Nat.le_of_dvd two_pos (J.factorial_dvd_two_of_sphere (r := 2 * k) (by simp; omega))
  have := (2 * k).self_le_factorial
  omega

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
      (TangentSpace (𝓡 (4 * k)) : sphere (0 : E) 1 → Type)) :=
  ⟨fun J ↦ Nat.not_odd_iff_even.2 (even_two_mul k)
    (J.odd_of_sphere (j := 2 * k) (by omega) (by ring))⟩

/-- **The sphere `S^{4k+2}` has no almost complex structure for `k ≥ 2`.** For a real inner
product space `E` of dimension `4 k + 3` with `2 ≤ k`, the tangent bundle of the unit sphere
`S^{4k+2}` of `E` carries no continuous complex structure. -/
theorem isEmpty_continuousComplexStructure_sphere_four_mul_add_two {k : ℕ} (hk : 2 ≤ k)
    [Fact (finrank ℝ E = 4 * k + 3)] :
    IsEmpty (ContinuousComplexStructure (EuclideanSpace ℝ (Fin (4 * k + 2)))
      (TangentSpace (𝓡 (4 * k + 2)) : sphere (0 : E) 1 → Type)) :=
  ⟨fun J ↦ by have := J.eq_one_or_eq_three_of_sphere (j := 2 * k + 1) (by omega) (by ring); omega⟩

/-- **The sphere `S^{2n}` has no almost complex structure for `n ∉ {0, 1, 3}`.**
For `n ∉ {0, 1, 3}` and a real inner product space `E` of dimension `2 n + 1`, the tangent bundle
of the unit sphere `S^{2n}` of `E` carries no continuous complex structure. -/
theorem isEmpty_continuousComplexStructure_sphere {n : ℕ} (h₀ : n ≠ 0) (h₁ : n ≠ 1)
    (h₃ : n ≠ 3) [Fact (finrank ℝ E = 2 * n + 1)] :
    IsEmpty (ContinuousComplexStructure (EuclideanSpace ℝ (Fin (2 * n)))
      (TangentSpace (𝓡 (2 * n)) : sphere (0 : E) 1 → Type)) :=
  ⟨fun J ↦ by have := J.eq_one_or_eq_three_of_sphere h₀ rfl; omega⟩

/-- **The sphere `S^{2n}` has no smooth almost complex structure for `n ∉ {0, 1, 3}`.** For a
real inner product space `E` of dimension `2 n + 1`, the unit sphere `S^{2n}` of `E` carries no
smooth almost complex structure. -/
theorem isEmpty_smoothAlmostComplexStructure_sphere {n : ℕ} (h₀ : n ≠ 0) (h₁ : n ≠ 1)
    (h₃ : n ≠ 3) [Fact (finrank ℝ E = 2 * n + 1)] :
    IsEmpty (SmoothAlmostComplexStructure (𝓡 (2 * n)) (sphere (0 : E) 1)) :=
  ⟨fun J ↦ (isEmpty_continuousComplexStructure_sphere h₀ h₁ h₃).false
    (J.toContMDiff ⊤).toContinuousComplexStructure⟩

end SymplecticGeometry

end
