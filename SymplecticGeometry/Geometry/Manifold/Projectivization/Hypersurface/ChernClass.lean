/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.ChernClass
public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hypersurface.NormalBundle
public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.Splitting

/-!
# Chern classes of a smooth projective hypersurface

Let `X ⊆ ℂℙⁿ⁺¹` be a smooth projective hypersurface of degree `d`, with inclusion
`ι = X.embedding`, and let `h` be the hyperplane class of `ℂℙⁿ⁺¹`. This file computes the Chern
classes of the normal bundle `ν` and of the tangent bundle of `X` in terms of `ι^* h`.

The normal bundle is `ι^* 𝒪(d)` (`SmoothProjectiveHypersurface.normalSpaceEquiv`), so
`c₁(ν) = ι^* c₁(𝒪(d)) = d ι^* h`. A splitting `TX ⊕ ν ≅ ι^* TℂPⁿ⁺¹` of the tangent bundle along
the embedding (`TauCeti.SmoothEmbedding.tangentNormalEquiv`) and the Whitney sum formula then give
`c(TX) (1 + d ι^* h) = ι^* c(TℂPⁿ⁺¹) = (1 + ι^* h) ^ (n + 2)`. Since `(ι^* h) ^ (n + 2) = 0`, the
class `1 + d ι^* h` is invertible, and solving for `c(TX)` gives each Chern class of `X`.

## Main declarations

* `SymplecticGeometry.SmoothProjectiveHypersurface.hyperplaneClass`: the class `ι^* h` in
  `H²(X; ℤ)`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.chernClass_one_normalSpace`:
  `c₁(ν) = d ι^* h`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.totalChernClass_tangentSpace_mul`:
  `c(TX) (1 + d ι^* h) = (1 + ι^* h) ^ (n + 2)`.
* `SymplecticGeometry.SmoothProjectiveHypersurface.chernClass_tangentSpace`: for every `k`,
  `c_k(TX) = (∑_{j ≤ k} (n + 2).choose (k - j) (-d) ^ j) (ι^* h) ^ k`, and
  `SymplecticGeometry.SmoothProjectiveHypersurface.chernClass_one_tangentSpace`:
  `c₁(TX) = (n + 2 - d) ι^* h`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Examples 4.4.3 and 4.4.4 and Exercise 4.4.6 (the Chern classes of a hypersurface).
* [P. Griffiths and J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 1, §1.
-/

public section

noncomputable section

open Module Projectivization SymplecticGeometry.Bundle
open scoped LinearAlgebra.Projectivization Manifold

namespace SymplecticGeometry

namespace SmoothProjectiveHypersurface

variable {n d : ℕ} (X : SmoothProjectiveHypersurface n d)

/-! ### The restriction of the hyperplane class -/

/-- The restriction `ι^* h ∈ H²(X; ℤ)` of the hyperplane class of `ℂℙⁿ⁺¹` to the hypersurface:
its pull-back by the inclusion. -/
def hyperplaneClass : (TopCat.of X).integralCohomology 2 :=
  TopCat.singularCohomologyMap (TopCat.ofHom X.embedding.toContinuousMap) 2
    (Projectivization.hyperplaneClass (Fin (n + 2) → ℂ))

theorem hyperplaneClass_def :
    X.hyperplaneClass = TopCat.singularCohomologyMap (TopCat.ofHom X.embedding.toContinuousMap) 2
      (Projectivization.hyperplaneClass (Fin (n + 2) → ℂ)) :=
  (rfl)

/-- In the even integral cohomology rings, the inclusion pulls the hyperplane class of `ℂℙⁿ⁺¹`
back to `ι^* h`. -/
theorem evenIntegralCohomologyMap_hyperplaneClass :
    TopCat.evenIntegralCohomologyMap (TopCat.ofHom X.embedding.toContinuousMap)
        ((TopCat.of (ℙ ℂ (Fin (n + 2) → ℂ))).evenIntegralCohomologyOf 1
          (Projectivization.hyperplaneClass (Fin (n + 2) → ℂ))) =
      (TopCat.of X).evenIntegralCohomologyOf 1 X.hyperplaneClass := by
  rw [TopCat.evenIntegralCohomologyMap_of, hyperplaneClass_def]

/-- `ι^* h` is nilpotent: `(ι^* h) ^ (n + 2) = 0`, since `h ^ (n + 2) = 0` on `ℂℙⁿ⁺¹`. -/
theorem hyperplaneClass_pow_eq_zero :
    (TopCat.of X).evenIntegralCohomologyOf 1 X.hyperplaneClass ^ (n + 2) = 0 := by
  rw [← evenIntegralCohomologyMap_hyperplaneClass, ← map_pow,
    Projectivization.hyperplaneClass_pow_eq_zero (by simp), map_zero]

/-! ### The normal bundle -/

/-- **The first Chern class of the normal bundle of a hypersurface.** For a smooth hypersurface
`X ⊆ ℂℙⁿ⁺¹` of degree `d`, the normal bundle `ν` has `c₁(ν) = d ι^* h`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem chernClass_one_normalSpace :
    chernClass ℂ (fun x : X ↦ X.embedding.isImmersion.NormalSpace x WithTop.top_ne_zero) 1 =
      d • X.hyperplaneClass := by
  rw [chernClass_congr _ X.continuous_normalSpaceEquiv]
  refine (chernClass_pullback X.embedding.toContinuousMap 1).trans ?_
  rw [chernClass_one_twistCore, map_zsmul, natCast_zsmul, hyperplaneClass_def]

/-- The total Chern class of the normal bundle of a hypersurface is `1 + d ι^* h`. -/
theorem totalChernClass_normalSpace :
    totalChernClass ℂ (fun x : X ↦ X.embedding.isImmersion.NormalSpace x WithTop.top_ne_zero) =
      1 + d • (TopCat.of X).evenIntegralCohomologyOf 1 X.hyperplaneClass := by
  rw [totalChernClass_eq_one_add_of_finrank_eq_one _ _ (finrank_self ℂ),
    chernClass_one_normalSpace, map_nsmul]

/-! ### The tangent bundle -/

/-- **The total Chern class of a hypersurface.** For a smooth hypersurface `X ⊆ ℂℙⁿ⁺¹` of degree
`d`, `c(TX) (1 + d ι^* h) = (1 + ι^* h) ^ (n + 2)` in the even integral cohomology ring of `X`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem totalChernClass_tangentSpace_mul :
    totalChernClass (Fin n → ℂ)
        (TangentSpace 𝓘(ℂ, Fin n → ℂ) : X → Type) *
        (1 + d • (TopCat.of X).evenIntegralCohomologyOf 1 X.hyperplaneClass) =
      (1 + (TopCat.of X).evenIntegralCohomologyOf 1 X.hyperplaneClass) ^ (n + 2) := by
  rw [← totalChernClass_normalSpace, ← totalChernClass_prod,
    totalChernClass_congr _ (X.embedding.continuous_tangentNormalEquiv WithTop.top_ne_zero _
      (X.embedding.normalClass_normalRightInverse WithTop.top_ne_zero)
      (X.embedding.continuous_normalRightInverse WithTop.top_ne_zero))]
  refine (totalChernClass_pullback X.embedding.toContinuousMap).trans ?_
  rw [totalChernClass_tangentSpace, map_pow, map_add, map_one,
    evenIntegralCohomologyMap_hyperplaneClass]

/-- The polynomial `(∑_{j < N} (-d X) ^ j) (1 + X) ^ (n + 2)`, whose value at `ι^* h` is `c(TX)`
for `N ≥ n + 2`. -/
private def tangentPoly (n d N : ℕ) : Polynomial ℤ :=
  (∑ j ∈ Finset.range N, (Polynomial.C (-(d : ℤ)) * Polynomial.X) ^ j) *
    (1 + Polynomial.X) ^ (n + 2)

private theorem coeff_tangentPoly {N k : ℕ} (hk : k < N) :
    (tangentPoly n d N).coeff k =
      ∑ j ∈ Finset.range (k + 1), ((n + 2).choose (k - j) : ℤ) * (-(d : ℤ)) ^ j := by
  rw [tangentPoly, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  simp only [mul_pow, ← Polynomial.C_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, add_comm (1 : Polynomial ℤ), Polynomial.coeff_X_add_one_pow]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.2 (by omega)), mul_comm]

/-- `c(TX)` is the value at `ι^* h` of `(∑_{j < N} (-d X) ^ j) (1 + X) ^ (n + 2)`, for any
`N ≥ n + 2`. -/
private theorem totalChernClass_eq_aeval {N : ℕ} (hN : n + 2 ≤ N) :
    totalChernClass (Fin n → ℂ)
        (TangentSpace 𝓘(ℂ, Fin n → ℂ) : X → Type) =
      Polynomial.aeval ((TopCat.of X).evenIntegralCohomologyOf 1 X.hyperplaneClass)
        (tangentPoly n d N) := by
  set a := (TopCat.of X).evenIntegralCohomologyOf 1 X.hyperplaneClass
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
  -- `∑_{j < N} (-d a) ^ j` inverts `1 + d a`, since `a ^ N = 0`.
  have hinv := geom_sum_mul_neg (-(d • a)) (n + 2 + M)
  rw [neg_pow, smul_pow, pow_add a, X.hyperplaneClass_pow_eq_zero, zero_mul,
    smul_zero, mul_zero, sub_zero, sub_neg_eq_add] at hinv
  simp only [tangentPoly, map_mul, map_sum, map_pow, map_add, map_one, Polynomial.aeval_X,
    map_neg, map_nsmul, eq_intCast, Int.cast_natCast, neg_mul, ← nsmul_eq_mul]
  rw [← X.totalChernClass_tangentSpace_mul, mul_comm, mul_assoc, mul_comm (1 + d • a), hinv,
    mul_one]

/-- **The Chern classes of a hypersurface.** For a smooth hypersurface `X ⊆ ℂℙⁿ⁺¹` of degree `d`
and every `k`, `c_k(TX) = (∑_{j ≤ k} (n + 2).choose (k - j) (-d) ^ j) (ι^* h) ^ k`, where
`(ι^* h) ^ k` is read in `H^{2k}(X; ℤ)`. This solves `totalChernClass_tangentSpace_mul` for
`c(TX)`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem chernClass_tangentSpace (k : ℕ) :
    chernClass (Fin n → ℂ)
        (TangentSpace 𝓘(ℂ, Fin n → ℂ) : X → Type) k =
      (∑ j ∈ Finset.range (k + 1), ((n + 2).choose (k - j) : ℤ) * (-(d : ℤ)) ^ j) •
        ((TopCat.of X).evenIntegralCohomologyOf 1 X.hyperplaneClass ^ k) k := by
  rw [← totalChernClass_apply, X.totalChernClass_eq_aeval (N := n + 2 + k + 1) (by omega),
    TopCat.aeval_evenIntegralCohomologyOf_apply, coeff_tangentPoly (by omega)]

/-- **The first Chern class of a hypersurface.** For a smooth hypersurface `X ⊆ ℂℙⁿ⁺¹` of degree
`d`, `c₁(TX) = (n + 2 - d) ι^* h`.

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem chernClass_one_tangentSpace :
    chernClass (Fin n → ℂ)
        (TangentSpace 𝓘(ℂ, Fin n → ℂ) : X → Type) 1 =
      ((n + 2 : ℤ) - d) • X.hyperplaneClass := by
  rw [chernClass_tangentSpace, pow_one, DirectSum.of_eq_same]
  congr 1
  simp [Finset.sum_range_succ]
  ring

end SmoothProjectiveHypersurface

end SymplecticGeometry

end
