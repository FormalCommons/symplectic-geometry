/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.EulerSequence
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.FirstChernClass
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Tensor

/-!
# Chern classes on complex projective space

On `ℂℙᵐ = ℙ ℂ (Fin (m + 1) → ℂ)`, with `h = hyperplaneClass (Fin (m + 1) → ℂ)` the hyperplane
class, this file computes the Chern classes of the line bundles `𝒪(k)` (Tau Ceti's
`Projectivization.twistCore k`), of their direct sums, and of the tangent bundle.

## Main results

* `Projectivization.chernClass_one_twistCore_add`: `c₁(𝒪(k + l)) = c₁(𝒪(k)) + c₁(𝒪(l))`, from
  the isomorphism `𝒪(k + l) ≅ 𝒪(k) ⊗ 𝒪(l)` and
  `SymplecticGeometry.Bundle.chernClass_one_tensorProduct`.
* `Projectivization.chernClass_one_twistCore`: `c₁(𝒪(k)) = k h` for every `k : ℤ`, and
  `Projectivization.totalChernClass_twistCore`: `c(𝒪(k)) = 1 + k h`.
* `Projectivization.totalChernClass_twistPiCore`: `c(𝒪(k)^{⊕ r}) = (1 + k h) ^ r`, by the Whitney
  sum formula.
* `Projectivization.totalChernClass_tangentSpace`: `c(TℂPᵐ) = (1 + h) ^ (m + 1)`, from the
  splitting `TℂPᵐ ⊕ ℂ ≅ 𝒪(1)^{⊕ (m + 1)}` of the Euler sequence.
* `Projectivization.firstChernClass_tangentSpace`: `c₁(TℂPᵐ) = (m + 1) h`, the degree-two part
  of `totalChernClass_tangentSpace`, through `chernClass_one_eq_firstChernClass`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Example 4.4.3 (the total Chern class of complex projective space).
* J. Milnor, J. Stasheff, *Characteristic Classes*, Theorem 14.10 (the same computation, from
  the splitting of the tangent bundle plus a trivial line into copies of the hyperplane bundle).
-/

public section

noncomputable section

open Bundle Module SymplecticGeometry.Bundle
open scoped LinearAlgebra.Projectivization Manifold TensorProduct TauCeti.ModuleTopology

namespace Projectivization

variable {m : ℕ}

/-- **The first Chern class of `𝒪(k)` is additive in `k`.** On `ℂℙᵐ`,
`c₁(𝒪(k + l)) = c₁(𝒪(k)) + c₁(𝒪(l))`. It holds since `𝒪(k + l) ≅ 𝒪(k) ⊗ 𝒪(l)`. -/
theorem chernClass_one_twistCore_add (k l : ℤ) :
    chernClass ℂ (twistCore (𝕜 := ℂ) (n := m) (k + l)).Fiber 1 =
      chernClass ℂ (twistCore (𝕜 := ℂ) (n := m) k).Fiber 1 +
        chernClass ℂ (twistCore (𝕜 := ℂ) (n := m) l).Fiber 1 := by
  rw [← chernClass_one_tensorProduct (finrank_self ℂ) (finrank_self ℂ)]
  exact chernClass_congr _ (continuous_twistCoreTensorEquiv (𝕜 := ℂ) (n := m) k l) 1

/-- **The first Chern class of `𝒪(k)`.** On `ℂℙᵐ`, `c₁(𝒪(k)) = k h`, where `h` is the hyperplane
class. -/
theorem chernClass_one_twistCore (k : ℤ) :
    chernClass ℂ (twistCore (𝕜 := ℂ) (n := m) k).Fiber 1 =
      k • hyperplaneClass (Fin (m + 1) → ℂ) := by
  have h₁ : chernClass ℂ (twistCore (𝕜 := ℂ) (n := m) 1).Fiber 1 =
      hyperplaneClass (Fin (m + 1) → ℂ) := by
    rw [chernClass_one_eq_complexEulerClass _ _ (finrank_self ℂ)]
    exact complexEulerClass_twistCore_one
  induction k using Int.induction_on with
  | zero =>
    rw [chernClass_one_eq_complexEulerClass _ _ (finrank_self ℂ), complexEulerClass_twistCore_zero,
      map_zero, zero_smul]
  | succ k hk => rw [chernClass_one_twistCore_add, hk, h₁, add_zsmul, one_zsmul]
  | pred k hk =>
    rw [← sub_add_cancel (-(k : ℤ)) 1, chernClass_one_twistCore_add, h₁, sub_add_cancel] at hk
    rw [eq_sub_of_add_eq hk, sub_zsmul, one_zsmul, sub_eq_add_neg]

/-- **The total Chern class of `𝒪(k)`.** On `ℂℙᵐ`, `c(𝒪(k)) = 1 + k h`, where `h` is the
hyperplane class. -/
theorem totalChernClass_twistCore (k : ℤ) :
    totalChernClass ℂ (twistCore (𝕜 := ℂ) (n := m) k).Fiber =
      1 + k • (TopCat.of (ℙ ℂ (Fin (m + 1) → ℂ))).evenIntegralCohomologyOf 1
        (hyperplaneClass (Fin (m + 1) → ℂ)) := by
  rw [totalChernClass_eq_one_add_of_finrank_eq_one _ _ (finrank_self ℂ),
    chernClass_one_twistCore, map_zsmul]

/-- **The total Chern class of `𝒪(k)^{⊕ r}`.** On `ℂℙᵐ`, the direct sum of `r` copies of `𝒪(k)`
has total Chern class `(1 + k h) ^ r`, where `h` is the hyperplane class. -/
theorem totalChernClass_twistPiCore (k : ℤ) (r : ℕ) :
    totalChernClass (Fin r → ℂ) (twistPiCore (𝕜 := ℂ) (n := m) k (Fin r)).Fiber =
      (1 + k • (TopCat.of (ℙ ℂ (Fin (m + 1) → ℂ))).evenIntegralCohomologyOf 1
        (hyperplaneClass (Fin (m + 1) → ℂ))) ^ r := by
  induction r with
  | zero => rw [totalChernClass_eq_one_of_finrank_eq_zero _ _ (by simp), pow_zero]
  | succ r hr =>
    rw [totalChernClass_congr _ (continuous_twistPiCoreCongr (𝕜 := ℂ) (n := m) k (Fin (r + 1))
        (finSuccEquiv r)),
      totalChernClass_congr _ (continuous_twistPiCoreOptionEquiv (𝕜 := ℂ) (n := m) k (Fin r)),
      totalChernClass_prod, totalChernClass_twistCore, hr, pow_succ', mul_comm]

/-- **The total Chern class of complex projective space.** The tangent bundle of `ℂℙᵐ` has total
Chern class `(1 + h) ^ (m + 1)`, where `h` is the hyperplane class: by the Euler sequence,
`TℂPᵐ ⊕ ℂ ≅ 𝒪(1)^{⊕ (m + 1)}` (`eulerSequenceEquiv`).

Milestone: *Chern classes of projective hypersurfaces*. -/
theorem totalChernClass_tangentSpace :
    totalChernClass (Fin m → ℂ)
        (TangentSpace 𝓘(ℂ, Fin m → ℂ) : ℙ ℂ (Fin (m + 1) → ℂ) → Type) =
      (1 + (TopCat.of (ℙ ℂ (Fin (m + 1) → ℂ))).evenIntegralCohomologyOf 1
        (hyperplaneClass (Fin (m + 1) → ℂ))) ^ (m + 1) := by
  have h := totalChernClass_congr _ (continuous_eulerSequenceEquiv (m := m))
  rw [totalChernClass_prod, totalChernClass_trivial, mul_one, totalChernClass_twistPiCore,
    one_smul] at h
  exact h

/-- **The first Chern class of complex projective space.** The tangent bundle of `ℂℙᵐ` has first
Chern class `(m + 1) h`, read in integral cohomology, where `h` is the hyperplane class. This
holds for every `m`, `m = 0` included.

Milestone: *First Chern class of a complex vector bundle*. -/
theorem firstChernClass_tangentSpace :
    ((TopCat.of (ℙ ℂ (Fin (m + 1) → ℂ))).uliftIntegralCohomologyIso 2).hom
        (firstChernClass (Fin m → ℂ)
          (TangentSpace 𝓘(ℂ, Fin m → ℂ) : ℙ ℂ (Fin (m + 1) → ℂ) → Type)) =
      ((m + 1 : ℕ) : ℤ) • hyperplaneClass (Fin (m + 1) → ℂ) := by
  rw [← chernClass_one_eq_firstChernClass, ← totalChernClass_apply, totalChernClass_tangentSpace,
    TopCat.one_add_evenIntegralCohomologyOf_pow_apply_one]

end Projectivization
