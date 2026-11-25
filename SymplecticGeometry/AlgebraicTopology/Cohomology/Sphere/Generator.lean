/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralCohomologyULift
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Product

/-!
# The integral generator of the top cohomology of a sphere

Let `θ ∈ Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` be Tau Ceti's class `singularCohomologyTopCatSphereGenerator`, dual to the
standard generator of `H_{d+1}(Sᵈ⁺¹)`, carried into the library's integral cohomology by
`TopCat.integralCohomologyEquiv`. This file shows that `θ` generates `Hᵈ⁺¹(Sᵈ⁺¹; ℤ)`, and that
cup product with its pull-back to `Sᵈ⁺¹ × Y` keeps classes of infinite order.

## Main results

* `TopCat.exists_eq_zsmul_sphereGenerator`: every class of `Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` is an integer
  multiple of `θ`.
* `TopCat.not_isOfFinAddOrder_integralCup_sphereGenerator`: for a space `Y` and a class `c` of
  infinite order in `Hⁿ(Y; ℤ)`, the class `pr₁^* θ ⌣ pr₂^* c` of `Sᵈ⁺¹ × Y` has infinite order.
  It is read off Tau Ceti's decomposition `TopCat.singularCohomologySphereProdSlantEquiv` of the
  cohomology of `Sᵈ⁺¹ × Y`, whose inverse sends `(0, c)` to `pr₁^* θ ⌣ pr₂^* c`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 3.15 (the Künneth
  formula).
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace TopCat

open TauCeti

/-- Every class of `Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` is an integer multiple of the generator `θ`, the integral
class dual to the standard generator of `H_{d+1}(Sᵈ⁺¹)`. -/
theorem exists_eq_zsmul_sphereGenerator {d : ℕ}
    (x : (sphere.{0} (d + 1)).integralCohomology (d + 1)) :
    ∃ r : ℤ, x = r • ((sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1)).symm
      (singularCohomologyTopCatSphereGenerator ℤ d) := by
  set e := (sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1)
  set s := singularCohomologyTopCatSphereEquiv ℤ (𝟙_ (ModuleCat.{0} ℤ)) d
  have hθ : s (singularCohomologyTopCatSphereGenerator ℤ d) = 1 :=
    (singularCohomologyTopCatSphereEquiv_apply _ _ _ _).trans
      (singularKronecker_singularCohomologyTopCatSphereGenerator ℤ d)
  refine ⟨s (e x), e.injective (s.injective ?_)⟩
  rw [map_zsmul, map_zsmul, LinearEquiv.apply_symm_apply, hθ, smul_eq_mul, mul_one]

/-- **Products with the sphere generator keep infinite order.** Let `θ ∈ Hᵈ⁺¹(Sᵈ⁺¹; ℤ)` be the
integral class dual to the standard generator of `H_{d+1}(Sᵈ⁺¹)`. If `c ∈ Hⁿ(Y; ℤ)` has infinite
order, then so has `pr₁^* θ ⌣ pr₂^* c ∈ H^N(Sᵈ⁺¹ × Y; ℤ)`, `N = d + 1 + n`. -/
theorem not_isOfFinAddOrder_integralCup_sphereGenerator (Y : TopCat.{0}) {d n N : ℕ}
    (h : d + 1 + n = N) {c : Y.integralCohomology n} (hc : ¬IsOfFinAddOrder c) :
    ¬IsOfFinAddOrder ((sphere.{0} (d + 1) ⊗ Y).integralCup (d + 1) n N h
      (TopCat.singularCohomologyMap (fst _ Y) (d + 1)
        (((sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1)).symm
          (singularCohomologyTopCatSphereGenerator ℤ d)))
      (TopCat.singularCohomologyMap (snd _ Y) n c)) := by
  obtain rfl : N = n + (d + 1) := by omega
  -- the class is the image of `(0, c)` under the decomposition of the cohomology of `Sᵈ⁺¹ × Y`
  set e₁ := (sphere.{0} (d + 1) ⊗ Y).integralCohomologyEquiv (n + (d + 1))
  set S := singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{0} ℤ)) Y (sphereBasePoint d) n
  have hFc : (sphere.{0} (d + 1) ⊗ Y).integralCup (d + 1) n (n + (d + 1)) h
      (TopCat.singularCohomologyMap (fst _ Y) (d + 1)
        (((sphere.{0} (d + 1)).integralCohomologyEquiv (d + 1)).symm
          (singularCohomologyTopCatSphereGenerator ℤ d)))
      (TopCat.singularCohomologyMap (snd _ Y) n c) =
        e₁.symm (S.symm (0, Y.integralCohomologyEquiv n c)) := by
    rw [singularCohomologySphereProdSlantEquiv_symm_apply, map_zero, zero_add,
      integralCohomologyEquiv_symm_singularCup, integralCohomologyEquiv_symm_naturality,
      integralCohomologyEquiv_symm_naturality, LinearEquiv.symm_apply_apply]
  rw [hFc]
  refine fun hfin ↦ hc ?_
  rw [isOfFinAddOrder_iff_nsmul_eq_zero] at hfin ⊢
  obtain ⟨k, hk, hkc⟩ := hfin
  refine ⟨k, hk, (Y.integralCohomologyEquiv n).injective ?_⟩
  have := congrArg (fun x ↦ (S (e₁ x)).2) hkc
  simpa using this

end TopCat

end
