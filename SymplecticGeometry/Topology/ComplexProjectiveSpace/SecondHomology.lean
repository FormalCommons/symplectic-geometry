/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.ComplexProjectiveSpace

/-!
# The hyperplane class on the second homology of complex projective space

Let `V` be a complex normed space with `finrank ℂ V = n + 1` and `n ≥ 1`, and let
`h = Projectivization.hyperplaneClass V ∈ H²(ℙ ℂ V; ℤ)`. This file shows that the Kronecker pairing
`x ↦ ⟨h, x⟩` with `h` is a bijection from `H₂(ℙ ℂ V; ℤ)` onto `ℤ`, so that `h` takes the value
`±1` on a generator of `H₂(ℙ ℂ V; ℤ)`. The pairing is Tau Ceti's `TopCat.singularKronecker`,
applied to `h` read through `TopCat.integralCohomologyEquiv`; the sign is not fixed here.

## Main results

* `Projectivization.bijective_singularKronecker_hyperplaneClass`: `x ↦ ⟨h, x⟩` is a bijection
  `H₂(ℙ ℂ V; ℤ) → ℤ`.
* `Projectivization.singularKronecker_hyperplaneClass_eq_one_or_neg_one`: `⟨h, x⟩ = ±1` for
  every generator `x` of `H₂(ℙ ℂ V; ℤ)`.

## Proof

`H₂(ℙ ℂ V; ℤ)` is isomorphic to `ℤ`: carry it along
`Projectivization.complexProjectiveSpaceHomeomorph` to Tau Ceti's `ℂPⁿ`, where the Hurewicz map
`π₂ → H₂` is bijective (`HomotopyGroup.bijective_hurewiczIntHom_of_simplyConnectedSpace`) and
`π₂(ℂPⁿ) ≅ ℤ` (`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt`). The Kronecker map
`H²(ℙ ℂ V; ℤ) → Hom(H₂(ℙ ℂ V; ℤ), ℤ)` is onto (`TopCat.singularKronecker_surjective`), and every
class of `H²(ℙ ℂ V; ℤ)` is a multiple `m • h` (`Projectivization.exists_eq_zsmul_hyperplaneClass`).
So an isomorphism `H₂(ℙ ℂ V; ℤ) ≅ ℤ` is `m` times the pairing with `h`; being onto, it forces
`m = ±1`, and the pairing with `h` is `±` that isomorphism.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (the universal
  coefficient theorem) and Section 4.2 (the Hurewicz theorem and the homotopy groups of complex
  projective space).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup Metric Module
open scoped LinearAlgebra.Projectivization MonoidalCategory

/- The Kronecker pairing below is that of cohomology with chain coefficients and cochain values
`𝟙_ (ModuleCat ℤ)`, the target of `TopCat.integralCohomologyEquiv`, which carries the structure
`ModuleCat.instLinear`; instance search would otherwise find
`CategoryTheory.Linear.preadditiveIntLinear`, the structure of integral cohomology. -/
attribute [local instance high] ModuleCat.instLinear

namespace Projectivization

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}

/-- The integral second homology of a complex projective space `ℙ ℂ V` with
`finrank ℂ V = n + 1` and `n ≠ 0` is isomorphic to `ℤ`. -/
private def singularHomologyTwoLinearEquivInt (hV : finrank ℂ V = n + 1) (hn : n ≠ 0) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (𝟙_ (ModuleCat.{0} ℤ))).obj
        (TopCat.of (ℙ ℂ V)) ≃ₗ[ℤ] ℤ :=
  let v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let e : _ ≃+ ℤ :=
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (𝟙_ (ModuleCat.{0} ℤ))).mapIso
      (TopCat.isoOfHomeo (complexProjectiveSpaceHomeomorph hV))).toLinearEquiv.toAddEquiv.symm.trans
    ((AddEquiv.ofBijective _ (bijective_hurewiczIntHom_of_simplyConnectedSpace
        (TauCeti.ComplexProjectiveSpace.mk n v))).symm.trans
      (TauCeti.ComplexProjectiveSpace.pi2MulEquivInt v hn).toAdditive)
  { e with map_smul' := fun m y => (map_intCast_smul e ℤ ℤ m y).trans (by simp) }

/-- The Kronecker pairing with the hyperplane class `h`, `x ↦ ⟨h, x⟩`, is a bijection from the
integral second homology of `ℙ ℂ V` onto `ℤ`, when `finrank ℂ V = n + 1` and `n ≠ 0`. -/
theorem bijective_singularKronecker_hyperplaneClass (hV : finrank ℂ V = n + 1) (hn : n ≠ 0) :
    Function.Bijective ((TopCat.of (ℙ ℂ V)).singularKronecker ℤ 2
      ((TopCat.of (ℙ ℂ V)).integralCohomologyEquiv 2 (hyperplaneClass V))).hom := by
  set X := TopCat.of (ℙ ℂ V)
  set φ := X.singularKronecker ℤ 2 (X.integralCohomologyEquiv 2 (hyperplaneClass V))
  set ψ := singularHomologyTwoLinearEquivInt hV hn
  obtain ⟨c, hc⟩ := X.singularKronecker_surjective (k := ℤ) (R := 𝟙_ (ModuleCat.{0} ℤ))
    (M := 𝟙_ (ModuleCat.{0} ℤ)) 2 (ModuleCat.ofHom ψ.toLinearMap)
  obtain ⟨m, hm⟩ := exists_eq_zsmul_hyperplaneClass hV ((X.integralCohomologyEquiv 2).symm c)
  have hψ : ∀ y, ψ y = m * φ.hom y := fun y => by
    rw [LinearEquiv.symm_apply_eq] at hm
    have := congrArg (fun f => f.hom y) hc
    simp only [hm, map_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply, smul_eq_mul] at this
    -- `ModuleCat.hom_ofHom` does not fire here: the source of `ModuleCat.ofHom ψ` is
    -- `ModuleCat.of ℤ H` rather than `H`, which agree only up to unfolding
    exact this.symm
  obtain ⟨y₀, hy₀⟩ := ψ.surjective 1
  have hm1 : m * m = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one ((hψ y₀).symm.trans hy₀) with rfl | rfl <;> rfl
  have hφ : ⇑φ.hom = (fun k => m * k) ∘ ψ := funext fun y => by
    rw [Function.comp_apply, hψ, ← mul_assoc, hm1, one_mul]
  rw [hφ]
  exact (Function.Involutive.bijective fun k => by
    rw [← mul_assoc, hm1, one_mul]).comp ψ.bijective

/-- The hyperplane class `h` of `ℙ ℂ V`, with `finrank ℂ V = n + 1` and `n ≠ 0`, takes the value
`1` or `-1` on every generator of the integral second homology. -/
theorem singularKronecker_hyperplaneClass_eq_one_or_neg_one (hV : finrank ℂ V = n + 1)
    (hn : n ≠ 0) {x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (𝟙_ (ModuleCat.{0} ℤ))).obj (TopCat.of (ℙ ℂ V))} (hx : AddSubgroup.zmultiples x = ⊤) :
    ((TopCat.of (ℙ ℂ V)).singularKronecker ℤ 2
        ((TopCat.of (ℙ ℂ V)).integralCohomologyEquiv 2 (hyperplaneClass V))).hom x = 1 ∨
      ((TopCat.of (ℙ ℂ V)).singularKronecker ℤ 2
        ((TopCat.of (ℙ ℂ V)).integralCohomologyEquiv 2 (hyperplaneClass V))).hom x = -1 := by
  obtain ⟨y, hy⟩ := (bijective_singularKronecker_hyperplaneClass hV hn).2 1
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (hx ▸ AddSubgroup.mem_top y)
  rw [map_zsmul, smul_eq_mul] at hy
  exact Int.eq_one_or_neg_one_of_mul_eq_one' hy |>.elim (fun h => Or.inl h.2) fun h => Or.inr h.2

end Projectivization
