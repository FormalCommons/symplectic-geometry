/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralKronecker
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace
public import TauCeti.AlgebraicTopology.Cellular.ComplexProjective.Basic
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
import SymplecticGeometry.Topology.ComplexProjectiveSpace.Homeomorph

/-!
# The hyperplane class on the second homology of complex projective space

Let `V` be a complex normed space with `finrank ℂ V = n + 1` and `n ≥ 1`, and let
`h = Projectivization.hyperplaneClass V ∈ H²(ℙ ℂ V; ℤ)`. This file shows that the Kronecker pairing
`x ↦ ⟨h, x⟩` with `h` is a bijection from `H₂(ℙ ℂ V; ℤ)` onto `ℤ`, so that `h` takes the value
`±1` on a generator of `H₂(ℙ ℂ V; ℤ)`. The pairing is the integral Kronecker pairing
`TopCat.integralKronecker`; the sign is not fixed here. It follows that the map of projective
spaces induced by an injective linear map `V →ₗ[ℂ] W` is a bijection on `H₂(-; ℤ)`.

## Main results

* `Projectivization.bijective_integralKronecker_hyperplaneClass`: `x ↦ ⟨h, x⟩` is a bijection
  `H₂(ℙ ℂ V; ℤ) → ℤ`.
* `Projectivization.integralKronecker_hyperplaneClass_eq_one_or_neg_one`: `⟨h, x⟩ = ±1` for
  every generator `x` of `H₂(ℙ ℂ V; ℤ)`.
* `Projectivization.bijective_singularHomologyMap_map_two`: for an injective linear map
  `f : V →ₗ[ℂ] W` of finite-dimensional spaces, the induced map `ℙ ℂ V → ℙ ℂ W` is a bijection
  on `H₂(-; ℤ)`.

## Proof

`H₂(ℙ ℂ V; ℤ)` is isomorphic to `ℤ`: carry it along
`Projectivization.complexProjectiveSpaceHomeomorph` to Tau Ceti's `ℂPⁿ`, whose singular homology
in degree `2` is that of its cellular chain complex, a single copy of `ℤ` from its one `2`-cell
(`TauCeti.ComplexProjectiveSpace.singularHomologyIso`). The Kronecker map
`H²(ℙ ℂ V; ℤ) → Hom(H₂(ℙ ℂ V; ℤ), ℤ)` is onto (`TopCat.singularKronecker_surjective`), and every
class of `H²(ℙ ℂ V; ℤ)` is a multiple `m • h` (`Projectivization.exists_eq_zsmul_hyperplaneClass`).
So an isomorphism `H₂(ℙ ℂ V; ℤ) ≅ ℤ` is `m` times the pairing with `h`; being onto, it forces
`m = ±1`, and the pairing with `h` is `±` that isomorphism.

For the map `g : ℙ ℂ V → ℙ ℂ W` induced by `f`, the hyperplane classes satisfy `g^* h_W = h_V`
(`Projectivization.hyperplaneClass_map`), so by naturality of the Kronecker pairing
`⟨h_W, g_* x⟩ = ⟨h_V, x⟩`. Both pairings are bijections onto `ℤ`, hence so is `g_*`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2 (the cellular
  homology of complex projective space) and Section 3.1 (the universal coefficient theorem).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Module
open scoped LinearAlgebra.Projectivization MonoidalCategory

namespace Projectivization

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}

/-- The integral second homology of a complex projective space `ℙ ℂ V` with
`finrank ℂ V = n + 1` and `n ≠ 0` is isomorphic to `ℤ`. -/
private def singularHomologyTwoLinearEquivInt (hV : finrank ℂ V = n + 1) (hn : n ≠ 0) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (𝟙_ (ModuleCat.{0} ℤ))).obj
        (TopCat.of (ℙ ℂ V)) ≃ₗ[ℤ] ℤ :=
  ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (𝟙_ (ModuleCat.{0} ℤ))).mapIso
      (TopCat.isoOfHomeo (complexProjectiveSpaceHomeomorph hV))).symm ≪≫
    TauCeti.ComplexProjectiveSpace.singularHomologyIso (i := 1) _ (by omega)).toLinearEquiv

/-- The Kronecker pairing with the hyperplane class `h`, `x ↦ ⟨h, x⟩`, is a bijection from the
integral second homology of `ℙ ℂ V` onto `ℤ`, when `finrank ℂ V = n + 1` and `n ≠ 0`. -/
theorem bijective_integralKronecker_hyperplaneClass (hV : finrank ℂ V = n + 1) (hn : n ≠ 0) :
    Function.Bijective ((TopCat.of (ℙ ℂ V)).integralKronecker 2 (hyperplaneClass V)) := by
  set X := TopCat.of (ℙ ℂ V)
  set ψ := singularHomologyTwoLinearEquivInt hV hn
  obtain ⟨c, hc⟩ := X.singularKronecker_surjective (k := ℤ) (R := 𝟙_ (ModuleCat.{0} ℤ))
    (M := 𝟙_ (ModuleCat.{0} ℤ)) 2 (ModuleCat.ofHom ψ.toLinearMap)
  obtain ⟨m, hm⟩ := exists_eq_zsmul_hyperplaneClass hV ((X.integralCohomologyEquiv 2).symm c)
  have hψ : ∀ y, ψ y = m * X.integralKronecker 2 (hyperplaneClass V) y := fun y => by
    have := congrArg (fun f => f.hom y) hc
    rw [← X.integralKronecker_integralCohomologyEquiv_symm, hm] at this
    simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at this
    -- `ModuleCat.hom_ofHom` does not fire here: the source of `ModuleCat.ofHom ψ` is
    -- `ModuleCat.of ℤ H` rather than `H`, which agree only up to unfolding
    exact this.symm
  obtain ⟨y₀, hy₀⟩ := ψ.surjective 1
  have hm1 : m * m = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one ((hψ y₀).symm.trans hy₀) with rfl | rfl <;> rfl
  have hφ : ⇑(X.integralKronecker 2 (hyperplaneClass V)) = (fun k => m * k) ∘ ψ :=
    funext fun y => by rw [Function.comp_apply, hψ, ← mul_assoc, hm1, one_mul]
  rw [hφ]
  exact (Function.Involutive.bijective fun k => by
    rw [← mul_assoc, hm1, one_mul]).comp ψ.bijective

/-- The hyperplane class `h` of `ℙ ℂ V`, with `finrank ℂ V = n + 1` and `n ≠ 0`, takes the value
`1` or `-1` on every generator of the integral second homology. -/
theorem integralKronecker_hyperplaneClass_eq_one_or_neg_one (hV : finrank ℂ V = n + 1)
    (hn : n ≠ 0) {x : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (𝟙_ (ModuleCat.{0} ℤ))).obj (TopCat.of (ℙ ℂ V))} (hx : AddSubgroup.zmultiples x = ⊤) :
    (TopCat.of (ℙ ℂ V)).integralKronecker 2 (hyperplaneClass V) x = 1 ∨
      (TopCat.of (ℙ ℂ V)).integralKronecker 2 (hyperplaneClass V) x = -1 := by
  obtain ⟨y, hy⟩ := (bijective_integralKronecker_hyperplaneClass hV hn).2 1
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (hx ▸ AddSubgroup.mem_top y)
  rw [map_zsmul, smul_eq_mul] at hy
  exact Int.eq_one_or_neg_one_of_mul_eq_one' hy |>.elim (fun h => Or.inl h.2) fun h => Or.inr h.2

section map

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ V]
  [FiniteDimensional ℂ W]

/-- An injective linear map `f : V →ₗ[ℂ] W` with `finrank ℂ V = n + 1` and `n ≠ 0` induces a
bijection `H₂(ℙ ℂ V; ℤ) → H₂(ℙ ℂ W; ℤ)` on integral second homology. -/
theorem bijective_singularHomologyMap_map_two (f : V →ₗ[ℂ] W) (hf : Function.Injective f)
    (hV : finrank ℂ V = n + 1) (hn : n ≠ 0) :
    Function.Bijective
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (𝟙_ (ModuleCat.{0} ℤ))).map
        (TopCat.ofHom
          ⟨map f hf, continuous_map hf (LinearMap.continuous_of_finiteDimensional f)⟩)) := by
  have hle := LinearMap.finrank_le_finrank_of_injective hf
  have hW : finrank ℂ W = (finrank ℂ W - 1) + 1 := by omega
  have hcomp : ⇑((TopCat.of (ℙ ℂ V)).integralKronecker 2 (hyperplaneClass V)) =
      (TopCat.of (ℙ ℂ W)).integralKronecker 2 (hyperplaneClass W) ∘
        ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (𝟙_ (ModuleCat.{0} ℤ))).map
          (TopCat.ofHom
          ⟨map f hf, continuous_map hf (LinearMap.continuous_of_finiteDimensional f)⟩) := by
    ext x
    rw [Function.comp_apply, ← TopCat.integralKronecker_naturality, hyperplaneClass_map]
  rw [← (bijective_integralKronecker_hyperplaneClass hW (by omega)).of_comp_iff', ← hcomp]
  exact bijective_integralKronecker_hyperplaneClass hV hn

end map

end Projectivization
