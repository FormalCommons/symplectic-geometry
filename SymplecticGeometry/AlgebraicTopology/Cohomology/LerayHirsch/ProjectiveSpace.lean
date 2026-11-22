/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.LerayHirsch.Bundle
public import SymplecticGeometry.AlgebraicTopology.Singular.Nullhomotopic
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.ProjectiveSpace

/-!
# Degree two of the integral cohomology of `X × ℙ ℂ V`

Let `V` be a complex normed space with `finrank ℂ V = n + 1`, `h ∈ H²(ℙ ℂ V; ℤ)` its hyperplane
class (`Projectivization.hyperplaneClass`), and `X` a path-connected space. This file describes
`H²(X × ℙ ℂ V; ℤ)`, the product being the cartesian product `X ⊗ TopCat.of (ℙ ℂ V)` of `TopCat`.

## Main results

* `Projectivization.exists_eq_add_zsmul_hyperplaneClass`: every class of `H²(X × ℙ ℂ V; ℤ)` is
  `pr₁^* a + m • pr₂^* h` for some `a ∈ H²(X; ℤ)` and `m ∈ ℤ`.
* `Projectivization.eq_zero_of_singularCohomologyMap_eq_zero`: for points `x₀ : X` and
  `y₀ : ℙ ℂ V`, a class of `H²(X × ℙ ℂ V; ℤ)` whose pull-backs along `x ↦ (x, y₀)` and
  `y ↦ (x₀, y)` both vanish is zero.

## Proof

The integral cohomology of `ℙ ℂ V` is free in every degree
(`Projectivization.free_integralCohomology`) and its homology is projective and finitely
generated (`Projectivization.projective_singularHomology`, and Tau Ceti's
`TauCeti.finite_singularHomology_of_finiteCWType` for the finite CW structure
`TauCeti.finiteCWType_projectivization_complex`), so the integral Leray–Hirsch theorem for a
product, `TopCat.integralLerayHirsch_fst_bijective`, applies to `X × ℙ ℂ V` with any bases of the
cohomology of the fibre. In degree two only the fibre degrees `0`, `1` and `2` contribute. In
degree `0` every class of the fibre is a multiple of the unit, so its summand gives the classes
`pr₁^* a`; degree `1` is zero (`Projectivization.isZero_integralCohomology_of_odd`); in degree
`2` every class of the fibre is a multiple of `h`
(`Projectivization.exists_eq_zsmul_hyperplaneClass`),
and the coefficient in `H⁰(X; ℤ)` is a multiple of the unit as `X` is path-connected
(`TopCat.bijective_zsmul_integralCohomologyOne`).

For the vanishing criterion, restriction to `X × {y₀}` gives back `a`, since `h` pulls back to
zero through a point (`TopCat.singularCohomologyMap_const_eq_zero`); restriction to
`{x₀} × ℙ ℂ V` then gives `m • h`, so `m • h = 0` and `m • pr₂^* h = pr₂^* (m • h)` vanishes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4D.1 (Leray–Hirsch).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Module TauCeti
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}

/-- **Degree two of the integral cohomology of `X × ℙ ℂ V`.** For `finrank ℂ V = n + 1` and `X`
path-connected, every class `c ∈ H²(X × ℙ ℂ V; ℤ)` is `pr₁^* a + m • pr₂^* h` for some class
`a ∈ H²(X; ℤ)` and some integer `m`, with `h` the hyperplane class of `ℙ ℂ V`. -/
theorem exists_eq_add_zsmul_hyperplaneClass (hV : finrank ℂ V = n + 1) (X : TopCat.{0})
    [PathConnectedSpace X] (c : (X ⊗ TopCat.of (ℙ ℂ V)).integralCohomology 2) :
    ∃ (a : X.integralCohomology 2) (m : ℤ),
      c = TopCat.singularCohomologyMap (fst X _) 2 a +
        m • TopCat.singularCohomologyMap (snd X _) 2 (hyperplaneClass V) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  have := fun d ↦ free_integralCohomology hV d
  have : Module.Projective ℤ (𝟙_ (ModuleCat.{0} ℤ)) := inferInstanceAs (Module.Projective ℤ ℤ)
  have : Module.Finite ℤ (𝟙_ (ModuleCat.{0} ℤ)) := inferInstanceAs (Module.Finite ℤ ℤ)
  have := fun d ↦ projective_singularHomology (𝟙_ (ModuleCat.{0} ℤ)) hV d
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ hV
  classical
  let b (d : ℕ) := Module.Free.chooseBasis ℤ ((TopCat.of (ℙ ℂ V)).integralCohomology d)
  obtain ⟨g, rfl⟩ := (TopCat.integralLerayHirsch_fst_bijective (n := 2) X (TopCat.of (ℙ ℂ V)) b
    fun d _ ↦ finite_singularHomology_of_finiteCWType _ _ d).2 c
  have h0 {Y : TopCat.{0}} [PathConnectedSpace Y] (y : Y.integralCohomology 0) :
      ∃ m : ℤ, y = m • Y.integralCohomologyOne :=
    ((TopCat.bijective_zsmul_integralCohomologyOne Y).2 y).imp fun _ h ↦ h.symm
  induction g using DirectSum.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | add g g' hg hg' =>
    obtain ⟨a, m, h⟩ := hg
    obtain ⟨a', m', h'⟩ := hg'
    exact ⟨a + a', m + m', by rw [map_add, h, h', map_add, add_zsmul]; abel⟩
  | of j β =>
    obtain ⟨⟨⟨p, q⟩, hpq⟩, i⟩ := j
    rw [TopCat.integralLerayHirsch_of]
    have hp : p ≤ 2 := by simp only at hpq; omega
    interval_cases p
    · obtain rfl : q = 2 := by simp only at hpq; omega
      obtain ⟨m, hm⟩ := h0 (b 0 i)
      refine ⟨m • β, 0, ?_⟩
      rw [hm, map_zsmul, TopCat.singularCohomologyMap_integralCohomologyOne, map_zsmul,
        TopCat.integralCup_integralCohomologyOne_right, map_zsmul, zero_zsmul, add_zero]
    · obtain rfl : q = 1 := by simp only at hpq; omega
      have := ModuleCat.subsingleton_of_isZero (isZero_integralCohomology_of_odd hV odd_one)
      refine ⟨0, 0, ?_⟩
      rw [Subsingleton.elim (b 1 i) 0]
      simp
    · obtain rfl : q = 0 := by simp only at hpq; omega
      obtain ⟨m, rfl⟩ := h0 β
      obtain ⟨m', hm'⟩ := exists_eq_zsmul_hyperplaneClass hV (b 2 i)
      refine ⟨0, m * m', ?_⟩
      rw [hm', map_zsmul (TopCat.singularCohomologyMap (fst X _) 0).hom,
        map_zsmul (TopCat.singularCohomologyMap (snd X _) 2).hom,
        TopCat.singularCohomologyMap_integralCohomologyOne, map_zero, zero_add, mul_zsmul,
        TopCat.integralCup_zsmul_left, TopCat.integralCup_integralCohomologyOne]

/-- **A vanishing criterion in degree two of the integral cohomology of `X × ℙ ℂ V`.** For
`finrank ℂ V = n + 1`, `X` path-connected and points `x₀ : X`, `y₀ : ℙ ℂ V`, a class
`c ∈ H²(X × ℙ ℂ V; ℤ)` whose pull-backs along `x ↦ (x, y₀)` and along `y ↦ (x₀, y)`
(`TopCat.prodFiberInclusion`) both vanish is zero. -/
theorem eq_zero_of_singularCohomologyMap_eq_zero (hV : finrank ℂ V = n + 1) {X : TopCat.{0}}
    [PathConnectedSpace X] (x₀ : X) (y₀ : ℙ ℂ V)
    {c : (X ⊗ TopCat.of (ℙ ℂ V)).integralCohomology 2}
    (h₁ : TopCat.singularCohomologyMap
      (lift (𝟙 X) (TopCat.const (X := X) (y₀ : TopCat.of (ℙ ℂ V)))) 2 c = 0)
    (h₂ : TopCat.singularCohomologyMap (TopCat.prodFiberInclusion X _ x₀) 2 c = 0) :
    c = 0 := by
  obtain ⟨a, m, rfl⟩ := exists_eq_add_zsmul_hyperplaneClass hV X c
  rw [map_add, map_zsmul, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    lift_fst, TopCat.singularCohomologyMap_id, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, lift_snd,
    TopCat.singularCohomologyMap_const_eq_zero _ two_ne_zero] at h₁
  simp only [ConcreteCategory.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply, zsmul_zero,
    add_zero] at h₁
  subst h₁
  rw [map_zero, zero_add] at h₂ ⊢
  rw [map_zsmul, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    TopCat.prodFiberInclusion_snd, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply] at h₂
  rw [← map_zsmul, h₂, map_zero]

end Projectivization
