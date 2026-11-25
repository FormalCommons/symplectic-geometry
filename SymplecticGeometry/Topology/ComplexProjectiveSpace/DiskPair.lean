/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.ComplexProjectiveSpace.SecondHomology
public import SymplecticGeometry.Topology.ComplexProjectiveSpace.SimplyConnected
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Singular.DiskSphere

/-!
# Maps of the disk pair into complex projective space

Let `N ≥ 1`, let `ℙ = ℙ ℂ (Fin (N + 1) → ℂ)`, let `h = Projectivization.hyperplaneClass` be its
hyperplane class and `p` a point of `ℙ`. A relative class `h_p ∈ H²(ℙ, {p}; ℤ)` that maps to `h`
in `H²(ℙ; ℤ)` exists (`Projectivization.exists_singularCohomologyπ_eq_hyperplaneClass`). This file
shows that every class of `H²(D², S¹; ℤ)` is the pull-back of any such `h_p` along a map of pairs
`(D², S¹) ⟶ (ℙ, {p})`, that is, a map from the disk that is constant at `p` on the boundary circle
(`Projectivization.exists_hom_diskBoundaryPair_singularCohomologyMap_eq`). The disk pair is Tau
Ceti's `TauCeti.diskBoundaryPair 2`, and cohomology has chain coefficients and cochain values the
unit object `ℤ` of `ModuleCat ℤ`, the target of `TopCat.integralCohomologyEquiv`.

## Proof

The disk pair is the cube pair `(I², ∂I²)` (`TauCeti.diskBoundaryPairIsoCube`), whose relative
homology is `ℤ` in degree `2` and zero below (`TauCeti.singularHomologyCubeBoundaryPairIso`,
`TauCeti.isZero_singularHomology_cubeBoundaryPair_of_ne`). So by the relative universal coefficient
theorem (`TopPair.singularKronecker_bijective_of_projective_homology_lt`) a class of `H²(I², ∂I²)`
is determined by its value on the generator. A generalized loop `γ ∈ Ω²(ℙ, p)` is a map of pairs
`(I², ∂I²) ⟶ (ℙ, {p})` (`GenLoop.toCubeBoundaryPairHom`), and by naturality of the Kronecker
pairing the pull-back of `h_p` along it takes the value `⟨h, hurewicz [γ]⟩` on the generator. The
Hurewicz map `π₂(ℙ, p) → H₂(ℙ; ℤ)` is bijective, `ℙ` being simply connected
(`HomotopyGroup.bijective_hurewiczIntHom_of_simplyConnectedSpace`), and so is `x ↦ ⟨h, x⟩` on
`H₂(ℙ; ℤ)` (`Projectivization.bijective_singularKronecker_hyperplaneClass`), so every value is
attained.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (the universal
  coefficient theorem) and Section 4.2 (the Hurewicz map).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology TauCeti
open scoped LinearAlgebra.Projectivization MonoidalCategory

/- The cohomology below is that of `TopCat.integralCohomologyEquiv`, with the structure
`ModuleCat.instLinear`; instance search would otherwise find
`CategoryTheory.Linear.preadditiveIntLinear`. -/
attribute [local instance high] ModuleCat.instLinear

namespace Projectivization

variable {N : ℕ}

/-- The hyperplane class of `ℙ ℂ (Fin (N + 1) → ℂ)` lifts to a relative class in
`H²(ℙ ℂ (Fin (N + 1) → ℂ), {p}; ℤ)`, for every point `p`. -/
theorem exists_singularCohomologyπ_eq_hyperplaneClass (p : ℙ ℂ (Fin (N + 1) → ℂ)) :
    ∃ hp : (TopPair.ofSubset ({p} : Set (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))))).singularCohomology
        (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 2,
      (TopPair.ofSubset ({p} : Set (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))))).singularCohomologyπ
          (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 2 hp =
        (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))).integralCohomologyEquiv 2
          (hyperplaneClass (Fin (N + 1) → ℂ)) :=
  (ModuleCat.epi_iff_surjective _).1 (TopPair.epi_singularCohomologyπ_of_nullhomotopic _
    ⟨p, by
      rw [TopPair.ofSubset_map]
      convert ContinuousMap.Homotopic.refl _
      ext x
      -- the inclusion of `{p}` sends `x` to its underlying point, `p`
      exact (Set.mem_singleton_iff.1 x.property).symm⟩ two_ne_zero) _

/-- Let `N ≠ 0`, `p` a point of `ℙ ℂ (Fin (N + 1) → ℂ)` and `hp ∈ H²(ℙ ℂ (Fin (N + 1) → ℂ), {p}; ℤ)`
a relative class that maps to the hyperplane class. Every class `c ∈ H²(D², S¹; ℤ)` is the
pull-back of `hp` along some map of pairs `(D², S¹) ⟶ (ℙ ℂ (Fin (N + 1) → ℂ), {p})`. -/
theorem exists_hom_diskBoundaryPair_singularCohomologyMap_eq (hN : N ≠ 0)
    {p : ℙ ℂ (Fin (N + 1) → ℂ)}
    (hp : (TopPair.ofSubset ({p} : Set (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))))).singularCohomology
      (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 2)
    (hhp : (TopPair.ofSubset ({p} : Set (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))))).singularCohomologyπ
        (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 2 hp =
      (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))).integralCohomologyEquiv 2
        (hyperplaneClass (Fin (N + 1) → ℂ)))
    (c : (diskBoundaryPair.{0} 2).singularCohomology
      (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 2) :
    ∃ f : diskBoundaryPair.{0} 2 ⟶
        TopPair.ofSubset ({p} : Set (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ)))),
      TopPair.singularCohomologyMap f 2 hp = c := by
  set e := diskBoundaryPairIsoCube.{0} 2
  set E := singularHomologyCubeBoundaryPairIso (𝟙_ (ModuleCat.{0} ℤ)) 2
  set c' := TopPair.singularCohomologyMap e.inv 2 c
  set κ := (cubeBoundaryPair.{0} 2).singularKronecker (R := 𝟙_ (ModuleCat.{0} ℤ))
    (M := 𝟙_ (ModuleCat.{0} ℤ)) ℤ 2
  have hκ : Function.Injective κ :=
    ((cubeBoundaryPair.{0} 2).singularKronecker_bijective_of_projective_homology_lt _ _ 2
      fun j hj ↦ (isZero_singularHomology_cubeBoundaryPair_of_ne _ 2 (by omega)).projective).1
  -- A class `a ∈ π₂(ℙ, p)` with `⟨h, hurewicz a⟩` the value of `c'` on the generator.
  obtain ⟨a, ha⟩ := ((bijective_singularKronecker_hyperplaneClass (V := Fin (N + 1) → ℂ)
    (by simp) hN).comp (HomotopyGroup.bijective_hurewiczIntHom_of_simplyConnectedSpace p)).2
      ((E.inv ≫ κ c').hom 1)
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep a.toMul
  refine ⟨e.hom ≫ GenLoop.toCubeBoundaryPairHom γ, ?_⟩
  suffices h : TopPair.singularCohomologyMap (GenLoop.toCubeBoundaryPairHom γ) 2 hp = c' by
    rw [TopPair.singularCohomologyMap_comp_apply, h, ← TopPair.singularCohomologyMap_comp_apply,
      e.hom_inv_id, TopPair.singularCohomologyMap_id, ModuleCat.id_apply]
  refine hκ ((cancel_epi E.inv).1 (ModuleCat.hom_ext (LinearMap.ext_ring ?_)))
  have key : E.inv ≫ κ (TopPair.singularCohomologyMap (GenLoop.toCubeBoundaryPairHom γ) 2 hp) =
      GenLoop.hurewicz (𝟙_ (ModuleCat.{0} ℤ)) γ ≫
        (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))).singularKronecker ℤ 2
          ((TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))).integralCohomologyEquiv 2
            (hyperplaneClass (Fin (N + 1) → ℂ))) := by
    rw [TopPair.singularKronecker_naturality,
      ← GenLoop.hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom_assoc,
      singularHomologyIsoOfSubsetSingleton_hom]
    -- `exact` rather than `rw`: the source of `singularHomologyπ` is the homology of the singular
    -- simplicial set, which is the absolute singular homology only up to unfolding.
    exact congrArg (GenLoop.hurewicz _ γ ≫ ·)
      (((TopPair.ofSubset _).singularKronecker_singularCohomologyπ ℤ 2 hp).symm.trans
        (congrArg _ hhp))
  rw [← ha, key, Function.comp_apply, HomotopyGroup.hurewiczIntHom_apply, ← hγ,
    HomotopyGroup.hurewicz_mk, ModuleCat.comp_apply]
  -- The unit object `𝟙_ (ModuleCat ℤ)` is `ModuleCat.of ℤ ℤ`, the coefficients of
  -- `HomotopyGroup.hurewiczIntHom`, by definition.
  rfl

end Projectivization

end
