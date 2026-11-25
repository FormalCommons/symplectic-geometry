/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.ComplexProjectiveSpace.SecondHomology
import TauCeti.AlgebraicTopology.Cohomology.Sphere.Basic
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.DiskBoundary
import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact

/-!
# Null-homotopic maps from the two-sphere to complex projective space

Let `V` be a complex normed space with `finrank ℂ V = n + 1`, and let
`h = Projectivization.hyperplaneClass V ∈ H²(ℙ ℂ V; ℤ)`. This file shows that a continuous map
`g : S² → ℙ ℂ V`, with `S²` the sphere `TopCat.diskBoundary 3`, is null-homotopic if and only if
the pull-back `g^* h` vanishes in `H²(S²; ℤ)`
(`Projectivization.nullhomotopic_iff_singularCohomologyMap_hyperplaneClass_eq_zero`). For `n = 0`
both sides hold, since `ℙ ℂ V` is a point.

## Proof

For `n ≠ 0`, `ℙ ℂ V` is simply connected, being homeomorphic to Tau Ceti's sphere-quotient model of
`ℂPⁿ`, so by the Hurewicz theorem `g` is null-homotopic exactly when it sends the generator `[S²]`
of `H₂(S²; ℤ)` to zero (`TopCat.Hom.nullhomotopic_iff_singularHomologyMap_eq_zero`). The pairing
with `h` is injective on `H₂(ℙ ℂ V; ℤ)`
(`Projectivization.bijective_singularKronecker_hyperplaneClass`), and
`⟨h, g_*[S²]⟩ = ⟨g^* h, [S²]⟩` (`TopCat.singularKronecker_naturality`). Finally a class of
`H²(S²; ℤ)` is zero exactly when it vanishes on `[S²]`, since evaluation on `[S²]` is a linear
equivalence `H²(S²; ℤ) ≃ ℤ` (`TauCeti.singularCohomologyTopCatSphereEquiv`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (the universal
  coefficient theorem) and Section 4.2 (the Hurewicz theorem).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Module
open scoped LinearAlgebra.Projectivization MonoidalCategory

namespace Projectivization

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}

section UnitCoefficients

/- The Kronecker pairings in this section are those of cohomology with chain coefficients and
cochain values `𝟙_ (ModuleCat ℤ)`, the target of `TopCat.integralCohomologyEquiv`, which carries
the structure `ModuleCat.instLinear`; instance search would otherwise find
`CategoryTheory.Linear.preadditiveIntLinear`, the structure of integral cohomology. -/
attribute [local instance high] ModuleCat.instLinear

/-- A class of `Hᵈ⁺²(Sᵈ⁺²; ℤ)` vanishes exactly when it vanishes on the generator `[Sᵈ⁺²]`, in
the form that `TopCat.Hom.nullhomotopic_iff_singularHomologyMap_eq_zero` uses. This is Tau Ceti's
`TauCeti.singularCohomologyTopCatSphereEquiv`, read in that form; it is stated for every `d`,
since Lean matches `d + 1 + 1` with `d + 2` at once, but not `1 + 1` with `2` in these terms. -/
private theorem singularKronecker_sphere_eq_zero_iff (d : ℕ)
    (c : (TopCat.diskBoundary.{0} (d + 3)).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (𝟙_ (ModuleCat.{0} ℤ)) (d + 2)) :
    ((TopCat.diskBoundary.{0} (d + 3)).singularKronecker ℤ (d + 2) c).hom
        ((TauCeti.reducedSingularHomologyι (ModuleCat.of ℤ ℤ) (d + 2)).app
          (TopCat.diskBoundary.{0} (d + 3))
          ((TauCeti.reducedSingularHomologyTopCatSphereIso (ModuleCat.of ℤ ℤ) (d + 2)).inv 1)) =
        0 ↔ c = 0 := by
  have hgen : TauCeti.singularHomologyTopCatSphereGenerator ℤ (d + 1) =
      (TauCeti.reducedSingularHomologyι (ModuleCat.of ℤ ℤ) (d + 2)).app
        (TopCat.diskBoundary.{0} (d + 3))
        ((TauCeti.reducedSingularHomologyTopCatSphereIso (ModuleCat.of ℤ ℤ) (d + 2)).inv 1) := by
    rw [TauCeti.singularHomologyTopCatSphereGenerator_def]
    -- `TopCat.sphere (d + 2)` is `TopCat.diskBoundary (d + 3)` by definition
    rfl
  rw [← hgen]
  exact (Eq.congr_left (TauCeti.singularCohomologyTopCatSphereEquiv_apply ℤ
    (𝟙_ (ModuleCat.{0} ℤ)) (d + 1) c)).symm.trans
      (TauCeti.singularCohomologyTopCatSphereEquiv ℤ (𝟙_ (ModuleCat.{0} ℤ)) (d + 1)).map_eq_zero_iff

end UnitCoefficients

/-- A continuous map `g` from the two-sphere `TopCat.diskBoundary 3` to the complex projective
space `ℙ ℂ V`, with `finrank ℂ V = n + 1`, is null-homotopic if and only if it pulls the
hyperplane class back to zero in `H²(S²; ℤ)`. -/
theorem nullhomotopic_iff_singularCohomologyMap_hyperplaneClass_eq_zero
    (hV : finrank ℂ V = n + 1) (g : TopCat.diskBoundary.{0} 3 ⟶ TopCat.of (ℙ ℂ V)) :
    g.hom.Nullhomotopic ↔ TopCat.singularCohomologyMap g 2 (hyperplaneClass V) = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : Subsingleton (ℙ ℂ V) :=
      (complexProjectiveSpaceHomeomorph hV).symm.injective.subsingleton
    have : Nonempty (ℙ ℂ V) := ⟨g (TauCeti.sphereBasePoint 1)⟩
    have hh : hyperplaneClass V = 0 :=
      (ModuleCat.subsingleton_of_isZero (isZero_integralCohomology_of_lt hV (m := 2)
        (by omega))).elim _ _
    rw [hh, map_zero]
    exact iff_of_true (nullhomotopic_of_indiscrete _) rfl
  have : SimplyConnectedSpace (ℙ ℂ V) :=
    (complexProjectiveSpaceHomeomorph hV).toHomotopyEquiv.simplyConnectedSpace_iff.1
      inferInstance
  have hz : ℙ ℂ V := g (TauCeti.sphereBasePoint 1)
  rw [TopCat.Hom.nullhomotopic_iff_singularHomologyMap_eq_zero (n := 0) (z := hz)
      fun k hk => TauCeti.subsingleton_homotopyGroup_of_lt_two hz hk,
    ← ((TopCat.diskBoundary 3).integralCohomologyEquiv 2).map_eq_zero_iff,
    TopCat.integralCohomologyEquiv_naturality,
    ← (bijective_singularKronecker_hyperplaneClass hV hn).1.eq_iff' (map_zero _)]
  refine Iff.trans ?_ (singularKronecker_sphere_eq_zero_iff 0 _)
  rw [TopCat.singularKronecker_naturality, ModuleCat.hom_comp]
  -- `LinearMap.comp_apply`, which `rw` cannot apply here: the two sides write the degree of
  -- `H₂(S²; ℤ)` as `2` and as `0 + 2`
  exact Iff.rfl

end Projectivization
