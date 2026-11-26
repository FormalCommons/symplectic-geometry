/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.ComplexProjectiveSpace.SecondHomology
import SymplecticGeometry.AlgebraicTopology.Cohomology.Sphere.Basic
import SymplecticGeometry.Topology.ComplexProjectiveSpace.SimplyConnected
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.DiskBoundary
import TauCeti.AlgebraicTopology.Sphere.PointedMap
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact
import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# Null-homotopic maps from spheres to complex projective space

Let `V` be a complex normed space with `finrank ℂ V = n + 1`, and let
`h = Projectivization.hyperplaneClass V ∈ H²(ℙ ℂ V; ℤ)`. This file shows that a continuous map
`g : S² → ℙ ℂ V`, with `S²` the sphere `TopCat.diskBoundary 3`, is null-homotopic if and only if
the pull-back `g^* h` vanishes in `H²(S²; ℤ)`
(`Projectivization.nullhomotopic_iff_singularCohomologyMap_hyperplaneClass_eq_zero`). For `n = 0`
both sides hold, since `ℙ ℂ V` is a point.

In dimensions `3` to `2n`, every map from a sphere to `ℙ ℂ V` is null-homotopic
(`Projectivization.nullhomotopic_of_three_le_of_le`). The sphere is the unit sphere of any real
normed space of that dimension plus one, such as the spheres of the characteristic maps of a CW
complex, which carry the sup norm.

## Proof

For `n ≠ 0`, `ℙ ℂ V` is simply connected (`Projectivization.instSimplyConnectedSpaceComplex`), so
by the Hurewicz theorem `g` is null-homotopic exactly when it sends the generator `[S²]`
of `H₂(S²; ℤ)` to zero (`TopCat.Hom.nullhomotopic_iff_singularHomologyMap_eq_zero`). The pairing
with `h` is injective on `H₂(ℙ ℂ V; ℤ)`
(`Projectivization.bijective_singularKronecker_hyperplaneClass`), and
`⟨h, g_*[S²]⟩ = ⟨g^* h, [S²]⟩` (`TopCat.singularKronecker_naturality`). Finally a class of
`H²(S²; ℤ)` is zero exactly when it vanishes on `[S²]`, since evaluation on `[S²]` is a linear
equivalence `H²(S²; ℤ) ≃ ℤ`
(`TopCat.singularKronecker_singularHomologyTopCatSphereGenerator_eq_zero_iff`).

In dimensions `3 ≤ k ≤ 2n`, Tau Ceti shows that `πₖ` of its model `ComplexProjectiveSpace n` of
`ℂℙⁿ` vanishes, through the long exact sequence of the Hopf fibration
(`TauCeti.ComplexProjectiveSpace.subsingleton_homotopyGroup`, with `πₖ` modelled on the cube
`I^(Option (Fin (k - 1)))`). A map from a sphere whose homotopy group is trivial is null-homotopic
(`ContinuousMap.nullhomotopic_of_subsingleton_homotopyGroup`), and the statement is carried to
`ℙ ℂ V` along `Projectivization.complexProjectiveSpaceHomeomorph` and to other spheres along
`TauCeti.sphereHomeomorphOfFinrankEq`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (the universal
  coefficient theorem) and Section 4.2 (the Hurewicz theorem, and the long exact
  sequence of the Hopf fibration `S¹ → S²ⁿ⁺¹ → ℂPⁿ`).
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

/-- A class of `Hᵈ⁺²(Sᵈ⁺²; ℤ)` vanishes exactly when it vanishes on the generator `[Sᵈ⁺²]` of
`H_{d+2}(Sᵈ⁺²; ℤ)`, with `[Sᵈ⁺²]` written out as the class that
`TopCat.Hom.nullhomotopic_iff_singularHomologyMap_eq_zero` names; this is
`TopCat.singularKronecker_singularHomologyTopCatSphereGenerator_eq_zero_iff`. A step of the proof
of `nullhomotopic_iff_singularCohomologyMap_hyperplaneClass_eq_zero`, at `d = 0`. -/
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
  exact TopCat.singularKronecker_singularHomologyTopCatSphereGenerator_eq_zero_iff _ (d + 1) c

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
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ hV
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
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


section Higher

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℂ W] [T2Space W]

open Metric TauCeti in
/-- **Maps from spheres of dimension `3` to `2n` into `ℂPⁿ` are null-homotopic.** Let `W` be a
complex vector space of dimension `n + 1` and `E` a real normed space of dimension `k + 1`, with
`3 ≤ k ≤ 2n`. Every continuous map from the unit sphere of `E` to `ℙ ℂ W` is null-homotopic. -/
theorem nullhomotopic_of_three_le_of_le (hV : finrank ℂ W = n + 1) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} (hE : finrank ℝ E = k + 1) (hk : 3 ≤ k)
    (hkn : k ≤ 2 * n) (g : C(sphere (0 : E) 1, ℙ ℂ W)) : g.Nullhomotopic := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let e : sphere (0 : EuclideanSpace ℝ (Fin (j + 1 + 1))) 1 ≃ₜ sphere (0 : E) 1 :=
    sphereHomeomorphOfFinrankEq (by rw [finrank_euclideanSpace_fin, hE])
  let c := complexProjectiveSpaceHomeomorph hV
  let g' : C(sphere (0 : EuclideanSpace ℝ (Fin (j + 1 + 1))) 1, ComplexProjectiveSpace n) :=
    (c.symm : C(ℙ ℂ W, ComplexProjectiveSpace n)).comp (g.comp e)
  have hg' : g'.Nullhomotopic := by
    refine ContinuousMap.nullhomotopic_of_subsingleton_homotopyGroup g' ?_
    obtain ⟨v, hv⟩ := ComplexProjectiveSpace.mk_surjective n (g' (sphereNorthPole (j + 1)))
    have : Nontrivial (Fin j) := Fin.nontrivial_iff_two_le.2 (by omega)
    have := ComplexProjectiveSpace.subsingleton_homotopyGroup (N := Fin j) v (by simp; omega)
    rw [← hv]
    exact (HomotopyGroup.congrEquiv (finSuccEquiv j)).subsingleton
  have h := (hg'.comp_right (c : C(ComplexProjectiveSpace n, ℙ ℂ W))).comp_left
    (e.symm : C(sphere (0 : E) 1, sphere (0 : EuclideanSpace ℝ (Fin (j + 1 + 1))) 1))
  convert h using 1
  ext y
  simp [g']

end Higher

end Projectivization
