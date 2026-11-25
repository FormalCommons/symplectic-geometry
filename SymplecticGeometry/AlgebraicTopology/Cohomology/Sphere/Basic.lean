/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Basic
public import TauCeti.AlgebraicTopology.Disk

/-!
# Cohomology of spheres away from and in the top degree

Let `E` be a real normed space of dimension `n + 1`. The unit sphere of `E` has vanishing integral
cohomology `H^q(S^n; ℤ)` in every degree `q` other than `0` and `n`
(`TopCat.isZero_integralCohomology_sphere_of_ne`). This is Tau Ceti's
`TauCeti.isZero_singularCohomology_topCatSphere_of_ne` for `TopCat.sphere n`, carried to the unit
sphere of `E` by the homeomorphism `TauCeti.sphereHomeomorphTopCatSphere` and to the library's
integral cohomology by `TopCat.integralCohomologyEquiv`.

It also shows that, over a commutative ring `k` and with values in a `k`-module `M`, a class of
`Hⁿ⁺¹(Sⁿ⁺¹; M)` vanishes exactly when its Kronecker pairing with Tau Ceti's generator
`TauCeti.singularHomologyTopCatSphereGenerator` of `Hₙ₊₁(Sⁿ⁺¹; k)` vanishes
(`TopCat.singularKronecker_singularHomologyTopCatSphereGenerator_eq_zero_iff`), since that pairing
is the linear equivalence `TauCeti.singularCohomologyTopCatSphereEquiv`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.2 (the cohomology of
  spheres).
-/

public section

open CategoryTheory Limits MonoidalCategory Module

namespace TopCat

/-- **The integral cohomology of a sphere vanishes away from degrees `0` and `n`.** For a real
normed space `E` of dimension `n + 1`, `H^q(S^n; ℤ) = 0` for the unit sphere `S^n` of `E` and every
`q ≠ 0, n`. -/
theorem isZero_integralCohomology_sphere_of_ne {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n q : ℕ} (hE : finrank ℝ E = n + 1) (hq₀ : q ≠ 0) (hq : q ≠ n) :
    IsZero ((TopCat.of (Metric.sphere (0 : E) 1)).integralCohomology q) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq₀
  have hz := TauCeti.isZero_singularCohomology_topCatSphere_of_ne ℤ (𝟙_ (ModuleCat.{0} ℤ)) n q
    (by omega)
  have : Subsingleton ((TopCat.sphere.{0} n).integralCohomology (q + 1)) :=
    ((TopCat.sphere.{0} n).integralCohomologyEquiv (q + 1)).toEquiv.subsingleton_congr.2
      (ModuleCat.subsingleton_of_isZero hz)
  exact (ModuleCat.isZero_of_subsingleton
    ((TopCat.sphere.{0} n).integralCohomology (q + 1))).of_iso
    ((TauCeti.singularCohomologyFunctor _ ℤ _ (q + 1)).mapIso
      (TopCat.isoOfHomeo (TauCeti.sphereHomeomorphTopCatSphere.{0} hE)).symm.op)

/-- A class `α ∈ Hⁿ⁺¹(Sⁿ⁺¹; M)` is zero if and only if its Kronecker pairing with the generator
of `Hₙ₊₁(Sⁿ⁺¹; k)` is zero. -/
theorem singularKronecker_singularHomologyTopCatSphereGenerator_eq_zero_iff
    {k : Type} [CommRing k] (M : ModuleCat.{0} k) (n : ℕ)
    (α : (TopCat.sphere.{0} (n + 1)).singularCohomology (ModuleCat.of k k) k M (n + 1)) :
    (TopCat.sphere (n + 1)).singularKronecker k (n + 1) α
      (TauCeti.singularHomologyTopCatSphereGenerator k n) = 0 ↔ α = 0 := by
  rw [← TauCeti.singularCohomologyTopCatSphereEquiv_apply]
  exact LinearEquiv.map_eq_zero_iff _

end TopCat

end
