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
# Integral cohomology of unit spheres away from the top degree

Let `E` be a real normed space of dimension `n + 1`. The unit sphere of `E` has vanishing integral
cohomology `H^q(S^n; ℤ)` in every degree `q` other than `0` and `n`
(`TopCat.isZero_integralCohomology_sphere_of_ne`). This is Tau Ceti's
`TauCeti.isZero_singularCohomology_topCatSphere_of_ne` for `TopCat.sphere n`, carried to the unit
sphere of `E` by the homeomorphism `TauCeti.sphereHomeomorphTopCatSphere` and to the library's
integral cohomology by `TopCat.integralCohomologyEquiv`.

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
  let φ := TopCat.isoOfHomeo (X := TopCat.of (Metric.sphere (0 : E) 1))
    (TauCeti.sphereHomeomorphTopCatSphere.{0} hE)
  -- Pull-back along the homeomorphism is surjective, with section the pull-back along its inverse.
  have hs : Function.Surjective (TopCat.singularCohomologyMap φ.hom (q + 1)
      (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := ModuleCat.of ℤ ℤ)) := fun x ↦
    ⟨TopCat.singularCohomologyMap φ.inv (q + 1) x, by
      rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, φ.hom_inv_id,
        TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]⟩
  have := hs.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end TopCat

end
