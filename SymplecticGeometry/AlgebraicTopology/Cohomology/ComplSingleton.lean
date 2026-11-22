/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Point

/-!
# Singular cohomology of a punctured real normed space

Let `F` be a real normed space of finite dimension `d` and `x : F`. The space `F ∖ {x}` is
homotopy equivalent to the sphere `Sᵈ⁻¹`, so its singular cohomology vanishes in every positive
degree `m` with `m + 1 ≠ d`. This file proves that vanishing
(`TauCeti.isZero_singularCohomology_complSingleton_subtype_of_ne`) over a commutative ring `k`, for
projective chain coefficients `R` and any value module `N`, through the long exact sequence of the
pair `(F, F ∖ {x})`: `F` is contractible (`TauCeti.isZero_singularCohomology_of_contractibleSpace`),
so the connecting map `Hᵐ(F ∖ {x}) ⟶ Hᵐ⁺¹(F, F ∖ {x})` is injective for `m ≠ 0`, and its target
vanishes for `m + 1 ≠ d` (`TauCeti.isZero_singularCohomology_complSingleton_of_ne`). For `d = 0`
the space `F ∖ {x}` is empty, and the statement covers every positive degree.

## Main results

* `TauCeti.isZero_singularCohomology_complSingleton_subtype_of_ne`: `Hᵐ(F ∖ {x}; R, N) = 0` for
  `m ≠ 0` and `m + 1 ≠ finrank ℝ F`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1 (the long exact sequence of a pair) and Section 3.3 (local homology).
-/

public section

open CategoryTheory Limits Module

universe w

namespace TauCeti

variable {k : Type*} [CommRing k] (R N : ModuleCat.{w} k) [Module.Projective k R]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The cohomology of a punctured real vector space.** For a real normed space `F` of finite
dimension `d` and a point `x : F`, the singular cohomology `Hᵐ(F ∖ {x}; R, N)` vanishes for
`m ≠ 0` and `m + 1 ≠ d`, for projective coefficients `R` and any coefficient module `N`. -/
theorem isZero_singularCohomology_complSingleton_subtype_of_ne (x : F) {d m : ℕ}
    (h : finrank ℝ F = d) (hm : m ≠ 0) (hmd : m + 1 ≠ d) :
    IsZero ((TopCat.of ({x}ᶜ : Set F)).singularCohomology R k N m) := by
  let P := TopPair.ofSubset ({x}ᶜ : Set (TopCat.of F))
  -- In the exact sequence `Hᵐ(F) ⟶ Hᵐ(F ∖ {x}) ⟶ Hᵐ⁺¹(F, F ∖ {x})`, both ends vanish.
  exact (P.singularCohomology_exact_subspace R k N m (m + 1)).isZero_X₂
    ((isZero_singularCohomology_of_contractibleSpace R k N (TopCat.of F) hm).eq_of_src _ _)
    ((isZero_singularCohomology_complSingleton_of_ne R N (OpenPartialHomeomorph.refl F)
      (x := x) (Set.mem_univ _) h (by omega)).eq_of_tgt _ _)

end TauCeti

end
