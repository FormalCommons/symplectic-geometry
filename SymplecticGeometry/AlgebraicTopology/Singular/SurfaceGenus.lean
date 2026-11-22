/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.RationalCoefficients
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.CapDuality
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.AlgebraicTopology.Singular.SurfaceGenus

/-!
# The genus of surfaces

Facts about Tau Ceti's `TauCeti.surfaceGenus`, half the rank of the first rational singular
homology, rounded down. The file has the name of Tau Ceti's file on the same subject, so that the
two can merge.

## Main results

* `TauCeti.surfaceGenus_sphere_of_finrank_eq_three`: the unit sphere of a real normed space of
  dimension `3` has genus `0`, since its first rational homology vanishes (Tau Ceti's
  `ModuleCat.finrank_singularHomology_sphere_of_finrank_eq_succ`).
* `TauCeti.surfaceGenus_sphere`: the case of `S²` in `EuclideanSpace ℝ (Fin 3)`.
* `TauCeti.HomologicalOrientation.even_finrank_singularHomology_of_odd`: for a compact
  homologically oriented manifold of dimension `n = 2p` with `p` odd, the middle rational Betti
  number `finrank ℚ Hₚ(M; ℚ)` is even. By rational Poincaré duality
  (`TauCeti.HomologicalOrientation.bijective_singularCapLinearMap_fundamentalClass`), capping
  with the image of the fundamental class in `Hₙ(M; ℚ)` is injective on `Hᵖ(M; ℚ)`, and
  Tau Ceti's `TopCat.even_finrank_singularHomology_of_injective_singularCapLinearMap` turns this
  into evenness through the alternating cup product pairing.
* `TauCeti.HomologicalOrientation.even_finrank_singularHomology_one`: the case `p = 1`; a compact
  homologically oriented surface has even first rational Betti number. Together with Tau Ceti's
  `TauCeti.HomologicalOrientation.eulerChar_eq_two_sub_two_mul_genus_iff_even_finrank`, it gives
  `χ(M) = 2 - 2 · genus M` for such a surface that is connected and of finite CW type.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, Theorem 3.30
  and Proposition 3.38.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace TauCeti

/-- **The 2-sphere has genus `0`.** The unit sphere of a real normed space `E` of dimension `3`
has genus `0`, since its first rational homology vanishes. -/
@[simp]
theorem surfaceGenus_sphere_of_finrank_eq_three {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hE : Module.finrank ℝ E = 3) :
    surfaceGenus (Metric.sphere (0 : E) 1) = 0 := by
  rw [surfaceGenus_def, ModuleCat.finrank_singularHomology_sphere_of_finrank_eq_succ
    (ModuleCat.of ℚ ℚ) (d := 2) hE 1]
  simp

/-- The unit sphere `S²` of `ℝ³ = EuclideanSpace ℝ (Fin 3)` has genus `0`, since its first
rational homology vanishes. -/
theorem surfaceGenus_sphere :
    surfaceGenus (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) = 0 :=
  surfaceGenus_sphere_of_finrank_eq_three finrank_euclideanSpace_fin

/-- **The middle Betti number of a closed oriented manifold of dimension `2p`, `p` odd, is
even.** If `M` is a compact Hausdorff space with charts in a real normed space of dimension `n`
and a homological orientation, `p` is odd and `p + p = n`, then `Hₚ(M; ℚ)` has even `finrank`
over `ℚ`. `M` need not be connected. -/
theorem HomologicalOrientation.even_finrank_singularHomology_of_odd {M E : Type}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] {n p : ℕ} (o : HomologicalOrientation M E n)
    (hn : Module.finrank ℝ E = n) (hp : Odd p) (h : p + p = n) :
    Even (Module.finrank ℚ (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) p).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of M))) :=
  (TopCat.of M).even_finrank_singularHomology_of_injective_singularCapLinearMap ℚ two_ne_zero
    hp h _ (o.bijective_singularCapLinearMap_fundamentalClass hn h).injective

/-- **The first Betti number of a closed oriented surface is even.** If `M` is a compact
Hausdorff space with charts in a real normed space of dimension `2` and a homological orientation,
then `H₁(M; ℚ)` has even `finrank` over `ℚ`. `M` need not be connected. -/
theorem HomologicalOrientation.even_finrank_singularHomology_one {M E : Type}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] (o : HomologicalOrientation M E 2)
    (hn : Module.finrank ℝ E = 2) :
    Even (Module.finrank ℚ (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) 1).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of M))) :=
  o.even_finrank_singularHomology_of_odd hn odd_one rfl

end TauCeti

end
