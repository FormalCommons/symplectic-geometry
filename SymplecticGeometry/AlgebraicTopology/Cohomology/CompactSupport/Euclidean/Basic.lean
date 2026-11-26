/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Euclidean.Basic
public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Vanishing
public import SymplecticGeometry.Analysis.Convex.Opens

/-!
# Vanishing of cohomology with compact supports above the dimension

Let `F` be a finite-dimensional real normed space and `j : U → F` an open embedding. Then
`Hⁿ_c(U; R, N) = 0` for every `n > finrank ℝ F`, for projective coefficients `R`
(`TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`).

Tau Ceti proves the vanishing outside the dimension for an open embedding with convex image
(`TopCat.isZero_compactSupportCohomology_of_convex`). The open sets of `U` with convex image are
closed under intersection (`TopologicalSpace.Opens.infClosed_setOf_convex_image`) and cover `U`
(`Topology.IsOpenEmbedding.sSup_setOf_convex_image_eq_top`), so the induction over finite unions
of Hatcher's Lemma 3.36, run for vanishing alone
(`TopCat.isZero_compactSupportCohomology_of_infClosed`), carries the vanishing above the dimension
to `U`.

## Main results

* `TopCat.isZero_compactSupportCohomology_of_isOpenEmbedding`: `Hⁿ_c(U) = 0` for
  `n > finrank ℝ F` and any `U` embedded openly in `F`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Lemma 3.36 and the proof of Theorem 3.35.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Module Set

universe v

namespace TopCat

variable {k : Type v} [CommRing k] (R N : ModuleCat.{v} k) [Module.Projective k R]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {U : Type v} [TopologicalSpace U]

/-- **Cohomology with compact supports of an open subset of `F` vanishes above the dimension.**
For an open embedding `j : U → F` into a finite-dimensional real normed space,
`Hⁿ_c(U; R, N) = 0` for `n > finrank ℝ F`, for projective coefficients `R`. -/
theorem isZero_compactSupportCohomology_of_isOpenEmbedding {j : U → F} (hj : IsOpenEmbedding j)
    {n : ℕ} (hn : finrank ℝ F < n) :
    IsZero ((of U).compactSupportCohomology R k N n) := by
  have := hj.isEmbedding.t2Space
  refine isZero_compactSupportCohomology_of_infClosed R k N
    (Opens.infClosed_setOf_convex_image hj.injective) hj.sSup_setOf_convex_image_eq_top
    (fun W hW m hm ↦ ?_) hn
  refine isZero_compactSupportCohomology_of_convex R N (U := of W)
    (j := ofHom ⟨j ∘ Subtype.val, hj.continuous.comp continuous_subtypeVal⟩)
    (hj.comp W.isOpenEmbedding') ?_ (by omega)
  rwa [ConcreteCategory.hom_ofHom, ContinuousMap.coe_mk, range_comp, Subtype.range_coe]

end TopCat

end
