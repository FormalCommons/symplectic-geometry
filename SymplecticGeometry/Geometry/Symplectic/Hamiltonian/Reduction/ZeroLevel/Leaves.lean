/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Reduction.ZeroLevel.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold

/-!
# The zero level of an equivariant moment map is coisotropic

Let a Lie group `G` act smoothly on a Hausdorff manifold `(M, σ)` with nondegenerate `σ` and
coadjoint-equivariant moment map `μ : M → 𝔤*`, freely at the points of `Z = μ⁻¹(0)`. With the
atlases of `ZeroLevel/Basic.lean`, this file describes the form `i^* σ` that `σ` induces on `Z`
through the inclusion `i : Z → M`.

* `isCoisotropicMap_coe_zeroLevel`: the inclusion `i` is a coisotropic map. Its tangent images
  are the kernels `ker dμ_z` (`range_mfderiv_coe_zeroLevel`), and `ker dμ_z` is coisotropic since
  `0` is fixed by the coadjoint action (Tau Ceti's `IsMomentMap.isCoisotropic_ker_differential_iff`
  with `lieAnnihilator_zero`). No dimension count is needed, and an empty level is no special case.
* `ker_bilinFormAt_mpullback_coe_zeroLevel`: if `G` also acts properly on `Z`, the kernel of
  `(i^* σ)_z` is the kernel of the differential of the orbit projection `π : Z → Z / G` at `z`:
  the null directions of the level are its orbit directions. This combines Tau Ceti's
  `IsMomentMap.ker_bilinFormAt_mpullback` at `c = 0` with
  `ker_mfderiv_quotientMk_zeroLevel_eq_comap_map_lieAnnihilator`.

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`, beside those
of `ZeroLevel/Basic.lean`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Proposition 5.4.13.
* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* K. Meyer, *Symmetries and integrals in mechanics*, in *Dynamical Systems* (M. Peixoto, ed.),
  Academic Press, 1973, 259–273.
-/

public section

open Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {n : ℕ}
  (h : σ.IsEquivariantMomentMap μ) (hσ : σ.IsNondegenerate)
  (hfree : ∀ x, μ x = 0 → MulAction.stabilizer G x = ⊥)
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)

/-- **The zero level is coisotropic.** If `σ` is nondegenerate and `G` acts freely at every point
of `μ⁻¹(0)`, the inclusion of the zero level into `M`, for the atlas `zeroLevelChartedSpace`, is a
coisotropic map: each tangent image `ker dμ_z` contains its symplectic complement. -/
theorem isCoisotropicMap_coe_zeroLevel :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    hσ.IsCoisotropicMap 𝓘(ℝ, Fin n → ℝ) (Subtype.val : h.zeroLevel → M) := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  refine IsNondegenerate.isCoisotropicMap_iff.2 fun z ↦ ?_
  rw [h.range_mfderiv_coe_zeroLevel hσ hfree hn z,
    h.toIsMomentMap.isCoisotropic_ker_differential_iff hσ (h.momentCocycle_eq_zero z),
    h.mem_zeroLevel.1 z.property, lieAnnihilator_zero]

/-- **The null directions of the zero level are the orbit directions.** If moreover `G` acts
properly on the zero level, then at each of its points `z` the kernel of the form `i^* σ` induced
by the inclusion `i` is the kernel of the differential at `z` of the orbit projection
`μ⁻¹(0) → μ⁻¹(0) / G`, for the atlases `zeroLevelChartedSpace` and
`zeroLevelQuotientChartedSpace`. -/
theorem ker_bilinFormAt_mpullback_coe_zeroLevel [ProperSMul G h.zeroLevel] (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
    haveI := h.isManifold_zeroLevel hσ hfree hn
    LinearMap.ker ((SmoothForm.mpullback Subtype.val
        (h.isSmoothEmbedding_coe_zeroLevel hσ hfree hn).contMDiff σ).bilinFormAt z) =
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
        (Quotient.mk (MulAction.orbitRel G h.zeroLevel)) z).ker := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  have := h.isManifold_zeroLevel hσ hfree hn
  rw [h.ker_mfderiv_quotientMk_zeroLevel_eq_comap_map_lieAnnihilator hσ hfree hn,
    h.toIsMomentMap.ker_bilinFormAt_mpullback _ (hσ.nondegenerate_bilinFormAt z)
      (h.momentCocycle_eq_zero z) (h.range_mfderiv_coe_zeroLevel hσ hfree hn z),
    h.mem_zeroLevel.1 z.property]

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti

end
