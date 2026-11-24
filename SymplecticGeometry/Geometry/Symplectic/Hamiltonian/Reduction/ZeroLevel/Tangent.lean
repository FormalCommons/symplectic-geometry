/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Reduction.ZeroLevel.Leaves
public import TauCeti.Geometry.Symplectic.LinearReduction

/-!
# The tangent spaces of the reduced space at zero, and Marsden–Weinstein reduction

Let a Lie group `G` act smoothly on a Hausdorff manifold `(M, σ)` with nondegenerate `σ` and
coadjoint-equivariant moment map `μ : M → 𝔤*`, freely at the points of `Z = μ⁻¹(0)` and properly
on `Z`. With the atlases of `ZeroLevel/Basic.lean`, write `i : Z → M` for the inclusion and
`π : Z → Z / G` for the orbit projection. At a point `z` of `Z`, let `K = ker dμ_z` and let
`K_red = K ⧸ (K ∩ K^σ)` be its linear symplectic reduction
(`TauCeti.SymplecticForm.ReducedSpace`), on which `σ_z` induces the symplectic form
`TauCeti.SymplecticForm.reduction`.

* `zeroLevelTangentEquiv`: the linear equivalence `K_red ≃ T_{π z}(Z / G)`. The differential of
  `i` identifies `T_z Z` with `K` (`range_mfderiv_coe_zeroLevel`), and under it the kernel of
  `dπ_z`, which is the kernel of `i^* σ` at `z` (`ker_bilinFormAt_mpullback_coe_zeroLevel`), goes
  to `K ∩ K^σ`; since `dπ_z` is onto, it descends to the equivalence.
* `zeroLevelTangentEquiv_mk` and `zeroLevelTangentEquiv_symm_mfderiv_quotientMk`: the class of
  `di_z v` goes to `dπ_z v`, and back.
* `map_subtype_ker_restrict_zeroLevel`: the null directions `K ∩ K^σ` divided out are the orbit
  directions `𝔤 · z`, so that `K_red` is `ker dμ_z / 𝔤 · z`.
* `eval₂_zeroLevelTangentEquiv` and `isSymplectomorphism_zeroLevelTangentEquiv`: if `η` is a
  two-form on `Z / G` with `π^* η = i^* σ`, then the equivalence carries the reduced form of `σ_z`
  to `η` at `π z`.
* `SymplecticGeometry.symplecticReduction_zeroLevel`: the theorem of Marsden, Weinstein and
  Meyer at the zero level, in the sign of `DESIGN.md`, where the moment map is `fun x ↦ -μ x` for
  Tau Ceti's predicates. It collects the results of `ZeroLevel/Basic.lean`,
  `ZeroLevel/Leaves.lean` and this file.

The building declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`,
beside those of `ZeroLevel/Basic.lean`; the milestone is in `SymplecticGeometry`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Proposition 5.4.13 and Remark 5.4.14.
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001Lectures],
  Lecture 23.
* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* K. Meyer, *Symmetries and integrals in mechanics*, in *Dynamical Systems* (M. Peixoto, ed.),
  Academic Press, 1973, 259–273.
-/

public section

noncomputable section

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

/-- The differential of the inclusion of the zero level at `z`, with values in `ker dμ_z`, followed
by the projection to the reduced space of `ker dμ_z`. It is onto, with kernel the kernel of the
pulled-back form at `z`. -/
private def tangentToReducedSpace (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    TangentSpace 𝓘(ℝ, Fin n → ℝ) z →ₗ[ℝ]
      (hσ.symplecticFormAt (z : M)).ReducedSpace (LinearMap.ker (h.differential z)) :=
  letI := h.zeroLevelChartedSpace hσ hfree hn
  Submodule.mkQ _ ∘ₗ
    (mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.zeroLevel → M) z).toLinearMap.codRestrict _
      fun v ↦ h.range_mfderiv_coe_zeroLevel hσ hfree hn z ▸ LinearMap.mem_range_self _ v

private theorem tangentToReducedSpace_apply (z : h.zeroLevel) (v) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    h.tangentToReducedSpace hσ hfree hn z v = Submodule.Quotient.mk
      ⟨mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.zeroLevel → M) z v,
        h.range_mfderiv_coe_zeroLevel hσ hfree hn z ▸ LinearMap.mem_range_self _ v⟩ :=
  (rfl)

private theorem surjective_tangentToReducedSpace (z : h.zeroLevel) :
    Function.Surjective (h.tangentToReducedSpace hσ hfree hn z) := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H u =>
  obtain ⟨v, hv⟩ : (u : TangentSpace I' (z : M)) ∈ LinearMap.range
      (mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.zeroLevel → M) z).toLinearMap := by
    rw [h.range_mfderiv_coe_zeroLevel hσ hfree hn z]
    exact u.property
  exact ⟨v, by rw [tangentToReducedSpace_apply]; congr 1; exact Subtype.ext hv⟩

private theorem ker_tangentToReducedSpace [ProperSMul G h.zeroLevel] (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
    LinearMap.ker (h.tangentToReducedSpace hσ hfree hn z) =
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
        (Quotient.mk (MulAction.orbitRel G h.zeroLevel)) z).ker := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  have := h.isManifold_zeroLevel hσ hfree hn
  rw [← h.ker_bilinFormAt_mpullback_coe_zeroLevel hσ hfree hn]
  have hrange := h.range_mfderiv_coe_zeroLevel hσ hfree hn z
  ext v
  rw [LinearMap.mem_ker, tangentToReducedSpace_apply, SymplecticForm.ReducedSpace.mk_eq_zero_iff,
    SymplecticForm.mem_orthogonal_iff', LinearMap.mem_ker, LinearMap.ext_iff]
  simp only [LinearMap.zero_apply, SmoothForm.bilinFormAt_apply, SmoothForm.eval₂_mpullback]
  refine ⟨fun hv w ↦ ?_, fun hv y hy ↦ ?_⟩
  · rw [← IsNondegenerate.symplecticFormAt_apply hσ]
    exact hv _ (hrange ▸ LinearMap.mem_range_self _ w)
  · obtain ⟨w, rfl⟩ := hrange ▸ hy
    simpa [hσ.toBilinForm_symplecticFormAt, SmoothForm.bilinFormAt_apply] using hv w

/-- **The tangent space of the reduced space at zero.** If `σ` is nondegenerate and `G` acts
freely at every point of `μ⁻¹(0)` and properly on the zero level, then at each point `z` of the
zero level the linear symplectic reduction of `ker dμ_z`, the quotient of `ker dμ_z` by its
intersection with its `σ_z`-orthogonal, is linearly equivalent to the tangent space of the
reduced space `μ⁻¹(0) / G` at the orbit of `z`: the class of `di_z v` goes to `dπ_z v`, for the
inclusion `i` and the orbit projection `π`. -/
def zeroLevelTangentEquiv [ProperSMul G h.zeroLevel] (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
    (hσ.symplecticFormAt (z : M)).ReducedSpace (LinearMap.ker (h.differential z)) ≃ₗ[ℝ]
      TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
        (Quotient.mk (MulAction.orbitRel G h.zeroLevel) z) :=
  letI := h.zeroLevelChartedSpace hσ hfree hn
  letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
  ((h.tangentToReducedSpace hσ hfree hn z).quotKerEquivOfSurjective
      (h.surjective_tangentToReducedSpace hσ hfree hn z)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (h.ker_tangentToReducedSpace hσ hfree hn z) ≪≫ₗ
    (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
        (Quotient.mk (MulAction.orbitRel G h.zeroLevel)) z).toLinearMap.quotKerEquivOfSurjective
      ((h.isSubmersion_quotientMk_zeroLevel hσ hfree hn).surjective_mfderiv (by simp) z)

/-- `zeroLevelTangentEquiv` sends the class of `di_z v` to `dπ_z v`, for a tangent vector `v` of
the zero level at `z`, the inclusion `i` and the orbit projection `π`. -/
@[simp]
theorem zeroLevelTangentEquiv_mk [ProperSMul G h.zeroLevel] (z : h.zeroLevel) (v) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
    h.zeroLevelTangentEquiv hσ hfree hn z (Submodule.Quotient.mk
        ⟨mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.zeroLevel → M) z v,
          h.range_mfderiv_coe_zeroLevel hσ hfree hn z ▸ LinearMap.mem_range_self _ v⟩) =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
        (Quotient.mk (MulAction.orbitRel G h.zeroLevel)) z v := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  let := h.zeroLevelQuotientChartedSpace hσ hfree hn
  rw [zeroLevelTangentEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    ← tangentToReducedSpace_apply, (LinearEquiv.symm_apply_eq _).2
      (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ v).symm,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    ContinuousLinearMap.coe_coe]

/-- The inverse of `zeroLevelTangentEquiv` sends `dπ_z v` to the class of `di_z v`, for a tangent
vector `v` of the zero level at `z`, the inclusion `i` and the orbit projection `π`. -/
theorem zeroLevelTangentEquiv_symm_mfderiv_quotientMk [ProperSMul G h.zeroLevel]
    (z : h.zeroLevel) (v) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
    (h.zeroLevelTangentEquiv hσ hfree hn z).symm
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
          (Quotient.mk (MulAction.orbitRel G h.zeroLevel)) z v) =
      Submodule.Quotient.mk
        ⟨mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.zeroLevel → M) z v,
          h.range_mfderiv_coe_zeroLevel hσ hfree hn z ▸ LinearMap.mem_range_self _ v⟩ := by
  rw [LinearEquiv.symm_apply_eq, zeroLevelTangentEquiv_mk]

omit [I'.Boundaryless] [T2Space M] in
/-- **The directions divided out are the orbit directions.** At a point `z` of the zero level,
the null directions `ker dμ_z ∩ (ker dμ_z)^σ` of `σ_z` on `ker dμ_z`, which the reduced space of
`ker dμ_z` divides out, are the orbit tangent space `𝔤 · z`. -/
theorem map_subtype_ker_restrict_zeroLevel (z : h.zeroLevel) :
    (LinearMap.ker ((hσ.symplecticFormAt (z : M)).toBilinForm.restrict
        (LinearMap.ker (h.differential z)))).map (LinearMap.ker (h.differential z)).subtype =
      (InfinitesimalAction.fundamental I G I' M).orbitTangent z := by
  rw [SymplecticForm.map_subtype_ker_restrict, SymplecticForm.orthogonal_def,
    hσ.toBilinForm_symplecticFormAt,
    h.toIsMomentMap.ker_differential_inf_orthogonal (hσ.nondegenerate_bilinFormAt z)
      (h.momentCocycle_eq_zero z), h.mem_zeroLevel.1 z.property, lieAnnihilator_zero,
    LieSubalgebra.top_toSubmodule, Submodule.map_top, InfinitesimalAction.orbitTangent_eq_range]

/-- **The reduced form on tangent spaces.** Let `η` be a two-form on the reduced space
`μ⁻¹(0) / G` with `π^* η = i^* σ`, for the orbit projection `π` and the inclusion `i`. Then for
`v, w ∈ ker dμ_z`, the value of `η` at the orbit of `z` on the images under
`zeroLevelTangentEquiv` of the classes of `v` and `w` is `σ_z(v, w)`. -/
theorem eval₂_zeroLevelTangentEquiv [ProperSMul G h.zeroLevel] (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
    haveI := h.isManifold_zeroLevel hσ hfree hn
    haveI := h.isManifold_zeroLevelQuotient hσ hfree hn
    ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
        (MulAction.orbitRel.Quotient G h.zeroLevel),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_zeroLevel hσ hfree hn).contMDiff η =
          SmoothForm.mpullback Subtype.val (h.isSmoothEmbedding_coe_zeroLevel hσ hfree hn).contMDiff
            σ →
        ∀ v w : LinearMap.ker (h.differential z),
          SmoothBundleForm.eval₂ η (Quotient.mk (MulAction.orbitRel G h.zeroLevel) z)
              (h.zeroLevelTangentEquiv hσ hfree hn z (Submodule.Quotient.mk v))
              (h.zeroLevelTangentEquiv hσ hfree hn z (Submodule.Quotient.mk w)) =
            SmoothBundleForm.eval₂ σ z v w := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  let := h.zeroLevelQuotientChartedSpace hσ hfree hn
  have := h.isManifold_zeroLevel hσ hfree hn
  have := h.isManifold_zeroLevelQuotient hσ hfree hn
  have hrange := h.range_mfderiv_coe_zeroLevel hσ hfree hn z
  intro η hη ⟨v, hv⟩ ⟨w, hw⟩
  obtain ⟨v', hv'⟩ := hrange ▸ hv
  obtain rfl : mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.zeroLevel → M) z v' = v := hv'
  obtain ⟨w', hw'⟩ := hrange ▸ hw
  obtain rfl : mfderiv 𝓘(ℝ, Fin n → ℝ) I' (Subtype.val : h.zeroLevel → M) z w' = w := hw'
  rw [zeroLevelTangentEquiv_mk, zeroLevelTangentEquiv_mk,
    ← SmoothForm.eval₂_mpullback _ (h.isSubmersion_quotientMk_zeroLevel hσ hfree hn).contMDiff, hη]
  exact SmoothForm.eval₂_mpullback _ _ _ _ _ _

/-- **The tangent spaces of the reduced space, symplectically.** If `η` is a nondegenerate
two-form on the reduced space `μ⁻¹(0) / G` with `π^* η = i^* σ`, then at each point `z` of the
zero level, `zeroLevelTangentEquiv` is a symplectomorphism from the linear symplectic reduction of
`(ker dμ_z, σ_z)` to the tangent space of `μ⁻¹(0) / G` at the orbit of `z` with the form `η`. -/
theorem isSymplectomorphism_zeroLevelTangentEquiv [ProperSMul G h.zeroLevel] (z : h.zeroLevel) :
    letI := h.zeroLevelChartedSpace hσ hfree hn
    letI := h.zeroLevelQuotientChartedSpace hσ hfree hn
    haveI := h.isManifold_zeroLevel hσ hfree hn
    haveI := h.isManifold_zeroLevelQuotient hσ hfree hn
    ∀ (η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
        (MulAction.orbitRel.Quotient G h.zeroLevel)) (hη : η.IsNondegenerate),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_zeroLevel hσ hfree hn).contMDiff η =
          SmoothForm.mpullback Subtype.val (h.isSmoothEmbedding_coe_zeroLevel hσ hfree hn).contMDiff
            σ →
        SymplecticForm.IsSymplectomorphism
          ((hσ.symplecticFormAt (z : M)).reduction (LinearMap.ker (h.differential z)))
          (hη.symplecticFormAt (Quotient.mk (MulAction.orbitRel G h.zeroLevel) z))
          (h.zeroLevelTangentEquiv hσ hfree hn z) := by
  let := h.zeroLevelChartedSpace hσ hfree hn
  let := h.zeroLevelQuotientChartedSpace hσ hfree hn
  have := h.isManifold_zeroLevel hσ hfree hn
  have := h.isManifold_zeroLevelQuotient hσ hfree hn
  intro η hη hpull
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H v =>
  induction y using Submodule.Quotient.induction_on with
  | H w =>
  rw [IsNondegenerate.symplecticFormAt_apply, SymplecticForm.reduction_mk,
    IsNondegenerate.symplecticFormAt_apply]
  exact h.eval₂_zeroLevelTangentEquiv hσ hfree hn z η hpull v w

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti

namespace SymplecticGeometry

open TauCeti TauCeti.SmoothTwoForm TauCeti.SmoothTwoForm.IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] {n : ℕ}

/-- **Marsden–Weinstein reduction at zero.** Let a connected Lie group `G` act smoothly by
symplectomorphisms on a Hausdorff symplectic manifold `(M, σ)` with equivariant moment map `μ`,
in the sign of `DESIGN.md` (so that `fun x ↦ -μ x` is a moment map for Tau Ceti's predicates).
Suppose that `G` acts freely at the points of `Z = μ⁻¹(0)` and properly on `Z`, and let
`n = dim M - dim 𝔤`. Then, for the atlases `zeroLevelChartedSpace` of `Z` and
`zeroLevelQuotientChartedSpace` of `Z / G`, with `i : Z → M` the inclusion and `π : Z → Z / G` the
orbit projection:
1. `0` is a regular value of `μ` (`h.differential x` is `-dμ_x`);
2. `Z` is a manifold, `i` is a smooth embedding, and `n + dim 𝔤 = dim M` if `Z` is nonempty;
3. `i` is coisotropic;
4. the leaves of the characteristic foliation of `i` are the `G`-orbits;
5. `Z / G` is a manifold, with a unique symplectic form `ω_red` such that `π^* ω_red = i^* σ`;
6. `dim (Z / G) + 2 dim 𝔤 = dim M` if `Z` is nonempty;
7. at each `z ∈ Z`, the null directions of `σ_z` on `ker dμ_z` are the orbit directions `𝔤 · z`,
  and for every symplectic `η` on `Z / G` with `π^* η = i^* σ`, `zeroLevelTangentEquiv` is a
  symplectomorphism from the linear reduction `ker dμ_z ⧸ (𝔤 · z)` of `σ_z` to the tangent space
  of `Z / G` at `π z` with the form `η`.

Milestone: *Marsden–Weinstein reduction*. -/
theorem symplecticReduction_zeroLevel [ConnectedSpace G] {σ : SmoothTwoForm I' M}
    {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (h : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hfree : ∀ x, μ x = 0 → MulAction.stabilizer G x = ⊥) [ProperSMul G h.zeroLevel]
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n) :
    have hfree' : ∀ x, -μ x = 0 → MulAction.stabilizer G x = ⊥ :=
      fun x hx ↦ hfree x (neg_eq_zero.1 hx)
    letI := h.zeroLevelChartedSpace hσ.isNondegenerate hfree' hn
    letI := h.zeroLevelQuotientChartedSpace hσ.isNondegenerate hfree' hn
    haveI := h.isManifold_zeroLevel hσ.isNondegenerate hfree' hn
    haveI := h.isManifold_zeroLevelQuotient hσ.isNondegenerate hfree' hn
    haveI : IsManifold 𝓘(ℝ, Fin n → ℝ) (1 + 1) h.zeroLevel := .of_le (n := ∞) (by norm_num)
    (∀ x, μ x = 0 → Function.Surjective (h.differential x)) ∧
    (IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ h.zeroLevel ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin n → ℝ) I' ∞ (Subtype.val : h.zeroLevel → M) ∧
      (Nonempty h.zeroLevel → n + finrank ℝ (GroupLieAlgebra I G) = finrank ℝ E')) ∧
    hσ.isNondegenerate.IsCoisotropicMap 𝓘(ℝ, Fin n → ℝ) (Subtype.val : h.zeroLevel → M) ∧
    (∀ z : h.zeroLevel,
      ((h.isCoisotropicMap_coe_zeroLevel hσ.isNondegenerate hfree' hn).characteristicFoliation
        (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree' hn).isImmersion
        (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree' hn).contMDiff hσ.isClosed
        le_rfl).leaf z = MulAction.orbit G z) ∧
    (IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ)) ∞
        (MulAction.orbitRel.Quotient G h.zeroLevel) ∧
      ∃! η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
          (MulAction.orbitRel.Quotient G h.zeroLevel),
        η.IsSymplectic ∧
          SmoothForm.mpullback _
              (h.isSubmersion_quotientMk_zeroLevel hσ.isNondegenerate hfree' hn).contMDiff η =
            SmoothForm.mpullback Subtype.val
              (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree' hn).contMDiff σ) ∧
    (Nonempty h.zeroLevel →
      finrank ℝ (ProperSMul.QuotientModelSpace E (Fin n → ℝ)) +
        2 * finrank ℝ (GroupLieAlgebra I G) = finrank ℝ E') ∧
    ∀ z : h.zeroLevel,
      (LinearMap.ker ((hσ.isNondegenerate.symplecticFormAt (z : M)).toBilinForm.restrict
          (LinearMap.ker (h.differential z)))).map (LinearMap.ker (h.differential z)).subtype =
        (InfinitesimalAction.fundamental I G I' M).orbitTangent z ∧
      ∀ (η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin n → ℝ))
          (MulAction.orbitRel.Quotient G h.zeroLevel)) (hη : η.IsSymplectic),
        SmoothForm.mpullback _
            (h.isSubmersion_quotientMk_zeroLevel hσ.isNondegenerate hfree' hn).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree' hn).contMDiff σ →
        SymplecticForm.IsSymplectomorphism
          ((hσ.isNondegenerate.symplecticFormAt (z : M)).reduction
            (LinearMap.ker (h.differential z)))
          (hη.isNondegenerate.symplecticFormAt (Quotient.mk (MulAction.orbitRel G h.zeroLevel) z))
          (h.zeroLevelTangentEquiv hσ.isNondegenerate hfree' hn z) := by
  intro hfree'
  let := h.zeroLevelChartedSpace hσ.isNondegenerate hfree' hn
  let := h.zeroLevelQuotientChartedSpace hσ.isNondegenerate hfree' hn
  have := h.isManifold_zeroLevel hσ.isNondegenerate hfree' hn
  have := h.isManifold_zeroLevelQuotient hσ.isNondegenerate hfree' hn
  refine ⟨fun x hx ↦ h.forall_differential_surjective_of_stabilizer_eq_bot hσ.isNondegenerate
      hfree' x (neg_eq_zero.2 hx),
    ⟨h.isManifold_zeroLevel hσ.isNondegenerate hfree' hn,
      h.isSmoothEmbedding_coe_zeroLevel hσ.isNondegenerate hfree' hn,
      fun ⟨z⟩ ↦ h.finrank_add_finrank_zeroLevel hσ.isNondegenerate hfree' hn z⟩,
    h.isCoisotropicMap_coe_zeroLevel hσ.isNondegenerate hfree' hn,
    h.leaf_characteristicFoliation_zeroLevel hfree' hn hσ,
    ⟨h.isManifold_zeroLevelQuotient hσ.isNondegenerate hfree' hn,
      h.existsUnique_isSymplectic_mpullback_quotientMk_zeroLevel_eq_mpullback hσ hG hfree' hn⟩,
    fun ⟨z⟩ ↦ h.finrank_quotientModelSpace_zeroLevel hσ.isNondegenerate hfree' hn z,
    fun z ↦ ⟨h.map_subtype_ker_restrict_zeroLevel hσ.isNondegenerate z,
      fun η hη hpull ↦ h.isSymplectomorphism_zeroLevelTangentEquiv hσ.isNondegenerate hfree' hn z
        η hη.isNondegenerate hpull⟩⟩

end SymplecticGeometry

end
