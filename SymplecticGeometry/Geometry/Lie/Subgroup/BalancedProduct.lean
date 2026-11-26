/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Lie.Subgroup.BalancedProduct
public import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
public import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Slice

/-!
# The vertical directions of the projection `G × Z → G ×_K Z`

Let `G` be a finite-dimensional real Lie group, `K` a closed subgroup with a Lie group structure
for which it acts smoothly on `G` by left multiplication, and `Z` a manifold on which `K` acts
smoothly. Tau Ceti's `TauCeti.Geometry.Lie.Subgroup.BalancedProduct` makes the balanced product
`G ×_K Z`, the quotient of `G × Z` by `h • (g, z) = (g h⁻¹, h • z)`, a smooth manifold
(`TauCeti.BalancedProduct.rightTranslationChartedSpace`) for which the projection
`π : (g, z) ↦ [g, z]` is a submersion. This file describes the kernel of `dπ`.

The action of `K` on `G` by `h • g = g h⁻¹` has the fundamental vector field
`ξ_G(g) = -d(L_g)(ξ')`, where `ξ'` is the image of `ξ ∈ Lie(K)` in `Lie(G)`: the orbit map of `g`
is `h ↦ g h⁻¹`, and inversion has differential `-1` at the identity
(`Subgroup.RightTranslation.fundamentalVectorField_toRightTranslation`). The kernel of `dπ` at a
point is the tangent space of its `K`-orbit, spanned by the fundamental vector fields of the
diagonal action; this is Tau Ceti's
`ProperSMul.ker_mfderiv_eq_orbitTangent_fundamental_of_isSubmersionAt`, applied as in the
proof of Tau Ceti's `ProperSMul.ker_mfderiv_quotientMk`. So the kernel of `dπ` at `(g, z)`
consists of the vectors `(-d(L_g)(ξ'), ξ_Z(z))` for `ξ ∈ Lie(K)`.

For a `K`-equivariant map `ι : Z → M` to a `G`-manifold, the lift `[g, z] ↦ g • ι z`
(`TauCeti.BalancedProduct.liftRightTranslation`) is smooth at `[g, z]` when `ι` is smooth at `z`:
this is the pointwise form of Tau Ceti's `TauCeti.BalancedProduct.contMDiff_liftRightTranslation`,
whose proof it follows; likewise it is differentiable at `[g, z]` when `ι` is differentiable at
`z`, by Tau Ceti's `TauCeti.mdifferentiableAt_smul_slice`. Composed with `dπ` at `(1, z)`, its
differential at `[1, z]` sends `(ξ, v)` to `ξ_M(ι z) + dι v`, by Tau Ceti's
`TauCeti.mfderiv_smul_slice_apply`.

At a point `z` fixed by `K`, `dπ` at `(1, z)` kills `(ξ, 0)` for every `ξ` whose one-parameter
subgroup lies in `K`, since the curve `t ↦ (exp (t ξ), z)` stays in the class `[1, z]`. So the
lift is a local diffeomorphism at `[1, z]` when its differential composed with `dπ` is onto and
vanishes only on such vectors `(ξ, 0)`: its own differential is then bijective, and Tau Ceti's
inverse function theorem `TauCeti.isLocalDiffeomorphAt_iff_exists_mfderiv_eq` applies. Since the
lift is `G`-equivariant, the points where it is a local diffeomorphism are `G`-invariant
(`SymplecticGeometry.isLocalDiffeomorphAt_smul_iff`); so it is one at `[g, z]` exactly when it is
one at `[1, z]`, and the set of such `z` is open and `K`-invariant.

## Main results

* `TauCeti.BalancedProduct.ker_mfderiv_quotientMk_rightTranslation`: on
  `K.RightTranslation × Z`, the kernel of `dπ` is the orbit tangent space of the diagonal action.
* `TauCeti.BalancedProduct.mem_ker_mfderiv_mk_toRightTranslation_iff`: on `G × Z`, a tangent
  vector at `(g, z)` is vertical exactly when it is `(-d(L_g)(ξ'), ξ_Z(z))` for some `ξ ∈ Lie(K)`.
* `TauCeti.BalancedProduct.surjective_mk_toRightTranslation`,
  `TauCeti.BalancedProduct.isSubmersion_mk_toRightTranslation`: on `G × Z`, the projection is a
  surjective smooth submersion.
* `TauCeti.BalancedProduct.contMDiffAt_liftRightTranslation`: the lift of an equivariant map is
  smooth at `[g, z]` when the map is smooth at `z`.
* `TauCeti.BalancedProduct.mdifferentiableAt_liftRightTranslation`: the lift is differentiable
  at `[g, z]` when the map is differentiable at `z`.
* `TauCeti.BalancedProduct.mfderiv_liftRightTranslation_mfderiv_quotientMk`: the differential of
  the lift at `[1, z]`, composed with `dπ`, is `(ξ, v) ↦ ξ_M(ι z) + dι v`.
* `TauCeti.BalancedProduct.mfderiv_quotientMk_apply_eq_zero_of_forall_mem`: at a `K`-fixed point,
  `dπ` kills the directions of `Lie(G)` whose one-parameter subgroups lie in `K`.
* `TauCeti.BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_mk_one`: the inverse
  function theorem for the lift at `[1, z]`, in terms of its differential composed with `dπ`.
* `TauCeti.BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_mk_iff`,
  `TauCeti.BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_mk_one_smul_iff`,
  `TauCeti.BalancedProduct.isOpen_setOf_isLocalDiffeomorphAt_liftRightTranslation_mk_one`: where
  the lift is a local diffeomorphism.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 21 (the quotient manifold theorem) and Chapter 20 (infinitesimal
  generators of Lie group actions).
* J. J. Duistermaat and J. A. C. Kolk, *Lie Groups*, Universitext, Springer, 2000, Section 2.4.
-/

public section

open Function Manifold Set TauCeti
open scoped ContDiff Manifold

namespace Subgroup.RightTranslation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {G : Type*} [Group G] {K : Subgroup G}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace G] [ChartedSpace H G] [LieGroup I 1 G]
  {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace 𝕜 EK] [TopologicalSpace HK]
  {IK : ModelWithCorners 𝕜 EK HK} [ChartedSpace HK K] [ContMDiffSMul IK I 1 K G]

/-- **The fundamental vector fields of right translation.** For the action `h • g = g h⁻¹` of a
subgroup `K` on `G`, the fundamental vector field of `ξ ∈ Lie(K)` at `g` is `-d(L_g)(ξ')`, minus
the left-invariant vector field of the image `ξ'` of `ξ` in `Lie(G)`. -/
theorem fundamentalVectorField_toRightTranslation (ξ : GroupLieAlgebra IK K) (g : G) :
    fundamentalVectorField I ξ (K.toRightTranslation g) =
      -mulInvariantVectorField (K.subtype.groupLieAlgebraMap IK I ξ) g := by
  have hsub : MDifferentiableAt IK I K.subtype 1 :=
    (K.contMDiff_subtypeVal_of_contMDiffSMul (I := I) (I' := IK) (n := 1)).mdifferentiableAt
      one_ne_zero
  have hinv : MDifferentiableAt I I (fun x : G ↦ x⁻¹) 1 :=
    (contMDiff_inv I 1).mdifferentiableAt one_ne_zero
  have hmul : MDifferentiableAt I I (fun x : G ↦ g * x) 1 :=
    (contMDiff_mul_left (I := I) (n := 1)).mdifferentiableAt one_ne_zero
  rw [fundamentalVectorField_apply]
  -- `K.RightTranslation` is `G` with the same charts, `K.toRightTranslation` is the identity, and
  -- `k • g = g k⁻¹`, so the orbit map of `g` is `k ↦ g k⁻¹`, a map into `G`.
  change mfderiv IK I ((fun x : G ↦ g * x) ∘ (fun x : G ↦ x⁻¹) ∘ K.subtype) 1 ξ = _
  rw [mfderiv_comp_apply_of_eq 1 hmul (hinv.comp_of_eq 1 hsub (by simp)) (by simp),
    mfderiv_comp_apply_of_eq 1 hinv hsub (by simp), ← MonoidHom.groupLieAlgebraMap_apply,
    GroupLieAlgebra.mfderiv_inv_one_apply, map_neg, GroupLieAlgebra.mulInvariantVectorField_apply]
  -- The two sides agree up to how the base point of their tangent space is written.
  rfl

end Subgroup.RightTranslation

namespace TauCeti.BalancedProduct

variable {G : Type*} [Group G] {K : Subgroup G} {Z : Type*} [MulAction K Z]

/-- The projection `(g, z) ↦ [g, z]` from `G × Z` onto the balanced product `G ×_K Z` is
surjective. -/
theorem surjective_mk_toRightTranslation :
    Surjective fun p : G × Z ↦ mk K (K.toRightTranslation p.1) p.2 :=
  fun y ↦ induction_on_toRightTranslation y fun g z ↦ ⟨(g, z), rfl⟩

/-- At a point `z` fixed by `K`, each `k ∈ K` fixes the class `[1, z]` of `G ×_K Z`:
`k • [1, z] = [1, k • z] = [1, z]`. -/
theorem smul_mk_toRightTranslation_one {z : Z} (hz : ∀ k : K, k • z = z) (k : K) :
    (k : G) • mk K (K.toRightTranslation 1) z = mk K (K.toRightTranslation 1) z := by
  rw [← mk_toRightTranslation_one_smul, hz]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace G]
  [ChartedSpace H G] [LieGroup I ∞ G] [IsClosed (K : Set G)]
  {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ} [IZ.Boundaryless] [TopologicalSpace Z]
  [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [T2Space Z]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  [ContMDiffSMul 𝓘(ℝ, F) IZ ∞ K Z]

/-- **The vertical directions of `K.RightTranslation × Z → G ×_K Z`.** The kernel of the
differential at `x` of the projection onto the balanced product is the orbit tangent space at `x`
of the diagonal action `h • (g, z) = (g h⁻¹, h • z)` of `K`, spanned by its fundamental vector
fields. -/
theorem ker_mfderiv_quotientMk_rightTranslation (x : K.RightTranslation × Z) :
    letI := rightTranslationChartedSpace K Z I IZ F
    (mfderiv (I.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
      (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z))) x).ker =
      (InfinitesimalAction.fundamental 𝓘(ℝ, F) K (I.prod IZ)
        (K.RightTranslation × Z)).orbitTangent x := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have := ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, F)) (I' := IZ) (G := K) (M := Z) ∞
  exact ProperSMul.ker_mfderiv_eq_orbitTangent_fundamental_of_isSubmersionAt (I := 𝓘(ℝ, F))
    (IsCancelSMul.stabilizer_eq_bot x)
    ((isSubmersion_quotientMk_rightTranslation (I := I) (IZ := IZ) (F := F)).isSubmersionAt x)
    (by simp)
    (Filter.Eventually.of_forall fun _ ↦ MulAction.orbitRel.Quotient.quotient_smul_eq)
    (Filter.Eventually.of_forall fun _ h ↦
      MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact h)))

/-- **The vertical directions of `G × Z → G ×_K Z`.** A tangent vector at `(g, z)` lies in the
kernel of the differential of `(g, z) ↦ [g, z]` exactly when it is `(-d(L_g)(ξ'), ξ_Z(z))` for
some `ξ` in the Lie algebra of `K`, where `ξ'` is the image of `ξ` in `Lie(G)` and `ξ_Z` is the
fundamental vector field of `ξ` on `Z`. -/
theorem mem_ker_mfderiv_mk_toRightTranslation_iff (g : G) (z : Z)
    (v : TangentSpace (I.prod IZ) (g, z)) :
    letI := rightTranslationChartedSpace K Z I IZ F
    v ∈ (mfderiv (I.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
      (fun p : G × Z ↦ mk K (K.toRightTranslation p.1) p.2) (g, z)).ker ↔
      ∃ ξ : GroupLieAlgebra 𝓘(ℝ, F) K,
        v = (-mulInvariantVectorField (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ) g,
          fundamentalVectorField IZ ξ z) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  -- `K.RightTranslation` is `G` with the same charts and `K.toRightTranslation` is the identity,
  -- so the map is the projection of `K.RightTranslation × Z` onto the balanced product, and its
  -- kernel is the orbit tangent space at `(g, z)`.
  refine (SetLike.ext_iff.1
    (ker_mfderiv_quotientMk_rightTranslation (K.toRightTranslation g, z)) v).trans
    ((InfinitesimalAction.mem_orbitTangent_iff _ _).trans (exists_congr fun ξ ↦ ?_))
  have h : (Manifold.prodVectorField (fundamentalVectorField I ξ)
      (fundamentalVectorField IZ ξ) (K.toRightTranslation g, z) : E × EZ) =
      (-mulInvariantVectorField (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ) g,
        fundamentalVectorField IZ ξ z) :=
    Prod.ext ((Manifold.prodVectorField_fst _ _ _).trans
      (Subgroup.RightTranslation.fundamentalVectorField_toRightTranslation ξ g))
      (Manifold.prodVectorField_snd _ _ _)
  rw [InfinitesimalAction.fundamental_prod, InfinitesimalAction.prod_apply,
    InfinitesimalAction.fundamental_apply, InfinitesimalAction.fundamental_apply]
  exact h ▸ eq_comm

/-- The projection `(g, z) ↦ [g, z]` from `G × Z` onto the balanced product `G ×_K Z` is a smooth
submersion. -/
theorem isSubmersion_mk_toRightTranslation :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsSubmersion (I.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞
      (fun p : G × Z ↦ mk K (K.toRightTranslation p.1) p.2) :=
  -- `K.RightTranslation` is `G` with the same charts and `K.toRightTranslation` is the identity,
  -- so the map is Tau Ceti's quotient map of `K.RightTranslation × Z`.
  isSubmersion_quotientMk_rightTranslation

section Lift

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [MulAction G M] {ι : Z →ₑ[((↑) : K → G)] M} {z : Z}

/-- **The action map to a `G`-manifold is smooth at `[g, z]`** when the `K`-equivariant map `ι`
is smooth at `z`. -/
theorem contMDiffAt_liftRightTranslation [ContMDiffSMul I IM ∞ G M]
    (hι : ContMDiffAt IZ IM ∞ ι z) (g : G) :
    letI := rightTranslationChartedSpace K Z I IZ F
    ContMDiffAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞ (liftRightTranslation ι)
      (mk K (K.toRightTranslation g) z) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  have hπ := (isSubmersion_quotientMk_rightTranslation (K := K) (Z := Z) (I := I) (IZ := IZ)
    (F := F)).isSubmersionAt (K.toRightTranslation g, z)
  refine (hπ.contMDiffAt_comp_iff le_rfl).1 ?_
  rw [liftRightTranslation_comp_quotientMk]
  exact ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm (I := I) ∞).comp
    (contMDiff_fst (J := IZ) (N := Z))).contMDiffAt.smul (hι.comp _ contMDiffAt_snd)

/-- **The action map to a `G`-manifold is differentiable at `[g, z]`** when the `K`-equivariant
map `ι` is differentiable at `z`. -/
theorem mdifferentiableAt_liftRightTranslation [ContMDiffSMul I IM 1 G M]
    (hι : MDifferentiableAt IZ IM ι z) (g : G) :
    letI := rightTranslationChartedSpace K Z I IZ F
    MDifferentiableAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM (liftRightTranslation ι)
      (mk K (K.toRightTranslation g) z) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  have hπ := (isSubmersion_quotientMk_rightTranslation (K := K) (Z := Z) (I := I) (IZ := IZ)
    (F := F)).isSubmersionAt (K.toRightTranslation g, z)
  refine (hπ.mdifferentiableAt_comp_iff (by simp)).1 ?_
  rw [liftRightTranslation_comp_quotientMk]
  exact mdifferentiableAt_smul_slice (G := G) (I := I) (σ := ι) hι g

/-- **The differential of the action map at `[1, z]`.** Composed with the differential at
`(1, z)` of the projection `π : G × Z → G ×_K Z`, the differential at `[1, z]` of the map
`[g, z] ↦ g • ι z` sends `(ξ, v)` to `ξ_M(ι z) + dι v`, when `ι` is differentiable at `z`. -/
theorem mfderiv_liftRightTranslation_mfderiv_quotientMk [ContMDiffSMul I IM 1 G M]
    (hι : MDifferentiableAt IZ IM ι z) (ξ : GroupLieAlgebra I G) (v : TangentSpace IZ z) :
    letI := rightTranslationChartedSpace K Z I IZ F
    mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM (liftRightTranslation ι)
        (Quotient.mk _ (K.toRightTranslation 1, z))
        (mfderiv (I.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
          (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)))
          (K.toRightTranslation 1, z) (ξ, v)) =
      fundamentalVectorField IM ξ (ι z) + mfderiv IZ IM ι z v := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  have hπ := (isSubmersion_quotientMk_rightTranslation (K := K) (Z := Z) (I := I) (IZ := IZ)
    (F := F)).contMDiff.mdifferentiableAt (x := (K.toRightTranslation 1, z)) (by simp)
  have hΦ : MDifferentiableAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM
      (liftRightTranslation ι) (Quotient.mk _ (K.toRightTranslation 1, z)) :=
    mdifferentiableAt_liftRightTranslation hι 1
  refine (mfderiv_comp_apply _ hΦ hπ _).symm.trans ?_
  rw [liftRightTranslation_comp_quotientMk]
  -- `K.RightTranslation` is `G` with the same charts, and `toRightTranslation` is the identity,
  -- so this is the differential of `(g, z) ↦ g • ι z` on `G × Z` at `(1, z)`.
  exact mfderiv_smul_slice_apply (σ := ι) hι ξ v

/-! ### Where the lift is a local diffeomorphism -/

variable (F) in
/-- **The projection is constant along directions of `K` at a fixed point.** If `z` is fixed by
`K` and the one-parameter subgroup `t ↦ exp (t ξ)` of `ξ ∈ Lie(G)` lies in `K`, then the
differential at `(1, z)` of the projection `G × Z → G ×_K Z` vanishes on `(ξ, 0)`: the curve
`t ↦ (exp (t ξ), z)` stays in the class `[1, z]`. -/
theorem mfderiv_quotientMk_apply_eq_zero_of_forall_mem [T2Space G] (hz : ∀ k : K, k • z = z)
    {ξ : GroupLieAlgebra I G} (hξ : ∀ t : ℝ, mulInvariantExp (I := I) (t • ξ) ∈ K) :
    letI := rightTranslationChartedSpace K Z I IZ F
    mfderiv (I.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
      (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)))
      (K.toRightTranslation 1, z) (ξ, 0) = 0 := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  -- The curve `γ t = (exp (t ξ), z)` in `G × Z`, with velocity `(ξ, 0)` at `0`.
  let γ : ℝ → K.RightTranslation × Z :=
    fun t ↦ (K.toRightTranslation (mulInvariantExp (I := I) (t • ξ)), z)
  have hγ : HasMFDerivAt 𝓘(ℝ, ℝ) (I.prod IZ) γ 0 (((1 : ℝ →L[ℝ] ℝ).smulRight ξ).prod 0) :=
    (hasMFDerivAt_mulInvariantExp_smul_zero (I := I) (G := G) ξ).prodMk
      (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := IZ) z 0)
  -- It stays in the class `[1, z]`.
  have hconst : Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)) ∘ γ =
      fun _ ↦ Quotient.mk _ (K.toRightTranslation 1, z) := by
    funext t
    simp only [comp_apply, γ]
    rw [quotientMk_eq_mk_toRightTranslation, quotientMk_eq_mk_toRightTranslation,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← one_mul (mulInvariantExp (t • ξ))]
    exact (mk_toRightTranslation_mul 1 ⟨_, hξ t⟩ z).trans (congrArg _ (hz _))
  have hγ0 : γ 0 = (K.toRightTranslation 1, z) := by
    simp only [γ, zero_smul, mulInvariantExp_zero]
  have h := TauCeti.mfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_const (J := 𝓘(ℝ, ℝ))
    (I := I.prod IZ) (K := 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)))
    (s := 0) (.of_eq hconst) (1 : ℝ)
  rw [hγ.mfderiv, hγ0] at h
  -- The velocity of `γ` applied to `1` is `(ξ, 0)`.
  convert h using 1
  exact congrArg _ (Prod.ext (one_smul ℝ ξ).symm rfl)

variable (F) in
/-- **The inverse function theorem for the lift at `[1, z]`.** Let `z` be fixed by `K`, and let the
`K`-equivariant map `ι` be smooth on an open neighbourhood of `z`. If the differential of the lift
`[g, z] ↦ g • ι z` at `[1, z]`, composed with that of the projection `π : G × Z → G ×_K Z` at
`(1, z)`, is onto, and vanishes at `(ξ, v)` only when `v = 0` and the one-parameter subgroup of `ξ`
lies in `K`, then the lift is a local diffeomorphism at `[1, z]`. -/
theorem isLocalDiffeomorphAt_liftRightTranslation_mk_one [T2Space G] [IsManifold IM ∞ M]
    [ContMDiffSMul I IM ∞ G M]
    {s : Set Z} (hs : IsOpen s) (hzs : z ∈ s) (hι : ContMDiffOn IZ IM ∞ ι s)
    (hz : ∀ k : K, k • z = z) :
    letI := rightTranslationChartedSpace K Z I IZ F
    (Surjective fun p : GroupLieAlgebra I G × TangentSpace IZ z ↦
      mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM (liftRightTranslation ι)
        (Quotient.mk _ (K.toRightTranslation 1, z))
        (mfderiv (I.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
          (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)))
          (K.toRightTranslation 1, z) p)) →
    (∀ (ξ : GroupLieAlgebra I G) (v : TangentSpace IZ z),
      mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM (liftRightTranslation ι)
        (Quotient.mk _ (K.toRightTranslation 1, z))
        (mfderiv (I.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
          (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z)))
          (K.toRightTranslation 1, z) (ξ, v)) = 0 →
        (∀ t : ℝ, mulInvariantExp (I := I) (t • ξ) ∈ K) ∧ v = 0) →
    IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞
      (liftRightTranslation ι) (Quotient.mk _ (K.toRightTranslation 1, z)) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  intro hsurj hker
  have := isManifold_rightTranslation (K := K) (Z := Z) (I := I) (IZ := IZ) (F := F)
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have := ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, F)) (I' := IZ) (G := K) (M := Z) ∞
  have hπ := (isSubmersion_quotientMk_rightTranslation (K := K) (Z := Z) (I := I) (IZ := IZ)
    (F := F)).surjective_mfderiv (by simp) (K.toRightTranslation 1, z)
  -- The lift is smooth on the open image of `G × s`.
  have hopen : IsOpen ((fun p : G × Z ↦ mk K (K.toRightTranslation p.1) p.2) '' (univ ×ˢ s)) :=
    isOpenQuotientMap_mk_toRightTranslation.isOpenMap _ (isOpen_univ.prod hs)
  have hsmooth : ContMDiffOn 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞
      (liftRightTranslation ι) ((fun p : G × Z ↦ mk K (K.toRightTranslation p.1) p.2) ''
        (univ ×ˢ s)) := by
    rintro _ ⟨⟨g, z'⟩, ⟨-, hz'⟩, rfl⟩
    exact (contMDiffAt_liftRightTranslation (hι.contMDiffAt (hs.mem_nhds hz')) g).contMDiffWithinAt
  set A := mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM (liftRightTranslation ι)
    (Quotient.mk _ (K.toRightTranslation 1, z))
  have hAsurj : Surjective A := fun w ↦ by
    obtain ⟨p, hp⟩ := hsurj w
    exact ⟨_, hp⟩
  have hAinj : Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun w hw ↦ ?_
    obtain ⟨⟨ξ, v⟩, rfl⟩ := hπ w
    obtain ⟨hξ, rfl⟩ := hker ξ v hw
    exact mfderiv_quotientMk_apply_eq_zero_of_forall_mem F hz hξ
  refine (isLocalDiffeomorphAt_iff_exists_mfderiv_eq hsmooth hopen
    ⟨(1, z), ⟨mem_univ _, hzs⟩, rfl⟩ BoundarylessManifold.isInteriorPoint (by simp)).2
    ⟨(LinearEquiv.ofBijective A.toLinearMap ⟨hAinj, hAsurj⟩).toContinuousLinearEquiv, ?_⟩
  ext w
  -- `LinearEquiv.ofBijective_apply` does not match here, as the tangent spaces are type synonyms
  -- of the model spaces; the equivalence applies `A` by definition.
  rfl

variable (F) in
/-- **The lift is a local diffeomorphism at `[g, z]` exactly when it is one at `[1, z]`**, since
the lift of a `K`-equivariant map is `G`-equivariant. -/
theorem isLocalDiffeomorphAt_liftRightTranslation_mk_iff [ContMDiffSMul I IM ∞ G M] (g : G)
    (z : Z) :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞
        (liftRightTranslation ι) (mk K (K.toRightTranslation g) z) ↔
      IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞
        (liftRightTranslation ι) (mk K (K.toRightTranslation 1) z) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  have := contMDiffSMul_rightTranslation (K := K) (Z := Z) (I := I) (IZ := IZ) (F := F)
  have : ContMDiffConstSMul 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) ∞ G
      (BalancedProduct K K.RightTranslation Z) :=
    ContMDiffSMul.contMDiffConstSMul I
  have : ContMDiffConstSMul IM ∞ G M := ContMDiffSMul.contMDiffConstSMul I
  have h := SymplecticGeometry.isLocalDiffeomorphAt_smul_iff
    (I := 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))) (J := IM) (n := ∞)
    (liftRightTranslation_smul ι) g
    (x := mk K (K.toRightTranslation 1) z)
  rwa [smul_mk_toRightTranslation, mul_one] at h

variable (F) in
/-- The points `z` at whose class `[1, z]` the lift is a local diffeomorphism are invariant
under `K`: the class `[1, k • z]` is `k • [1, z]`, and the lift is `G`-equivariant. -/
theorem isLocalDiffeomorphAt_liftRightTranslation_mk_one_smul_iff [ContMDiffSMul I IM ∞ G M]
    (k : K) (z : Z) :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞
        (liftRightTranslation ι) (mk K (K.toRightTranslation 1) (k • z)) ↔
      IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞
        (liftRightTranslation ι) (mk K (K.toRightTranslation 1) z) := by
  rw [mk_toRightTranslation_one_smul, smul_mk_toRightTranslation, mul_one]
  exact isLocalDiffeomorphAt_liftRightTranslation_mk_iff F (k : G) z

variable (F) in
/-- The set of points `z` at whose class `[1, z]` the lift is a local diffeomorphism is open. -/
theorem isOpen_setOf_isLocalDiffeomorphAt_liftRightTranslation_mk_one :
    letI := rightTranslationChartedSpace K Z I IZ F
    IsOpen {z : Z | IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ)) IM ∞
      (liftRightTranslation ι) (mk K (K.toRightTranslation 1) z)} := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
  have hc : Continuous fun z : Z ↦ mk K (K.toRightTranslation 1) z :=
    continuous_quotient_mk'.comp (continuous_const.prodMk continuous_id)
  exact hc.continuousAt.preimage_mem_nhds (IsLocalDiffeomorphAt.eventually hz)

end Lift

end TauCeti.BalancedProduct

end
