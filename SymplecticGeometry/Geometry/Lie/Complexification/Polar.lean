/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Complexification.Basic
public import SymplecticGeometry.Geometry.Lie.Exponential.Circle
public import TauCeti.Geometry.Lie.Subgroup.Commutative
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import SymplecticGeometry.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import SymplecticGeometry.Geometry.Lie.LeftTrivializedCurve.Deriv
import SymplecticGeometry.Geometry.Lie.GroupLieAlgebraLieHom
import TauCeti.LinearAlgebra.TotallyReal.Finrank
import SymplecticGeometry.Geometry.Lie.Adjoint.Commute
import TauCeti.Geometry.Lie.Adjoint.InvariantForm
import SymplecticGeometry.Geometry.Lie.Adjoint.InvariantForm
import SymplecticGeometry.Geometry.Lie.Exponential.Units
import SymplecticGeometry.LinearAlgebra.BilinearForm.CauchySchwarz
import SymplecticGeometry.Analysis.Calculus.Deriv.MeanValue
import SymplecticGeometry.Geometry.Lie.Exponential.Derivative
import SymplecticGeometry.Geometry.Lie.Exponential.Commute
import SymplecticGeometry.Geometry.Lie.Adjoint.Differential
import SymplecticGeometry.Analysis.Normed.Algebra.OneSubExpNegDivSelf
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# The polar decomposition of a complexification

For a complexification `C : SymplecticGeometry.LieComplexification I G IC Gc` (see
`SymplecticGeometry.Geometry.Lie.Complexification.Basic`), this file studies the exponential
`expI` of the imaginary directions and the polar decomposition `C.polar : 𝔤 × G ≃ Gc`,
`(ξ, u) ↦ expI ξ * toHom u`: how it meets inverses and conjugation by `G`, the polar radius
`a ↦ B η η` for `(η, u) = C.polar.symm a`, and the Gauss lemma that computes its derivative along
a curve. It ends with the example `Circle` in `ℂˣ`.

## Main definitions

* `SymplecticGeometry.LieComplexification.expI`: `ξ ↦ exp (cplx (lieMap ξ))`, the exponential
  of the imaginary directions.
* `SymplecticGeometry.LieComplexification.circle`: the example `Circle` in `ℂˣ`, with the
  inclusion `Circle.contMDiffToUnits`, the complex structure of the complex manifold `ℂˣ` at `1`
  (Tau Ceti's `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold`), which is multiplication
  by `i`, and the polar decomposition `(ξ, u) ↦ exp (i ξ) * u`, built from
  `Circle.polarDiffeo`.

## Main results

* `SymplecticGeometry.LieComplexification.contMDiff_expI`: `expI` is smooth.
* `SymplecticGeometry.LieComplexification.commute_expI_of_lie_eq_zero`: `expI η` and `expI ξ`
  commute when `⁅η, ξ⁆ = 0`.
* `SymplecticGeometry.LieComplexification.isClosedEmbedding_toHom`: `toHom` is a closed
  embedding.
* `SymplecticGeometry.LieComplexification.toHom_mul_expI_mul_inv`: for connected `G`, conjugation
  by `toHom u` sends `expI ξ` to `expI (Ad u ξ)`.
* `SymplecticGeometry.LieComplexification.polar_symm_inv`: for connected `G`, if
  `polar.symm a = (η, u)` then `polar.symm a⁻¹ = (-Ad u⁻¹ η, u⁻¹)`.
* `SymplecticGeometry.LieComplexification.contMDiff_polar_symm_fst_apply`,
  `SymplecticGeometry.LieComplexification.apply_polar_symm_inv_fst`: the polar radius
  `a ↦ B η η` is smooth, and for connected `G` and an `Ad`-invariant `B` it takes the same value
  at `a` and at `a⁻¹`.
* `SymplecticGeometry.LieComplexification.mfderiv_inv_mul_curveVelocity_expI_smul_mul_toHom`: for
  connected `G`, the left-trivialized velocity of `τ ↦ expI (τ • ξ) * toHom u` is
  `cplx (lieMap (Ad u⁻¹ ξ))` at every time.
* `SymplecticGeometry.LieComplexification.apply_im_mfderiv_inv_mul_mfderiv_expI_mul_toHom`: for
  connected `G`, an `Ad`-invariant form `B` and `g = expI ξ * toHom v` with `ξ`, `v` differentiable,
  `B (Ad v⁻¹ ξ) (im (g⁻¹ dg w)) = B ξ (dξ w)`.
* `SymplecticGeometry.LieComplexification.hasDerivAt_polar_symm_fst_comp`: the Gauss lemma for the
  polar decomposition. For connected `G` and a symmetric `Ad`-invariant form `B`, the polar radius
  `B η η` of a differentiable curve `a = expI η * toHom u` has derivative
  `2 B (Ad u⁻¹ η) (im (a⁻¹ ȧ))`.
* `SymplecticGeometry.LieComplexification.sqrt_polar_symm_fst_le_add_mul`: for such a `B` that is
  also nonnegative, the polar radius `√(B η η)` of a curve whose left-trivialized derivative has
  imaginary part of `B`-length at most `K` grows at most like `K * t`.
* `SymplecticGeometry.LieComplexification.circle_cplx_apply`,
  `SymplecticGeometry.LieComplexification.re_circle_lieMap`,
  `SymplecticGeometry.LieComplexification.circle_lieMap_circleLieGenerator`,
  `SymplecticGeometry.LieComplexification.coe_circle_polar_apply`,
  `SymplecticGeometry.LieComplexification.coe_circle_polar_smul_circleLieGenerator`: for
  `circle`, `cplx` is multiplication by `i`, the Lie algebra of `Circle` goes to `i ℝ`, with
  `circleLieGenerator` going to `i`, and `polar (ξ, u) = Complex.exp (i ξ) * u`, so that
  `polar (t • circleLieGenerator, u) = exp (-t) * u`. They read the Lie algebras of `ℂˣ` and
  `Circle` in `ℂ` through Tau Ceti's `groupLieAlgebraEquivModelVectorSpace`, and `polar_apply`
  takes its argument in the Lie algebra, so that `rw` and `simp` chain them.

The conjugation formula combines Tau Ceti's `TauCeti.Lie.conj_mulInvariantExp`, the naturality of
`Ad` along `toHom`, and the fact that `cplx`, which commutes with every `ad`, commutes with every
`Ad` of the connected group `Gc` (`TauCeti.Lie.map_tangentAd_apply_of_map_lie`).

The Gauss lemma differentiates `a = exp (cplx (lieMap η)) * toHom u` by the left-trivialized
product rule (`Lie.mfderiv_inv_mul_mfderiv_mul`) and the derivative of the exponential through the
series `(1 - e^{-z}) / z` of `ad` (`mfderiv_inv_mul_mfderiv_mulInvariantExp_comp`, from Tau Ceti's
`LeftInvariantDerivation.hasMFDerivAt_lieExp`). The `toHom u` factor contributes nothing to `im`,
the `Ad`-invariance of `B` removes `Ad u⁻¹`, and the functional `y ↦ B η (im y)` vanishes on the
image of `ad (cplx (lieMap η))`, since `im ⁅cplx (lieMap η), y⁆ = ⁅η, re y⁆` and `B` is
`ad`-invariant (Tau Ceti's `TauCeti.Lie.lieInvariant_of_isInvariantForm_adjointRepresentation`), so
it sees only the constant term of the series
(`ContinuousLinearMap.apply_oneSubExpNegDivSelf_apply_of_comp_eq_zero`).

The proof that the image of the Lie algebra of `Circle` is maximal totally real counts
dimensions, by Tau Ceti's `TauCeti.IsTotallyReal.isMaximalTotallyReal`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], §2 (the complexified group and its
  polar decomposition).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7
  (complexified Lie groups).
-/

public section

noncomputable section

open Function Manifold TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] (IC : ModelWithCorners ℝ EC HC)
  (Gc : Type*) [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace LieComplexification

variable {I G IC Gc} (C : LieComplexification I G IC Gc)

/-- The exponential of the imaginary direction `cplx (lieMap ξ)`. -/
def expI (ξ : GroupLieAlgebra I G) : Gc :=
  mulInvariantExp (C.cplx (C.lieMap ξ))

theorem expI_def (ξ : GroupLieAlgebra I G) : C.expI ξ = mulInvariantExp (C.cplx (C.lieMap ξ)) :=
  (rfl)

@[simp]
theorem expI_zero : C.expI 0 = 1 := by
  rw [expI_def, map_zero, AlmostComplexStructure.apply_zero, mulInvariantExp_zero (I := IC)]

/-- `expI (t • ξ)` is the exponential of `t • cplx (lieMap ξ)`. -/
theorem expI_smul (t : ℝ) (ξ : GroupLieAlgebra I G) :
    C.expI (t • ξ) = mulInvariantExp (t • C.cplx (C.lieMap ξ)) := by
  rw [expI_def, map_smul, AlmostComplexStructure.apply_smul]

theorem expI_add_smul (ξ : GroupLieAlgebra I G) (s t : ℝ) :
    C.expI ((s + t) • ξ) = C.expI (s • ξ) * C.expI (t • ξ) := by
  simp only [expI_def, map_smul, mulInvariantExp_add_smul (I := IC)]

/-- `expI (s • ξ)` and `expI (t • ξ)` commute. -/
theorem commute_expI_smul (ξ : GroupLieAlgebra I G) (s t : ℝ) :
    Commute (C.expI (s • ξ)) (C.expI (t • ξ)) := by
  rw [commute_iff_eq, ← C.expI_add_smul, ← C.expI_add_smul, add_comm]

/-- If `⁅η, ξ⁆ = 0`, then `expI η` and `expI ξ` commute. -/
theorem commute_expI_of_lie_eq_zero [FiniteDimensional ℝ E] {η ξ : GroupLieAlgebra I G}
    (h : ⁅η, ξ⁆ = 0) : Commute (C.expI η) (C.expI ξ) := by
  have := C.finiteDimensional
  rw [expI_def, expI_def]
  refine Lie.commute_mulInvariantExp_of_lie_eq_zero ?_
  rw [C.cplx_lie_cplx, ← LieHom.map_lie, h, map_zero, neg_zero]

/-- `expI (-ξ) = (expI ξ)⁻¹`. -/
theorem expI_neg (ξ : GroupLieAlgebra I G) :
    C.expI (-ξ) = (C.expI ξ)⁻¹ := by
  simp only [expI_def, map_neg, mulInvariantExp_neg (I := IC)]

/-- The polar decomposition: `polar (ξ, u) = expI ξ * toHom u`. Unlike the field `polar_apply'`,
it takes `ξ` in the Lie algebra `GroupLieAlgebra I G`, so that it rewrites `C.polar (ξ, u)` for
the elements of the Lie algebra, such as `t • ξ`. -/
@[simp]
theorem polar_apply (ξ : GroupLieAlgebra I G) (u : G) :
    C.polar (ξ, u) = C.expI ξ * C.toHom u := by
  rw [expI_def, lieMap_def]
  exact C.polar_apply' ξ u

/-- The exponential of the imaginary directions is smooth, as a map on the model space `E` of the
Lie algebra of `G`: it is `ξ ↦ polar (ξ, 1)`. -/
theorem contMDiff_expI : ContMDiff 𝓘(ℝ, E) IC ∞ fun ξ : E ↦ C.expI ξ :=
  (C.polar.contMDiff.comp (contMDiff_id.prodMk (contMDiff_const (c := (1 : G))))).congr
    fun ξ ↦ (C.polar_apply ξ 1).trans (by rw [map_one, mul_one]) |>.symm

/-- The first polar coordinate of `expI ξ` is `ξ`. -/
@[simp]
theorem polar_symm_expI_fst (ξ : GroupLieAlgebra I G) : (C.polar.symm (C.expI ξ)).1 = ξ := by
  rw [← mul_one (C.expI ξ), ← map_one C.toHom, ← C.polar_apply, Diffeomorph.symm_apply_apply]

/-- The inverse of the polar decomposition reads `expI ξ * toHom u` as the pair `(ξ, u)`. -/
@[simp]
theorem polar_symm_expI_mul_toHom (ξ : GroupLieAlgebra I G) (u : G) :
    C.polar.symm (C.expI ξ * C.toHom u) = (ξ, u) := by
  refine Prod.ext ?_ ?_ <;> rw [← C.polar_apply, Diffeomorph.symm_apply_apply]

/-- Every element of `Gc` is `expI ξ * toHom u` for the pair `(ξ, u)` that the inverse of the
polar decomposition gives it. -/
theorem expI_mul_toHom_polar_symm (g : Gc) :
    C.expI (C.polar.symm g).1 * C.toHom (C.polar.symm g).2 = g :=
  (C.polar_apply _ _).symm.trans (C.polar.apply_symm_apply g)

/-- The polar decomposition at `ξ = 0` is the inclusion `toHom`. -/
@[simp]
theorem polar_zero_apply (u : G) : C.polar (0, u) = C.toHom u :=
  -- `polar_apply` at the zero of the Lie algebra, which is the zero `0 : E` of the statement
  -- after unfolding `TangentSpace`.
  (C.polar_apply 0 u).trans (by rw [expI_zero, one_mul])

/-- The inclusion of `G` into its complexification is a closed embedding. -/
theorem isClosedEmbedding_toHom : Topology.IsClosedEmbedding C.toHom := by
  have h : (C.toHom : G → Gc) = C.polar.toHomeomorph ∘ Prod.mk 0 :=
    funext fun u ↦ (C.polar_zero_apply u).symm
  rw [h]
  refine C.polar.toHomeomorph.isClosedEmbedding.comp
    ⟨isEmbedding_prodMkRight 0, ?_⟩
  have hr : Set.range (Prod.mk (0 : E) : G → E × G) = {0} ×ˢ Set.univ := by
    ext ⟨ξ, u⟩
    simp [eq_comm]
  exact hr ▸ isClosed_singleton.prod isClosed_univ

/-- For connected `G`, conjugation by the inclusion of `u` acts on `expI` through the adjoint
action of `G`: `toHom u * expI ξ * (toHom u)⁻¹ = expI (Ad u ξ)`. -/
theorem toHom_mul_expI_mul_inv [FiniteDimensional ℝ EC] [ConnectedSpace G] (u : G)
    (ξ : GroupLieAlgebra I G) :
    C.toHom u * C.expI ξ * (C.toHom u)⁻¹ = C.expI (Lie.tangentAd (I := I) u ξ) := by
  have := C.connectedSpace
  rw [expI_def, expI_def, Lie.conj_mulInvariantExp, lieMap_def,
    ContMDiffMonoidMorphism.groupLieAlgebraLieHom_tangentAd, ← lieMap_def,
    Lie.map_tangentAd_apply_of_map_lie C.cplx.toLinearMap C.cplx_lie]

/-- For connected `G`, the polar decomposition of an inverse: if it reads `a` as `(η, u)`, then
it reads `a⁻¹` as `(-Ad u⁻¹ η, u⁻¹)`, that is, `a⁻¹ = expI (-Ad u⁻¹ η) * toHom u⁻¹`. -/
theorem polar_symm_inv [FiniteDimensional ℝ EC] [ConnectedSpace G] {a : Gc}
    {η : GroupLieAlgebra I G} {u : G} (h : C.polar.symm a = (η, u)) :
    C.polar.symm a⁻¹ = (-Lie.tangentAd (I := I) u⁻¹ η, u⁻¹) := by
  have ha : a⁻¹ = C.expI (-Lie.tangentAd (I := I) u⁻¹ η) * C.toHom u⁻¹ := by
    rw [← C.expI_mul_toHom_polar_symm a, h, ← map_neg, ← C.toHom_mul_expI_mul_inv, expI_neg,
      map_inv]
    group
  rw [ha, polar_symm_expI_mul_toHom]

/-- The polar radius `a ↦ B η η`, for `(η, u) = C.polar.symm a`, is smooth on `Gc`. -/
theorem contMDiff_polar_symm_fst_apply [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)) :
    ContMDiff IC 𝓘(ℝ) ∞ fun a ↦ B (C.polar.symm a).1 (C.polar.symm a).1 := by
  let Bc : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousBilinearMap B
  have hq : ContDiff ℝ ∞ fun e : E ↦ Bc e e := Bc.isBoundedBilinearMap.contDiff.comp
    (contDiff_id.prodMk contDiff_id)
  exact hq.contMDiff.comp (contMDiff_fst.comp C.polar.symm.contMDiff)

/-- For connected `G` and an `Ad`-invariant form `B` on its Lie algebra, `a` and `a⁻¹` have the
same polar radius: `B η' η' = B η η`, for the first components `η` of `C.polar.symm a` and `η'`
of `C.polar.symm a⁻¹`. -/
theorem apply_polar_symm_inv_fst [FiniteDimensional ℝ EC] [ConnectedSpace G]
    {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
    (hB : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B) (a : Gc) :
    B (C.polar.symm a⁻¹).1 (C.polar.symm a⁻¹).1 = B (C.polar.symm a).1 (C.polar.symm a).1 := by
  obtain ⟨η, u, h⟩ : ∃ (η : GroupLieAlgebra I G) (u : G), C.polar.symm a = (η, u) :=
    ⟨_, _, rfl⟩
  rw [C.polar_symm_inv h, h]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  exact hB.apply_tangentAd _ _ _

/-- For connected `G`, the radial curve `τ ↦ expI (τ • ξ) * toHom u` of the polar decomposition
has, at every time, the left-trivialized velocity `cplx (lieMap (Ad u⁻¹ ξ))`. -/
theorem mfderiv_inv_mul_curveVelocity_expI_smul_mul_toHom [FiniteDimensional ℝ EC]
    [ConnectedSpace G] (ξ : GroupLieAlgebra I G) (u : G) (t : ℝ) :
    mfderiv IC IC ((C.expI (t • ξ) * C.toHom u)⁻¹ * ·) (C.expI (t • ξ) * C.toHom u)
        (Manifold.curveVelocity IC (fun τ : ℝ ↦ C.expI (τ • ξ) * C.toHom u) t) =
      C.cplx (C.lieMap (Lie.tangentAd (I := I) u⁻¹ ξ)) := by
  -- Conjugating by `toHom u` turns the curve into a left-translated exponential line.
  have h (τ : ℝ) : C.expI (τ • ξ) * C.toHom u =
      C.toHom u * mulInvariantExp (τ • C.cplx (C.lieMap (Lie.tangentAd (I := I) u⁻¹ ξ))) := by
    rw [← C.expI_smul, ← map_smul, ← C.toHom_mul_expI_mul_inv, map_inv, inv_inv]
    group
  rw [funext h, h t]
  exact mfderiv_inv_mul_curveVelocity_mul_mulInvariantExp_smul _ _ t

/-- For connected `G` and an `Ad`-invariant form `B` on its Lie algebra, a map
`g z = expI (ξ z) * toHom (v z)` from a manifold into `Gc`, with `ξ` and `v` differentiable at `z`,
has a left-trivialized derivative `(g z)⁻¹ dg_z w` whose component `im` pairs with
`Ad (v z)⁻¹ (ξ z)` under `B` as `dξ_z w` pairs with `ξ z`:
`B (Ad (v z)⁻¹ (ξ z)) (im ((g z)⁻¹ dg_z w)) = B (ξ z) (dξ_z w)`. -/
theorem apply_im_mfderiv_inv_mul_mfderiv_expI_mul_toHom [FiniteDimensional ℝ E]
    [ConnectedSpace G] {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
    (hB : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B)
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    {ξ : M → E} {v : M → G} {z : M} (hξ : MDifferentiableAt IM 𝓘(ℝ, E) ξ z)
    (hv : MDifferentiableAt IM I v z) (w : TangentSpace IM z) :
    B (Lie.tangentAd (I := I) (v z)⁻¹ (ξ z))
        (C.im (mfderiv IC IC ((C.expI (ξ z) * C.toHom (v z))⁻¹ * ·) (C.expI (ξ z) * C.toHom (v z))
          (mfderiv IM IC (fun z ↦ C.expI (ξ z) * C.toHom (v z)) z w))) =
      B (ξ z) (mfderiv IM 𝓘(ℝ, E) ξ z w) := by
  have := C.connectedSpace
  have := C.finiteDimensional
  -- The imaginary direction `z ↦ cplx (lieMap (ξ z))`, read in the model space `EC`.
  let L : E →L[ℝ] EC :=
    LinearMap.toContinuousLinearMap (C.cplx.toLinearMap ∘ₗ C.lieMap.toLinearMap)
  have hL (x : E) : L x = C.cplx (C.lieMap x) := rfl
  have hexp (z : M) : C.expI (ξ z) = mulInvariantExp (I := IC) (L (ξ z) : GroupLieAlgebra IC Gc) :=
    (C.expI_def _).trans (congrArg _ (hL _).symm)
  have hX : MDifferentiableAt IM 𝓘(ℝ, EC) (fun z ↦ L (ξ z)) z := L.mdifferentiableAt.comp z hξ
  have hb : MDifferentiableAt IM IC (fun z ↦ C.toHom (v z)) z :=
    ((C.toHom.contMDiff_toFun.mdifferentiable (by simp)) (v z)).comp z hv
  -- The product rule splits the left-trivialized derivative into the part of `exp` and the part
  -- of `toHom ∘ v`, whose component `im` vanishes.
  have hprod := Lie.mfderiv_inv_mul_mfderiv_mul (I := IC) (G := Gc)
    (a := fun z ↦ mulInvariantExp (L (ξ z) : GroupLieAlgebra IC Gc)) (b := fun z ↦ C.toHom (v z))
    ((contMDiff_mulInvariantExp (I := IC) (G := Gc)).mdifferentiableAt (by simp) |>.comp z hX) hb w
  have hv0 := C.im_mfderiv_inv_mul_mfderiv_toHom_comp hv w
  rw [Function.comp_def] at hv0
  have hAd (y : GroupLieAlgebra IC Gc) : C.im (Lie.adjointContinuousLinearMap (C.toHom (v z)⁻¹) y) =
      Lie.tangentAd (I := I) (v z)⁻¹ (C.im y) := by
    rw [← Lie.tangentAd_apply, im_tangentAd_toHom]
  have hg : (fun z ↦ C.expI (ξ z) * C.toHom (v z)) =
      fun z ↦ mulInvariantExp (I := IC) (L (ξ z) : GroupLieAlgebra IC Gc) * C.toHom (v z) :=
    funext fun z ↦ congrArg (· * C.toHom (v z)) (hexp z)
  rw [hg, hexp, hprod, map_add]
  -- `dsimp only` drops the `show` that types the second summand of `hprod` in the Lie algebra.
  dsimp only
  rw [hv0, add_zero, ← map_inv]
  -- The terms below mix `E` and `GroupLieAlgebra I G`, which are the same type only up to
  -- unfolding, so the equalities are chained as terms.
  refine (congrArg (B _) (hAd _)).trans ((hB.apply_tangentAd _ _ _).trans ?_)
  refine (congrArg (fun y ↦ B (ξ z) (C.im y))
    (mfderiv_inv_mul_mfderiv_mulInvariantExp_comp hX w)).trans ?_
  -- The functional `y ↦ B (ξ z) (im y)` vanishes on the image of `ad (L (ξ z))`, by
  -- `im ⁅cplx (lieMap η), y⁆ = ⁅η, re y⁆` and the `ad`-invariance of `B`, so it sees only the
  -- constant term of the series.
  let φ : EC →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (B (ξ z) ∘ₗ C.im)
  have hφ : φ ∘L Module.End.toContinuousLinearMap EC
      ((groupLieAlgebraEquivModelVectorSpace (I := IC) (G := Gc)).conj
        (LieAlgebra.ad ℝ (GroupLieAlgebra IC Gc) (L (ξ z)))) = 0 := by
    ext y₀
    obtain ⟨y, rfl⟩ : ∃ y : GroupLieAlgebra IC Gc, y = y₀ := ⟨y₀, rfl⟩
    let η : GroupLieAlgebra I G := ξ z
    have hl := Lie.lieInvariant_of_isInvariantForm_adjointRepresentation hB η η (C.re y)
    rw [lie_self, map_zero, LinearMap.zero_apply, eq_comm, neg_eq_zero] at hl
    -- `φ`, the conjugation by the identity `groupLieAlgebraEquivModelVectorSpace` and `L` are
    -- unfolded to state the value in the Lie algebra.
    change B η (C.im ⁅C.cplx (C.lieMap η), y⁆) = 0
    rw [im_lie_cplx_lieMap]
    exact hl
  refine (φ.apply_oneSubExpNegDivSelf_apply_of_comp_eq_zero hφ _).trans ?_
  have hd : mfderiv IM 𝓘(ℝ, EC) (fun z ↦ L (ξ z)) z w = L (mfderiv IM 𝓘(ℝ, E) ξ z w) :=
    congrArg (· w) (L.hasMFDerivAt.comp z hξ.hasMFDerivAt).mfderiv
  exact (congrArg (fun y ↦ B (ξ z) (C.im y)) hd).trans (congrArg (B (ξ z)) (C.im_cplx_lieMap _))

/-- **The Gauss lemma for the polar decomposition.** For connected `G`, a symmetric
`Ad`-invariant form `B` on its Lie algebra, and a curve `a` in `Gc` differentiable at `t`, with
`C.polar.symm (a t) = (η, u)`: the polar radius `s ↦ B (η s) (η s)`, where `η s` is the first
component of `C.polar.symm (a s)`, has at `t` the derivative `2 * B (Ad u⁻¹ η) (im (a⁻¹ ȧ))`,
where `a⁻¹ ȧ` is the velocity of `a` at `t` translated back to the identity. -/
theorem hasDerivAt_polar_symm_fst_comp [FiniteDimensional ℝ E]
    [ConnectedSpace G] {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)} (hBs : B.IsSymm)
    (hB : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B)
    {a : ℝ → Gc} {t : ℝ} (ha : MDifferentiableAt 𝓘(ℝ) IC a t) {η : GroupLieAlgebra I G} {u : G}
    (h : C.polar.symm (a t) = (η, u)) :
    HasDerivAt (fun s ↦ B (C.polar.symm (a s)).1 (C.polar.symm (a s)).1)
      (2 * B (Lie.tangentAd (I := I) u⁻¹ η)
        (C.im (mfderiv IC IC ((a t)⁻¹ * ·) (a t) (Manifold.curveVelocity IC a t)))) t := by
  rw [Manifold.curveVelocity_apply]
  have hp : MDifferentiableAt 𝓘(ℝ) (𝓘(ℝ, E).prod I) (fun s ↦ C.polar.symm (a s)) t :=
    (C.polar.symm.contMDiff.mdifferentiableAt (by simp)).comp t ha
  set ξ : ℝ → E := fun s ↦ (C.polar.symm (a s)).1
  set v : ℝ → G := fun s ↦ (C.polar.symm (a s)).2
  have hξ : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) ξ t := hp.fst
  have hη : ξ t = η := congrArg Prod.fst h
  -- `a = expI ξ * toHom v`, so the derivative of `a` is the one computed above.
  have hv : MDifferentiableAt 𝓘(ℝ) I v t := hp.snd
  have hkey := C.apply_im_mfderiv_inv_mul_mfderiv_expI_mul_toHom hB hξ hv (1 : ℝ)
  have hav : a = fun s ↦ C.expI (ξ s) * C.toHom (v s) :=
    funext fun s ↦ (C.expI_mul_toHom_polar_symm (a s)).symm
  rw [← hav, C.expI_mul_toHom_polar_symm (a t), hη,
    show v t = u from congrArg Prod.snd h] at hkey
  have hd : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) ξ t (1 : ℝ) = deriv ξ t := by
    rw [← Manifold.curveVelocity_apply, Manifold.curveVelocity_eq_deriv]
  let Bc : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousBilinearMap B
  have hξd : HasDerivAt ξ (deriv ξ t) t := (mdifferentiableAt_iff_differentiableAt.1 hξ).hasDerivAt
  -- `Bc` is `B`, read on the model space `E`, so its values are `B`'s by definition.
  refine (HasDerivAt.clm_apply_self (hasDerivAt_const t Bc) hξd
    fun v w ↦ hBs.eq v w).congr_deriv ?_
  rw [zero_apply, zero_apply, zero_add, hkey, ← hd, hη]
  exact congrArg (2 * ·) (LinearMap.toContinuousBilinearMap_apply B η _)

/-- **Linear growth of the polar radius.** For connected `G` and a symmetric, nonnegative,
`Ad`-invariant form `B` on its Lie algebra, let `a` be a curve in `Gc` with left-trivialized
derivative `v` at every time, and let `√(B (im (v s)) (im (v s))) ≤ K` for every `s`. Then for
`t ≥ 0` the polar radius `√(B η η)` of `a t`, where `η` is the first component of
`C.polar.symm (a t)`, is at most that of `a 0` plus `K * t`. -/
theorem sqrt_polar_symm_fst_le_add_mul [FiniteDimensional ℝ E]
    [ConnectedSpace G] {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)} (hBs : B.IsSymm)
    (hpos : B.IsNonneg) (hB : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B)
    {a : ℝ → Gc} {v : ℝ → GroupLieAlgebra IC Gc} (ha : HasLeftTrivializedDerivOn a v Set.univ)
    {K : ℝ} (hK : ∀ s, √(B (C.im (v s)) (C.im (v s))) ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    √(B (C.polar.symm (a t)).1 (C.polar.symm (a t)).1) ≤
      √(B (C.polar.symm (a 0)).1 (C.polar.symm (a 0)).1) + K * t := by
  set f : ℝ → ℝ := fun s ↦ B (C.polar.symm (a s)).1 (C.polar.symm (a s)).1
  set b : ℝ → ℝ := fun s ↦
    B (Lie.tangentAd (I := I) (C.polar.symm (a s)).2⁻¹ (C.polar.symm (a s)).1) (C.im (v s))
  have hfd (s : ℝ) : HasDerivAt f (2 * b s) s := by
    have hd := C.hasDerivAt_polar_symm_fst_comp hBs hB (ha.mdifferentiableAt Filter.univ_mem)
      (Prod.mk.eta ..).symm (t := s)
    rwa [ha.mfderiv_inv_mul_curveVelocity Filter.univ_mem] at hd
  -- Cauchy–Schwarz for `B`, with `B (Ad u⁻¹ η) (Ad u⁻¹ η) = B η η`.
  have hb (s : ℝ) : b s ≤ √(f s) * K := by
    refine (le_abs_self _).trans <| (B.abs_apply_le_sqrt_mul_sqrt hBs hpos _ _).trans ?_
    refine (congrArg (fun r ↦ √r * √(B (C.im (v s)) (C.im (v s))))
      (hB.apply_tangentAd _ _ _)).trans_le ?_
    exact mul_le_mul_of_nonneg_left (hK s) (Real.sqrt_nonneg _)
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans (hK 0)
  simpa using Real.sqrt_le_sqrt_add_mul_of_hasDerivAt_le (fun s _ ↦ hpos.nonneg _)
    (fun s _ ↦ hfd s) (fun s _ ↦ by linarith [hb s]) hK0 ht

end LieComplexification

end SymplecticGeometry

section Circle

/-! ### `Circle` in `ℂˣ` -/

open Function Manifold TauCeti Complex

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace SymplecticGeometry.LieComplexification

/-- The Lie algebra map of the inclusion of `Circle`, with values in `ℂ`. -/
-- The Lie algebras `GroupLieAlgebra (𝓡 1) Circle` and `GroupLieAlgebra 𝓘(ℝ, ℂ) ℂˣ` are the model
-- spaces `EuclideanSpace ℝ (Fin 1)` and `ℂ` by definition, but `rw` does not see through
-- `TangentSpace`. The steps below are stated on the model spaces, and the proofs pass between the
-- two readings by term-mode `trans` and `exact`, which unfold `TangentSpace` and `lieHomC`. The
-- public lemmas read the Lie algebras in the model spaces through Tau Ceti's
-- `groupLieAlgebraEquivModelVectorSpace` instead, so that `rw` and `simp` chain them.
private def lieHomC : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] ℂ :=
  Circle.contMDiffToUnits.groupLieAlgebraLieHom.toLinearMap

/-- The Lie algebra map of the inclusion of `Circle` is purely imaginary. -/
private theorem re_lieHomC (ξ : EuclideanSpace ℝ (Fin 1)) : (lieHomC ξ).re = 0 := by
  have h := congrArg (fun z : ℂˣ ↦ ‖(z : ℂ)‖) (Circle.contMDiffToUnits.map_mulInvariantExp ξ)
  simp only [Circle.coe_contMDiffToUnits_apply, Circle.norm_coe,
    coe_mulInvariantExp_eq_exp_complex] at h
  exact Real.exp_eq_one_iff _ |>.1 ((Complex.norm_exp (lieHomC ξ)).symm.trans h.symm)

/-- The Lie algebra map of the inclusion of `Circle` sends the generator to `i`. -/
private theorem lieHomC_circleLieGenerator : lieHomC circleLieGenerator = I := by
  have h (t : ℝ) : Complex.exp (t * lieHomC circleLieGenerator) = Complex.exp (t * I) := by
    have h := congrArg Units.val
      (Circle.contMDiffToUnits.map_mulInvariantExp (t • circleLieGenerator))
    simp only [mulInvariantExp_smul_circleLieGenerator, Circle.coe_contMDiffToUnits_apply,
      Circle.coe_exp, coe_mulInvariantExp_eq_exp_complex, map_smul] at h
    exact (congrArg Complex.exp (Complex.real_smul (x := t))).symm.trans h.symm
  have hd (c : ℂ) : HasDerivAt (fun t : ℝ ↦ Complex.exp (t * c)) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const c).cexp
  exact (funext h ▸ hd (lieHomC circleLieGenerator)).unique (hd I)

private theorem lieHomC_injective : Injective lieHomC :=
  Circle.contMDiffToUnits.groupLieAlgebraLieHom_injective
    Circle.injective_contMDiffToUnits

/-- The imaginary part of `lieHomC`, a linear isomorphism from the Lie algebra of `Circle` to
`ℝ`. -/
private def imLieHom : EuclideanSpace ℝ (Fin 1) ≃ₗ[ℝ] ℝ :=
  (imLm ∘ₗ lieHomC).linearEquivOfInjective
    (fun ξ η h ↦ lieHomC_injective (Complex.ext (by rw [re_lieHomC, re_lieHomC]) h)) (by simp)

private theorem imLieHom_apply (ξ : EuclideanSpace ℝ (Fin 1)) :
    imLieHom ξ = (lieHomC ξ).im :=
  LinearMap.linearEquivOfInjective_apply _ _ ξ

private theorem lieHomC_eq (ξ : EuclideanSpace ℝ (Fin 1)) :
    lieHomC ξ = (imLieHom ξ : ℂ) * I := by
  apply Complex.ext
  · simp [re_lieHomC]
  · simp [imLieHom_apply]

/-- The complex structure of the complex manifold `ℂˣ` at `1`, multiplication by `i`. -/
private def cplxUnits : AlmostComplexStructure (GroupLieAlgebra 𝓘(ℝ, ℂ) ℂˣ) :=
  (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂˣ).almostComplexStructureAt 1

private theorem cplxUnits_apply (x : ℂ) : cplxUnits x = I * x :=
  (SmoothAlmostComplexStructure.almostComplexStructureAt_apply _ 1 x).trans
    ((SmoothAlmostComplexStructure.ofComplexManifold_apply (E := ℂ) (M := ℂˣ) 1 x).trans
      (smul_eq_mul (α := ℂ) _ _))

private theorem cplxUnits_lieHomC (ξ : EuclideanSpace ℝ (Fin 1)) :
    cplxUnits (lieHomC ξ) = -(imLieHom ξ : ℂ) := by
  refine (cplxUnits_apply (lieHomC ξ)).trans ?_
  rw [lieHomC_eq, mul_left_comm, I_mul_I, mul_neg_one]

private theorem isMaximalTotallyReal_range_lieHom :
    IsMaximalTotallyReal cplxUnits.toLinearMap
      (LinearMap.range Circle.contMDiffToUnits.groupLieAlgebraLieHom.toLinearMap) := by
  refine IsTotallyReal.isMaximalTotallyReal ?_
    (fun _ _ h ↦ Subtype.ext (cplxUnits.injective h)) ?_
  · rw [isTotallyReal_iff, Submodule.disjoint_def]
    rintro _ ⟨ξ, rfl⟩ ⟨_, ⟨η, rfl⟩, h⟩
    have h' : lieHomC ξ = -(imLieHom η : ℂ) := h.symm.trans (cplxUnits_lieHomC η)
    exact Complex.ext (re_lieHomC ξ) ((congrArg Complex.im h').trans
      ((by simp : (-(imLieHom η : ℂ)).im = 0).trans Complex.zero_im.symm))
  · refine (congrArg (2 * ·) (LinearMap.finrank_range_of_inj lieHomC_injective)).trans ?_
    exact (congrArg (2 * ·) finrank_groupLieAlgebra_circle).trans
      Complex.finrank_real_complex.symm

/-- The rescaling `ξ ↦ -im (lieHomC ξ)` of the Lie algebra of `Circle` onto `ℝ`. -/
private def negImLieHom : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (imLieHom.trans (LinearEquiv.neg ℝ)).toContinuousLinearEquiv

private theorem negImLieHom_apply (ξ : EuclideanSpace ℝ (Fin 1)) :
    negImLieHom ξ = -imLieHom ξ :=
  (rfl)

/-- `Circle` in `ℂˣ` as a complexification: the inclusion `Circle.contMDiffToUnits`, the complex
structure of the complex manifold `ℂˣ` at `1`, which is multiplication by `i`
(`circle_cplx_apply`), and the polar decomposition `(ξ, u) ↦ exp (i ξ) * u`, where the
exponential is `Complex.exp` (`coe_circle_polar_apply`). It is `Circle.polarDiffeo` after the
rescaling of the Lie algebra of `Circle` that sends `t • circleLieGenerator` to `-t`, so that
`polar (t • circleLieGenerator, u) = exp (-t) * u` (`coe_circle_polar_smul_circleLieGenerator`). -/
def circle : LieComplexification (𝓡 1) Circle 𝓘(ℝ, ℂ) ℂˣ where
  toHom := Circle.contMDiffToUnits
  toHom_injective := Circle.injective_contMDiffToUnits
  cplx := cplxUnits
  cplx_lie x y := by
    rw [trivial_lie_zero, trivial_lie_zero, AlmostComplexStructure.apply_zero]
  isMaximalTotallyReal_range := isMaximalTotallyReal_range_lieHom
  polar := (negImLieHom.toDiffeomorph.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans
    Circle.polarDiffeo
  polar_apply' ξ u := by
    refine Units.ext ?_
    rw [Diffeomorph.coe_trans, comp_apply, Diffeomorph.coe_prodCongr, Prod.map_apply,
      Diffeomorph.coe_refl, id, ContinuousLinearEquiv.coe_toDiffeomorph, negImLieHom_apply,
      Circle.coe_polarDiffeo_apply, Units.val_mul, Circle.coe_contMDiffToUnits_apply,
      coe_mulInvariantExp_eq_exp_complex, ofReal_neg]
    exact congrArg (fun z ↦ Complex.exp z * u) (cplxUnits_lieHomC ξ).symm

@[simp]
theorem circle_toHom : circle.toHom = Circle.contMDiffToUnits :=
  (rfl)

/-- The complex structure of the complexification `circle` is that of the complex manifold `ℂˣ`
at `1`. -/
theorem circle_cplx :
    circle.cplx =
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂˣ).almostComplexStructureAt 1 :=
  (rfl)

/-- The complex structure of the complexification `circle` is multiplication by `i`, with the Lie
algebra of `ℂˣ` read in `ℂ`. -/
@[simp]
theorem circle_cplx_apply (v : GroupLieAlgebra 𝓘(ℝ, ℂ) ℂˣ) :
    groupLieAlgebraEquivModelVectorSpace (circle.cplx v) =
      I * groupLieAlgebraEquivModelVectorSpace v :=
  cplxUnits_apply v

/-- The Lie algebra map of the complexification `circle`, read in `ℂ`, is purely imaginary. -/
@[simp]
theorem re_circle_lieMap (ξ : GroupLieAlgebra (𝓡 1) Circle) :
    (groupLieAlgebraEquivModelVectorSpace (circle.lieMap ξ)).re = 0 := by
  rw [lieMap_def, circle_toHom]
  exact re_lieHomC ξ

/-- The Lie algebra map of the complexification `circle` sends the generator `circleLieGenerator`
of the Lie algebra of `Circle` to `i`, read in `ℂ`. -/
@[simp]
theorem circle_lieMap_circleLieGenerator :
    groupLieAlgebraEquivModelVectorSpace (circle.lieMap circleLieGenerator) = I := by
  rw [lieMap_def, circle_toHom]
  exact lieHomC_circleLieGenerator

/-- The polar decomposition of the complexification `circle`, with the exponential of `ℂˣ`
written as `Complex.exp`: `polar (ξ, u) = exp (i ξ) * u`, with `ξ` read in `ℂ` through
`circle.lieMap`. -/
theorem coe_circle_polar_apply (ξ : GroupLieAlgebra (𝓡 1) Circle) (u : Circle) :
    (circle.polar (ξ, u) : ℂ) =
      Complex.exp (I * groupLieAlgebraEquivModelVectorSpace (circle.lieMap ξ)) * u := by
  rw [polar_apply, Units.val_mul, expI_def, coe_mulInvariantExp_eq_exp_complex, circle_cplx_apply,
    circle_toHom, Circle.coe_contMDiffToUnits_apply]

/-- The polar decomposition of the complexification `circle` in the coordinate of
`circleLieGenerator`: `polar (t • circleLieGenerator, u) = exp (-t) * u`. -/
theorem coe_circle_polar_smul_circleLieGenerator (t : ℝ) (u : Circle) :
    (circle.polar (t • circleLieGenerator, u) : ℂ) = Complex.exp (-t) * u := by
  rw [coe_circle_polar_apply, map_smul, map_smul, circle_lieMap_circleLieGenerator,
    Complex.real_smul, mul_left_comm, I_mul_I, mul_neg_one]

end SymplecticGeometry.LieComplexification

end Circle

end
