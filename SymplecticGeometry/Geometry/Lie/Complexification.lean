/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.LinearAlgebra.Projection
public import SymplecticGeometry.Geometry.Lie.Exponential.Units
public import TauCeti.Geometry.Lie.Subgroup.Commutative
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.TotallyReal.Basic
public import SymplecticGeometry.Geometry.Lie.GroupLieAlgebraLieHom
public import SymplecticGeometry.Geometry.Manifold.Instances.Sphere

/-!
# Complexifications of Lie groups

A complexification of a real Lie group `G` (over `I`) is recorded here as data with
hypotheses, `SymplecticGeometry.LieComplexification I G IC Gc`: a real Lie group `Gc` (over
`IC`) containing `G` through an injective smooth homomorphism `toHom`, a complex structure
`cplx` on the Lie algebra of `Gc` (a `TauCeti.AlmostComplexStructure`) that commutes with every
`ad`, for which the image `𝔤` of the Lie algebra of `G` is maximal totally real
(`TauCeti.IsMaximalTotallyReal`: the Lie algebra of `Gc` is the direct sum of `𝔤` and `cplx 𝔤`),
and a polar decomposition: a diffeomorphism `𝔤 × G ≃ Gc`, `(ξ, u) ↦ exp (cplx ξ) * u`.

Neither Mathlib nor Tau Ceti constructs the complexification of a compact Lie group, and its
construction needs more than the results built on it, so the structure takes these as fields.
The complex structure `cplx` is not determined by the other fields.

## Main definitions

* `SymplecticGeometry.LieComplexification`: the structure.
* `SymplecticGeometry.LieComplexification.lieMap`: the Lie algebra map of `toHom`, Tau Ceti's
  `ContMDiffMonoidMorphism.groupLieAlgebraLieHom`.
* `SymplecticGeometry.LieComplexification.expI`: `ξ ↦ exp (cplx (lieMap ξ))`, the exponential
  of the imaginary directions.
* `SymplecticGeometry.LieComplexification.re`, `SymplecticGeometry.LieComplexification.im`: the
  two components of an element of the Lie algebra of `Gc` in the decomposition
  `lieMap 𝔤 ⊕ cplx (lieMap 𝔤)`.
* `SymplecticGeometry.LieComplexification.circle`: the example `Circle` in `ℂˣ`, with the
  inclusion `Circle.contMDiffToUnits`, the complex structure of the complex manifold `ℂˣ` at `1`
  (Tau Ceti's `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold`), which is multiplication
  by `i`, and the polar decomposition `(ξ, u) ↦ exp (i ξ) * u`.

## Main results

* `SymplecticGeometry.LieComplexification.toHom_mulInvariantExp`: `toHom` intertwines the
  exponentials through `lieMap`.
* `SymplecticGeometry.LieComplexification.lieMap_injective`: `lieMap` is injective.
* `SymplecticGeometry.LieComplexification.lieMap_re_add_cplx_lieMap_im`: every element `x` is
  `lieMap (re x) + cplx (lieMap (im x))`.
* `SymplecticGeometry.LieComplexification.connectedSpace`: `Gc` is connected if `G` is.
* `SymplecticGeometry.LieComplexification.isClosedEmbedding_toHom`: `toHom` is a closed
  embedding.
* `SymplecticGeometry.LieComplexification.circle_cplx_apply`,
  `SymplecticGeometry.LieComplexification.re_circle_lieMap`,
  `SymplecticGeometry.LieComplexification.coe_circle_polar_apply`: for `circle`, `cplx` is
  multiplication by `i`, the Lie algebra of `Circle` goes to `i ℝ`, and
  `polar (ξ, u) = Complex.exp (i ξ) * u`. So `polar (ξ, u) = exp (-t) * u` when `ξ` goes to `t i`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], §2 (the complexified group and its
  polar decomposition).
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

/-- A complexification of the real Lie group `G`: a real Lie group `Gc` with an injective smooth
homomorphism `toHom : G → Gc`, a complex structure `cplx` on the Lie algebra of `Gc` (a real-linear
map with `cplx ∘ cplx = -1`) that commutes with every `ad` (so that the Lie algebra of `Gc` is a
complex Lie algebra), for which the image of the Lie algebra `𝔤` of `G` is maximal totally real
(the Lie algebra of `Gc` is the direct sum of the image of `𝔤` and of its image under `cplx`), and
a diffeomorphism `polar : 𝔤 × G ≃ Gc`, `(ξ, u) ↦ exp (cplx ξ) * toHom u`. The source of `polar`
is written `E × G`: the Lie algebra `GroupLieAlgebra I G` is the model space `E` by definition,
but carries no charted-space instance of its own.

The laws of the structure do not determine `cplx`. For `Circle` in `ℂˣ`, with Lie algebras `i ℝ`
and `ℂ`, every real-linear `J` on `ℂ` with `J ∘ J = -1` and `J i = a + b i`, `a ≠ 0`, satisfies
all of them, and such a `J` is multiplication by a complex number only when it is `±i`. What ties
`cplx` to a complex structure elsewhere is a compatibility condition with an action, not this
structure. -/
structure LieComplexification where
  /-- The inclusion of `G` into its complexification. -/
  toHom : ContMDiffMonoidMorphism I IC ∞ G Gc
  toHom_injective : Injective toHom
  /-- The complex structure of the Lie algebra of the complexification. -/
  cplx : AlmostComplexStructure (GroupLieAlgebra IC Gc)
  cplx_lie (x y : GroupLieAlgebra IC Gc) : cplx ⁅x, y⁆ = ⁅x, cplx y⁆
  isMaximalTotallyReal_range : IsMaximalTotallyReal cplx.toLinearMap
    (LinearMap.range toHom.groupLieAlgebraLieHom.toLinearMap)
  /-- The polar decomposition of the complexification. -/
  polar : (E × G) ≃ₘ⟮𝓘(ℝ, E).prod I, IC⟯ Gc
  polar_apply' (ξ : E) (u : G) :
    polar (ξ, u) = mulInvariantExp (cplx (toHom.groupLieAlgebraLieHom ξ)) * toHom u

namespace LieComplexification

variable {I G IC Gc} (C : LieComplexification I G IC Gc)

/-- The Lie algebra map of the inclusion `C.toHom`, its differential at `1`. -/
def lieMap : GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra IC Gc :=
  C.toHom.groupLieAlgebraLieHom

theorem lieMap_def : C.lieMap = C.toHom.groupLieAlgebraLieHom :=
  (rfl)

theorem lieMap_apply (ξ : GroupLieAlgebra I G) : C.lieMap ξ = mfderiv I IC C.toHom 1 ξ := by
  rw [lieMap_def, ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom,
    MonoidHom.groupLieAlgebraMap_apply, ContMDiffMonoidMorphism.coe_toMonoidHom]

theorem isMaximalTotallyReal_range_lieMap :
    IsMaximalTotallyReal C.cplx.toLinearMap (LinearMap.range C.lieMap.toLinearMap) :=
  C.isMaximalTotallyReal_range

/-- The ranges of `lieMap` and of `cplx ∘ lieMap` are complementary. -/
theorem isCompl_range_lieMap : IsCompl (LinearMap.range C.lieMap.toLinearMap)
    (LinearMap.range (C.cplx.toLinearMap ∘ₗ C.lieMap.toLinearMap)) := by
  rw [LinearMap.range_comp]
  exact C.isMaximalTotallyReal_range_lieMap.isCompl

/-- The complex structure also commutes with brackets on the right: `cplx ⁅x, y⁆ = ⁅cplx x, y⁆`.
-/
theorem cplx_lie' (x y : GroupLieAlgebra IC Gc) : C.cplx ⁅x, y⁆ = ⁅C.cplx x, y⁆ := by
  rw [← lie_skew, ← neg_one_smul ℝ ⁅y, x⁆, C.cplx.apply_smul, C.cplx_lie, neg_one_smul, lie_skew]

section FiniteDimensional

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ EC]

/-- The inclusion of `G` into its complexification intertwines the exponentials:
`toHom (exp ξ) = exp (lieMap ξ)`. -/
theorem toHom_mulInvariantExp [T2Space G] [BoundarylessManifold I G] (ξ : GroupLieAlgebra I G) :
    C.toHom (mulInvariantExp ξ) = mulInvariantExp (C.lieMap ξ) :=
  C.toHom.map_mulInvariantExp ξ

/-- The Lie algebra map of the inclusion of `G` into its complexification is injective. -/
theorem lieMap_injective : Injective C.lieMap :=
  C.toHom.groupLieAlgebraLieHom_injective C.toHom_injective

theorem cplx_comp_lieMap_injective : Injective (C.cplx.toLinearMap ∘ₗ C.lieMap.toLinearMap) :=
  C.cplx.injective.comp C.lieMap_injective

/-- The component of an element of the Lie algebra of `Gc` along `lieMap 𝔤`, read in `𝔤`. -/
def re : GroupLieAlgebra IC Gc →ₗ[ℝ] GroupLieAlgebra I G :=
  LinearMap.linearProjOfIsCompl _ C.lieMap.toLinearMap C.lieMap_injective C.isCompl_range_lieMap

/-- The component of an element of the Lie algebra of `Gc` along `cplx (lieMap 𝔤)`, read in
`𝔤`. -/
def im : GroupLieAlgebra IC Gc →ₗ[ℝ] GroupLieAlgebra I G :=
  LinearMap.linearProjOfIsCompl _ (C.cplx.toLinearMap ∘ₗ C.lieMap.toLinearMap)
    C.cplx_comp_lieMap_injective C.isCompl_range_lieMap.symm

@[simp]
theorem re_lieMap (ξ : GroupLieAlgebra I G) : C.re (C.lieMap ξ) = ξ :=
  LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ ξ

@[simp]
theorem re_cplx_lieMap (ξ : GroupLieAlgebra I G) : C.re (C.cplx (C.lieMap ξ)) = 0 :=
  LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ _ ⟨ξ, rfl⟩

@[simp]
theorem im_cplx_lieMap (ξ : GroupLieAlgebra I G) : C.im (C.cplx (C.lieMap ξ)) = ξ :=
  LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ ξ

@[simp]
theorem im_lieMap (ξ : GroupLieAlgebra I G) : C.im (C.lieMap ξ) = 0 :=
  LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ _ ⟨ξ, rfl⟩

/-- Every element of the Lie algebra of `Gc` is `lieMap (re x) + cplx (lieMap (im x))`. -/
theorem lieMap_re_add_cplx_lieMap_im (x : GroupLieAlgebra IC Gc) :
    C.lieMap (C.re x) + C.cplx (C.lieMap (C.im x)) = x := by
  obtain ⟨_, ⟨ξ, rfl⟩, _, ⟨η, rfl⟩, rfl⟩ :=
    Submodule.mem_sup.1 (C.isCompl_range_lieMap.sup_eq_top ▸ Submodule.mem_top (x := x))
  simp

end FiniteDimensional

/-- The exponential of the imaginary direction `cplx (lieMap ξ)`. -/
def expI (ξ : GroupLieAlgebra I G) : Gc :=
  mulInvariantExp (C.cplx (C.lieMap ξ))

theorem expI_def (ξ : GroupLieAlgebra I G) : C.expI ξ = mulInvariantExp (C.cplx (C.lieMap ξ)) :=
  (rfl)

@[simp]
theorem expI_zero : C.expI 0 = 1 := by
  rw [expI_def, map_zero, AlmostComplexStructure.apply_zero, mulInvariantExp_zero (I := IC)]

/-- `expI_zero` with `0` written in the model space `E`, the form in which `polar_apply` gives
`C.polar (0, u)`. -/
@[simp]
theorem expI_zero' : C.expI (0 : E) = 1 :=
  -- The zeros of `E` and of `GroupLieAlgebra I G` agree only after unfolding `TangentSpace`.
  C.expI_zero

theorem expI_add_smul (ξ : GroupLieAlgebra I G) (s t : ℝ) :
    C.expI ((s + t) • ξ) = C.expI (s • ξ) * C.expI (t • ξ) := by
  simp only [expI_def, map_smul, mulInvariantExp_add_smul (I := IC)]

/-- The polar decomposition: `polar (ξ, u) = expI ξ * toHom u`. -/
@[simp]
theorem polar_apply (ξ : E) (u : G) :
    C.polar (ξ, u) = C.expI ξ * C.toHom u :=
  C.polar_apply' ξ u

/-- The polar decomposition at `ξ = 0` is the inclusion `toHom`. -/
theorem polar_zero_apply (u : G) : C.polar (0, u) = C.toHom u := by
  rw [polar_apply, expI_zero', one_mul]

/-- A complexification is determined by its inclusion and its complex structure. -/
@[ext]
theorem ext {C C' : LieComplexification I G IC Gc} (htoHom : C.toHom = C'.toHom)
    (hcplx : C.cplx = C'.cplx) : C = C' := by
  obtain ⟨toHom, hinj, cplx, h₁, h₂, polar, hpolar⟩ := C
  obtain ⟨toHom', hinj', cplx', h₁', h₂', polar', hpolar'⟩ := C'
  obtain rfl : toHom = toHom' := htoHom
  obtain rfl : cplx = cplx' := hcplx
  obtain rfl : polar = polar' := Diffeomorph.ext fun ⟨ξ, u⟩ ↦ by rw [hpolar, hpolar']
  rfl

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

/-- The complexification of a connected Lie group is connected. -/
theorem connectedSpace (C : LieComplexification I G IC Gc) [ConnectedSpace G] : ConnectedSpace Gc :=
  Function.Surjective.connectedSpace C.polar.toHomeomorph.surjective
    C.polar.toHomeomorph.continuous

end LieComplexification

end SymplecticGeometry

section Circle

/-! ### `Circle` in `ℂˣ` -/

open Function Manifold TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace Circle

/-- The inclusion of the unit circle into `ℂˣ`, as a smooth group homomorphism. -/
def contMDiffToUnits : ContMDiffMonoidMorphism (𝓡 1) 𝓘(ℝ, ℂ) ∞ Circle ℂˣ where
  toMonoidHom := Circle.toUnits
  contMDiff_toFun := by
    have := finrank_real_complex_fact'
    exact ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val contMDiff_coe_sphere

@[simp]
theorem coe_contMDiffToUnits_apply (u : Circle) : ((contMDiffToUnits u : ℂˣ) : ℂ) = u :=
  (rfl)

end Circle

namespace SymplecticGeometry.LieComplexification

open Complex

/-- The Lie algebra map of the inclusion of `Circle`, with values in `ℂ`. -/
-- The Lie algebras `GroupLieAlgebra (𝓡 1) Circle` and `GroupLieAlgebra 𝓘(ℝ, ℂ) ℂˣ` are the model
-- spaces `EuclideanSpace ℝ (Fin 1)` and `ℂ` by definition, but `rw` does not see through
-- `TangentSpace`. The steps below are stated on the model spaces, and the proofs pass between the
-- two readings by term-mode `trans` and `exact`, which unfold `TangentSpace` and `lieHomC`.
private def lieHomC : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] ℂ :=
  Circle.contMDiffToUnits.groupLieAlgebraLieHom.toLinearMap

/-- The Lie algebra map of the inclusion of `Circle` is purely imaginary. -/
private theorem re_lieHomC (ξ : EuclideanSpace ℝ (Fin 1)) : (lieHomC ξ).re = 0 := by
  have h := congrArg (fun z : ℂˣ ↦ ‖(z : ℂ)‖) (Circle.contMDiffToUnits.map_mulInvariantExp ξ)
  simp only [Circle.coe_contMDiffToUnits_apply, Circle.norm_coe,
    coe_mulInvariantExp_eq_exp_complex] at h
  exact Real.exp_eq_one_iff _ |>.1 ((Complex.norm_exp (lieHomC ξ)).symm.trans h.symm)

private theorem lieHomC_injective : Injective lieHomC :=
  Circle.contMDiffToUnits.groupLieAlgebraLieHom_injective
    (fun _ _ huv ↦ Circle.ext (congrArg Units.val huv))

/-- The imaginary part of `lieHomC`, a linear isomorphism from the Lie algebra of `Circle` to
`ℝ`. -/
private def imLieHom : EuclideanSpace ℝ (Fin 1) ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective (imLm ∘ₗ lieHomC) <| by
    have hinj : Injective (imLm ∘ₗ lieHomC) := fun ξ η h ↦
      lieHomC_injective (Complex.ext (by rw [re_lieHomC, re_lieHomC]) h)
    refine ⟨hinj, ?_⟩
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    simp

private theorem imLieHom_apply (ξ : EuclideanSpace ℝ (Fin 1)) :
    imLieHom ξ = (lieHomC ξ).im :=
  (rfl)

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
    I * lieHomC ξ = -(imLieHom ξ : ℂ) := by
  rw [lieHomC_eq, mul_left_comm, I_mul_I, mul_neg_one]

/-- The polar map `(ξ, u) ↦ exp (i ξ) * u` of `Circle` in `ℂˣ`. -/
private def polarFun (p : EuclideanSpace ℝ (Fin 1) × Circle) : ℂˣ :=
  mulInvariantExp (cplxUnits (Circle.contMDiffToUnits.groupLieAlgebraLieHom p.1)) *
    Circle.contMDiffToUnits p.2

private theorem coe_polarFun (p : EuclideanSpace ℝ (Fin 1) × Circle) :
    (polarFun p : ℂ) = Complex.exp (-(imLieHom p.1 : ℂ)) * p.2 := by
  rw [polarFun, Units.val_mul, coe_mulInvariantExp_eq_exp_complex,
    Circle.coe_contMDiffToUnits_apply]
  exact congrArg (fun z ↦ Complex.exp z * p.2)
    ((cplxUnits_apply (lieHomC p.1)).trans (cplxUnits_lieHomC p.1))

/-- The inverse of `polarFun`, through the argument of a nonzero complex number. -/
private def polarInv (z : ℂˣ) : EuclideanSpace ℝ (Fin 1) × Circle :=
  (imLieHom.symm (-Real.log ‖(z : ℂ)‖), Circle.exp (arg z))

private theorem norm_polarFun (p : EuclideanSpace ℝ (Fin 1) × Circle) :
    ‖(polarFun p : ℂ)‖ = Real.exp (-imLieHom p.1) := by
  rw [coe_polarFun, norm_mul, Circle.norm_coe, mul_one, Complex.norm_exp, neg_re, ofReal_re]

private theorem polarInv_polarFun (p : EuclideanSpace ℝ (Fin 1) × Circle) :
    polarInv (polarFun p) = p := by
  refine Prod.ext ?_ ?_
  · rw [polarInv, norm_polarFun, Real.log_exp, neg_neg]
    exact imLieHom.symm_apply_apply p.1
  · rw [polarInv, coe_polarFun, ← ofReal_neg, ← ofReal_exp, arg_ofReal_mul (Real.exp_pos _),
      Circle.exp_arg]

private theorem polarFun_polarInv (z : ℂˣ) : polarFun (polarInv z) = z := by
  have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
  refine Units.ext ?_
  rw [coe_polarFun, polarInv, LinearEquiv.apply_symm_apply, ofReal_neg, neg_neg, ← ofReal_exp,
    Real.exp_log hz, Circle.coe_exp, norm_mul_exp_arg_mul_I]

private theorem contDiff_imLieHom : ContDiff ℝ ∞ (imLieHom : EuclideanSpace ℝ (Fin 1) → ℝ) :=
  (LinearMap.toContinuousLinearMap (imLieHom : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] ℝ)).contDiff

private theorem contDiff_imLieHom_symm :
    ContDiff ℝ ∞ (imLieHom.symm : ℝ → EuclideanSpace ℝ (Fin 1)) :=
  (LinearMap.toContinuousLinearMap
    (imLieHom.symm : ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 1))).contDiff

private theorem contMDiff_polarFun :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 1)).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞ polarFun := by
  have := finrank_real_complex_fact'
  refine ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val ?_
  have h : Units.val ∘ polarFun = (fun q : ℂ × ℂ ↦ q.1 * q.2) ∘
      fun p ↦ (Complex.exp (-(imLieHom p.1 : ℂ)), (p.2 : ℂ)) :=
    funext coe_polarFun
  rw [h]
  refine (contMDiff_iff_contDiff.2 contDiff_mul).comp (ContMDiff.prodMk_space ?_
    (contMDiff_coe_sphere.comp contMDiff_snd))
  refine (ContDiff.contMDiff (f := fun x : EuclideanSpace ℝ (Fin 1) ↦
    Complex.exp (-(imLieHom x : ℂ))) ?_).comp contMDiff_fst
  exact Complex.contDiff_exp.comp (ofRealCLM.contDiff.comp contDiff_imLieHom).neg

private theorem contMDiff_polarInv :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, EuclideanSpace ℝ (Fin 1)).prod (𝓡 1)) ∞ polarInv := by
  refine ContMDiff.prodMk (fun z ↦ ?_) (fun z ↦ ?_)
  · have hz : (z : ℂ) ≠ 0 := z.ne_zero
    refine ContMDiffAt.comp (g := fun w : ℂ ↦ imLieHom.symm (-Real.log ‖w‖)) z
      (ContDiffAt.contMDiffAt ?_) Units.contMDiff_val.contMDiffAt
    exact contDiff_imLieHom_symm.contDiffAt.comp _
      ((Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hz)).comp _ (contDiffAt_norm ℝ hz)).neg
  · exact (Circle.contMDiffOn_exp_arg.contMDiffAt
      (isOpen_compl_singleton.mem_nhds z.ne_zero)).comp z Units.contMDiff_val.contMDiffAt

/-- The polar decomposition `ℝ × Circle ≃ ℂˣ` as a diffeomorphism. -/
private def polarDiffeo :
    (EuclideanSpace ℝ (Fin 1) × Circle) ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1)).prod (𝓡 1), 𝓘(ℝ, ℂ)⟯
      ℂˣ where
  toFun := polarFun
  invFun := polarInv
  left_inv := polarInv_polarFun
  right_inv := polarFun_polarInv
  contMDiff_toFun := contMDiff_polarFun
  contMDiff_invFun := contMDiff_polarInv

private theorem isMaximalTotallyReal_range_lieHom :
    IsMaximalTotallyReal cplxUnits.toLinearMap
      (LinearMap.range Circle.contMDiffToUnits.groupLieAlgebraLieHom.toLinearMap) := by
  rw [isMaximalTotallyReal_iff]
  constructor
  · rw [Submodule.disjoint_def]
    rintro _ ⟨ξ, rfl⟩ ⟨_, ⟨η, rfl⟩, h⟩
    have h' : lieHomC ξ = -(imLieHom η : ℂ) :=
      h.symm.trans ((cplxUnits_apply (lieHomC η)).trans (cplxUnits_lieHomC η))
    have h0 : lieHomC ξ = 0 := Complex.ext (re_lieHomC ξ) (by simp [h'])
    exact h0
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    intro z
    refine ⟨_, _, ⟨imLieHom.symm z.im, rfl⟩, ⟨_, ⟨imLieHom.symm (-z.re), rfl⟩, rfl⟩, ?_⟩
    have e1 : lieHomC (imLieHom.symm z.im) = z.im * I := by
      rw [lieHomC_eq, LinearEquiv.apply_symm_apply]
    have e2 : I * lieHomC (imLieHom.symm (-z.re)) = z.re := by
      rw [cplxUnits_lieHomC, LinearEquiv.apply_symm_apply, ofReal_neg, neg_neg]
    have e3 : cplxUnits (lieHomC (imLieHom.symm (-z.re))) = (z.re : ℂ) :=
      (cplxUnits_apply _).trans e2
    exact (congrArg₂ (fun a b : ℂ ↦ a + b) e1 e3).trans ((add_comm _ _).trans (re_add_im z))

/-- `Circle` in `ℂˣ` as a complexification: the inclusion `Circle.contMDiffToUnits`, the complex
structure of the complex manifold `ℂˣ` at `1`, which is multiplication by `i`
(`circle_cplx_apply`), and the polar decomposition `(ξ, u) ↦ exp (i ξ) * u`, where the
exponential is `Complex.exp` (`coe_circle_polar_apply`). If the Lie algebra map of the inclusion
sends `ξ` to `t i`, then `polar (ξ, u) = exp (-t) * u`. -/
def circle : LieComplexification (𝓡 1) Circle 𝓘(ℝ, ℂ) ℂˣ where
  toHom := Circle.contMDiffToUnits
  toHom_injective _ _ h := Circle.ext (congrArg Units.val h)
  cplx := cplxUnits
  cplx_lie x y := by
    rw [trivial_lie_zero, trivial_lie_zero, AlmostComplexStructure.apply_zero]
  isMaximalTotallyReal_range := isMaximalTotallyReal_range_lieHom
  polar := polarDiffeo
  -- `polarDiffeo` is `polarFun`, which is this product by definition.
  polar_apply' _ _ := rfl

@[simp]
theorem circle_toHom : circle.toHom = Circle.contMDiffToUnits :=
  (rfl)

/-- The complex structure of the complexification `circle` is multiplication by `i`. -/
theorem circle_cplx_apply (x : ℂ) : circle.cplx x = I * x :=
  cplxUnits_apply x

/-- The Lie algebra map of the complexification `circle` is purely imaginary. -/
theorem re_circle_lieMap (ξ : EuclideanSpace ℝ (Fin 1)) : Complex.re (circle.lieMap ξ) = 0 :=
  re_lieHomC ξ

/-- The polar decomposition of the complexification `circle`, with the exponential of `ℂˣ`
written as `Complex.exp`: `polar (ξ, u) = exp (i ξ) * u`. -/
theorem coe_circle_polar_apply (ξ : EuclideanSpace ℝ (Fin 1)) (u : Circle) :
    (circle.polar (ξ, u) : ℂ) = Complex.exp (circle.cplx (circle.lieMap ξ)) * u := by
  rw [polar_apply, Units.val_mul, circle_toHom, Circle.coe_contMDiffToUnits_apply]
  exact congrArg (· * (u : ℂ))
    ((congrArg Units.val (circle.expI_def ξ)).trans (coe_mulInvariantExp_eq_exp_complex _))

end SymplecticGeometry.LieComplexification

end Circle

end
