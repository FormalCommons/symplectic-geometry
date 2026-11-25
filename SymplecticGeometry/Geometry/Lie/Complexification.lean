/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import SymplecticGeometry.Geometry.Lie.Exponential.Circle
public import SymplecticGeometry.Geometry.Lie.Exponential.Units
public import TauCeti.Geometry.Lie.Subgroup.Commutative
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.TotallyReal.Basic
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import SymplecticGeometry.Geometry.Lie.GroupLieAlgebraLieHom
public import SymplecticGeometry.Geometry.Manifold.Instances.Sphere
import TauCeti.LinearAlgebra.TotallyReal.Finrank
import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic
import SymplecticGeometry.Geometry.Lie.Adjoint.Commute
import SymplecticGeometry.Geometry.Lie.Exponential.Derivative

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
  by `i`, and the polar decomposition `(ξ, u) ↦ exp (i ξ) * u`, built from
  `Circle.polarDiffeo`.

## Main results

* `SymplecticGeometry.LieComplexification.toHom_mulInvariantExp`: `toHom` intertwines the
  exponentials through `lieMap`.
* `SymplecticGeometry.LieComplexification.lieMap_injective`: `lieMap` is injective.
* `SymplecticGeometry.LieComplexification.contMDiff_expI`: `expI` is smooth.
* `SymplecticGeometry.LieComplexification.lieMap_re_add_cplx_lieMap_im`: every element `x` is
  `lieMap (re x) + cplx (lieMap (im x))`.
* `SymplecticGeometry.LieComplexification.cplx_lie_cplx`: `⁅cplx x, cplx y⁆ = -⁅x, y⁆`.
* `SymplecticGeometry.LieComplexification.lie_add_cplx`,
  `SymplecticGeometry.LieComplexification.lie_lieMap_add_cplx_lieMap`,
  `SymplecticGeometry.LieComplexification.re_lie`, `SymplecticGeometry.LieComplexification.im_lie`:
  the bracket multiplies like complex numbers,
  `re ⁅x, y⁆ = ⁅re x, re y⁆ - ⁅im x, im y⁆` and `im ⁅x, y⁆ = ⁅re x, im y⁆ + ⁅im x, re y⁆`.
* `SymplecticGeometry.LieComplexification.connectedSpace`: `Gc` is connected if `G` is.
* `SymplecticGeometry.LieComplexification.isClosedEmbedding_toHom`: `toHom` is a closed
  embedding.
* `SymplecticGeometry.LieComplexification.toHom_mul_expI_mul_inv`: for connected `G`, conjugation
  by `toHom u` sends `expI ξ` to `expI (Ad u ξ)`.
* `SymplecticGeometry.LieComplexification.mfderiv_inv_mul_mfderiv_expI_smul_mul_toHom`: for
  connected `G`, the left-trivialized velocity of `τ ↦ expI (τ • ξ) * toHom u` is
  `cplx (lieMap (Ad u⁻¹ ξ))` at every time.
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

The proof that the image of the Lie algebra of `Circle` is maximal totally real counts
dimensions, by Tau Ceti's `TauCeti.IsTotallyReal.isMaximalTotallyReal`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], §2 (the complexified group and its
  polar decomposition).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7
  (complexified Lie groups and the complex structure of their Lie algebras).
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

/-- The bracket of two images under the complex structure: `⁅cplx x, cplx y⁆ = -⁅x, y⁆`. -/
theorem cplx_lie_cplx (x y : GroupLieAlgebra IC Gc) : ⁅C.cplx x, C.cplx y⁆ = -⁅x, y⁆ := by
  rw [← C.cplx_lie, ← C.cplx_lie', AlmostComplexStructure.apply_apply]

/-- The bracket multiplies like complex numbers:
`⁅x + cplx y, z + cplx w⁆ = ⁅x, z⁆ - ⁅y, w⁆ + cplx (⁅x, w⁆ + ⁅y, z⁆)`. -/
theorem lie_add_cplx (x y z w : GroupLieAlgebra IC Gc) :
    ⁅x + C.cplx y, z + C.cplx w⁆ = ⁅x, z⁆ - ⁅y, w⁆ + C.cplx (⁅x, w⁆ + ⁅y, z⁆) := by
  rw [add_lie, lie_add, lie_add, cplx_lie_cplx, ← C.cplx_lie, ← C.cplx_lie', map_add]
  abel

/-- The bracket in the decomposition `lieMap 𝔤 ⊕ cplx (lieMap 𝔤)`, as for complex numbers:
`⁅lieMap a + cplx (lieMap b), lieMap c + cplx (lieMap d)⁆` is
`lieMap (⁅a, c⁆ - ⁅b, d⁆) + cplx (lieMap (⁅a, d⁆ + ⁅b, c⁆))`. -/
theorem lie_lieMap_add_cplx_lieMap (a b c d : GroupLieAlgebra I G) :
    ⁅C.lieMap a + C.cplx (C.lieMap b), C.lieMap c + C.cplx (C.lieMap d)⁆ =
      C.lieMap (⁅a, c⁆ - ⁅b, d⁆) + C.cplx (C.lieMap (⁅a, d⁆ + ⁅b, c⁆)) := by
  simp only [lie_add_cplx, map_sub, map_add, LieHom.map_lie]

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

/-- The real part of a bracket: `re ⁅x, y⁆ = ⁅re x, re y⁆ - ⁅im x, im y⁆`. -/
@[simp]
theorem re_lie (x y : GroupLieAlgebra IC Gc) :
    C.re ⁅x, y⁆ = ⁅C.re x, C.re y⁆ - ⁅C.im x, C.im y⁆ := by
  conv_lhs => rw [← C.lieMap_re_add_cplx_lieMap_im x, ← C.lieMap_re_add_cplx_lieMap_im y,
    lie_lieMap_add_cplx_lieMap]
  rw [map_add, re_lieMap, re_cplx_lieMap, add_zero]

/-- The imaginary part of a bracket: `im ⁅x, y⁆ = ⁅re x, im y⁆ + ⁅im x, re y⁆`. -/
@[simp]
theorem im_lie (x y : GroupLieAlgebra IC Gc) :
    C.im ⁅x, y⁆ = ⁅C.re x, C.im y⁆ + ⁅C.im x, C.re y⁆ := by
  conv_lhs => rw [← C.lieMap_re_add_cplx_lieMap_im x, ← C.lieMap_re_add_cplx_lieMap_im y,
    lie_lieMap_add_cplx_lieMap]
  rw [map_add, im_lieMap, im_cplx_lieMap, zero_add]

end FiniteDimensional

/-- The exponential of the imaginary direction `cplx (lieMap ξ)`. -/
def expI (ξ : GroupLieAlgebra I G) : Gc :=
  mulInvariantExp (C.cplx (C.lieMap ξ))

theorem expI_def (ξ : GroupLieAlgebra I G) : C.expI ξ = mulInvariantExp (C.cplx (C.lieMap ξ)) :=
  (rfl)

@[simp]
theorem expI_zero : C.expI 0 = 1 := by
  rw [expI_def, map_zero, AlmostComplexStructure.apply_zero, mulInvariantExp_zero (I := IC)]

theorem expI_add_smul (ξ : GroupLieAlgebra I G) (s t : ℝ) :
    C.expI ((s + t) • ξ) = C.expI (s • ξ) * C.expI (t • ξ) := by
  simp only [expI_def, map_smul, mulInvariantExp_add_smul (I := IC)]

/-- `expI (-ξ) = (expI ξ)⁻¹`. -/
theorem expI_neg (ξ : GroupLieAlgebra I G) :
    C.expI (-ξ) = (C.expI ξ)⁻¹ := by
  simp only [expI_def, map_neg, mulInvariantExp_neg (I := IC)]

/-- The polar decomposition: `polar (ξ, u) = expI ξ * toHom u`. Unlike the field `polar_apply'`,
it takes `ξ` in the Lie algebra `GroupLieAlgebra I G`, so that it rewrites `C.polar (ξ, u)` for
the elements of the Lie algebra, such as `t • ξ`. -/
@[simp]
theorem polar_apply (ξ : GroupLieAlgebra I G) (u : G) :
    C.polar (ξ, u) = C.expI ξ * C.toHom u :=
  C.polar_apply' ξ u

/-- The exponential of the imaginary directions is smooth, as a map on the model space `E` of the
Lie algebra of `G`: it is `ξ ↦ polar (ξ, 1)`. -/
theorem contMDiff_expI : ContMDiff 𝓘(ℝ, E) IC ∞ fun ξ : E ↦ C.expI ξ :=
  (C.polar.contMDiff.comp (contMDiff_id.prodMk (contMDiff_const (c := (1 : G))))).congr
    fun ξ ↦ (C.polar_apply ξ 1).trans (by rw [map_one, mul_one]) |>.symm

/-- The inverse of the polar decomposition reads `expI ξ * toHom u` as the pair `(ξ, u)`. -/
@[simp]
theorem polar_symm_expI_mul_toHom (ξ : GroupLieAlgebra I G) (u : G) :
    C.polar.symm (C.expI ξ * C.toHom u) = (ξ, u) := by
  rw [← C.polar_apply, Diffeomorph.symm_apply_apply]
  -- The sides differ only in the type of `ξ`: the first component of a point of `E × G` on the
  -- left, an element of `GroupLieAlgebra I G` on the right, which is `E` by definition.
  rfl

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

/-- For connected `G`, conjugation by the inclusion of `u` acts on `expI` through the adjoint
action of `G`: `toHom u * expI ξ * (toHom u)⁻¹ = expI (Ad u ξ)`. -/
theorem toHom_mul_expI_mul_inv [FiniteDimensional ℝ EC] [ConnectedSpace G] (u : G)
    (ξ : GroupLieAlgebra I G) :
    C.toHom u * C.expI ξ * (C.toHom u)⁻¹ = C.expI (Lie.tangentAd (I := I) u ξ) := by
  have := C.connectedSpace
  rw [expI_def, expI_def, Lie.conj_mulInvariantExp, lieMap_def,
    ContMDiffMonoidMorphism.groupLieAlgebraLieHom_tangentAd, ← lieMap_def,
    Lie.map_tangentAd_apply_of_map_lie C.cplx.toLinearMap C.cplx_lie]

/-- For connected `G`, the radial curve `τ ↦ expI (τ • ξ) * toHom u` of the polar decomposition
has, at every time, the left-trivialized velocity `cplx (lieMap (Ad u⁻¹ ξ))`. -/
theorem mfderiv_inv_mul_mfderiv_expI_smul_mul_toHom [FiniteDimensional ℝ EC] [ConnectedSpace G]
    (ξ : GroupLieAlgebra I G) (u : G) (t : ℝ) :
    mfderiv IC IC ((C.expI (t • ξ) * C.toHom u)⁻¹ * ·) (C.expI (t • ξ) * C.toHom u)
        (mfderiv 𝓘(ℝ) IC (fun τ : ℝ ↦ C.expI (τ • ξ) * C.toHom u) t (1 : ℝ)) =
      C.cplx (C.lieMap (Lie.tangentAd (I := I) u⁻¹ ξ)) := by
  -- Conjugating by `toHom u` turns the curve into a left-translated exponential line.
  have h (τ : ℝ) : C.expI (τ • ξ) * C.toHom u =
      C.toHom u * mulInvariantExp (τ • C.cplx (C.lieMap (Lie.tangentAd (I := I) u⁻¹ ξ))) := by
    rw [← C.cplx.apply_smul, ← map_smul, ← expI_def, ← map_smul, ← C.toHom_mul_expI_mul_inv,
      map_inv, inv_inv]
    group
  rw [funext h, h t]
  exact mfderiv_inv_mul_mfderiv_mul_mulInvariantExp_smul _ _ t

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
    (groupLieAlgebraEquivModelVectorSpace (circle.lieMap ξ)).re = 0 :=
  re_lieHomC ξ

/-- The Lie algebra map of the complexification `circle` sends the generator `circleLieGenerator`
of the Lie algebra of `Circle` to `i`, read in `ℂ`. -/
@[simp]
theorem circle_lieMap_circleLieGenerator :
    groupLieAlgebraEquivModelVectorSpace (circle.lieMap circleLieGenerator) = I :=
  lieHomC_circleLieGenerator

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
