/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.TotallyReal.Basic
public import SymplecticGeometry.Geometry.Lie.GroupLieAlgebraLieHom

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

## Main results

* `SymplecticGeometry.LieComplexification.toHom_mulInvariantExp`: `toHom` intertwines the
  exponentials through `lieMap`.
* `SymplecticGeometry.LieComplexification.lieMap_injective`: `lieMap` is injective.
* `SymplecticGeometry.LieComplexification.lieMap_re_add_cplx_lieMap_im`: every element `x` is
  `lieMap (re x) + cplx (lieMap (im x))`.
* `SymplecticGeometry.LieComplexification.connectedSpace`: `Gc` is connected if `G` is.
* `SymplecticGeometry.LieComplexification.isClosedEmbedding_toHom`: `toHom` is a closed
  embedding.

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

end
