/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic

/-!
# Complexifications of Lie groups

A complexification of a real Lie group `G` (over `I`) is recorded here as data with
hypotheses, `SymplecticGeometry.LieComplexification I G IC Gc`: a real Lie group `Gc` (over
`IC`) containing `G` through an injective smooth homomorphism `toHom`, a complex structure
`cplx` on the Lie algebra of `Gc` that commutes with every `ad`, for which the Lie algebra of `Gc`
is the direct sum of the image `𝔤` of the Lie algebra of `G` and of `cplx 𝔤`, and a polar
decomposition: a diffeomorphism `𝔤 × G ≃ Gc`, `(ξ, u) ↦ exp (cplx ξ) * u`.

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
* `SymplecticGeometry.LieComplexification.injective_lieMap`: `lieMap` is injective.
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
homomorphism `toHom : G → Gc`, a real-linear map `cplx` on the Lie algebra of `Gc` with
`cplx ∘ cplx = -1` that commutes with every `ad` (so that the Lie algebra of `Gc` is a complex
Lie algebra), for which the Lie algebra of `Gc` is the direct sum of the image of the Lie algebra
`𝔤` of `G` and of its image under `cplx`, and a diffeomorphism
`polar : 𝔤 × G ≃ Gc`, `(ξ, u) ↦ exp (cplx ξ) * toHom u`.

The laws of the structure do not determine `cplx`: for `Circle` in `ℂˣ`, multiplication by any
`a + i b` with `a ≠ 0` on the Lie algebra `ℂ` satisfies all of them. What ties `cplx` to a
complex structure elsewhere is a compatibility condition with an action, not this structure. -/
structure LieComplexification where
  /-- The inclusion of `G` into its complexification. -/
  toHom : ContMDiffMonoidMorphism I IC ∞ G Gc
  injective_toHom : Injective toHom
  /-- The complex structure of the Lie algebra of the complexification. -/
  cplx : GroupLieAlgebra IC Gc →ₗ[ℝ] GroupLieAlgebra IC Gc
  cplx_cplx (x : GroupLieAlgebra IC Gc) : cplx (cplx x) = -x
  cplx_lie (x y : GroupLieAlgebra IC Gc) : cplx ⁅x, y⁆ = ⁅x, cplx y⁆
  isCompl_range : IsCompl (LinearMap.range toHom.groupLieAlgebraLieHom.toLinearMap)
    (LinearMap.range (cplx ∘ₗ toHom.groupLieAlgebraLieHom.toLinearMap))
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
  rw [lieMap_def, ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom]
  exact MonoidHom.groupLieAlgebraMap_apply _ _ ξ

theorem isCompl_range_lieMap : IsCompl (LinearMap.range C.lieMap.toLinearMap)
    (LinearMap.range (C.cplx ∘ₗ C.lieMap.toLinearMap)) :=
  C.isCompl_range

@[simp]
theorem cplx_lie_left (x y : GroupLieAlgebra IC Gc) : C.cplx ⁅x, y⁆ = ⁅x, C.cplx y⁆ :=
  C.cplx_lie x y

/-- The complex structure also commutes with right brackets. -/
theorem cplx_lie_right (x y : GroupLieAlgebra IC Gc) : C.cplx ⁅x, y⁆ = ⁅C.cplx x, y⁆ := by
  rw [← lie_skew, map_neg, C.cplx_lie, ← lie_skew, neg_neg]

theorem injective_cplx : Injective C.cplx := fun x y h ↦ by
  simpa [C.cplx_cplx] using congrArg C.cplx h

section FiniteDimensional

variable [T2Space G] [BoundarylessManifold I G] [FiniteDimensional ℝ E] [FiniteDimensional ℝ EC]

/-- The inclusion of `G` into its complexification intertwines the exponentials:
`toHom (exp ξ) = exp (lieMap ξ)`. -/
theorem toHom_mulInvariantExp (ξ : GroupLieAlgebra I G) :
    C.toHom (mulInvariantExp ξ) = mulInvariantExp (C.lieMap ξ) := by
  obtain ⟨X, rfl⟩ := (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint).surjective ξ
  have h := map_lieExp C.toHom X
  simp only [lieExp_eq_mulInvariantExp] at h
  rw [h, lieMap_def, ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom,
    MonoidHom.groupLieAlgebraMap_apply, ← leftInvariantDerivationLieEquivGroupLieAlgebra_apply,
    ← leftInvariantDerivationLieEquivGroupLieAlgebra_apply]
  exact congrArg _ (leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap C.toHom X)

/-- The Lie algebra map of the inclusion of `G` into its complexification is injective. -/
theorem injective_lieMap : Injective C.lieMap := by
  refine (injective_iff_map_eq_zero C.lieMap).2 fun ξ hξ ↦ ?_
  have hconst : (fun t : ℝ ↦ mulInvariantExp (I := I) (G := G) (t • ξ)) = fun _ ↦ 1 := by
    funext t
    apply C.injective_toHom
    rw [toHom_mulInvariantExp, map_smul, hξ, smul_zero, mulInvariantExp_zero, map_one]
  have h := hasMFDerivAt_mulInvariantExp_smul_zero (I := I) (G := G) ξ
  rw [hconst] at h
  have h0 : (1 : ℝ →L[ℝ] ℝ).smulRight ξ = 0 :=
    h.mfderiv.symm.trans (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := I) (1 : G) (0 : ℝ)).mfderiv
  simpa using congrArg (fun L : ℝ →L[ℝ] GroupLieAlgebra I G ↦ L (1 : ℝ)) h0

theorem injective_cplx_comp_lieMap : Injective (C.cplx ∘ₗ C.lieMap.toLinearMap) :=
  C.injective_cplx.comp C.injective_lieMap

/-- The component of an element of the Lie algebra of `Gc` along `lieMap 𝔤`, read in `𝔤`. -/
def re : GroupLieAlgebra IC Gc →ₗ[ℝ] GroupLieAlgebra I G :=
  LinearMap.linearProjOfIsCompl _ C.lieMap.toLinearMap C.injective_lieMap C.isCompl_range_lieMap

/-- The component of an element of the Lie algebra of `Gc` along `cplx (lieMap 𝔤)`, read in
`𝔤`. -/
def im : GroupLieAlgebra IC Gc →ₗ[ℝ] GroupLieAlgebra I G :=
  LinearMap.linearProjOfIsCompl _ (C.cplx ∘ₗ C.lieMap.toLinearMap) C.injective_cplx_comp_lieMap
    C.isCompl_range_lieMap.symm

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
  rw [expI_def, map_zero, map_zero, mulInvariantExp_zero (I := IC)]

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
  -- `0 : E` is the zero of `GroupLieAlgebra I G` only up to unfolding `TangentSpace`, so
  -- `expI_zero` is applied by `exact` rather than `rw`.
  rw [polar_apply]
  exact (congrArg (· * C.toHom u) C.expI_zero).trans (one_mul _)

/-- A complexification is determined by its inclusion and its complex structure. -/
@[ext]
theorem ext {C C' : LieComplexification I G IC Gc} (htoHom : C.toHom = C'.toHom)
    (hcplx : C.cplx = C'.cplx) : C = C' := by
  obtain ⟨toHom, hinj, cplx, h₁, h₂, h₃, polar, hpolar⟩ := C
  obtain ⟨toHom', hinj', cplx', h₁', h₂', h₃', polar', hpolar'⟩ := C'
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
