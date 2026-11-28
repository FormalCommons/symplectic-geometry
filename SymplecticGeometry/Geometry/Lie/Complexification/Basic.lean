/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.TotallyReal.CompatibleForm
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.Functor
import SymplecticGeometry.Geometry.Lie.GroupLieAlgebraLieHom
import SymplecticGeometry.Analysis.RCLike.Basic
import SymplecticGeometry.Geometry.Lie.Adjoint.Commute

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

This file holds the structure and the linear algebra of the complexified Lie algebra: the
components `re` and `im`, how the bracket and the adjoint action of `G` meet them, the form built
from a form on the Lie algebra of `G`, and the conjugation. The exponential of the imaginary
directions, the polar decomposition with its Gauss lemma, and the example `Circle` in `ℂˣ` are in
`SymplecticGeometry.Geometry.Lie.Complexification.Polar`.

## Main definitions

* `SymplecticGeometry.LieComplexification`: the structure.
* `SymplecticGeometry.LieComplexification.lieMap`: the Lie algebra map of `toHom`, Tau Ceti's
  `ContMDiffMonoidMorphism.groupLieAlgebraLieHom`.
* `SymplecticGeometry.LieComplexification.re`, `SymplecticGeometry.LieComplexification.im`: the
  two components of an element of the Lie algebra of `Gc` in the decomposition
  `lieMap 𝔤 ⊕ cplx (lieMap 𝔤)`.
* `SymplecticGeometry.LieComplexification.complexifyForm`: the form
  `(x, y) ↦ B (re x) (re y) + B (im x) (im y)` on the Lie algebra of `Gc` induced by a form `B`
  on that of `G`, defined as Tau Ceti's `TauCeti.IsMaximalTotallyReal.compatibleForm` of
  `(x, y) ↦ B (re x) (re y)` for the maximal totally real image of `lieMap`.
* `SymplecticGeometry.LieComplexification.conj`: the conjugation
  `x ↦ lieMap (re x) - cplx (lieMap (im x))`.

## Main results

* `SymplecticGeometry.LieComplexification.finiteDimensional`: the Lie algebra of `Gc` is
  finite-dimensional if that of `G` is.
* `SymplecticGeometry.LieComplexification.toHom_mulInvariantExp`: `toHom` intertwines the
  exponentials through `lieMap`.
* `SymplecticGeometry.LieComplexification.lieMap_injective`: `lieMap` is injective.
* `SymplecticGeometry.LieComplexification.lieMap_re_add_cplx_lieMap_im`: every element `x` is
  `lieMap (re x) + cplx (lieMap (im x))`.
* `SymplecticGeometry.LieComplexification.im_mfderiv_inv_mul_mfderiv_toHom_comp`: a map into
  `Gc` that factors through `toHom` has left-trivialized derivatives with vanishing `im`.
* `SymplecticGeometry.LieComplexification.cplx_lie_cplx`: `⁅cplx x, cplx y⁆ = -⁅x, y⁆`.
* `SymplecticGeometry.LieComplexification.lie_add_cplx`,
  `SymplecticGeometry.LieComplexification.lie_lieMap_add_cplx_lieMap`,
  `SymplecticGeometry.LieComplexification.re_lie`, `SymplecticGeometry.LieComplexification.im_lie`:
  the bracket multiplies like complex numbers,
  `re ⁅x, y⁆ = ⁅re x, re y⁆ - ⁅im x, im y⁆` and `im ⁅x, y⁆ = ⁅re x, im y⁆ + ⁅im x, re y⁆`.
* `SymplecticGeometry.LieComplexification.re_cplx`,
  `SymplecticGeometry.LieComplexification.im_cplx`: `re (cplx x) = -im x` and
  `im (cplx x) = re x`.
* `SymplecticGeometry.LieComplexification.projection_range_lieMap_apply`: the projection onto
  the image of `lieMap` along its image under `cplx` is `lieMap ∘ re`.
* `SymplecticGeometry.LieComplexification.re_lie_cplx_lieMap`,
  `SymplecticGeometry.LieComplexification.im_lie_cplx_lieMap`: for `A = ad (cplx (lieMap ξ))`,
  `re (A x) = -⁅ξ, im x⁆` and `im (A x) = ⁅ξ, re x⁆`.
* `SymplecticGeometry.LieComplexification.isSymm_complexifyForm`,
  `SymplecticGeometry.LieComplexification.complexifyForm_apply_self_pos`: `complexifyForm B` is
  symmetric, or positive definite, when `B` is, from Tau Ceti's
  `TauCeti.IsMaximalTotallyReal.isSymm_compatibleForm` and
  `TauCeti.IsMaximalTotallyReal.compatibleForm_pos`.
* `SymplecticGeometry.LieComplexification.isSelfAdjoint_ad_cplx_lieMap`: for an `ad`-invariant
  `B`, the operator `ad (cplx (lieMap ξ))` is self-adjoint for `complexifyForm B`, in the form
  that Tau Ceti's `LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top` takes.
* `SymplecticGeometry.LieComplexification.self_add_conj`: `x + conj x = 2 • lieMap (re x)`.
* `SymplecticGeometry.LieComplexification.conj_lie`,
  `SymplecticGeometry.LieComplexification.conj_lie_cplx_lieMap`: `conj` preserves brackets, so
  it anticommutes with `ad (cplx (lieMap ξ))`.
* `SymplecticGeometry.LieComplexification.connectedSpace`: `Gc` is connected if `G` is.
* `SymplecticGeometry.LieComplexification.tangentAd_toHom_apply`,
  `SymplecticGeometry.LieComplexification.re_tangentAd_toHom`,
  `SymplecticGeometry.LieComplexification.im_tangentAd_toHom`: for connected `G`, `Ad (toHom u)`
  acts componentwise, so `re (Ad (toHom u) x) = Ad u (re x)`, and the same for `im`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], §2 (the complexified group and its
  polar decomposition) and Appendix E (the inner product on the complexified Lie algebra built
  from an invariant one on the Lie algebra of `G`, for which `ad` of an imaginary direction is
  self-adjoint, and the conjugation fixing the real directions).
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

/-- The Lie algebra of a complexification of a finite-dimensional Lie group is
finite-dimensional: it is the sum of the images of `lieMap` and `cplx ∘ lieMap`. This is not an
instance, since instance search cannot find `C`; use it as `have := C.finiteDimensional`. -/
theorem finiteDimensional (C : LieComplexification I G IC Gc) [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ EC := by
  have hs : Surjective (C.lieMap.toLinearMap.coprod (C.cplx.toLinearMap ∘ₗ C.lieMap.toLinearMap)) :=
    LinearMap.range_eq_top.1 (by rw [LinearMap.range_coprod, C.isCompl_range_lieMap.sup_eq_top])
  exact Module.Finite.of_surjective _ hs

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

variable [FiniteDimensional ℝ E]

/-- The inclusion of `G` into its complexification intertwines the exponentials:
`toHom (exp ξ) = exp (lieMap ξ)`. -/
theorem toHom_mulInvariantExp [T2Space G] [BoundarylessManifold I G] (ξ : GroupLieAlgebra I G) :
    C.toHom (mulInvariantExp ξ) = mulInvariantExp (C.lieMap ξ) := by
  have := C.finiteDimensional
  exact C.toHom.map_mulInvariantExp ξ

/-- The Lie algebra map of the inclusion of `G` into its complexification is injective. -/
theorem lieMap_injective : Injective C.lieMap := by
  have := C.finiteDimensional
  exact C.toHom.groupLieAlgebraLieHom_injective C.toHom_injective

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

theorem re_cplx_lieMap (ξ : GroupLieAlgebra I G) : C.re (C.cplx (C.lieMap ξ)) = 0 :=
  LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ _ ⟨ξ, rfl⟩

theorem im_cplx_lieMap (ξ : GroupLieAlgebra I G) : C.im (C.cplx (C.lieMap ξ)) = ξ :=
  LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ ξ

@[simp]
theorem im_lieMap (ξ : GroupLieAlgebra I G) : C.im (C.lieMap ξ) = 0 :=
  LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ _ ⟨ξ, rfl⟩

/-- A map into `Gc` that factors through `C.toHom` has left-trivialized derivatives in the image
of `lieMap`, so their component `im` vanishes: for `f : N → G` differentiable at `z` and `w`
tangent at `z`, `im (d(L_{g⁻¹})_g (d(toHom ∘ f)_z w)) = 0`, where `g = toHom (f z)`. -/
theorem im_mfderiv_inv_mul_mfderiv_toHom_comp {EN : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] {f : N → G} {z : N}
    (hf : MDifferentiableAt IN I f z) (w : TangentSpace IN z) :
    C.im (mfderiv IC IC ((C.toHom (f z))⁻¹ * ·) (C.toHom (f z))
      (mfderiv IN IC (C.toHom ∘ f) z w)) = 0 := by
  have hc := mfderiv_comp_apply z ((C.toHom.contMDiff_toFun.mdifferentiable (by simp)) (f z)) hf w
  have h0 (ξ : GroupLieAlgebra I G) : C.im (C.toHom.groupLieAlgebraLieHom ξ) = 0 := by
    rw [← lieMap_def, im_lieMap]
  -- `rw` cannot rewrite under `C.im` here: its argument has type
  -- `TangentSpace IC ((C.toHom (f z))⁻¹ * C.toHom (f z))`, which is `GroupLieAlgebra IC Gc` only
  -- up to unfolding, so the equalities are chained as terms.
  exact (congrArg (fun v ↦ C.im (mfderiv IC IC ((C.toHom (f z))⁻¹ * ·) (C.toHom (f z)) v)) hc).trans
    ((congrArg C.im (C.toHom.mfderiv_inv_mul_mfderiv (f z) (mfderiv IN I f z w))).trans (h0 _))

/-- Every element of the Lie algebra of `Gc` is `lieMap (re x) + cplx (lieMap (im x))`. -/
theorem lieMap_re_add_cplx_lieMap_im (x : GroupLieAlgebra IC Gc) :
    C.lieMap (C.re x) + C.cplx (C.lieMap (C.im x)) = x := by
  obtain ⟨_, ⟨ξ, rfl⟩, _, ⟨η, rfl⟩, rfl⟩ :=
    Submodule.mem_sup.1 (C.isCompl_range_lieMap.sup_eq_top ▸ Submodule.mem_top (x := x))
  simp [re_cplx_lieMap, im_cplx_lieMap]

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

/-- The real part of a bracket with an imaginary direction:
`re ⁅cplx (lieMap ξ), x⁆ = -⁅ξ, im x⁆`. -/
theorem re_lie_cplx_lieMap (ξ : GroupLieAlgebra I G) (x : GroupLieAlgebra IC Gc) :
    C.re ⁅C.cplx (C.lieMap ξ), x⁆ = -⁅ξ, C.im x⁆ := by
  rw [re_lie, re_cplx_lieMap, im_cplx_lieMap, zero_lie, zero_sub]

/-- The imaginary part of a bracket with an imaginary direction:
`im ⁅cplx (lieMap ξ), x⁆ = ⁅ξ, re x⁆`. -/
theorem im_lie_cplx_lieMap (ξ : GroupLieAlgebra I G) (x : GroupLieAlgebra IC Gc) :
    C.im ⁅C.cplx (C.lieMap ξ), x⁆ = ⁅ξ, C.re x⁆ := by
  rw [im_lie, re_cplx_lieMap, im_cplx_lieMap, zero_lie, zero_add]

/-- The real part of an image under the complex structure: `re (cplx x) = -im x`. -/
@[simp]
theorem re_cplx (x : GroupLieAlgebra IC Gc) : C.re (C.cplx x) = -C.im x := by
  conv_lhs => rw [← C.lieMap_re_add_cplx_lieMap_im x]
  rw [map_add, AlmostComplexStructure.apply_apply, map_add, map_neg, re_cplx_lieMap, re_lieMap,
    zero_add]

/-- The imaginary part of an image under the complex structure: `im (cplx x) = re x`. -/
@[simp]
theorem im_cplx (x : GroupLieAlgebra IC Gc) : C.im (C.cplx x) = C.re x := by
  conv_lhs => rw [← C.lieMap_re_add_cplx_lieMap_im x]
  rw [map_add, AlmostComplexStructure.apply_apply, map_add, map_neg, im_cplx_lieMap, im_lieMap,
    neg_zero, add_zero]

/-- The projection onto the image of `lieMap` along its image under `cplx` is `lieMap ∘ re`. -/
theorem projection_range_lieMap_apply (x : GroupLieAlgebra IC Gc) :
    (LinearMap.range C.lieMap.toLinearMap).projection
        ((LinearMap.range C.lieMap.toLinearMap).map C.cplx.toLinearMap)
        C.isMaximalTotallyReal_range_lieMap.isCompl x = C.lieMap (C.re x) := by
  have hmem (ξ : GroupLieAlgebra I G) : C.lieMap ξ ∈ LinearMap.range C.lieMap.toLinearMap := by
    simp
  conv_lhs => rw [← C.lieMap_re_add_cplx_lieMap_im x]
  rw [map_add, Submodule.projection_apply_of_mem_left _ (hmem _),
    C.isMaximalTotallyReal_range_lieMap.projection_map_of_mem (hmem _), add_zero]

/-- Two elements of the Lie algebra of `Gc` with the same components `re` and `im` are equal. -/
theorem ext_re_im {x y : GroupLieAlgebra IC Gc} (hre : C.re x = C.re y) (him : C.im x = C.im y) :
    x = y := by
  rw [← C.lieMap_re_add_cplx_lieMap_im x, ← C.lieMap_re_add_cplx_lieMap_im y, hre, him]

/-- The bilinear form on the Lie algebra of `Gc` induced by a bilinear form `B` on that of `G`,
`(x, y) ↦ B (re x) (re y) + B (im x) (im y)`, which pairs the components of `x` and `y` in the
decomposition `lieMap 𝔤 ⊕ cplx (lieMap 𝔤)`. It is Tau Ceti's
`TauCeti.IsMaximalTotallyReal.compatibleForm` of the form `(x, y) ↦ B (re x) (re y)`, for the
maximal totally real image of `lieMap`, so it is `cplx`-invariant
(`TauCeti.IsMaximalTotallyReal.compatibleForm_map_map`) and makes the two summands orthogonal. -/
def complexifyForm (B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)) :
    LinearMap.BilinForm ℝ (GroupLieAlgebra IC Gc) :=
  C.isMaximalTotallyReal_range_lieMap.compatibleForm (B.compl₁₂ C.re C.re)

theorem complexifyForm_def (B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)) :
    C.complexifyForm B = C.isMaximalTotallyReal_range_lieMap.compatibleForm (B.compl₁₂ C.re C.re) :=
  (rfl)

@[simp]
theorem complexifyForm_apply (B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G))
    (x y : GroupLieAlgebra IC Gc) :
    C.complexifyForm B x y = B (C.re x) (C.re y) + B (C.im x) (C.im y) := by
  rw [complexifyForm_def, IsMaximalTotallyReal.compatibleForm_apply]
  simp only [projection_range_lieMap_apply, LinearMap.compl₁₂_apply, re_lieMap, re_cplx,
    LinearMap.map_neg, LinearMap.neg_apply, neg_neg]

/-- The form induced by a symmetric form is symmetric. -/
theorem isSymm_complexifyForm {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)} (hB : B.IsSymm) :
    (C.complexifyForm B).IsSymm :=
  IsMaximalTotallyReal.isSymm_compatibleForm _ (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simpa using hB.eq (C.re (C.lieMap a)) (C.re (C.lieMap b)))

/-- The form induced by a positive definite form is positive definite. -/
theorem complexifyForm_apply_self_pos {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
    (hB : ∀ v, v ≠ 0 → 0 < B v v) (x : GroupLieAlgebra IC Gc) (hx : x ≠ 0) :
    0 < C.complexifyForm B x x :=
  IsMaximalTotallyReal.compatibleForm_pos C.cplx.square_neg _ (by
    rintro _ ⟨ξ, rfl⟩ h
    simpa using hB ξ (by rintro rfl; simp at h)) hx

/-- For an `ad`-invariant form `B`, the operator `ad (cplx (lieMap ξ))` is self-adjoint for the
induced form `complexifyForm B`. -/
theorem isSelfAdjoint_ad_cplx_lieMap {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
    (hB : B.lieInvariant (GroupLieAlgebra I G)) (ξ : GroupLieAlgebra I G) :
    (C.complexifyForm B).IsSelfAdjoint (LieAlgebra.ad ℝ _ (C.cplx (C.lieMap ξ))) := by
  intro x y
  simp only [LieAlgebra.ad_apply, complexifyForm_apply, re_lie_cplx_lieMap, im_lie_cplx_lieMap,
    map_neg, LinearMap.neg_apply, hB ξ]
  ring

/-- The conjugation of the Lie algebra of `Gc` that fixes the image of `lieMap` and negates its
image under `cplx`: `x ↦ lieMap (re x) - cplx (lieMap (im x))`. -/
def conj : GroupLieAlgebra IC Gc →ₗ[ℝ] GroupLieAlgebra IC Gc :=
  C.lieMap.toLinearMap ∘ₗ C.re - C.cplx.toLinearMap ∘ₗ C.lieMap.toLinearMap ∘ₗ C.im

theorem conj_apply (x : GroupLieAlgebra IC Gc) :
    C.conj x = C.lieMap (C.re x) - C.cplx (C.lieMap (C.im x)) :=
  (rfl)

@[simp]
theorem re_conj (x : GroupLieAlgebra IC Gc) : C.re (C.conj x) = C.re x := by
  simp [conj_apply]

@[simp]
theorem im_conj (x : GroupLieAlgebra IC Gc) : C.im (C.conj x) = -C.im x := by
  simp [conj_apply]

@[simp]
theorem conj_conj (x : GroupLieAlgebra IC Gc) : C.conj (C.conj x) = x :=
  C.ext_re_im (by simp) (by simp)

/-- The analogue of `Complex.add_conj`: `x + conj x = 2 • lieMap (re x)`. -/
theorem self_add_conj (x : GroupLieAlgebra IC Gc) :
    x + C.conj x = (2 : ℝ) • C.lieMap (C.re x) := by
  nth_rw 1 [← C.lieMap_re_add_cplx_lieMap_im x]
  rw [conj_apply]
  module

@[simp]
theorem conj_lieMap (ξ : GroupLieAlgebra I G) : C.conj (C.lieMap ξ) = C.lieMap ξ :=
  C.ext_re_im (by simp) (by simp)

@[simp]
theorem conj_cplx_lieMap (ξ : GroupLieAlgebra I G) :
    C.conj (C.cplx (C.lieMap ξ)) = -C.cplx (C.lieMap ξ) :=
  C.ext_re_im (by simp) (by simp)

/-- The conjugation is a morphism of real Lie algebras: `conj ⁅x, y⁆ = ⁅conj x, conj y⁆`. -/
theorem conj_lie (x y : GroupLieAlgebra IC Gc) : C.conj ⁅x, y⁆ = ⁅C.conj x, C.conj y⁆ := by
  exact C.ext_re_im (by simp) (by simp [add_comm])

/-- The conjugation anticommutes with `ad (cplx (lieMap ξ))`:
`conj ⁅cplx (lieMap ξ), x⁆ = -⁅cplx (lieMap ξ), conj x⁆`. -/
theorem conj_lie_cplx_lieMap (ξ : GroupLieAlgebra I G) (x : GroupLieAlgebra IC Gc) :
    C.conj ⁅C.cplx (C.lieMap ξ), x⁆ = -⁅C.cplx (C.lieMap ξ), C.conj x⁆ := by
  rw [conj_lie, conj_cplx_lieMap, neg_lie]

end FiniteDimensional

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

/-- The complexification of a connected Lie group is connected. -/
theorem connectedSpace (C : LieComplexification I G IC Gc) [ConnectedSpace G] : ConnectedSpace Gc :=
  Function.Surjective.connectedSpace C.polar.toHomeomorph.surjective
    C.polar.toHomeomorph.continuous

/-- For connected `G`, the adjoint action of `toHom u` acts on the decomposition
`x = lieMap (re x) + cplx (lieMap (im x))` componentwise, through the adjoint action of `u`:
`Ad (toHom u) x = lieMap (Ad u (re x)) + cplx (lieMap (Ad u (im x)))`. -/
theorem tangentAd_toHom_apply [FiniteDimensional ℝ E] [ConnectedSpace G]
    (u : G) (x : GroupLieAlgebra IC Gc) :
    Lie.tangentAd (I := IC) (C.toHom u) x =
      C.lieMap (Lie.tangentAd (I := I) u (C.re x)) +
        C.cplx (C.lieMap (Lie.tangentAd (I := I) u (C.im x))) := by
  have := C.connectedSpace
  have := C.finiteDimensional
  conv_lhs => rw [← C.lieMap_re_add_cplx_lieMap_im x]
  rw [map_add, lieMap_def, ContMDiffMonoidMorphism.groupLieAlgebraLieHom_tangentAd,
    ContMDiffMonoidMorphism.groupLieAlgebraLieHom_tangentAd, ← lieMap_def]
  congr 1
  exact (Lie.map_tangentAd_apply_of_map_lie C.cplx.toLinearMap C.cplx_lie _ _).symm

/-- For connected `G`, the component `re` commutes with the adjoint actions:
`re (Ad (toHom u) x) = Ad u (re x)`. -/
theorem re_tangentAd_toHom [FiniteDimensional ℝ E] [ConnectedSpace G]
    (u : G) (x : GroupLieAlgebra IC Gc) :
    C.re (Lie.tangentAd (I := IC) (C.toHom u) x) = Lie.tangentAd (I := I) u (C.re x) := by
  rw [tangentAd_toHom_apply, map_add, re_lieMap, re_cplx_lieMap, add_zero]

/-- For connected `G`, the component `im` commutes with the adjoint actions:
`im (Ad (toHom u) x) = Ad u (im x)`. -/
theorem im_tangentAd_toHom [FiniteDimensional ℝ E] [ConnectedSpace G]
    (u : G) (x : GroupLieAlgebra IC Gc) :
    C.im (Lie.tangentAd (I := IC) (C.toHom u) x) = Lie.tangentAd (I := I) u (C.im x) := by
  rw [tangentAd_toHom_apply, map_add, im_lieMap, im_cplx_lieMap, zero_add]


end LieComplexification

end SymplecticGeometry

end
