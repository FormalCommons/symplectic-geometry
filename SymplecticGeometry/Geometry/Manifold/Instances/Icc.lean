/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorField.Prod
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The inclusion and the unit vector field of a closed interval

The inclusion `Icc x y → ℝ` of a closed interval, `x < y`, is differentiable everywhere, ends
included (`mdifferentiable_subtypeVal_Icc`, `mdifferentiableAt_subtypeVal_Icc`), by Mathlib's
`contMDiff_subtypeVal_Icc`.

A closed interval `[x, y]`, `x < y`, with its manifold-with-boundary structure, carries the unit
tangent vector `1` of Mathlib's `oneTangentSpaceIcc` at every point. This file shows that the
vector field `z ↦ 1` is smooth, up to both ends (`contMDiff_totalSpaceMk_one_Icc`). It is not the
constant field of the model space `EuclideanSpace ℝ (Fin 1)`, since the chart at the right end
reverses orientation. It is the tangent map of the projection `Set.projIcc` applied to the
constant field `1` of `ℝ`, which is how the smoothness is proved.

On a cylinder `[0, 1] × P`, the product (Tau Ceti's `TauCeti.Manifold.prodVectorField`) of this
field with the zero field of `P` is the unit time field `∂ₜ = (1, 0)`. It is smooth, up to both
ends (`contMDiff_prodVectorField_one_zero`), so it is a smooth section of the tangent bundle
(`unitIntervalTimeField`).

Every tangent vector of the interval is a real multiple of `1`: a vector that the inclusion sends
to `r` is `r • 1` (`eq_smul_one_of_mfderiv_subtypeVal_Icc`). So the derivative of a map into the
interval is read off from that of its composite with the inclusion
(`mfderiv_apply_eq_smul_one_Icc`), and continuous linear maps on a tangent space of the interval
agree when they agree on `1` (`ContinuousLinearMap.ext_tangentSpace_Icc`).

Between two points `s` and `t` of `[x, y]`, the derivative of Mathlib's convex combination
`Set.Icc.convexComb s t`, from the unit interval, sends the unit vector to `t - s` times the
unit vector (`Set.Icc.mfderiv_convexComb_one`); its smoothness is Tau Ceti's
`ContMDiff.convexComb`.

Mathlib's affine homeomorphism `iccHomeoI x y h : [x, y] ≃ₜ [0, 1]` and its inverse are smooth,
up to both ends (`contMDiff_iccHomeoI`, `contMDiff_iccHomeoI_symm`), since their composites with
the inclusions into `ℝ` are affine.

On the unit interval, the derivative of left multiplication `s ↦ T s` sends the unit vector at
`t` to `T` times the unit vector at `T t` (`unitInterval.mfderiv_mul_left_one`).
-/

public section

open Set
open scoped Manifold ContDiff

variable {x y : ℝ} [Fact (x < y)] {n : WithTop ℕ∞}

namespace SymplecticGeometry

/-- The inclusion `Icc x y → ℝ` of a closed interval is differentiable, up to both ends. -/
theorem mdifferentiable_subtypeVal_Icc :
    MDifferentiable (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) :=
  (contMDiff_subtypeVal_Icc (n := 1)).mdifferentiable one_ne_zero

/-- The inclusion `Icc x y → ℝ` of a closed interval is differentiable at each point, ends
included. -/
theorem mdifferentiableAt_subtypeVal_Icc (z : Icc x y) :
    MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z :=
  mdifferentiable_subtypeVal_Icc z

/-- The unit vector field `z ↦ 1` of a closed interval is smooth, up to both ends. -/
theorem contMDiff_totalSpaceMk_one_Icc :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1).tangent n
      (fun z : Icc x y ↦ (⟨z, 1⟩ : TangentBundle (𝓡∂ 1) (Icc x y))) := by
  have hT := (contMDiffOn_projIcc (x := x) (y := y) (n := ω)).contMDiffOn_tangentMapWithin
    (m := n) le_top (uniqueDiffOn_Icc (Fact.out : x < y)).uniqueMDiffOn
  have hg : ContMDiff (𝓡∂ 1) 𝓘(ℝ).tangent n
      (fun z : Icc x y ↦ (⟨z, (1 : TangentSpace 𝓘(ℝ) (z : ℝ))⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
    contMDiff_tangentBundle_mk_modelSpace contMDiff_subtypeVal_Icc contMDiff_const
  refine (hT.comp_contMDiff hg fun z ↦ z.property).congr fun z ↦ ?_
  simp only [Function.comp_apply, tangentMapWithin]
  rw [mfderivWithin_projIcc_one z.property, projIcc_val]

section Cylinder

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [IsManifold J 1 P]

/-- The unit time field `∂ₜ = (1, 0)` of the cylinder `[0, 1] × P` is smooth, up to both ends. -/
theorem contMDiff_prodVectorField_one_zero :
    ContMDiff ((𝓡∂ 1).prod J) ((𝓡∂ 1).prod J).tangent ∞ (fun p : unitInterval × P ↦
      (⟨p, TauCeti.Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
        (0 : Π y : P, TangentSpace J y) p⟩ : TangentBundle ((𝓡∂ 1).prod J) (unitInterval × P))) :=
  TauCeti.Manifold.contMDiff_prodVectorField contMDiff_totalSpaceMk_one_Icc
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace J))

/-- The unit time field `∂ₜ = (1, 0)` of the cylinder `[0, 1] × P`, as a smooth section of the
tangent bundle. -/
noncomputable def unitIntervalTimeField :
    Cₛ^∞⟮(𝓡∂ 1).prod J; EuclideanSpace ℝ (Fin 1) × E',
      TangentSpace ((𝓡∂ 1).prod J) (M := unitInterval × P)⟯ :=
  ⟨TauCeti.Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
    (0 : Π y : P, TangentSpace J y), contMDiff_prodVectorField_one_zero⟩

/-- The unit time field of the cylinder is the product field of `1` on `[0, 1]` and `0` on
`P`. -/
@[simp]
theorem coe_unitIntervalTimeField :
    ⇑(unitIntervalTimeField : Cₛ^∞⟮(𝓡∂ 1).prod J; EuclideanSpace ℝ (Fin 1) × E',
      TangentSpace ((𝓡∂ 1).prod J) (M := unitInterval × P)⟯) =
      TauCeti.Manifold.prodVectorField (fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
        (0 : Π y : P, TangentSpace J y) :=
  (rfl)

end Cylinder

/-- A tangent vector `v` of a closed interval `[x, y]`, `x < y`, is `r` times the unit tangent
vector `1` when the inclusion `Icc x y → ℝ` sends it to `r`. -/
theorem eq_smul_one_of_mfderiv_subtypeVal_Icc {z : Icc x y} {v : TangentSpace (𝓡∂ 1) z} {r : ℝ}
    (h : mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z v = r) :
    v = r • (1 : TangentSpace (𝓡∂ 1) z) := by
  -- The inclusion has invertible derivative, which sends `1` to `1`.
  refine (TauCeti.isInvertible_mfderiv_subtypeVal_Icc z).injective ?_
  rw [map_smul, mfderiv_subtypeVal_Icc_one, h]
  exact (mul_one (M := ℝ) _).symm

/-- Let `f` be a map from a manifold `M` into a closed interval `[x, y]`, `x < y`, differentiable
at `t`. If the derivative at `t` of `Subtype.val ∘ f : M → ℝ` sends `v` to `r`, then the
derivative of `f` at `t` sends `v` to `r` times the unit tangent vector `1` at `f t`. -/
theorem mfderiv_apply_eq_smul_one_Icc {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {f : M → Icc x y} {t : M} (hf : MDifferentiableAt I (𝓡∂ 1) f t) {v : TangentSpace I t}
    {r : ℝ} (h : mfderiv I 𝓘(ℝ) (Subtype.val ∘ f) t v = r) :
    mfderiv I (𝓡∂ 1) f t v = r • (1 : TangentSpace (𝓡∂ 1) (f t)) := by
  refine eq_smul_one_of_mfderiv_subtypeVal_Icc ?_
  rw [← mfderiv_comp_apply t (mdifferentiableAt_subtypeVal_Icc _) hf, h]

end SymplecticGeometry

/-- Two continuous linear maps on a tangent space of a closed interval `[x, y]`, `x < y`, are equal
when they agree on the unit tangent vector `1`. -/
theorem ContinuousLinearMap.ext_tangentSpace_Icc {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] {z : Icc x y} {f g : TangentSpace (𝓡∂ 1) z →L[ℝ] F} (h : f 1 = g 1) :
    f = g := by
  ext1 v
  obtain ⟨r, hr⟩ : ∃ r : ℝ, mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z v = r := ⟨_, rfl⟩
  rw [SymplecticGeometry.eq_smul_one_of_mfderiv_subtypeVal_Icc hr, map_smul, map_smul, h]

/-- Mathlib's affine homeomorphism `iccHomeoI x y h : Icc x y ≃ₜ unitInterval`,
`z ↦ (z - x) / (y - x)`, is `C^n` for every `n`, up to both ends. -/
theorem contMDiff_iccHomeoI (h : x < y) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) n (iccHomeoI x y h) := by
  refine contMDiff_iff_comp_subtypeVal_Icc.mpr ⟨(iccHomeoI x y h).continuous, ?_⟩
  have hval : Subtype.val ∘ iccHomeoI x y h = (fun z : ℝ ↦ (z - x) / (y - x)) ∘ Subtype.val :=
    funext (iccHomeoI_apply_coe x y h)
  rw [hval]
  exact ((contDiff_id.sub contDiff_const).div_const _).contMDiff.comp contMDiff_subtypeVal_Icc

/-- The inverse `u ↦ (y - x) u + x` of Mathlib's affine homeomorphism
`iccHomeoI x y h : Icc x y ≃ₜ unitInterval` is `C^n` for every `n`, up to both ends. -/
theorem contMDiff_iccHomeoI_symm (h : x < y) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) n (iccHomeoI x y h).symm := by
  refine contMDiff_iff_comp_subtypeVal_Icc.mpr ⟨(iccHomeoI x y h).symm.continuous, ?_⟩
  have hval : Subtype.val ∘ (iccHomeoI x y h).symm =
      (fun u : ℝ ↦ (y - x) * u + x) ∘ Subtype.val :=
    funext (iccHomeoI_symm_apply_coe x y h)
  rw [hval]
  exact ((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff.comp
    contMDiff_subtypeVal_Icc

namespace Set.Icc

/-- The derivative of Mathlib's convex combination `u ↦ (1 - u) s + u t`, the affine path from
`s` to `t` in a closed interval, sends the unit tangent vector to `t - s` times the unit tangent
vector. -/
theorem mfderiv_convexComb_one (s t : Icc x y) (u : unitInterval) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (convexComb s t) u 1 =
      ((t : ℝ) - s) • (1 : TangentSpace (𝓡∂ 1) (convexComb s t u)) := by
  have hc : ContMDiff (𝓡∂ 1) (𝓡∂ 1) 1 (convexComb s t) :=
    contMDiff_const.convexComb contMDiff_const contMDiff_id
  refine SymplecticGeometry.mfderiv_apply_eq_smul_one_Icc (hc.mdifferentiable one_ne_zero u) ?_
  have hval : Subtype.val ∘ convexComb s t = (fun r : ℝ ↦ (1 - r) * s + r * t) ∘ Subtype.val :=
    funext (coe_convexComb s t)
  have hd : HasDerivAt (fun r : ℝ ↦ (1 - r) * s + r * t) ((t : ℝ) - s) (u : ℝ) :=
    funext (AffineMap.lineMap_apply_ring (s : ℝ) t) ▸ AffineMap.hasDerivAt_lineMap
  rw [hval, mfderiv_comp_apply u hd.differentiableAt.mdifferentiableAt
    (SymplecticGeometry.mdifferentiableAt_subtypeVal_Icc u), mfderiv_subtypeVal_Icc_one,
    mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.toSpanSingleton_apply]
  -- The tangent spaces of `ℝ` are `ℝ` itself, through `NormedSpace.fromTangentSpace`, which is
  -- the identity; Mathlib has no lemma that evaluates it.
  exact one_smul ℝ ((t : ℝ) - s)

end Set.Icc

namespace unitInterval

/-- The derivative of `s ↦ T s` on the unit interval sends the unit tangent vector at `t` to `T`
times the unit tangent vector at `T t`. -/
theorem mfderiv_mul_left_one (T t : unitInterval) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (T * ·) t 1 = (T : ℝ) • (1 : TangentSpace (𝓡∂ 1) (T * t)) := by
  refine SymplecticGeometry.mfderiv_apply_eq_smul_one_Icc mdifferentiableAt_mul_left ?_
  have hval : (Subtype.val : unitInterval → ℝ) ∘ (T * ·) = (T : ℝ) • Subtype.val :=
    funext fun s ↦ Set.Icc.coe_mul T s
  rw [hval, const_smul_mfderiv (SymplecticGeometry.mdifferentiableAt_subtypeVal_Icc t)]
  -- The tangent spaces of `ℝ` at `t` and at `(T • Subtype.val) t` are equal only up to
  -- unfolding, so `smul_apply` does not rewrite the left side.
  exact (congrArg ((T : ℝ) • ·) (mfderiv_subtypeVal_Icc_one t)).trans (mul_one (M := ℝ) _)

end unitInterval

end
