/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
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

Every tangent vector of the interval is a real multiple of `1`, so continuous linear maps on a
tangent space of the interval agree when they agree on `1`
(`ContinuousLinearMap.ext_tangentSpace_Icc`).

On the unit interval, left multiplication `s ↦ T s` is a `C^n` map for every `n`
(`unitInterval.contMDiffMapMulLeft`, from Tau Ceti's `ContMDiffMul` instance), and its
derivative sends the unit vector at `t` to `T` times the unit vector at `T t`
(`unitInterval.mfderiv_mul_left_one`).
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

end SymplecticGeometry

/-- Two continuous linear maps on a tangent space of a closed interval `[x, y]`, `x < y`, are equal
when they agree on the unit tangent vector `1`. -/
theorem ContinuousLinearMap.ext_tangentSpace_Icc {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] {z : Icc x y} {f g : TangentSpace (𝓡∂ 1) z →L[ℝ] F} (h : f 1 = g 1) :
    f = g := by
  -- The inclusion has invertible derivative, which sends `1` to `1`, so `v = r • 1` for the image
  -- `r` of `v` in `ℝ`.
  have hv (v : TangentSpace (𝓡∂ 1) z) (r : ℝ)
      (hr : mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z v = r) :
      v = r • (1 : TangentSpace (𝓡∂ 1) z) := by
    refine (TauCeti.isInvertible_mfderiv_subtypeVal_Icc z).injective ?_
    rw [map_smul, mfderiv_subtypeVal_Icc_one, hr]
    exact (mul_one (M := ℝ) _).symm
  ext1 v
  obtain ⟨r, hr⟩ : ∃ r : ℝ, mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z v = r := ⟨_, rfl⟩
  rw [hv v r hr, map_smul, map_smul, h]

namespace unitInterval

/-- Left multiplication `s ↦ T s` by `T ∈ [0, 1]`, as a `C^n` map of the unit interval into
itself, for every `n`. -/
noncomputable def contMDiffMapMulLeft {n : WithTop ℕ∞} (T : unitInterval) :
    C^n⟮𝓡∂ 1, unitInterval; 𝓡∂ 1, unitInterval⟯ :=
  ⟨(T * ·), (contMDiff_mul_left (n := ω)).of_le le_top⟩

@[simp]
theorem contMDiffMapMulLeft_apply {n : WithTop ℕ∞} (T s : unitInterval) :
    contMDiffMapMulLeft (n := n) T s = T * s :=
  (rfl)

/-- The derivative of `s ↦ T s` on the unit interval sends the unit tangent vector at `t` to `T`
times the unit tangent vector at `T t`. -/
theorem mfderiv_mul_left_one (T t : unitInterval) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (T * ·) t 1 = (T : ℝ) • (1 : TangentSpace (𝓡∂ 1) (T * t)) := by
  have hmul : MDifferentiableAt (𝓡∂ 1) (𝓡∂ 1) (T * ·) t :=
    ((contMDiff_mul_left (n := ω)).of_le (le_top : (1 : WithTop ℕ∞) ≤ ω)).mdifferentiableAt
      one_ne_zero
  have hval : (Subtype.val : unitInterval → ℝ) ∘ (T * ·) = (T : ℝ) • Subtype.val :=
    funext fun s ↦ Set.Icc.coe_mul T s
  refine (TauCeti.isInvertible_mfderiv_subtypeVal_Icc (T * t)).injective ?_
  rw [← mfderiv_comp_apply t (SymplecticGeometry.mdifferentiableAt_subtypeVal_Icc _) hmul, hval,
    const_smul_mfderiv (SymplecticGeometry.mdifferentiableAt_subtypeVal_Icc t),
    map_smul, mfderiv_subtypeVal_Icc_one]
  -- The tangent spaces of `ℝ` at `T t` and at `(T • Subtype.val) t` are equal only up to
  -- unfolding, so `smul_apply` does not rewrite the left side.
  exact congrArg ((T : ℝ) • ·) (mfderiv_subtypeVal_Icc_one t)

end unitInterval

end
