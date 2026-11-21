/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The unit vector field of a closed interval

A closed interval `[x, y]`, `x < y`, with its manifold-with-boundary structure, carries the unit
tangent vector `1` of Mathlib's `oneTangentSpaceIcc` at every point. This file shows that the
vector field `z ↦ 1` is smooth, up to both ends (`contMDiff_totalSpaceMk_one_Icc`). It is not the
constant field of the model space `EuclideanSpace ℝ (Fin 1)`, since the chart at the right end
reverses orientation. It is the tangent map of the projection `Set.projIcc` applied to the
constant field `1` of `ℝ`, which is how the smoothness is proved.
-/

public section

open Set
open scoped Manifold ContDiff

variable {x y : ℝ} [Fact (x < y)] {n : WithTop ℕ∞}

/-- The unit vector field `z ↦ 1` of a closed interval is smooth, up to both ends. -/
theorem contMDiff_totalSpaceMk_one_Icc :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1).tangent n
      (fun z : Icc x y ↦ (⟨z, 1⟩ : TangentBundle (𝓡∂ 1) (Icc x y))) := by
  have hT := (contMDiffOn_projIcc (x := x) (y := y) (n := ω)).contMDiffOn_tangentMapWithin
    (m := n) le_top (uniqueDiffOn_Icc (Fact.out : x < y)).uniqueMDiffOn
  have hg : ContMDiff (𝓡∂ 1) 𝓘(ℝ).tangent n
      (fun z : Icc x y ↦ (⟨z, (1 : TangentSpace 𝓘(ℝ) (z : ℝ))⟩ : TangentBundle 𝓘(ℝ) ℝ)) := by
    have h : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ × ℝ) n (fun z : Icc x y ↦ ((z : ℝ), (1 : ℝ))) :=
      contMDiff_subtypeVal_Icc.prodMk_space contMDiff_const
    rw [modelWithCornersSelf_prod] at h
    -- `TotalSpace.toProd` has no simp lemma for its inverse; it is `(b, v) ↦ ⟨b, v⟩` by
    -- definition, and the unit vector of `ℝ` is `(1 : ℝ)` by definition.
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ))).comp h
  refine (hT.comp_contMDiff hg fun z ↦ z.property).congr fun z ↦ ?_
  simp only [Function.comp_apply, tangentMapWithin]
  rw [mfderivWithin_projIcc_one z.property, projIcc_val]

end
