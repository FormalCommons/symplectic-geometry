/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.IsManifold.Pi

/-!
# The product model of `𝕜^ι` and the Euclidean space

Mathlib models a finite product of manifolds modelled on `𝕜` (`ℝ` or `ℂ`), such as a torus
`ι → AddCircle p` over `ℝ`, on `ModelPi fun _ : ι ↦ 𝕜` with the product model
`ModelWithCorners.pi fun _ ↦ 𝓘(𝕜)`, whose norm is the sup norm. This file identifies that model
space with the Euclidean space `EuclideanSpace 𝕜 ι`, by a smooth diffeomorphism of model spaces
(`EuclideanSpace.modelPiDiffeomorph`). With `SymplecticGeometry.Remodel`, it charts such products
on an inner product space, as constructions like Tau Ceti's `TauCeti.ConnectedSum` need.

## Main definitions

* `EuclideanSpace.modelPiDiffeomorph 𝕜 ι n`: the identity of the coordinates, as a `C^n`
  diffeomorphism from `ModelPi fun _ : ι ↦ 𝕜`, with the product model, onto `EuclideanSpace 𝕜 ι`.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace EuclideanSpace

variable (𝕜 : Type*) [RCLike 𝕜] (ι : Type*) [Fintype ι] (n : ℕ∞ω)

/-- The model space `ModelPi fun _ : ι ↦ 𝕜` of a finite product of manifolds over `𝕜`, with its
product model, is `C^n` diffeomorphic to the Euclidean space `EuclideanSpace 𝕜 ι`, with its own
model, by the map keeping the coordinates. -/
def modelPiDiffeomorph :
    ModelPi (fun _ : ι ↦ 𝕜) ≃ₘ^n⟮ModelWithCorners.pi fun _ : ι ↦ 𝓘(𝕜), 𝓘(𝕜, EuclideanSpace 𝕜 ι)⟯
      EuclideanSpace 𝕜 ι where
  toFun x := (EuclideanSpace.equiv ι 𝕜).symm (ModelWithCorners.pi (fun _ : ι ↦ 𝓘(𝕜)) x)
  invFun v := (ModelWithCorners.pi fun _ : ι ↦ 𝓘(𝕜)).symm (EuclideanSpace.equiv ι 𝕜 v)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun :=
    (EuclideanSpace.equiv ι 𝕜).symm.contDiff.contMDiff.comp (ModelWithCorners.contMDiff _)
  contMDiff_invFun := by
    have h := (ModelWithCorners.pi fun _ : ι ↦ 𝓘(𝕜)).contMDiffOn_symm (n := n)
    rw [ModelWithCorners.range_eq_univ, contMDiffOn_univ] at h
    exact h.comp (EuclideanSpace.equiv ι 𝕜).contDiff.contMDiff

@[simp]
theorem modelPiDiffeomorph_apply (x : ModelPi fun _ : ι ↦ 𝕜) (i : ι) :
    modelPiDiffeomorph 𝕜 ι n x i = x i :=
  (rfl)

@[simp]
theorem modelPiDiffeomorph_symm_apply (v : EuclideanSpace 𝕜 ι) (i : ι) :
    (modelPiDiffeomorph 𝕜 ι n).symm v i = v i :=
  (rfl)

end EuclideanSpace

end
