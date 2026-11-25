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
# The product model of `ℝ^ι` and the Euclidean space

Mathlib models a finite product of manifolds modelled on `ℝ`, such as a torus
`ι → AddCircle p`, on `ModelPi fun _ : ι ↦ ℝ` with the product model
`ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)`, whose norm is the sup norm. This file identifies that model
space with the Euclidean space `EuclideanSpace ℝ ι`, by a smooth diffeomorphism of model spaces
(`EuclideanSpace.modelPiDiffeomorph`). With `SymplecticGeometry.Remodel`, it charts such products
on an inner product space, as constructions like Tau Ceti's `TauCeti.ConnectedSum` need.

## Main definitions

* `EuclideanSpace.modelPiDiffeomorph ι n`: the identity of the coordinates, as a `C^n`
  diffeomorphism from `ModelPi fun _ : ι ↦ ℝ`, with the product model, onto `EuclideanSpace ℝ ι`.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace EuclideanSpace

variable (ι : Type*) [Fintype ι] (n : ℕ∞ω)

/-- The model space `ModelPi fun _ : ι ↦ ℝ` of a finite product of manifolds over `ℝ`, with its
product model, is `C^n` diffeomorphic to the Euclidean space `EuclideanSpace ℝ ι`, with its own
model, by the map keeping the coordinates. -/
def modelPiDiffeomorph :
    ModelPi (fun _ : ι ↦ ℝ) ≃ₘ^n⟮ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ), 𝓘(ℝ, EuclideanSpace ℝ ι)⟯
      EuclideanSpace ℝ ι where
  toFun x := (EuclideanSpace.equiv ι ℝ).symm (ModelWithCorners.pi (fun _ : ι ↦ 𝓘(ℝ)) x)
  invFun v := (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).symm (EuclideanSpace.equiv ι ℝ v)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun :=
    (EuclideanSpace.equiv ι ℝ).symm.contDiff.contMDiff.comp (ModelWithCorners.contMDiff _)
  contMDiff_invFun := by
    have h := (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).contMDiffOn_symm (n := n)
    rw [ModelWithCorners.range_eq_univ, contMDiffOn_univ] at h
    exact h.comp (EuclideanSpace.equiv ι ℝ).contDiff.contMDiff

@[simp]
theorem modelPiDiffeomorph_apply (x : ModelPi fun _ : ι ↦ ℝ) (i : ι) :
    modelPiDiffeomorph ι n x i = x i :=
  (rfl)

@[simp]
theorem modelPiDiffeomorph_symm_apply (v : EuclideanSpace ℝ ι) (i : ι) :
    (modelPiDiffeomorph ι n).symm v i = v i :=
  (rfl)

end EuclideanSpace

end
