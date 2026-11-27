/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The coordinate one-forms of a basis

A basis `bs` of a finite-dimensional real normed space `E` gives, for each index `i`, the
constant one-form `dxᵢ = Module.Basis.coordOneForm bs i` on `E`, whose value on a tangent vector
is its `i`-th coordinate `bs.coord i`. It is Tau Ceti's `TauCeti.SmoothForm.const` of that
coordinate.

## Main definitions

* `Module.Basis.coordOneForm bs i`: the constant one-form `dxᵢ` on `E`.

## Main results

* `Module.Basis.coordOneForm_apply`: `dxᵢ` evaluates the `i`-th coordinate.
* `Module.Basis.mpullback_fst_coordOneForm_apply`: on a product `E × F`, the pull-back of `dxᵢ`
  along `Prod.fst` evaluates the `i`-th coordinate of the component along `E`.
-/

public section

noncomputable section

open scoped Manifold

namespace Module.Basis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} (bs : Module.Basis ι ℝ E)

/-- The constant one-form `dxᵢ` on a finite-dimensional real normed space `E`, for a basis `bs`
of `E`: its value on a tangent vector `v` is the `i`-th coordinate `bs.coord i v`. -/
def coordOneForm (i : ι) : TauCeti.SmoothForm 𝓘(ℝ, E) E ℝ 1 :=
  TauCeti.SmoothForm.const
    (ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ 0
      (LinearMap.toContinuousLinearMap (bs.coord i)))

/-- The one-form `dxᵢ` takes a tangent vector to its `i`-th coordinate in the basis `bs`. -/
@[simp]
theorem coordOneForm_apply (i : ι) (x : E) (v : Fin 1 → TangentSpace 𝓘(ℝ, E) x) :
    (bs.coordOneForm i).val x v = bs.coord i (v 0) := by
  rw [coordOneForm, TauCeti.SmoothForm.const_apply,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, NormedSpace.fromTangentSpace_apply,
    LinearMap.coe_toContinuousLinearMap']

/-- On a product `E × F`, the pull-back along `Prod.fst` of the one-form `dxᵢ` on `E` takes a
tangent vector to the `i`-th coordinate of its component along `E`. -/
theorem mpullback_fst_coordOneForm_apply {EF HF F : Type*} [NormedAddCommGroup EF]
    [NormedSpace ℝ EF] [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F]
    [ChartedSpace HF F] (i : ι) (z : E × F) (v : Fin 1 → TangentSpace (𝓘(ℝ, E).prod IF) z) :
    TauCeti.mpullback (𝓘(ℝ, E).prod IF) 𝓘(ℝ, E) Prod.fst (bs.coordOneForm i).val z v =
      bs.coord i (v 0).1 := by
  rw [TauCeti.mpullback_apply, coordOneForm_apply, TauCeti.mfderiv_fst_apply]

end Module.Basis
