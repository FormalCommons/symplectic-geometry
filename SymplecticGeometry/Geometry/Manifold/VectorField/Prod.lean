/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.ModelChart
public import TauCeti.Geometry.Manifold.VectorField.Prod

/-!
# Values of product vector fields

The tangent space of a product `M × N` in the model `I.prod J` is `E × E'`, so the value of
Tau Ceti's product field `TauCeti.Manifold.prodVectorField X Y` at `p` is the pair
`(X p.1, Y p.2)` of `E × E'`, for any models `I` and `J`.

In particular, let `v` be a vector of a real normed space `E` and `N` a manifold over a model
`J`. The product field `(v, 0)` on `E × N`, built from the constant field
`TauCeti.constVectorField v` of `E` and the zero field of `N`, takes the value `(v, 0)` of
`E × E'` at every point. For `E = ℝ` and `v = 1` this is the field `∂_s` on `ℝ × N`; written as
`(1, 0)` its image under a differential is the derivative of a slice `s ↦ f (s, y)`
(`MDifferentiableAt.mfderiv_uncurry_apply_mk_zero`).

The field `(v, 0)` is smooth, as the product of two smooth fields. For `E = ℝ` and `v = 1` this
gives the smoothness of the time field `∂_t = (1, 0)` on `ℝ × M`, so it is a smooth section
`SymplecticGeometry.timeField` of the tangent bundle of `ℝ × M`, whose underlying field is the
product field `(1, 0)` above (`SymplecticGeometry.coe_timeField_eq_prodVectorField`).

## Main results

* `TauCeti.Manifold.prodVectorField_apply`: the value of a product field `(X, Y)` at `p` is the
  pair `(X p.1, Y p.2)` of the model space.
* `TauCeti.Manifold.prodVectorField_constVectorField_zero_apply`: the value of `(v, 0)`.
* `TauCeti.Manifold.contMDiff_prodVectorField_constVectorField_zero`: the field `(v, 0)` is `C^n`
  for every `n`; `TauCeti.Manifold.contMDiff_prodVectorField_const_zero` states it with the
  constant field written as `fun x ↦ v`.
* `SymplecticGeometry.contMDiff_timeField`: the time field `∂_t = (1, 0)` on `ℝ × M` is smooth.
* `SymplecticGeometry.timeField`: the time field, as a smooth section of the tangent bundle.
* `SymplecticGeometry.coe_timeField_eq_prodVectorField`: the time field is the product of the
  constant field `1` of `ℝ` and the zero field of `M`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 8
  (vector fields).
-/

public section

open Manifold
open scoped Manifold

namespace TauCeti.Manifold

section Apply

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The value of the product field `(X, Y)` at `p` is the pair `(X p.1, Y p.2)` of the model
space `E × E'`. -/
theorem prodVectorField_apply (X : Π x : M, TangentSpace I x) (Y : Π y : N, TangentSpace J y)
    (p : M × N) : prodVectorField X Y p = ((X p.1, Y p.2) : E × E') :=
  Prod.ext (prodVectorField_fst _ _ _) (prodVectorField_snd _ _ _)

end Apply

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The product of the constant field `v` of `E` and the zero field of `N` takes the value
`(v, 0)` at every point of `E × N`. -/
theorem prodVectorField_constVectorField_zero_apply (v : E) (p : E × N) :
    prodVectorField (constVectorField v) (0 : Π y : N, TangentSpace J y) p = (v, (0 : E')) := by
  rw [prodVectorField_apply, constVectorField_apply, NormedSpace.fromTangentSpace_symm_apply,
    Pi.zero_apply]
  -- The zero of `TangentSpace J p.2` is that of `E'` under another name of the instance.
  rfl

/-- The product field `(v, 0)` on `E × N`, of the constant field `TauCeti.constVectorField v` of
`E` and the zero field of `N`, is a `C^n` section of the tangent bundle, for every `n`. -/
theorem contMDiff_prodVectorField_constVectorField_zero [IsManifold J 1 N] (v : E)
    {n : WithTop ℕ∞} :
    ContMDiff (𝓘(ℝ, E).prod J) (𝓘(ℝ, E).prod J).tangent n
      (T% (prodVectorField (constVectorField v) (0 : Π y : N, TangentSpace J y))) :=
  contMDiff_prodVectorField (contMDiff_constVectorField v)
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace J))

/-- The product field `(v, 0)` on `E × N`, of the constant field `v` of `E` and the zero field
of `N`, is a `C^n` section of the tangent bundle, for every `n`. This is
`contMDiff_prodVectorField_constVectorField_zero` with the constant field written as
`fun x ↦ v`. -/
theorem contMDiff_prodVectorField_const_zero [IsManifold J 1 N] (v : E) {n : WithTop ℕ∞} :
    ContMDiff (𝓘(ℝ, E).prod J) (𝓘(ℝ, E).prod J).tangent n
      (T% (prodVectorField (I := 𝓘(ℝ, E)) (fun x : E ↦ (v : TangentSpace 𝓘(ℝ, E) x))
        (0 : Π y : N, TangentSpace J y))) :=
  constVectorField_eq v ▸ contMDiff_prodVectorField_constVectorField_zero v

end TauCeti.Manifold

namespace SymplecticGeometry

open Bundle
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The time field `∂_t = (1, 0)` on `ℝ × M` is a smooth section of the tangent bundle. -/
theorem contMDiff_timeField :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent ∞
      (fun p : ℝ × M ↦ (⟨p, ((1 : ℝ), (0 : E))⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) := by
  simpa only [TauCeti.Manifold.prodVectorField_constVectorField_zero_apply] using
    TauCeti.Manifold.contMDiff_prodVectorField_constVectorField_zero (N := M) (1 : ℝ)

/-- The time field `∂_t = (1, 0)` on `ℝ × M`, as a smooth section of the tangent bundle. -/
noncomputable def timeField :
    Cₛ^∞⟮𝓘(ℝ, ℝ).prod I; ℝ × E, TangentSpace (𝓘(ℝ, ℝ).prod I) (M := ℝ × M)⟯ :=
  ⟨fun _ ↦ ((1 : ℝ), (0 : E)), contMDiff_timeField⟩

/-- The time field is `(1, 0)` at every point. -/
@[simp]
theorem coe_timeField :
    ⇑(timeField : Cₛ^∞⟮𝓘(ℝ, ℝ).prod I; ℝ × E, TangentSpace (𝓘(ℝ, ℝ).prod I) (M := ℝ × M)⟯) =
      fun _ ↦ ((1 : ℝ), (0 : E)) :=
  (rfl)

/-- The time field on `ℝ × M` is the product field of the constant field `1` of `ℝ` and the zero
field of `M`. -/
theorem coe_timeField_eq_prodVectorField :
    ⇑(timeField : Cₛ^∞⟮𝓘(ℝ, ℝ).prod I; ℝ × E, TangentSpace (𝓘(ℝ, ℝ).prod I) (M := ℝ × M)⟯) =
      TauCeti.Manifold.prodVectorField (TauCeti.constVectorField (1 : ℝ))
        (0 : Π y : M, TangentSpace I y) := by
  funext p
  rw [TauCeti.Manifold.prodVectorField_constVectorField_zero_apply, coe_timeField]

end SymplecticGeometry

end
