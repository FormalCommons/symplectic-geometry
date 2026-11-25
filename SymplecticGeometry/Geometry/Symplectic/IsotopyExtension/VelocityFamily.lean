/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.IsotopyExtension.Velocity
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Geometry.Manifold.VectorField.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Velocity forms of a family of isotopies with a parameter

Let `Ĝ : [0, 1]² × P → M` be smooth, and for each `t ∈ [0, 1]` let `k_t` be a smooth isotopy of
`P` into `M` with `k_t (s, x) = Ĝ ((t, s), x)`. At time `s`, the slice of the velocity form of
`k_t` (`TauCeti.SmoothIsotopy.velocityForm`) is the one-form
`v ↦ σ (∂ₛ Ĝ ((t, s), x), d (Ĝ ((t, s), ·))_x v)` on `P`. This file shows that these slices
depend smoothly on both parameters `(t, s)` (`SymplecticGeometry.IsSmoothFamily`): they are the
slices of the one-form `ι_{∂ₛ} Ĝ^* σ` on `[0, 1]² × P`, the contraction of `Ĝ^* σ` with the unit
field `∂ₛ = ((0, 1), 0)` of the second time coordinate. The computation is that of
`TauCeti.SmoothIsotopy.velocityForm_apply`, with one more time coordinate.

## Main results

* `SymplecticGeometry.isSmoothFamily_velocityForm`: the slices of the velocity forms of a jointly
  smooth family of isotopies form a smooth family over both parameters.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.3.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace SymplecticGeometry

open TauCeti

section Field

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [IsManifold J ∞ P]

/-- The field `∂ₛ = ((0, 1), 0)` on `[0, 1]² × P`, the unit field of the second time
coordinate, as a smooth section of the tangent bundle. -/
private def unitIntervalSqSndField :
    Cₛ^∞⟮((𝓡∂ 1).prod (𝓡∂ 1)).prod J;
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × E',
      TangentSpace (((𝓡∂ 1).prod (𝓡∂ 1)).prod J) (M := (unitInterval × unitInterval) × P)⟯ :=
  ⟨Manifold.prodVectorField
    (Manifold.prodVectorField (0 : Π t : unitInterval, TangentSpace (𝓡∂ 1) t)
      fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
    (0 : Π y : P, TangentSpace J y),
    Manifold.contMDiff_prodVectorField
      (Manifold.contMDiff_prodVectorField (Bundle.contMDiff_zeroSection ℝ _)
        contMDiff_one_tangentSpace_Icc)
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace J))⟩

/-- The field `∂ₛ` is the product field of `(0, 1)` on `[0, 1]²` and `0` on `P`. -/
private theorem coe_unitIntervalSqSndField :
    ⇑(unitIntervalSqSndField (J := J) (P := P)) = Manifold.prodVectorField
      (Manifold.prodVectorField (0 : Π t : unitInterval, TangentSpace (𝓡∂ 1) t)
        fun s : unitInterval ↦ (1 : TangentSpace (𝓡∂ 1) s))
      (0 : Π y : P, TangentSpace J y) :=
  (rfl)

/-- The value of `∂ₛ` at `((t, s), x)` is `((0, 1), 0)`. -/
private theorem unitIntervalSqSndField_apply (p : (unitInterval × unitInterval) × P) :
    unitIntervalSqSndField (J := J) p =
      (((0 : EuclideanSpace ℝ (Fin 1)), (1 : TangentSpace (𝓡∂ 1) p.1.2)), (0 : E')) := by
  rw [coe_unitIntervalSqSndField, Manifold.prodVectorField_apply, Manifold.prodVectorField_apply,
    Pi.zero_apply, Pi.zero_apply]
  -- The two sides differ only in the types `TangentSpace` and its model space for the zeros.
  rfl

end Field

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [IsManifold J ∞ P]

/-- **The velocity forms of a family of isotopies form a smooth family.** Let `Ĝ` be a smooth map
`[0, 1]² × P → M`, and `k_t`, for each `t`, a smooth isotopy with `k_t (s, x) = Ĝ ((t, s), x)`.
Then the slices `α_{t, s}` of the velocity forms of the `k_t` form a smooth family over
`[0, 1]²`: they are the slices of `ι_{∂ₛ} Ĝ^* σ`. -/
theorem isSmoothFamily_velocityForm (σ : SmoothTwoForm I M)
    {Ĝ : (unitInterval × unitInterval) × P → M}
    (hĜ : ContMDiff (((𝓡∂ 1).prod (𝓡∂ 1)).prod J) I ∞ Ĝ) {f₀ f₁ : unitInterval → C^∞⟮J, P; I, M⟯}
    (k : ∀ t, SmoothIsotopy (f₀ t) (f₁ t)) (hk : ∀ t p, k t p = Ĝ ((t, p.1), p.2)) :
    IsSmoothFamily ((𝓡∂ 1).prod (𝓡∂ 1)) fun q : unitInterval × unitInterval ↦
      SmoothForm.mpullback (Prod.mk q.2) (contMDiff_const.prodMk contMDiff_id)
        ((k q.1).velocityForm σ) := by
  refine isSmoothFamily_def.2 ⟨SmoothForm.interiorProduct unitIntervalSqSndField
    (SmoothForm.mpullback Ĝ hĜ σ),
    fun ⟨t, s⟩ ↦ Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun w ↦ ?_⟩
  have hw : w = ![w 0] := by
    ext i
    fin_cases i
    rfl
  have hkt : (k t : unitInterval × P → M) = fun p ↦ Ĝ ((t, p.1), p.2) := funext (hk t)
  have hĜd := hĜ.mdifferentiableAt (x := ((t, s), x)) (by simp)
  rw [hw, SmoothIsotopy.mpullback_prodMk_velocityForm σ (k t) s x (w 0), hkt]
  rw [SmoothForm.coe_mpullback, mpullback_apply, SmoothForm.coe_interiorProduct,
    RoughForm.interior_apply, SmoothForm.coe_mpullback, mpullback_apply,
    unitIntervalSqSndField_apply]
  congr 1
  funext i
  fin_cases i
  · exact (MDifferentiableAt.mfderiv_uncurry_apply_mk_zero (f := fun q y ↦ Ĝ (q, y)) hĜd _).trans
      (MDifferentiableAt.mfderiv_uncurry_apply_zero_mk (f := fun t' s' ↦ Ĝ ((t', s'), x))
        (MDifferentiableAt.curry_left (f := fun q y ↦ Ĝ (q, y)) hĜd) _)
  · exact (congrArg (mfderiv _ I Ĝ ((t, s), x)) (mfderiv_prodMk_right_apply (w 0))).trans
      (MDifferentiableAt.mfderiv_uncurry_apply_zero_mk (f := fun q y ↦ Ĝ (q, y)) hĜd _)

end SymplecticGeometry

end
