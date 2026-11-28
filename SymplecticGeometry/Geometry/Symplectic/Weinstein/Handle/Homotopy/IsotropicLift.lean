/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Model
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import SymplecticGeometry.Geometry.Symplectic.Complex.ImInner
import SymplecticGeometry.Geometry.Symplectic.Liouville.VectorField
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Liouville lift of a vector field on the core of the handle

On the model `ℂᵏ × ℂᵐ` of `Handle/Model.lean`, with points `(x + i y, w)` and the constant
symplectic form `Im ⟪·, ·⟫_ℂ ⊕ Im ⟪·, ·⟫_ℂ`, a vector field `Y` on `ℝᵏ` lifts to the field
`SymplecticGeometry.isotropicLiftField m Y`,
`(x + i y, w) ↦ (Y x + i (y - DY(x)ᵀ y), w / 2)`,
where the transpose is the adjoint for the Euclidean inner product of `ℝᵏ`. The core
`range (modelDisc k m)` is the copy `{(x, 0)}` of `ℝᵏ`, and the lift extends `Y` from the core to
a Liouville field of the model. This file proves the first properties of the lift, its zeros near
the core and its derivative on the core; the gradient-like property comes later.

## Main results

* `SymplecticGeometry.isotropicLiftField_apply`: the formula above, in the real coordinates
  `TauCeti.complexEuclideanEquivRealProd` of the first factor.
* `SymplecticGeometry.contMDiff_isotropicLiftField`: for `Y` of class `C^{n+1}` the lift is a
  `C^n` section of the tangent bundle.
* `SymplecticGeometry.fderiv_isotropicLiftField_apply`: for `Y` of class `C²`, the derivative of
  the lift at `(x + i y, w)` sends `(ξ + i η, ζ)` to
  `(DY(x) ξ + i (η - (D²Y(x) ξ)ᵀ y - DY(x)ᵀ η), ζ / 2)`. The adjoint of a differentiable family
  of operators is differentiated by Tau Ceti's `HasFDerivAt.clm_adjoint`.
* `SymplecticGeometry.isLiouvilleVectorField_isotropicLiftField`: for `Y` of class `C²` the lift
  is a Liouville field of the constant form. The field is not linear, so the criterion used is
  the pointwise one, `TauCeti.SymplecticForm.isLiouvilleVectorField_constSmooth_of_fderiv`: the
  derivative `A` of the field at every point satisfies `ω (A u) v + ω u (A v) = ω u v`
  (`SymplecticGeometry.prod_imInnerSymplecticForm_fderiv_isotropicLiftField_add`). In the
  coordinates `ω = ⟪x₁, y₂⟫ - ⟪y₁, x₂⟫` on the first factor
  (`TauCeti.imInnerSymplecticForm_apply_eq_inner_complexEuclideanEquivRealProd`), the terms in `DY`
  cancel in pairs, and the two terms in `D²Y` cancel by the symmetry of the second derivative
  (`ContDiffAt.isSymmSndFDerivAt`). The second factor carries `w / 2`, of trace `m`.
* `SymplecticGeometry.isotropicLiftField_apply_of_mem_range_modelDisc`: on the core the lift is
  tangent to the core and equals `Y` there, `Ŷ (ι₀ x) = ι₀ (Y x)`, so its zeros on the core are
  those of `Y` (`SymplecticGeometry.isotropicLiftField_modelDisc_eq_zero_iff`).
* `SymplecticGeometry.isotropicLiftField_neg_id_eq_modelHandleField`: for `Y = -id` the lift is
  the standard handle field `SymplecticGeometry.modelHandleField k m`.
* `SymplecticGeometry.exists_isOpen_image_modelDisc_subset_forall_isotropicLiftField_eq_zero`:
  for `Y` of class `C¹` and a set `K ⊆ ℝᵏ` such that `I - DY(x)ᵀ` is injective at each zero `x`
  of `Y` in `K`, the zeros of the lift on an open neighbourhood of `ι₀ '' K` all lie on the core,
  hence are the points `ι₀ x` with `Y x = 0`: the neighbourhood is the set of `(x + i y, w)` with
  `Y x ≠ 0` or `I - DY(x)ᵀ` invertible, an open condition, and a zero there has `y = 0`.
  Compactness of `K` is not needed. The book's hypothesis, a form `P` with `P(y, y - DY(x)ᵀ y)`
  positive definite, implies the injectivity.
* `SymplecticGeometry.fderiv_isotropicLiftField_modelDisc`: for `Y` of class `C²` at `x`, the
  derivative of the lift at `ι₀ x` is `DY(x) ⊕ (I - DY(x)ᵀ) ⊕ ½ I` in the real coordinates
  `(x, y, w)`, since the term in `D²Y` vanishes at `y = 0`; pointwise, this is
  `SymplecticGeometry.fderiv_isotropicLiftField_modelDisc_apply`.

In the book the lift is `p ∂_p + z ∂_z / 2 + X_H` on `T^*ℝᵏ × ℂᵐ`, with `H = ⟨p, Y(q)⟩`. Tau
Ceti's `TauCeti.cotangentLiouvilleField` and Hamiltonian fields live on cotangent models whose
points are pairs of a vector and a covector, not on `ℂᵏ`; carrying them to the model here would
cost more than the direct computation above, which needs only the derivative of the field.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Lemma 12.8 and the coordinate formula for the lift in its proof. Under the dictionary
  `q = x`, `p = y`, `z = w` of `Handle/Model.lean`, the book's `p ∂_p + X_H` is
  `Y(x) ∂_x + (y - DY(x)ᵀ y) ∂_y`. The book takes `dp ∧ dq` on `T^*ℝᵏ`, the opposite of the
  form here, which does not change the Liouville condition.
-/

public section

open Complex Set
open scoped Manifold ContDiff InnerProductSpace

namespace SymplecticGeometry

open TauCeti

variable {k : ℕ} (m : ℕ)

/-- The **Liouville lift** of a vector field `Y` on `ℝᵏ` to the model `ℂᵏ × ℂᵐ`:
`(x + i y, w) ↦ (Y x + i (y - DY(x)ᵀ y), w / 2)`, with the transpose taken for the Euclidean
inner product of `ℝᵏ`. -/
noncomputable def isotropicLiftField (Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) :=
  ((complexEuclideanEquivRealProd (Fin k)).symm
      (Y (complexEuclideanEquivRealProd (Fin k) p.1).1,
        (complexEuclideanEquivRealProd (Fin k) p.1).2 -
          (fderiv ℝ Y (complexEuclideanEquivRealProd (Fin k) p.1).1).adjoint
            (complexEuclideanEquivRealProd (Fin k) p.1).2),
    (2⁻¹ : ℝ) • p.2)

variable {m}

/-- The Liouville lift `(x + i y, w) ↦ (Y x + i (y - DY(x)ᵀ y), w / 2)`, with `x` and `y` the
real and imaginary parts `TauCeti.complexEuclideanEquivRealProd` of the first factor. -/
theorem isotropicLiftField_apply (Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    isotropicLiftField m Y p =
      ((complexEuclideanEquivRealProd (Fin k)).symm
          (Y (complexEuclideanEquivRealProd (Fin k) p.1).1,
            (complexEuclideanEquivRealProd (Fin k) p.1).2 -
              (fderiv ℝ Y (complexEuclideanEquivRealProd (Fin k) p.1).1).adjoint
                (complexEuclideanEquivRealProd (Fin k) p.1).2),
        (2⁻¹ : ℝ) • p.2) :=
  (rfl)

/-- In real coordinates, the first component of the Liouville lift is
`(x, y) ↦ (Y x, y - DY(x)ᵀ y)`. -/
@[simp]
theorem complexEuclideanEquivRealProd_isotropicLiftField_fst
    (Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    complexEuclideanEquivRealProd (Fin k) (isotropicLiftField m Y p).1 =
      (Y (complexEuclideanEquivRealProd (Fin k) p.1).1,
        (complexEuclideanEquivRealProd (Fin k) p.1).2 -
          (fderiv ℝ Y (complexEuclideanEquivRealProd (Fin k) p.1).1).adjoint
            (complexEuclideanEquivRealProd (Fin k) p.1).2) := by
  rw [isotropicLiftField_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- The second component of the Liouville lift is `w ↦ w / 2`. -/
@[simp]
theorem isotropicLiftField_apply_snd (Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (isotropicLiftField m Y p).2 = (2⁻¹ : ℝ) • p.2 :=
  (rfl)

/-- **The Liouville lift is smooth** as a section of the tangent bundle: if `Y` is `C^{n+1}`,
its lift is `C^n`, one order less, since the lift involves `DY`. -/
theorem contMDiff_isotropicLiftField {Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {n : WithTop ℕ∞} (hY : ContDiff ℝ (n + 1) Y) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
      𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)).tangent n
      (fun p ↦ (⟨p, isotropicLiftField m Y p⟩ :
        TangentBundle 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
          (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)))) := by
  refine contMDiff_tangentBundle_mk_modelSpace contMDiff_id (ContDiff.contMDiff ?_)
  set e := complexEuclideanEquivRealProd (Fin k)
  have hx : ContDiff ℝ n fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦ (e p.1).1 :=
    (contDiff_fst.comp (e.contDiff.comp contDiff_fst))
  have hy : ContDiff ℝ n fun p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) ↦ (e p.1).2 :=
    (contDiff_snd.comp (e.contDiff.comp contDiff_fst))
  have hDY : ContDiff ℝ n (fderiv ℝ Y) := hY.fderiv_right le_rfl
  refine ContDiff.prodMk (e.symm.contDiff.comp (ContDiff.prodMk
    ((hY.of_le le_self_add).comp hx) (hy.sub ((hDY.comp hx).clm_adjoint.clm_apply hy))))
    (contDiff_snd.const_smul _)

/-- **The derivative of the Liouville lift.** At `p = (x + i y, w)`, for `Y` of class `C²` at
`x`, the derivative of the lift sends `u = (ξ + i η, ζ)` to
`(DY(x) ξ + i (η - (D²Y(x) ξ)ᵀ y - DY(x)ᵀ η), ζ / 2)`. -/
theorem fderiv_isotropicLiftField_apply
    {Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
    (hY : ContDiffAt ℝ 2 Y (complexEuclideanEquivRealProd (Fin k) p.1).1)
    (u : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    fderiv ℝ (isotropicLiftField m Y) p u =
      ((complexEuclideanEquivRealProd (Fin k)).symm
          (fderiv ℝ Y (complexEuclideanEquivRealProd (Fin k) p.1).1
              (complexEuclideanEquivRealProd (Fin k) u.1).1,
            (complexEuclideanEquivRealProd (Fin k) u.1).2 -
              (fderiv ℝ (fderiv ℝ Y) (complexEuclideanEquivRealProd (Fin k) p.1).1
                  (complexEuclideanEquivRealProd (Fin k) u.1).1).adjoint
                (complexEuclideanEquivRealProd (Fin k) p.1).2 -
              (fderiv ℝ Y (complexEuclideanEquivRealProd (Fin k) p.1).1).adjoint
                (complexEuclideanEquivRealProd (Fin k) u.1).2),
        (2⁻¹ : ℝ) • u.2) := by
  set e := complexEuclideanEquivRealProd (Fin k)
  set Lx : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (ContinuousLinearMap.fst ℝ _ _) ∘L e.toContinuousLinearMap ∘L
      (ContinuousLinearMap.fst ℝ _ _)
  set Ly : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (ContinuousLinearMap.snd ℝ _ _) ∘L e.toContinuousLinearMap ∘L
      (ContinuousLinearMap.fst ℝ _ _)
  have hY₁ : HasFDerivAt Y (fderiv ℝ Y (Lx p)) (Lx p) :=
    (hY.differentiableAt (by norm_num)).hasFDerivAt
  have hB : HasFDerivAt (fderiv ℝ Y) (fderiv ℝ (fderiv ℝ Y) (Lx p)) (Lx p) :=
    ((hY.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h : HasFDerivAt (fun p ↦ (e.symm (Y (Lx p), Ly p - (fderiv ℝ Y (Lx p)).adjoint (Ly p)),
      (2⁻¹ : ℝ) • p.2)) _ p := (e.symm.hasFDerivAt.comp p ((hY₁.comp p Lx.hasFDerivAt).prodMk
    (Ly.hasFDerivAt.sub ((hB.comp p Lx.hasFDerivAt).clm_adjoint.clm_apply Ly.hasFDerivAt)))).prodMk
    (hasFDerivAt_snd.const_smul (2⁻¹ : ℝ))
  rw [show isotropicLiftField m Y = fun p ↦ (e.symm (Y (Lx p), Ly p - (fderiv ℝ Y (Lx p)).adjoint
    (Ly p)), (2⁻¹ : ℝ) • p.2) from funext fun p ↦ isotropicLiftField_apply Y p, h.fderiv]
  simp [Lx, Ly, sub_sub, add_comm]

/-- The derivative of the Liouville lift scales the constant product form at rate one:
`ω (A u) v + ω u (A v) = ω u v` for `A` the derivative at `p = (x + i y, w)`, when `Y` is `C²`
at `x`. -/
theorem prod_imInnerSymplecticForm_fderiv_isotropicLiftField_add
    {Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
    (hY : ContDiffAt ℝ 2 Y (complexEuclideanEquivRealProd (Fin k) p.1).1)
    (u v : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    (imInnerSymplecticForm _).prod (imInnerSymplecticForm _)
          (fderiv ℝ (isotropicLiftField m Y) p u) v +
        (imInnerSymplecticForm _).prod (imInnerSymplecticForm _) u
          (fderiv ℝ (isotropicLiftField m Y) p v) =
      (imInnerSymplecticForm _).prod (imInnerSymplecticForm _) u v := by
  set e := complexEuclideanEquivRealProd (Fin k)
  -- The second derivative of `Y` is symmetric.
  have hS (a b : EuclideanSpace ℝ (Fin k)) :
      fderiv ℝ (fderiv ℝ Y) (e p.1).1 a b = fderiv ℝ (fderiv ℝ Y) (e p.1).1 b a :=
    hY.isSymmSndFDerivAt (by simp) a b
  have hw : imInnerSymplecticForm (EuclideanSpace ℂ (Fin m)) ((2⁻¹ : ℝ) • u.2) v.2 +
      imInnerSymplecticForm (EuclideanSpace ℂ (Fin m)) u.2 ((2⁻¹ : ℝ) • v.2) =
        imInnerSymplecticForm (EuclideanSpace ℂ (Fin m)) u.2 v.2 := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  simp only [SymplecticForm.prod_apply, fderiv_isotropicLiftField_apply p hY,
    imInnerSymplecticForm_apply_eq_inner_complexEuclideanEquivRealProd (ι := Fin k),
    ContinuousLinearEquiv.apply_symm_apply, inner_sub_left, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  rw [hS]
  linear_combination hw + real_inner_comm (fderiv ℝ (fderiv ℝ Y) (e p.1).1 (e v.1).1 (e u.1).1)
    (e p.1).2

/-- **The Liouville lift is a Liouville field.** For `Y` of class `C²`, the lift
`(x + i y, w) ↦ (Y x + i (y - DY(x)ᵀ y), w / 2)` is a Liouville vector field of the constant form
`Im ⟪·, ·⟫_ℂ ⊕ Im ⟪·, ·⟫_ℂ` on `ℂᵏ × ℂᵐ`. -/
theorem isLiouvilleVectorField_isotropicLiftField
    {Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)} (hY : ContDiff ℝ 2 Y) :
    IsLiouvilleVectorField
      ((imInnerSymplecticForm (EuclideanSpace ℂ (Fin k))).prod
        (imInnerSymplecticForm (EuclideanSpace ℂ (Fin m)))).constSmooth.val
      (fun p ↦ isotropicLiftField m Y p :
        (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) →
          TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) p) :=
  SymplecticForm.isLiouvilleVectorField_constSmooth_of_fderiv _
    fun p ↦ prod_imInnerSymplecticForm_fderiv_isotropicLiftField_add p hY.contDiffAt

/-! ### The lift on the core -/

/-- On the core, the Liouville lift is `Y`: `Ŷ (ι₀ x) = ι₀ (Y x)`. -/
@[simp]
theorem isotropicLiftField_modelDisc (Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (x : EuclideanSpace ℝ (Fin k)) :
    isotropicLiftField m Y (modelDisc k m x) = modelDisc k m (Y x) := by
  refine Prod.ext ((complexEuclideanEquivRealProd (Fin k)).injective ?_) (by simp)
  rw [complexEuclideanEquivRealProd_isotropicLiftField_fst,
    complexEuclideanEquivRealProd_modelDisc_fst]
  ext j <;> simp

/-- **The Liouville lift is tangent to the core and equals `Y` there**: at a point `p = ι₀ x` of
the core, `Ŷ p = ι₀ (Y x)`, with `x = π₀ p`. -/
theorem isotropicLiftField_apply_of_mem_range_modelDisc
    (Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    {p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)} (hp : p ∈ range (modelDisc k m)) :
    isotropicLiftField m Y p = modelDisc k m (Y (modelDiscProj k m p)) := by
  obtain ⟨x, rfl⟩ := hp
  rw [isotropicLiftField_modelDisc, leftInverse_modelDiscProj x]

/-- The zeros of the Liouville lift on the core are those of `Y`. -/
theorem isotropicLiftField_modelDisc_eq_zero_iff
    {Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)} {x : EuclideanSpace ℝ (Fin k)} :
    isotropicLiftField m Y (modelDisc k m x) = 0 ↔ Y x = 0 := by
  rw [isotropicLiftField_modelDisc, ← map_zero (modelDisc k m), modelDisc_injective.eq_iff]

/-- **The standard handle field is a Liouville lift**: for `Y = -id`, the lift
`(x + i y, w) ↦ (-x + 2 i y, w / 2)` is `SymplecticGeometry.modelHandleField k m`. -/
theorem isotropicLiftField_neg_id_eq_modelHandleField :
    isotropicLiftField m (fun x ↦ -x) = ⇑(modelHandleField k m) := by
  have hD (x : EuclideanSpace ℝ (Fin k)) :
      fderiv ℝ (fun x : EuclideanSpace ℝ (Fin k) ↦ -x) x = -ContinuousLinearMap.id ℝ _ := by
    exact (hasFDerivAt_id x).neg.fderiv
  funext p
  refine Prod.ext ?_ (by simp)
  ext j
  rw [isotropicLiftField_apply, hD, modelHandleField_apply_fst_apply]
  simp [ContinuousLinearMap.adjoint_id]
  ring

/-! ### Zeros and derivative near the core -/

/-- **The zeros of the Liouville lift near the core.** Let `Y` be `C¹` on `ℝᵏ`, and `K ⊆ ℝᵏ` a set
such that `I - DY(x)ᵀ` is injective at every zero `x` of `Y` in `K`. Then some open set `U`
containing `ι₀ '' K` has no zero of the lift off the core: each zero of the lift in `U` is `ι₀ x`
for a zero `x` of `Y`. -/
theorem exists_isOpen_image_modelDisc_subset_forall_isotropicLiftField_eq_zero
    {Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)} (hY : ContDiff ℝ 1 Y)
    {K : Set (EuclideanSpace ℝ (Fin k))}
    (hK : ∀ x ∈ K, Y x = 0 →
      Function.Injective (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) -
        (fderiv ℝ Y x).adjoint)) :
    ∃ U, IsOpen U ∧ modelDisc k m '' K ⊆ U ∧
      ∀ p ∈ U, isotropicLiftField m Y p = 0 → ∃ x, Y x = 0 ∧ p = modelDisc k m x := by
  set e := complexEuclideanEquivRealProd (Fin k)
  -- Off the zeros of `Y`, and where `I - DY(x)ᵀ` is invertible.
  set V := {x | Y x ≠ 0} ∪
    {x | IsUnit (ContinuousLinearMap.id ℝ _ - (fderiv ℝ Y x).adjoint)}
  have hV : IsOpen V := (isOpen_ne_fun hY.continuous continuous_const).union
    (Units.isOpen.preimage (continuous_const.sub
      (ContinuousLinearMap.adjoint.continuous.comp (hY.continuous_fderiv one_ne_zero))))
  refine ⟨modelDiscProj k m ⁻¹' V, hV.preimage (modelDiscProj k m).continuous, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_preimage, leftInverse_modelDiscProj x]
    by_cases h : Y x = 0
    · exact Or.inr (ContinuousLinearMap.isUnit_iff_bijective.mpr
        ⟨hK x hx h, LinearMap.injective_iff_surjective.mp (hK x hx h)⟩)
    · exact Or.inl h
  · intro p hp h0
    have h1 := complexEuclideanEquivRealProd_isotropicLiftField_fst Y p
    rw [h0, Prod.fst_zero, map_zero, eq_comm, Prod.mk_eq_zero] at h1
    have h2 : p.2 = 0 := by
      have := isotropicLiftField_apply_snd Y p
      rwa [h0, Prod.snd_zero, eq_comm, smul_eq_zero, or_iff_right (by norm_num)] at this
    rw [mem_preimage, modelDiscProj_apply_eq_complexEuclideanEquivRealProd] at hp
    have hu := hp.resolve_left (not_not.mpr h1.1)
    have hy : (e p.1).2 = 0 := ContinuousLinearMap.isUnit_iff_bijective.mp hu |>.1 <| by
      simpa using h1.2
    refine ⟨(e p.1).1, h1.1, Prod.ext (e.injective ?_) (by simp [h2])⟩
    rw [complexEuclideanEquivRealProd_modelDisc_fst, ← hy]

/-- **The derivative of the Liouville lift on the core.** At `ι₀ x`, for `Y` of class `C²` at
`x`, the derivative of the lift sends `(ξ + i η, ζ)` to `(DY(x) ξ + i (η - DY(x)ᵀ η), ζ / 2)`. -/
theorem fderiv_isotropicLiftField_modelDisc_apply
    {Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)} {x : EuclideanSpace ℝ (Fin k)}
    (hY : ContDiffAt ℝ 2 Y x) (u : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) :
    fderiv ℝ (isotropicLiftField m Y) (modelDisc k m x) u =
      ((complexEuclideanEquivRealProd (Fin k)).symm
          (fderiv ℝ Y x (complexEuclideanEquivRealProd (Fin k) u.1).1,
            (complexEuclideanEquivRealProd (Fin k) u.1).2 -
              (fderiv ℝ Y x).adjoint (complexEuclideanEquivRealProd (Fin k) u.1).2),
        (2⁻¹ : ℝ) • u.2) := by
  rw [fderiv_isotropicLiftField_apply _ (by rwa [complexEuclideanEquivRealProd_modelDisc_fst]),
    complexEuclideanEquivRealProd_modelDisc_fst]
  simp

/-- **The derivative of the Liouville lift on the core is block diagonal**: at `ι₀ x`, for `Y` of
class `C²` at `x`, in the real coordinates `(x, y, w)` of `ℂᵏ × ℂᵐ` it is
`DY(x) ⊕ (I - DY(x)ᵀ) ⊕ ½ I`. -/
theorem fderiv_isotropicLiftField_modelDisc
    {Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)} {x : EuclideanSpace ℝ (Fin k)}
    (hY : ContDiffAt ℝ 2 Y x) :
    fderiv ℝ (isotropicLiftField m Y) (modelDisc k m x) =
      ((complexEuclideanEquivRealProd (Fin k)).prodCongr
          (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℂ (Fin m)))).symm.toContinuousLinearMap ∘L
        (((fderiv ℝ Y x).prodMap (ContinuousLinearMap.id ℝ _ - (fderiv ℝ Y x).adjoint)).prodMap
          ((2⁻¹ : ℝ) • ContinuousLinearMap.id ℝ _)) ∘L
        ((complexEuclideanEquivRealProd (Fin k)).prodCongr
          (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℂ (Fin m)))).toContinuousLinearMap := by
  refine ContinuousLinearMap.ext fun u ↦ ?_
  rw [fderiv_isotropicLiftField_modelDisc_apply hY]
  simp [Prod.map]

end SymplecticGeometry

end
