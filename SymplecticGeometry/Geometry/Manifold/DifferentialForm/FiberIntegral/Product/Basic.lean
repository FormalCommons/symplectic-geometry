/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import SymplecticGeometry.Analysis.Normed.Module.Alternating.AppendLeft
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Basic

/-!
# The integrand of the fibre integral on a product

Let `B` and `F` be manifolds and `α` a form of degree `r + m` on `B × F`. For `b : B` and tangent
vectors `v₁, …, vᵣ` at `b`, the form `SymplecticGeometry.prodFiberIntegrand α b v` of degree `m`
on `F` takes at `y` the value
`w ↦ α (b, y) ((v₁, 0), …, (vᵣ, 0), (0, w₁), …, (0, wₘ))`.
Integrating it over a closed oriented `F` gives the fibre integral of `α` at `b` on `v`. The base
vectors come first, as in Bott–Tu: with this order, integration over the fibre commutes with `d`
and satisfies the projection formula with no sign.

Pointwise, the integrand fixes the first `r` arguments of `α (b, y)` by
`ContinuousAlternatingMap.appendLeft`. That is alternating in the fixed arguments
(`ContinuousAlternatingMap.appendLeftAlternatingMap`), so the integrand is alternating in `v`
(`SymplecticGeometry.prodFiberIntegrandAlternatingMap`).

Smoothness is checked in charts. In the product chart at `(b, y₀)`, the coordinate expression of
the integrand is that of `α` along the slice through the chart point of `b`, followed by a fixed
continuous linear map (`TauCeti.RoughForm.inChartAt_prod_apply_append`). The proof follows that
of `TauCeti.IsSmoothForm.contDiffOn_inChartAt_mpullback_prodMk`, which treats the slices
themselves, the case `r = 0`.

## Main definitions

* `SymplecticGeometry.prodFiberIntegrand α b v`: the integrand on `F`.
* `SymplecticGeometry.prodFiberIntegrandAlternatingMap α b`: the same, as an alternating map
  of `v`.

## Main results

* `SymplecticGeometry.prodFiberIntegrand_apply`: its value on tangent vectors of `F`.
* `SymplecticGeometry.prodFiberIntegrand_add`, `SymplecticGeometry.prodFiberIntegrand_smul`,
  `SymplecticGeometry.prodFiberIntegrand_zero`, `SymplecticGeometry.prodFiberIntegrand_neg`,
  `SymplecticGeometry.prodFiberIntegrand_sub`: it is linear in `α`;
  `SymplecticGeometry.prodFiberIntegrand_update_add`,
  `SymplecticGeometry.prodFiberIntegrand_update_smul` and
  `SymplecticGeometry.prodFiberIntegrand_eq_zero_of_eq`: it is multilinear and alternating in `v`.
* `SymplecticGeometry.isSmoothForm_prodFiberIntegrand`: it is smooth when `α` is.
* `SymplecticGeometry.prodFiberIntegrand_degree_zero`: for `r = 0` it is the slice of `α` over
  `b`, its pull-back along `y ↦ (b, y)`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E H E' H' B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace F] [ChartedSpace H' F] {r m : ℕ}

/-- **The integrand of the fibre integral on a product.** For a form `α` of degree `r + m` on
`B × F`, a point `b : B` and tangent vectors `v₁, …, vᵣ` at `b`, the form of degree `m` on `F`
whose value at `y` is `w ↦ α (b, y) ((v₁, 0), …, (vᵣ, 0), (0, w₁), …, (0, wₘ))`, tangent vectors
of `B × F` being read through `Manifold.tangentSpaceProdEquiv`. -/
def prodFiberIntegrand (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) : RoughForm J F ℝ m := fun y ↦
  ((α (b, y)).appendLeft fun i ↦ (Manifold.tangentSpaceProdEquiv (b, y)).symm (v i, 0)
    ).compContinuousLinearMap
      ((Manifold.tangentSpaceProdEquiv (I := I) (J := J) (b, y)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr ℝ (TangentSpace I b) (TangentSpace J y)))

/-- The integrand at `y` fixes the first `r` arguments of `α (b, y)` to the lifts `(vᵢ, 0)` of
the base vectors, and reads the other `m` as the tangent vectors `(0, w)` of `B × F`. -/
theorem prodFiberIntegrand_def (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (y : F) :
    prodFiberIntegrand α b v y =
      ((α (b, y)).appendLeft fun i ↦ (Manifold.tangentSpaceProdEquiv (b, y)).symm (v i, 0)
        ).compContinuousLinearMap
          ((Manifold.tangentSpaceProdEquiv (I := I) (J := J) (b, y)).symm.toContinuousLinearMap.comp
            (ContinuousLinearMap.inr ℝ (TangentSpace I b) (TangentSpace J y))) := (rfl)

/-- The value of the integrand at `y` on `w` is that of `α` at `(b, y)` on
`(v₁, 0), …, (vᵣ, 0), (0, w₁), …, (0, wₘ)`. -/
@[simp]
theorem prodFiberIntegrand_apply (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (y : F) (w : Fin m → TangentSpace J y) :
    prodFiberIntegrand α b v y w = α (b, y) (fun p ↦ (Manifold.tangentSpaceProdEquiv (b, y)).symm
      (Fin.append (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) p)) := by
  rw [prodFiberIntegrand_def, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.appendLeft_apply]
  congr 1
  funext p
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) p <;>
    simp only [Fin.append_left, Fin.append_right, comp_apply,
      ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.inr_apply]

/-- The integrand is additive in the form. -/
@[simp]
theorem prodFiberIntegrand_add (α β : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    prodFiberIntegrand (α + β) b v = prodFiberIntegrand α b v + prodFiberIntegrand β b v := by
  funext y
  ext w
  simp

/-- The integrand is homogeneous in the form. -/
@[simp]
theorem prodFiberIntegrand_smul (c : ℝ) (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    prodFiberIntegrand (c • α) b v = c • prodFiberIntegrand α b v := by
  funext y
  ext w
  simp

/-- The integrand of the zero form is zero. -/
@[simp]
theorem prodFiberIntegrand_zero (b : B) (v : Fin r → TangentSpace I b) :
    prodFiberIntegrand (0 : RoughForm (I.prod J) (B × F) ℝ (r + m)) b v = 0 := by
  funext y
  ext w
  simp

/-- The integrand of `-α` is minus that of `α`. -/
@[simp]
theorem prodFiberIntegrand_neg (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    prodFiberIntegrand (-α) b v = -prodFiberIntegrand α b v := by
  funext y
  ext w
  simp

/-- The integrand is subtractive in the form. -/
@[simp]
theorem prodFiberIntegrand_sub (α β : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) :
    prodFiberIntegrand (α - β) b v = prodFiberIntegrand α b v - prodFiberIntegrand β b v := by
  funext y
  ext w
  simp

/-- `v ↦ prodFiberIntegrand α b v`, an alternating map of the base vectors. At each `y` it is
`ContinuousAlternatingMap.appendLeftAlternatingMap` of `α (b, y)` composed with the lift
`v ↦ (v, 0)` of tangent vectors of `B` to `B × F`. -/
def prodFiberIntegrandAlternatingMap (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B) :
    TangentSpace I b [⋀^Fin r]→ₗ[ℝ] RoughForm J F ℝ m :=
  AlternatingMap.pi fun y ↦
    (ContinuousAlternatingMap.compContinuousLinearMapₗ
      ((Manifold.tangentSpaceProdEquiv (I := I) (J := J) (b, y)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr ℝ (TangentSpace I b) (TangentSpace J y)))).compAlternatingMap
      ((α (b, y)).appendLeftAlternatingMap.compLinearMap
        ((Manifold.tangentSpaceProdEquiv (I := I) (J := J) (b, y)).symm.toLinearMap ∘ₗ
          LinearMap.inl ℝ (TangentSpace I b) (TangentSpace J y)))

/-- `prodFiberIntegrandAlternatingMap α b` sends `v` to `prodFiberIntegrand α b v`. -/
@[simp]
theorem prodFiberIntegrandAlternatingMap_apply (α : RoughForm (I.prod J) (B × F) ℝ (r + m))
    (b : B) (v : Fin r → TangentSpace I b) :
    prodFiberIntegrandAlternatingMap α b v = prodFiberIntegrand α b v := by
  funext y
  simp only [prodFiberIntegrandAlternatingMap, prodFiberIntegrand_def, AlternatingMap.pi_apply,
    LinearMap.compAlternatingMap_apply, AlternatingMap.compLinearMap_apply,
    ContinuousAlternatingMap.compContinuousLinearMapₗ_apply,
    ContinuousAlternatingMap.appendLeftAlternatingMap_apply,
    ContinuousLinearEquiv.toLinearEquiv_symm, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_symm_toLinearEquiv, LinearMap.coe_inl, comp_apply]

/-- The integrand is additive in each base vector `v i`. -/
theorem prodFiberIntegrand_update_add (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (i : Fin r) (x x' : TangentSpace I b) :
    prodFiberIntegrand α b (update v i (x + x')) =
      prodFiberIntegrand α b (update v i x) + prodFiberIntegrand α b (update v i x') := by
  simp only [← prodFiberIntegrandAlternatingMap_apply, AlternatingMap.map_update_add]

/-- The integrand is homogeneous in each base vector `v i`. -/
theorem prodFiberIntegrand_update_smul (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (i : Fin r) (c : ℝ) (x : TangentSpace I b) :
    prodFiberIntegrand α b (update v i (c • x)) = c • prodFiberIntegrand α b (update v i x) := by
  simp only [← prodFiberIntegrandAlternatingMap_apply, AlternatingMap.map_update_smul]

/-- The integrand vanishes when two base vectors are equal. -/
theorem prodFiberIntegrand_eq_zero_of_eq (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    {v : Fin r → TangentSpace I b} {i j : Fin r} (hv : v i = v j) (hij : i ≠ j) :
    prodFiberIntegrand α b v = 0 := by
  rw [← prodFiberIntegrandAlternatingMap_apply, AlternatingMap.map_eq_zero_of_eq _ v hv hij]

/-- **The integrand is smooth.** For a `C^n` form `α` on `B × F`, each integrand
`prodFiberIntegrand α b v` is a `C^n` form on `F`. -/
theorem isSmoothForm_prodFiberIntegrand [IsManifold I 1 B] [IsManifold J 1 F]
    {n : WithTop ℕ∞} {α : RoughForm (I.prod J) (B × F) ℝ (r + m)}
    (hα : IsSmoothForm (I.prod J) n α) (b : B) (v : Fin r → TangentSpace I b) :
    IsSmoothForm J n (prodFiberIntegrand α b v) := by
  refine IsSmoothForm.of_contDiffWithinAt_inChartAt_self fun y₀ ↦ ?_
  -- In the product chart at `(b, y₀)`, the integrand is read off the coordinate expression of `α`
  -- on the slice through the chart point of `b` by a fixed continuous linear map.
  let L : (E × E') [⋀^Fin (r + m)]→L[ℝ] ℝ →L[ℝ] E' [⋀^Fin m]→L[ℝ] ℝ :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (ContinuousLinearMap.inr ℝ E E')).comp
      (ContinuousAlternatingMap.appendLeftCLM ℝ ℝ m fun i ↦ ((v i : E), (0 : E')))
  have hb : extChartAt I b b ∈ (extChartAt I b).target := mem_extChartAt_target b
  have hslice : ContDiffWithinAt ℝ n (fun z ↦ α.inChartAt (b, y₀) (extChartAt I b b, z))
      (range J) (extChartAt J y₀ y₀) := by
    refine (hα.contDiffWithinAt_inChartAt_self (b, y₀)).comp_of_eq (extChartAt J y₀ y₀)
      (contDiffWithinAt_const.prodMk contDiffWithinAt_id) (fun z hz ↦ ?_) (by simp)
    rw [ModelWithCorners.range_prod]
    exact ⟨extChartAt_target_subset_range b hb, hz⟩
  have heq : ∀ z ∈ (extChartAt J y₀).target,
      (prodFiberIntegrand α b v).inChartAt y₀ z =
        (L ∘ fun z ↦ α.inChartAt (b, y₀) (extChartAt I b b, z)) z := by
    intro z hz
    ext w
    simp only [comp_apply, L, ContinuousLinearMap.comp_apply,
      ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
      ContinuousAlternatingMap.appendLeftCLM_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.appendLeft_apply]
    rw [RoughForm.inChartAt_apply, prodFiberIntegrand_apply]
    refine Eq.trans ?_ (RoughForm.inChartAt_prod_apply_append α rfl b y₀ hb hz
      (fun i ↦ (v i : E)) w).symm
    refine α.apply_congr (by rw [(extChartAt I b).left_inv (mem_extChartAt_source b)])
      fun p ↦ ?_
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) p <;>
      simp only [Fin.cast_eq_self, Fin.append_left, Fin.append_right,
        mfderivWithin_range_extChartAt_symm] <;>
      exact (Manifold.tangentSpaceProdEquiv_symm_apply (I := I) (J := J) _ _).trans
        (Manifold.tangentSpaceProdEquiv_symm_apply (I := I) (J := J) _ _).symm
  exact (L.contDiff.comp_contDiffWithinAt hslice).congr_of_eventuallyEq
    (Filter.eventually_of_mem (extChartAt_target_mem_nhdsWithin y₀) heq)
    (heq _ (mem_extChartAt_target y₀))

/-- **The integrand in degree zero.** For `r = 0`, the integrand at `b` is the slice of `α` over
`b`, its pull-back along `y ↦ (b, y)`, after the degree cast `0 + m = m`. -/
theorem prodFiberIntegrand_degree_zero (α : RoughForm (I.prod J) (B × F) ℝ (0 + m)) (b : B)
    (v : Fin 0 → TangentSpace I b) :
    prodFiberIntegrand α b v = mpullback J (I.prod J) (Prod.mk b)
      (LinearEquiv.cast (R := ℝ) (M := fun k ↦ RoughForm (I.prod J) (B × F) ℝ k) (zero_add m)
        α) := by
  funext y
  ext w
  rw [prodFiberIntegrand_apply, mpullback_apply, RoughForm.cast_apply]
  congr 1
  funext p
  obtain ⟨j, rfl⟩ : ∃ j, p = Fin.natAdd 0 j := ⟨Fin.cast (zero_add m) p, Fin.ext (by simp)⟩
  rw [Fin.append_right, mfderiv_prod_right, comp_apply,
    show Fin.cast (zero_add m) (Fin.natAdd 0 j) = j from Fin.ext (by simp)]
  exact Manifold.tangentSpaceProdEquiv_symm_apply (I := I) (J := J) _ _

end SymplecticGeometry
