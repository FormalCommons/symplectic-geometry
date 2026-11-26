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
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

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

Smoothness is checked in charts. In the product chart at `(b₀, y₀)`, the coordinate expression
of the integrand at `b` is that of `α` at the chart point of `b`, with the first arguments set to
the coordinate vectors of `v` in the tangent trivialization at `b₀`
(`SymplecticGeometry.inChartAt_prodFiberIntegrand`, from
`TauCeti.RoughForm.inChartAt_prod_apply_append`). For fixed `b` and `v` this is a fixed continuous
linear map of the coordinates of `α`, and the proof of
`SymplecticGeometry.isSmoothForm_prodFiberIntegrand` follows that of
`TauCeti.IsSmoothForm.contDiffOn_inChartAt_mpullback_prodMk`, which treats the slices themselves,
the case `r = 0`. When `b = g p` and `v = X p` vary smoothly with a parameter `p`, the coordinate
vectors vary smoothly too, and evaluating the coordinates of `α` on them gives the joint
smoothness in `(p, y)` (`SymplecticGeometry.contMDiff_prodFiberIntegrand`). That proof follows the
one of `ContMDiffAt.mpullback_form_family`: the section is read in the coordinates of the bundle
of alternating maps (`contMDiffAt_continuousAlternatingMap_bundle`), and a family of alternating
maps is smooth when its evaluations are (`TauCeti.contMDiffAt_continuousAlternatingMap_apply`).

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
* `SymplecticGeometry.inChartAt_prodFiberIntegrand`: its coordinate expression in charts.
* `SymplecticGeometry.isSmoothForm_prodFiberIntegrand`: it is smooth when `α` is.
* `SymplecticGeometry.contMDiff_prodFiberIntegrand`: along a smooth map `g : P → B` and smooth
  tangent vectors `X` along `g`, the integrands `prodFiberIntegrand α (g p) (X · p)` are jointly
  smooth in `(p, y)`.
* `SymplecticGeometry.prodFiberIntegrand_degree_zero`: for `r = 0` it is the slice of `α` over
  `b`, its pull-back along `y ↦ (b, y)`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

noncomputable section

open Set Function Bundle
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

/-- **The integrand in chart coordinates.** Let `b` lie in the chart of `B` at `b₀`, and `z` in
the target of the chart of `F` at `y₀`. At `z`, the coordinate expression of
`prodFiberIntegrand α b v` in the chart at `y₀` is that of `α` in the product chart at
`(b₀, y₀)`, at `(extChartAt I b₀ b, z)`, with its first `r` arguments set to `(cᵢ, 0)` and its
other `m` arguments taken in the second factor, where `cᵢ` is the coordinate vector of `vᵢ` in the
tangent trivialization at `b₀`. -/
theorem inChartAt_prodFiberIntegrand [IsManifold I 1 B] [IsManifold J 1 F]
    (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) {b₀ b : B} (hb : b ∈ (extChartAt I b₀).source)
    (v : Fin r → TangentSpace I b) (y₀ : F) {z : E'} (hz : z ∈ (extChartAt J y₀).target) :
    (prodFiberIntegrand α b v).inChartAt y₀ z =
      ((α.inChartAt (b₀, y₀) (extChartAt I b₀ b, z)).appendLeft fun i ↦
        ((trivializationAt E (TangentSpace I) b₀ ⟨b, v i⟩).2, (0 : E'))).compContinuousLinearMap
          (ContinuousLinearMap.inr ℝ E E') := by
  have hb' : b ∈ (chartAt H b₀).source := by rwa [extChartAt_source] at hb
  have hbt : extChartAt I b₀ b ∈ (extChartAt I b₀).target := (extChartAt I b₀).map_source hb
  -- The inverse chart derivative undoes the tangent trivialization at `b₀`.
  have hv (u : TangentSpace I b) : (mfderivWithin 𝓘(ℝ, E) I (extChartAt I b₀).symm (range I)
      (extChartAt I b₀ b) (trivializationAt E (TangentSpace I) b₀ ⟨b, u⟩).2 : E) = u := by
    have h := congrArg (fun L : E →L[ℝ] E ↦ L (trivializationAt E (TangentSpace I) b₀ ⟨b, u⟩).2)
      (TangentBundle.symmL_trivializationAt (I := I) hb')
    exact h.symm.trans ((Trivialization.symmL_apply _ hb' _).trans
      (Trivialization.symm_apply_apply_mk (trivializationAt E (TangentSpace I) b₀) hb' u))
  ext w
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.appendLeft_apply, RoughForm.inChartAt_apply, prodFiberIntegrand_apply]
  refine Eq.trans ?_ (RoughForm.inChartAt_prod_apply_append α rfl b₀ y₀ hbt hz
    (fun i ↦ (trivializationAt E (TangentSpace I) b₀ ⟨b, v i⟩).2) w).symm
  refine α.apply_congr (by rw [(extChartAt I b₀).left_inv hb]) fun p ↦ ?_
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) p
  · simp only [Fin.cast_eq_self, Fin.append_left]
    refine (Manifold.tangentSpaceProdEquiv_symm_apply (I := I) (J := J) _ _).trans (Eq.trans ?_
      (Manifold.tangentSpaceProdEquiv_symm_apply (I := I) (J := J)
        ((extChartAt I b₀).symm (extChartAt I b₀ b), (extChartAt J y₀).symm z) _).symm)
    exact Prod.ext (hv (v i)).symm rfl
  · simp only [Fin.cast_eq_self, Fin.append_right]
    exact (Manifold.tangentSpaceProdEquiv_symm_apply (I := I) (J := J) _ _).trans
      (Manifold.tangentSpaceProdEquiv_symm_apply (I := I) (J := J) _ _).symm

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
  have hslice : ContDiffWithinAt ℝ n (fun z ↦ α.inChartAt (b, y₀) (extChartAt I b b, z))
      (range J) (extChartAt J y₀ y₀) := by
    refine (hα.contDiffWithinAt_inChartAt_self (b, y₀)).comp_of_eq (extChartAt J y₀ y₀)
      (contDiffWithinAt_const.prodMk contDiffWithinAt_id) (fun z hz ↦ ?_) (by simp)
    rw [ModelWithCorners.range_prod]
    exact ⟨extChartAt_target_subset_range b (mem_extChartAt_target b), hz⟩
  -- Read in the tangent trivialization at `b` itself, each `v i` is its own coordinate vector.
  have hv (i : Fin r) : (trivializationAt E (TangentSpace I) b ⟨b, v i⟩).2 = v i :=
    ((trivializationAt E (TangentSpace I) b).continuousLinearMapAt_apply_of_mem (R := ℝ)
      (FiberBundle.mem_baseSet_trivializationAt' b) (v i)).symm.trans
      (Manifold.continuousLinearMapAt_trivializationAt_self b (v i))
  have heq : ∀ z ∈ (extChartAt J y₀).target,
      (prodFiberIntegrand α b v).inChartAt y₀ z =
        (L ∘ fun z ↦ α.inChartAt (b, y₀) (extChartAt I b b, z)) z := by
    intro z hz
    simp only [inChartAt_prodFiberIntegrand α (mem_extChartAt_source b) v y₀ hz, hv, comp_apply,
      L, ContinuousLinearMap.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
      ContinuousAlternatingMap.appendLeftCLM_apply]
  exact (L.contDiff.comp_contDiffWithinAt hslice).congr_of_eventuallyEq
    (Filter.eventually_of_mem (extChartAt_target_mem_nhdsWithin y₀) heq)
    (heq _ (mem_extChartAt_target y₀))

/-- **The integrand is jointly smooth along smooth base vectors.** Let `g : P → B` be `C^n`, and
let `X₁, …, Xᵣ` be tangent vectors of `B` along `g`, `Xᵢ p` at `g p`, each `C^n` as a map into
the tangent bundle. For a `C^n` form `α` on `B × F`, the values of the integrands
`prodFiberIntegrand α (g p) (X · p)` at `y` form a `C^n` section, over `P × F`, of the bundle of
`m`-forms of `F` along the projection `(p, y) ↦ y`. This is the form of the hypothesis on the
family in `TauCeti.contMDiff_integralTopForm`. -/
theorem contMDiff_prodFiberIntegrand {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [TopologicalSpace HP] {K : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
    [FiniteDimensional ℝ E'] {n : WithTop ℕ∞}
    [IsManifold I 1 B] [IsManifold J 1 F] [IsManifold I n B] [IsManifold J n F]
    {α : RoughForm (I.prod J) (B × F) ℝ (r + m)} (hα : IsSmoothForm (I.prod J) n α)
    {g : P → B} (hg : ContMDiff K I n g) {X : Fin r → (p : P) → TangentSpace I (g p)}
    (hX : ∀ i, ContMDiff K I.tangent n fun p ↦ (⟨g p, X i p⟩ : TangentBundle I B)) :
    ContMDiff (K.prod J) (J.prod 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ)) n
      (fun q : P × F ↦ TotalSpace.mk' (E' [⋀^Fin m]→L[ℝ] ℝ)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin m]→L[ℝ] Trivial F ℝ y) q.2
        (prodFiberIntegrand α (g q.1) (fun i ↦ X i q.1) q.2)) := by
  intro q₀
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨contMDiffAt_snd, ?_⟩
  -- The coordinates of `α` in the product chart at `(g q₀.1, q₀.2)`, along the family, and those
  -- of the base vectors in the tangent trivialization at `g q₀.1`.
  let A : P × F → (E × E') [⋀^Fin (r + m)]→L[ℝ] ℝ := fun q ↦
    α.inChartAt (g q₀.1, q₀.2) (extChartAt I (g q₀.1) (g q.1), extChartAt J q₀.2 q.2)
  let c : Fin r → P × F → E := fun i q ↦
    (trivializationAt E (TangentSpace I) (g q₀.1) ⟨g q.1, X i q.1⟩).2
  have hA : ContMDiffAt (K.prod J) 𝓘(ℝ, (E × E') [⋀^Fin (r + m)]→L[ℝ] ℝ) n A q₀ := by
    refine ContDiffWithinAt.comp_contMDiffWithinAt (s := univ) (t := range (I.prod J))
      (hα.contDiffWithinAt_inChartAt_self (g q₀.1, q₀.2)) ?_ fun q _ ↦ ?_
    · exact ((contMDiffAt_extChartAt.comp q₀.1 (hg q₀.1)).comp q₀ contMDiffAt_fst).prodMk_space
        (contMDiffAt_extChartAt.comp q₀ contMDiffAt_snd)
    · rw [ModelWithCorners.range_prod]
      exact ⟨mem_range_self _, mem_range_self _⟩
  have hc (i : Fin r) : ContMDiffAt (K.prod J) 𝓘(ℝ, E) n (c i) q₀ :=
    (contMDiffAt_totalSpace_iff.1 (hX i q₀.1)).2.comp q₀ contMDiffAt_fst
  have hG : ContMDiffAt (K.prod J) 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ) n (fun q ↦
      ((A q).appendLeft fun i ↦ (c i q, (0 : E'))).compContinuousLinearMap
        (ContinuousLinearMap.inr ℝ E E')) q₀ := by
    refine contMDiffAt_continuousAlternatingMap_apply.2 fun w ↦ ?_
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.appendLeft_apply]
    refine hA.continuousAlternatingMap_apply fun p ↦ Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) p
    · simpa only [Fin.append_left] using (hc i).prodMk_space contMDiffAt_const
    · simpa only [Fin.append_right] using contMDiffAt_const
  have hmem : {q : P × F | g q.1 ∈ (extChartAt I (g q₀.1)).source ∧
      q.2 ∈ (extChartAt J q₀.2).source} ∈ nhds q₀ :=
    Filter.inter_mem
      ((hg.continuous.comp continuous_fst).continuousAt.preimage_mem_nhds
        (extChartAt_source_mem_nhds (g q₀.1)))
      (continuous_snd.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds q₀.2))
  refine hG.congr_of_eventuallyEq (Filter.eventually_of_mem hmem fun q hq ↦ ?_)
  exact (RoughForm.inCoordinates_eq_inChartAt _ hq.2).trans
    (inChartAt_prodFiberIntegrand α hq.1 _ q₀.2 ((extChartAt J q₀.2).map_source hq.2))

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
