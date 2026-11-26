/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
import TauCeti.Data.Fin.Tuple.Basic

/-!
# The integrand of the fibre integral on a product

Let `B` and `F` be manifolds and `α` a form of degree `r + m` on `B × F`. For `b : B` and tangent
vectors `v₁, …, vᵣ` at `b`, the form `SymplecticGeometry.prodFiberIntegrand α b v` of degree `m`
on `F` takes at `y` the value
`w ↦ α (b, y) ((v₁, 0), …, (vᵣ, 0), (0, w₁), …, (0, wₘ))`.
Integrating it over a closed oriented `F` gives the fibre integral of `α` at `b` on `v`. The base
vectors come first, as in Bott–Tu: with this order, integration over the fibre commutes with `d`
and satisfies the projection formula with no sign.

The pointwise construction is `ContinuousAlternatingMap.appendLeft`, which fixes the first `r`
arguments of an alternating map of `r + m` arguments; it is continuous and linear in the map
(`ContinuousAlternatingMap.appendLeftCLM`).

Smoothness is checked in charts. In the product chart at `(b, y₀)`, the coordinate expression of
the integrand is that of `α` along the slice through the chart point of `b`, followed by a fixed
continuous linear map (`TauCeti.RoughForm.inChartAt_prod_apply_append`). The proof follows that
of `TauCeti.IsSmoothForm.contDiffOn_inChartAt_mpullback_prodMk`, which treats the slices
themselves, the case `r = 0`.

## Main definitions

* `ContinuousAlternatingMap.appendLeft f u`: the alternating map `w ↦ f (Fin.append u w)`.
* `ContinuousAlternatingMap.appendLeftCLM`: the same, as a continuous linear map in `f`.
* `SymplecticGeometry.prodFiberIntegrand α b v`: the integrand on `F`.

## Main results

* `SymplecticGeometry.prodFiberIntegrand_apply`: its value on tangent vectors of `F`.
* `SymplecticGeometry.prodFiberIntegrand_add`, `SymplecticGeometry.prodFiberIntegrand_smul`: it is
  linear in `α`; `SymplecticGeometry.prodFiberIntegrand_update_add`,
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

namespace ContinuousAlternatingMap

section Topological

variable {R W N : Type*} [CommSemiring R] [AddCommMonoid W] [Module R W] [TopologicalSpace W]
  [AddCommMonoid N] [Module R N] [TopologicalSpace N] {r m : ℕ}

/-- The alternating map of `m` arguments obtained from an alternating map `f` of `r + m`
arguments by fixing its first `r` arguments to `u`: `w ↦ f (Fin.append u w)`. -/
def appendLeft (f : W [⋀^Fin (r + m)]→L[R] N) (u : Fin r → W) : W [⋀^Fin m]→L[R] N where
  toFun w := f (Fin.append u w)
  map_update_add' := by
    intro _ w i x y
    obtain rfl := Subsingleton.elim ‹DecidableEq (Fin m)› (instDecidableEqFin _)
    simp only [← Fin.update_append_natAdd, f.map_update_add]
  map_update_smul' := by
    intro _ w i c x
    obtain rfl := Subsingleton.elim ‹DecidableEq (Fin m)› (instDecidableEqFin _)
    simp only [← Fin.update_append_natAdd, f.map_update_smul, RingHom.id_apply]
  cont := f.cont.comp <| continuous_pi fun p ↦ by
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) p
    · simpa only [Fin.append_left] using continuous_const
    · simpa only [Fin.append_right] using continuous_apply j
  map_eq_zero_of_eq' w i j hw hij := f.map_eq_zero_of_eq _
    (by simpa only [Fin.append_right] using hw) (Fin.natAdd_inj r |>.not.mpr hij)

/-- The value of `f.appendLeft u` on `w` is that of `f` on `Fin.append u w`. -/
@[simp]
theorem appendLeft_apply (f : W [⋀^Fin (r + m)]→L[R] N) (u : Fin r → W) (w : Fin m → W) :
    f.appendLeft u w = f (Fin.append u w) := (rfl)

/-- Fixing the first arguments is additive in the alternating map. -/
@[simp]
theorem appendLeft_add [ContinuousAdd N] (f g : W [⋀^Fin (r + m)]→L[R] N) (u : Fin r → W) :
    (f + g).appendLeft u = f.appendLeft u + g.appendLeft u := by
  ext w
  simp

/-- Fixing the first arguments commutes with scalar multiplication of the alternating map. -/
@[simp]
theorem appendLeft_smul {S : Type*} [Monoid S] [DistribMulAction S N] [ContinuousConstSMul S N]
    [SMulCommClass R S N] (c : S) (f : W [⋀^Fin (r + m)]→L[R] N) (u : Fin r → W) :
    (c • f).appendLeft u = c • f.appendLeft u := by
  ext w
  simp

/-- `f.appendLeft u` is additive in each fixed argument `u i`. -/
theorem appendLeft_update_add [ContinuousAdd N] [DecidableEq (Fin r)]
    (f : W [⋀^Fin (r + m)]→L[R] N)
    (u : Fin r → W) (i : Fin r) (x y : W) :
    f.appendLeft (update u i (x + y)) =
      f.appendLeft (update u i x) + f.appendLeft (update u i y) := by
  ext w
  obtain rfl := Subsingleton.elim ‹DecidableEq (Fin r)› (instDecidableEqFin _)
  simp only [appendLeft_apply, coe_add, Pi.add_apply, ← Fin.update_append_castAdd,
    f.map_update_add]

/-- `f.appendLeft u` is homogeneous in each fixed argument `u i`. -/
theorem appendLeft_update_smul [ContinuousConstSMul R N] [DecidableEq (Fin r)]
    (f : W [⋀^Fin (r + m)]→L[R] N)
    (u : Fin r → W) (i : Fin r) (c : R) (x : W) :
    f.appendLeft (update u i (c • x)) = c • f.appendLeft (update u i x) := by
  ext w
  obtain rfl := Subsingleton.elim ‹DecidableEq (Fin r)› (instDecidableEqFin _)
  simp only [appendLeft_apply, coe_smul, Pi.smul_apply, ← Fin.update_append_castAdd,
    f.map_update_smul]

/-- `f.appendLeft u` vanishes when two fixed arguments are equal. -/
theorem appendLeft_eq_zero_of_eq (f : W [⋀^Fin (r + m)]→L[R] N) {u : Fin r → W} {i j : Fin r}
    (hu : u i = u j) (hij : i ≠ j) : f.appendLeft u = 0 := by
  ext w
  exact f.map_eq_zero_of_eq _ (by simpa only [Fin.append_left] using hu)
    (Fin.castAdd_inj.not.mpr hij)

end Topological

section Normed

variable {𝕜 W N : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [NormedAddCommGroup N] [NormedSpace 𝕜 N] {r m : ℕ}

/-- The operator norm of `f.appendLeft u` is at most `‖f‖ * ∏ i, ‖u i‖`. -/
theorem norm_appendLeft_le (f : W [⋀^Fin (r + m)]→L[𝕜] N) (u : Fin r → W) :
    ‖f.appendLeft u‖ ≤ ‖f‖ * ∏ i, ‖u i‖ := by
  refine opNorm_le_bound _ (by positivity) fun w ↦ ?_
  calc ‖f.appendLeft u w‖ ≤ ‖f‖ * ∏ p, ‖Fin.append u w p‖ := f.le_opNorm _
    _ = ‖f‖ * (∏ i, ‖u i‖) * ∏ j, ‖w j‖ := by
      rw [Fin.prod_univ_add, mul_assoc]
      simp only [Fin.append_left, Fin.append_right]

variable (𝕜 N m) in
/-- `ContinuousAlternatingMap.appendLeft` with the fixed arguments `u`, as a continuous linear
map in the alternating map. -/
def appendLeftCLM (u : Fin r → W) : (W [⋀^Fin (r + m)]→L[𝕜] N) →L[𝕜] W [⋀^Fin m]→L[𝕜] N :=
  LinearMap.mkContinuous
    { toFun f := f.appendLeft u
      map_add' f g := appendLeft_add f g u
      map_smul' c f := appendLeft_smul c f u }
    (∏ i, ‖u i‖) fun f ↦ (norm_appendLeft_le f u).trans_eq (mul_comm _ _)

/-- `appendLeftCLM 𝕜 N m u` sends `f` to `f.appendLeft u`. -/
@[simp]
theorem appendLeftCLM_apply (u : Fin r → W) (f : W [⋀^Fin (r + m)]→L[𝕜] N) :
    appendLeftCLM 𝕜 N m u f = f.appendLeft u := (rfl)

end Normed

end ContinuousAlternatingMap

namespace TauCeti.RoughForm

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul ℝ V]

/-- A rough form cast along an equality of degrees `p = q` takes on `w` the value of the
original form on `w` reindexed along `Fin.cast h`. -/
theorem linearEquivCast_apply {p q : ℕ} (h : p = q) (α : RoughForm I M V p) (x : M)
    (w : Fin q → TangentSpace I x) :
    LinearEquiv.cast (R := ℝ) (M := fun k ↦ RoughForm I M V k) h α x w =
      α x (w ∘ Fin.cast h) := by
  subst h
  simp only [LinearEquiv.cast_apply, cast_eq, comp_def, Fin.cast_eq_self]

end TauCeti.RoughForm

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

/-- The value of the integrand at `y` on `w` is that of `α` at `(b, y)` on
`(v₁, 0), …, (vᵣ, 0), (0, w₁), …, (0, wₘ)`. -/
@[simp]
theorem prodFiberIntegrand_apply (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (y : F) (w : Fin m → TangentSpace J y) :
    prodFiberIntegrand α b v y w = α (b, y) (fun p ↦ (Manifold.tangentSpaceProdEquiv (b, y)).symm
      (Fin.append (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) p)) := by
  rw [prodFiberIntegrand, ContinuousAlternatingMap.compContinuousLinearMap_apply,
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

/-- The tuple of lifts `(vᵢ, 0)` of an updated tuple is the updated tuple of lifts. -/
private theorem update_lift (b : B) (y : F) (v : Fin r → TangentSpace I b) (i : Fin r)
    (x : TangentSpace I b) :
    (fun i' ↦ (Manifold.tangentSpaceProdEquiv (I := I) (J := J) (b, y)).symm
      (update v i x i', 0)) =
      update (fun i' ↦ (Manifold.tangentSpaceProdEquiv (b, y)).symm (v i', 0)) i
        ((Manifold.tangentSpaceProdEquiv (b, y)).symm (x, 0)) :=
  funext fun i' ↦ apply_update (fun _ t ↦ (Manifold.tangentSpaceProdEquiv (b, y)).symm (t, 0))
    v i x i'

/-- The integrand is additive in each base vector `v i`. -/
theorem prodFiberIntegrand_update_add (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (i : Fin r) (x x' : TangentSpace I b) :
    prodFiberIntegrand α b (update v i (x + x')) =
      prodFiberIntegrand α b (update v i x) + prodFiberIntegrand α b (update v i x') := by
  funext y
  have h : (Manifold.tangentSpaceProdEquiv (I := I) (J := J) (b, y)).symm (x + x', 0) =
      (Manifold.tangentSpaceProdEquiv (b, y)).symm (x, 0) +
        (Manifold.tangentSpaceProdEquiv (b, y)).symm (x', 0) := by
    rw [← map_add, Prod.mk_add_mk, add_zero]
  simp only [prodFiberIntegrand, update_lift, h, ContinuousAlternatingMap.appendLeft_update_add]
  ext w
  simp only [prodFiberIntegrand, update_lift,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Pi.add_apply,
    ContinuousAlternatingMap.add_apply]

/-- The integrand is homogeneous in each base vector `v i`. -/
theorem prodFiberIntegrand_update_smul (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    (v : Fin r → TangentSpace I b) (i : Fin r) (c : ℝ) (x : TangentSpace I b) :
    prodFiberIntegrand α b (update v i (c • x)) = c • prodFiberIntegrand α b (update v i x) := by
  funext y
  have h : (Manifold.tangentSpaceProdEquiv (I := I) (J := J) (b, y)).symm (c • x, 0) =
      c • (Manifold.tangentSpaceProdEquiv (b, y)).symm (x, 0) := by
    rw [← map_smul, Prod.smul_mk, smul_zero]
  simp only [prodFiberIntegrand, update_lift, h, ContinuousAlternatingMap.appendLeft_update_smul]
  ext w
  simp only [prodFiberIntegrand, update_lift,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply]

/-- The integrand vanishes when two base vectors are equal. -/
theorem prodFiberIntegrand_eq_zero_of_eq (α : RoughForm (I.prod J) (B × F) ℝ (r + m)) (b : B)
    {v : Fin r → TangentSpace I b} {i j : Fin r} (hv : v i = v j) (hij : i ≠ j) :
    prodFiberIntegrand α b v = 0 := by
  funext y
  ext w
  rw [prodFiberIntegrand, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.appendLeft_eq_zero_of_eq _
      (u := fun i ↦ (Manifold.tangentSpaceProdEquiv (I := I) (J := J) (b, y)).symm (v i, 0))
      (by simp only [hv]) hij]
  simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

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
  rw [prodFiberIntegrand_apply, mpullback_apply, RoughForm.linearEquivCast_apply]
  congr 1
  funext p
  obtain ⟨j, rfl⟩ : ∃ j, p = Fin.natAdd 0 j := ⟨Fin.cast (zero_add m) p, Fin.ext (by simp)⟩
  rw [Fin.append_right, mfderiv_prod_right, comp_apply,
    show Fin.cast (zero_add m) (Fin.natAdd 0 j) = j from Fin.ext (by simp)]
  exact Manifold.tangentSpaceProdEquiv_symm_apply (I := I) (J := J) _ _

end SymplecticGeometry
