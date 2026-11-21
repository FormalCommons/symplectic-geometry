/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.ODE.DysonSeries
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
public import TauCeti.Analysis.Calculus.ContinuousMap.Local

/-!
# Naturality and smooth parameter dependence of the Dyson series

This file adds two facts about Tau Ceti's Dyson series `TauCeti.dysonSeries p t`, the solution of
`Γ' = Γ p` with `Γ 0 = 1` in a real Banach algebra, and its left version
`TauCeti.dysonSeriesLeft p t`, the solution of `Γ' = p Γ`.

* **Naturality.** A continuous algebra homomorphism `f : B → C` between real Banach algebras
  commutes with the Dyson series: `f (dysonSeries p t) = dysonSeries (f ∘ p) t`, and the same
  holds for the iterated integrals and for the left series. For the algebra of operators this
  says that the propagator of `e A e⁻¹` is `e Γ e⁻¹`, for a linear isomorphism `e`.
* **Smooth parameter dependence.** If a family of paths `p x t` is `Cⁿ` jointly in a parameter
  `x` from an open subset of a normed space and the time `t`, then so is its Dyson series. This
  extends Tau Ceti's `TauCeti.continuous_parametric_dysonSeriesLeft` from continuity to `Cⁿ`.

The proof of the second fact rescales time: `dysonSeries p t` is the value at time `1` of the
Dyson series of the path `s ↦ t • p (t * s)` on `[0, 1]`. On the Banach space of continuous paths
`[0, 1] → B`, the Dyson series is the sum of the continuous homogeneous polynomials
`q ↦ ∫∫ q ⋯ q` of degree `k`, of norm at most `‖1‖ / k!`; it is a power series of infinite
radius, hence analytic. The rescaled path depends smoothly on the parameter and the time, by Tau
Ceti's smoothness of superposition operators (`ContinuousMap.contDiffAt_mkD_comp`).

## Main definitions

* `SymplecticGeometry.pathDysonMultilinear`: the `n`-linear map `(q₁, …, qₙ) ↦ ∫∫ q₁ ⋯ qₙ` on
  continuous paths on `[0, 1]`, whose diagonal is the `n`-th Dyson term.
* `SymplecticGeometry.pathDysonSeries`: these maps, as a formal power series on paths.

## Main results

* `SymplecticGeometry.map_dysonTerm`, `SymplecticGeometry.map_dysonSeries`,
  `SymplecticGeometry.map_dysonSeriesLeft`: naturality under continuous algebra homomorphisms.
* `SymplecticGeometry.dysonTerm_smul_comp_mul`: rescaling time in the iterated integrals.
* `SymplecticGeometry.radius_pathDysonSeries`,
  `SymplecticGeometry.analyticOnNhd_dysonSeries_projIcc`,
  `SymplecticGeometry.contDiff_dysonSeries_projIcc`: the Dyson series at time `1` is an entire
  function of the path on `[0, 1]`.
* `SymplecticGeometry.contDiffOn_parametric_dysonSeries`,
  `SymplecticGeometry.contDiffOn_parametric_dysonSeriesLeft`,
  `SymplecticGeometry.contDiff_parametric_dysonSeries`,
  `SymplecticGeometry.contDiff_parametric_dysonSeriesLeft`: `Cⁿ` dependence on a parameter and
  the time.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 2.6.3, the fibrewise linear Moser flow, for which these facts are needed. The analysis
  itself is the standard power series argument for linear differential equations.
-/

public section

noncomputable section

namespace SymplecticGeometry

open TauCeti Set MeasureTheory
open scoped Nat

section Naturality

variable {B C F : Type*} [NormedRing B] [NormedAlgebra ℝ B]
  [NormedRing C] [NormedAlgebra ℝ C] [CompleteSpace B] [CompleteSpace C]
  [FunLike F B C] [AlgHomClass F ℝ B C] {f : F} {p : ℝ → B}

/-- A continuous algebra homomorphism commutes with the iterated integrals of the Dyson
series. -/
theorem map_dysonTerm (hf : Continuous f) (hp : Continuous p) (n : ℕ) (t : ℝ) :
    f (dysonTerm p n t) = dysonTerm (f ∘ p) n t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have hi : IntervalIntegrable (fun s => dysonTerm p n s * p s) volume 0 t :=
      ((continuous_dysonTerm hp n).mul hp).intervalIntegrable 0 t
    have h := ((f : B →+ C).toRealLinearMap hf).intervalIntegral_comp_comm hi
    simp only [AddMonoidHom.coe_toRealLinearMap, AddMonoidHom.coe_ofClass] at h
    rw [dysonTerm_succ, dysonTerm_succ, ← h]
    congr 1
    ext s
    rw [map_mul, ih]
    rfl

/-- A continuous algebra homomorphism commutes with the Dyson series:
`f (dysonSeries p t) = dysonSeries (f ∘ p) t`. -/
theorem map_dysonSeries (hf : Continuous f) (hp : Continuous p) (t : ℝ) :
    f (dysonSeries p t) = dysonSeries (f ∘ p) t := by
  have h := (hasSum_dysonSeries hp t).map f hf
  simp only [Function.comp_def, map_dysonTerm hf hp] at h
  exact h.unique (hasSum_dysonSeries (hf.comp hp) t)

/-- A continuous algebra homomorphism commutes with the left Dyson series:
`f (dysonSeriesLeft p t) = dysonSeriesLeft (f ∘ p) t`. -/
theorem map_dysonSeriesLeft (hf : Continuous f) (hp : Continuous p) (t : ℝ) :
    f (dysonSeriesLeft p t) = dysonSeriesLeft (f ∘ p) t := by
  set g : Bᵐᵒᵖ →ₐ[ℝ] Cᵐᵒᵖ := AlgHom.op (AlgHom.ofClass f)
  have hg_apply (b : Bᵐᵒᵖ) : g b = MulOpposite.op (f b.unop) := by
    simp [g, AlgHom.op_apply_apply]
  have hg : Continuous g := by
    rw [show ⇑g = fun b => MulOpposite.op (f b.unop) from funext hg_apply]
    exact MulOpposite.continuous_op.comp (hf.comp MulOpposite.continuous_unop)
  apply MulOpposite.op_injective
  calc MulOpposite.op (f (dysonSeriesLeft p t))
      = g (MulOpposite.op (dysonSeriesLeft p t)) := by rw [hg_apply, MulOpposite.unop_op]
    _ = g (dysonSeries (fun s => MulOpposite.op (p s)) t) := by rw [op_dysonSeriesLeft]
    _ = dysonSeries (g ∘ fun s => MulOpposite.op (p s)) t :=
        map_dysonSeries hg (MulOpposite.continuous_op.comp hp) t
    _ = MulOpposite.op (dysonSeriesLeft (f ∘ p) t) := by
        rw [op_dysonSeriesLeft]
        simp only [Function.comp_def, hg_apply, MulOpposite.unop_op]

end Naturality
section Rescaling

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- Rescaling time in the iterated integrals: the Dyson terms of `s ↦ t • p (t * s)` are those of
`p` at the rescaled time. -/
theorem dysonTerm_smul_comp_mul (p : ℝ → B) (t : ℝ) (n : ℕ) (s : ℝ) :
    dysonTerm (fun u => t • p (t * u)) n s = dysonTerm p n (t * s) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    simp_rw [dysonTerm_succ, ih, mul_smul_comm]
    rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left
      (fun v => dysonTerm p n v * p v), mul_zero]

end Rescaling

section PathSpace

/-! ### The Dyson series on the space of continuous paths on `[0, 1]` -/

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- The bilinear map `(a, q) ↦ (s ↦ ∫₀ˢ a q)` on continuous paths on `[0, 1]`. -/
private def dysonStep :
    C(Icc (0 : ℝ) 1, B) →L[ℝ] C(Icc (0 : ℝ) 1, B) →L[ℝ] C(Icc (0 : ℝ) 1, B) :=
  ContinuousLinearMap.compL ℝ _ _ _ ContinuousMap.unitIntervalIntegral ∘L
    ContinuousLinearMap.mul ℝ _

/-- The continuous `n`-linear map `(q₁, …, qₙ) ↦ ∫∫ q₁ ⋯ qₙ` on continuous paths on `[0, 1]`,
defined by `1` for `n = 0` and by `(q₁, …, qₙ₊₁) ↦ (s ↦ ∫₀ˢ (∫∫ q₁ ⋯ qₙ) qₙ₊₁)`. Its value at
`(q, …, q)` is the `n`-th Dyson term of `q` (`pathDysonMultilinear_diag_apply`). -/
def pathDysonMultilinear :
    (n : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin n => C(Icc (0 : ℝ) 1, B))
      C(Icc (0 : ℝ) 1, B)
  | 0 => ContinuousMultilinearMap.constOfIsEmpty ℝ _ 1
  | n + 1 => ContinuousMultilinearMap.uncurryRight
      (Ei := fun _ : Fin (n + 1) => C(Icc (0 : ℝ) 1, B))
      (dysonStep.compContinuousMultilinearMap (pathDysonMultilinear n))

@[simp]
theorem pathDysonMultilinear_zero_apply (m : Fin 0 → C(Icc (0 : ℝ) 1, B)) :
    pathDysonMultilinear 0 m = 1 := (rfl)

theorem pathDysonMultilinear_succ_apply (n : ℕ) (m : Fin (n + 1) → C(Icc (0 : ℝ) 1, B)) :
    pathDysonMultilinear (n + 1) m = ContinuousMap.unitIntervalIntegral
      (pathDysonMultilinear n (Fin.init m) * m (Fin.last n)) := (rfl)

/-- The pointwise factorial bound on the multilinear Dyson terms:
`‖∫∫ q₁ ⋯ qₙ (s)‖ ≤ ‖1‖ / n! * ∏ ‖qᵢ‖ * s ^ n`. -/
theorem norm_pathDysonMultilinear_apply_le (n : ℕ) (m : Fin n → C(Icc (0 : ℝ) 1, B))
    (s : Icc (0 : ℝ) 1) :
    ‖pathDysonMultilinear n m s‖ ≤ ‖(1 : B)‖ / n ! * (∏ i, ‖m i‖) * (s : ℝ) ^ n := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    have hs := s.property.1
    rw [pathDysonMultilinear_succ_apply, ContinuousMap.unitIntervalIntegral_apply]
    set c := ‖(1 : B)‖ / n ! * (∏ i, ‖Fin.init m i‖) * ‖m (Fin.last n)‖
    calc _ ≤ ∫ u in (0 : ℝ)..s, c * u ^ n := by
          refine intervalIntegral.norm_integral_le_of_norm_le hs
            (Filter.Eventually.of_forall fun u hu => ?_)
            ((continuous_const.mul (continuous_pow n)).intervalIntegrable _ _)
          have hu' : u ∈ Icc (0 : ℝ) 1 := uIcc_subset_Icc (left_mem_Icc.2 zero_le_one)
            s.property (Ioc_subset_Icc_self.trans (by rw [uIcc_of_le hs]) hu)
          rw [projIcc_of_mem _ hu', ContinuousMap.mul_apply]
          refine (norm_mul_le _ _).trans ?_
          calc _ ≤ ‖(1 : B)‖ / n ! * (∏ i, ‖Fin.init m i‖) * u ^ n * ‖m (Fin.last n)‖ :=
                mul_le_mul (ih (Fin.init m) ⟨u, hu'⟩) (ContinuousMap.norm_coe_le_norm _ _)
                  (norm_nonneg _) (by have := hu'.1; positivity)
            _ = c * u ^ n := by ring
      _ = c * ((s : ℝ) ^ (n + 1) / (n + 1)) := by
          rw [intervalIntegral.integral_const_mul, integral_pow]; simp
      _ = _ := by
          rw [Fin.prod_univ_castSucc, Nat.factorial_succ]
          simp only [c, Fin.init]
          push_cast
          field_simp

/-- The multilinear Dyson terms have operator norm at most `‖1‖ / n!`. -/
theorem norm_pathDysonMultilinear_le (n : ℕ) :
    ‖pathDysonMultilinear (B := B) n‖ ≤ ‖(1 : B)‖ / n ! := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m =>
    (ContinuousMap.norm_le _ (by positivity)).2 fun s => ?_
  refine (norm_pathDysonMultilinear_apply_le n m s).trans ?_
  have h1 : (s : ℝ) ^ n ≤ 1 := pow_le_one₀ s.property.1 s.property.2
  have h0 : 0 ≤ ‖(1 : B)‖ / n ! * ∏ i, ‖m i‖ := by positivity
  simpa using mul_le_mul_of_nonneg_left h1 h0

/-- On the diagonal, the multilinear Dyson terms of a path `Q` on `[0, 1]` are the Dyson terms of
any path `q` on `ℝ` that agrees with `Q` on `[0, 1]`. -/
theorem pathDysonMultilinear_diag_apply {q : ℝ → B} {Q : C(Icc (0 : ℝ) 1, B)}
    (hQ : ∀ s, Q s = q s) (n : ℕ) (s : Icc (0 : ℝ) 1) :
    pathDysonMultilinear n (fun _ => Q) s = dysonTerm q n s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [pathDysonMultilinear_succ_apply, ContinuousMap.unitIntervalIntegral_apply, dysonTerm_succ]
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu' := uIcc_subset_Icc (left_mem_Icc.2 zero_le_one) s.property hu
    simp only [projIcc_of_mem _ hu', ContinuousMap.mul_apply]
    rw [← hQ ⟨u, hu'⟩, ← ih ⟨u, hu'⟩]
    rfl

/-- The Dyson series on continuous paths on `[0, 1]`, as a formal power series whose `n`-th term
is `pathDysonMultilinear n`. -/
def pathDysonSeries : FormalMultilinearSeries ℝ C(Icc (0 : ℝ) 1, B) C(Icc (0 : ℝ) 1, B) :=
  fun n => pathDysonMultilinear n

@[simp]
theorem pathDysonSeries_apply (n : ℕ) :
    pathDysonSeries (B := B) n = pathDysonMultilinear n := (rfl)

/-- The Dyson power series on paths has infinite radius of convergence. -/
@[simp]
theorem radius_pathDysonSeries : (pathDysonSeries (B := B)).radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_summable_norm _ fun r => ?_
  refine .of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((Real.summable_pow_div_factorial r).mul_left ‖(1 : B)‖)
  calc ‖pathDysonSeries (B := B) n‖ * (r : ℝ) ^ n ≤ ‖(1 : B)‖ / n ! * (r : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (norm_pathDysonMultilinear_le n) (by positivity)
    _ = ‖(1 : B)‖ * ((r : ℝ) ^ n / n !) := by ring

variable [CompleteSpace B]

/-- The Dyson power series on paths represents its sum on the whole space. -/
theorem hasFPowerSeriesOnBall_pathDysonSeries :
    HasFPowerSeriesOnBall (pathDysonSeries (B := B)).sum pathDysonSeries 0 ⊤ := by
  simpa using (pathDysonSeries (B := B)).hasFPowerSeriesOnBall (by simp)

/-- The Dyson terms at time `1` of a path `q` on `ℝ` sum to the value at `1` of the sum of the
Dyson power series at any continuous path `Q` on `[0, 1]` that agrees with `q` there. -/
theorem hasSum_dysonTerm_one {q : ℝ → B} {Q : C(Icc (0 : ℝ) 1, B)} (hQ : ∀ s, Q s = q s) :
    HasSum (fun n => dysonTerm q n 1)
      ((pathDysonSeries (B := B)).sum Q ⟨1, right_mem_Icc.2 zero_le_one⟩) := by
  have h := (hasFPowerSeriesOnBall_pathDysonSeries (B := B).hasSum
    (y := Q) (by simp)).mapL (ContinuousMap.evalCLM ℝ ⟨(1 : ℝ), right_mem_Icc.2 zero_le_one⟩)
  rw [zero_add] at h
  convert h using 2 with n
  · exact (pathDysonMultilinear_diag_apply hQ n ⟨1, right_mem_Icc.2 zero_le_one⟩).symm
  · rfl

/-- The Dyson series at time `1` of a continuous path `Q` on `[0, 1]`, extended to `ℝ` by
`projIcc`, is the value at `1` of the sum of the Dyson power series at `Q`. -/
theorem dysonSeries_projIcc_one (Q : C(Icc (0 : ℝ) 1, B)) :
    dysonSeries (fun u => Q (projIcc 0 1 zero_le_one u)) 1 =
      (pathDysonSeries (B := B)).sum Q ⟨1, right_mem_Icc.2 zero_le_one⟩ :=
  (hasSum_dysonSeries (Q.continuous.comp continuous_projIcc) 1).unique
    (hasSum_dysonTerm_one fun s => by simp)

/-- **The Dyson series is entire in its path.** The Dyson series at time `1` of a continuous
path `Q` on `[0, 1]` is an analytic function of `Q` on the whole Banach space `C([0, 1], B)`. -/
theorem analyticOnNhd_dysonSeries_projIcc :
    AnalyticOnNhd ℝ (fun Q : C(Icc (0 : ℝ) 1, B) =>
      dysonSeries (fun u => Q (projIcc 0 1 zero_le_one u)) 1) univ := by
  simp_rw [dysonSeries_projIcc_one]
  exact fun _ _ => (ContinuousMap.evalCLM ℝ _).analyticAt _ |>.comp
    (hasFPowerSeriesOnBall_pathDysonSeries.analyticAt_of_mem (by simp))

/-- The Dyson series at time `1` of a continuous path `Q` on `[0, 1]` is a `C^∞` function
of `Q`. -/
theorem contDiff_dysonSeries_projIcc {n : WithTop ℕ∞} :
    ContDiff ℝ n fun Q : C(Icc (0 : ℝ) 1, B) =>
      dysonSeries (fun u => Q (projIcc 0 1 zero_le_one u)) 1 :=
  analyticOnNhd_dysonSeries_projIcc.contDiff

end PathSpace

section Parametric

universe u v

variable {B : Type v} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The path `s ↦ ((x, t), s)` on `[0, 1]`. -/
private def timePath (y : E × ℝ) : C(Icc (0 : ℝ) 1, (E × ℝ) × ℝ) :=
  ⟨fun s => (y, s), by fun_prop⟩

private theorem contDiff_timePath {n : WithTop ℕ∞} : ContDiff ℝ n (timePath (E := E)) := by
  have hL : timePath (E := E) = fun y =>
      ((ContinuousLinearMap.inl ℝ (E × ℝ) ℝ).compLeftContinuous ℝ (Icc (0 : ℝ) 1)
        (ContinuousMap.const _ y)) + timePath 0 := by
    ext y s <;> simp [timePath]
  rw [hL]
  exact (((ContinuousLinearMap.inl ℝ (E × ℝ) ℝ).compLeftContinuous ℝ
    (Icc (0 : ℝ) 1)).comp (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) 1))).contDiff.add
    contDiff_const

/-- The rescaled path `s ↦ t • p x (t * s)` on `[0, 1]`, for `y = (x, t)`. It is built through
`ULift`, since Tau Ceti's smoothness of superposition operators asks the universe of the values
to contain that of the arguments. -/
private def rescaledPath (p : E → ℝ → B) (y : E × ℝ) : C(Icc (0 : ℝ) 1, B) :=
  (LinearIsometryEquiv.ulift ℝ B).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous
    ℝ (Icc (0 : ℝ) 1) (ContinuousMap.mkD (fun s => ULift.up.{u}
      ((timePath y s).1.2 • p (timePath y s).1.1 ((timePath y s).1.2 * (timePath y s).2))) 0)

omit [CompleteSpace B] [NormedSpace ℝ E] in
/-- Where `p y.1` is continuous, the rescaled path is `s ↦ y.2 • p y.1 (y.2 * s)`. -/
private theorem rescaledPath_apply {p : E → ℝ → B} {y : E × ℝ} (hp : Continuous (p y.1))
    (s : Icc (0 : ℝ) 1) : rescaledPath p y s = y.2 • p y.1 (y.2 * s) := by
  have hc : Continuous fun s : Icc (0 : ℝ) 1 => ULift.up.{u} ((timePath y s).1.2 •
      p (timePath y s).1.1 ((timePath y s).1.2 * (timePath y s).2)) := by
    simp only [timePath, ContinuousMap.coe_mk]; fun_prop
  -- Composing with `ULift.down` (the map `LinearIsometryEquiv.ulift`) is evaluation followed by
  -- `ULift.down`, by definition.
  have h : rescaledPath p y s = ULift.down (ContinuousMap.mkD (fun s => ULift.up.{u}
      ((timePath y s).1.2 • p (timePath y s).1.1 ((timePath y s).1.2 * (timePath y s).2))) 0 s) :=
    rfl
  rw [h, ContinuousMap.mkD_apply_of_continuous hc]
  rfl

/-- **Smooth dependence on parameters.** If a family of paths `p x t` in a real Banach algebra is
`Cⁿ` jointly in a parameter `x` from an open set `U` of a normed space and the time `t`, then so
is its Dyson series `dysonSeries (p x) t`. -/
theorem contDiffOn_parametric_dysonSeries {n : ℕ∞} {U : Set E} (hU : IsOpen U) {p : E → ℝ → B}
    (hp : ContDiffOn ℝ n (Function.uncurry p) (U ×ˢ univ)) :
    ContDiffOn ℝ n (fun q : E × ℝ => dysonSeries (p q.1) q.2) (U ×ˢ univ) := by
  set S : Set ((E × ℝ) × ℝ) := (U ×ˢ univ) ×ˢ univ
  have hS : IsOpen S := (hU.prod isOpen_univ).prod isOpen_univ
  have hg₀ : ContDiffOn ℝ n (fun z : (E × ℝ) × ℝ => z.1.2 • p z.1.1 (z.1.2 * z.2)) S := by
    refine (contDiff_snd.comp contDiff_fst).contDiffOn.smul (hp.comp
      (f := fun z : (E × ℝ) × ℝ => (z.1.1, z.1.2 * z.2)) (by fun_prop)
      fun z hz => ⟨hz.1.1, mem_univ _⟩)
  have hg : ContDiffOn ℝ n (fun z : (E × ℝ) × ℝ => ULift.up.{u}
      (z.1.2 • p z.1.1 (z.1.2 * z.2))) S :=
    (LinearIsometryEquiv.ulift ℝ B).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hg₀
  set one : Icc (0 : ℝ) 1 := ⟨1, right_mem_Icc.2 zero_le_one⟩
  have hmem {y : E × ℝ} (hy : y ∈ U ×ˢ univ) (s) : timePath y s ∈ S := ⟨⟨hy.1, trivial⟩, trivial⟩
  have hR {y : E × ℝ} (hy : y ∈ U ×ˢ univ) : ContDiffAt ℝ n (rescaledPath p) y :=
    ContinuousLinearMap.contDiff _ |>.contDiffAt.comp y <|
      (ContinuousMap.contDiffAt_mkD_comp n hS hg (hmem hy) 0).comp y contDiff_timePath.contDiffAt
  have key {y : E × ℝ} (hy : y ∈ U ×ˢ univ) :
      dysonSeries (p y.1) y.2 = (pathDysonSeries (B := B)).sum (rescaledPath p y) one := by
    have hpx : Continuous (p y.1) := hp.continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) fun _ => ⟨hy.1, trivial⟩
    have h := hasSum_dysonTerm_one (q := fun u => y.2 • p y.1 (y.2 * u))
      (rescaledPath_apply hpx)
    simp_rw [dysonTerm_smul_comp_mul, mul_one] at h
    exact (hasSum_dysonSeries hpx y.2).unique h
  intro y hy
  have hG : ContDiff ℝ n fun Q => (pathDysonSeries (B := B)).sum Q one := by
    simpa only [dysonSeries_projIcc_one] using contDiff_dysonSeries_projIcc (B := B) (n := n)
  refine ((hG.contDiffAt.comp y (hR hy)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(hU.prod isOpen_univ).mem_nhds hy] with z hz using key hz

/-- **Smooth dependence on parameters.** If a family of paths `p x t` in a real Banach algebra is
`Cⁿ` jointly in a parameter `x` from an open set `U` of a normed space and the time `t`, then so
is its left Dyson series `dysonSeriesLeft (p x) t`, the solution of `Γ' = p x Γ`, `Γ 0 = 1`. -/
theorem contDiffOn_parametric_dysonSeriesLeft {n : ℕ∞} {U : Set E} (hU : IsOpen U)
    {p : E → ℝ → B} (hp : ContDiffOn ℝ n (Function.uncurry p) (U ×ˢ univ)) :
    ContDiffOn ℝ n (fun q : E × ℝ => dysonSeriesLeft (p q.1) q.2) (U ×ˢ univ) := by
  have h := contDiffOn_parametric_dysonSeries hU (p := fun x s => MulOpposite.op (p x s))
    ((MulOpposite.opContinuousLinearEquiv ℝ).contDiff.comp_contDiffOn hp)
  refine ((MulOpposite.opContinuousLinearEquiv ℝ).symm.contDiff.comp_contDiffOn h).congr
    fun q _ => ?_
  rw [← MulOpposite.op_inj, op_dysonSeriesLeft]
  rfl

/-- **Smooth dependence on parameters.** If a family of paths `p x t` in a real Banach algebra is
`Cⁿ` jointly in a parameter `x` from a normed space and the time `t`, then so is its Dyson series
`dysonSeries (p x) t`. -/
theorem contDiff_parametric_dysonSeries {n : ℕ∞} {p : E → ℝ → B}
    (hp : ContDiff ℝ n (Function.uncurry p)) :
    ContDiff ℝ n fun q : E × ℝ => dysonSeries (p q.1) q.2 := by
  rw [← contDiffOn_univ, ← univ_prod_univ] at hp ⊢
  exact contDiffOn_parametric_dysonSeries isOpen_univ hp

/-- **Smooth dependence on parameters.** If a family of paths `p x t` in a real Banach algebra is
`Cⁿ` jointly in a parameter `x` from a normed space and the time `t`, then so is its left Dyson
series `dysonSeriesLeft (p x) t`. -/
theorem contDiff_parametric_dysonSeriesLeft {n : ℕ∞} {p : E → ℝ → B}
    (hp : ContDiff ℝ n (Function.uncurry p)) :
    ContDiff ℝ n fun q : E × ℝ => dysonSeriesLeft (p q.1) q.2 := by
  rw [← contDiffOn_univ, ← univ_prod_univ] at hp ⊢
  exact contDiffOn_parametric_dysonSeriesLeft isOpen_univ hp

end Parametric

end SymplecticGeometry
