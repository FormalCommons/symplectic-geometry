/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.IteratedFDeriv
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.RCLike.OperatorNorm
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Partial derivatives and the operator `∂̄ + μ ∂`

Write `∂ₐv = fun z ↦ fderiv ℝ v z a` for the partial derivative of `v` along `a`. This file
proves the three facts that let an estimate for `P v = ∂̄v + μ ∂v` in the plane pass from one order
to the next by applying it to the partial derivatives of `v`.

## Main results

* `TauCeti.conjWirtingerDeriv_fderiv_apply_add_smul_wirtingerDeriv`: the commutator of `P`
  with a partial derivative, `P (∂ₐv) = ∂ₐ (P v) - (∂ₐμ) ∂v`, at every point where `v` is `C²`
  and `μ` is differentiable. It rests on `ContDiffAt.fderiv_comp_fderiv_apply`, which moves a
  partial derivative inside a continuous linear image of `Dv` by Tau Ceti's
  `TauCeti.fderiv_fderiv_apply_comm` (symmetry of the second derivative), and gives
  `TauCeti.fderiv_conjWirtingerDeriv_apply` and `TauCeti.fderiv_wirtingerDeriv_apply`.
* `TauCeti.eLpNorm_iteratedFDeriv_succ_le` and `TauCeti.eLpNorm_iteratedFDeriv_fderiv_apply_le`:
  on the plane, the `Lᵖ` norm of `D^{n+1} v` is at most the sum of those of `D^n (∂₁v)` and
  `D^n (∂_I v)`, and the `Lᵖ` norm of `D^n (∂ₐv)` is at most `‖a‖` times that of `D^{n+1} v`.
  The first comes from the pointwise bound `TauCeti.norm_iteratedFDeriv_succ_le`, the second
  from Tau Ceti's `ContDiff.norm_iteratedFDeriv_fderiv_apply_le`.
* `TauCeti.exists_eLpNorm_iteratedFDeriv_fderiv_smul_wirtingerDeriv_le`: for `μ` of class
  `C^{k+1}` on an open set containing a compact `K`, the derivatives of order `j ≤ k` of
  `(∂ₐμ) ∂v` are bounded in `Lᵖ` by a constant times the sum of the `Lᵖ` norms of the derivatives
  of `v` of order at most `k + 1`, uniformly in the `C^{k+1}` maps `v` supported in `K`. The
  coefficient is first replaced by a compactly supported one that agrees with it near `K`, and
  the bound is then Tau Ceti's Leibniz rule
  `ContinuousLinearMap.eLpNorm_iteratedFDeriv_le_of_bilinear` with Tau Ceti's
  `TauCeti.iteratedFDeriv_wirtingerDeriv_one`.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B (elliptic regularity: higher derivatives from the estimate applied to partials).
-/

public section

open MeasureTheory Complex Filter Topology ContinuousLinearMap
open scoped ENNReal NNReal ContDiff

/-- The derivative at `x` of `y ↦ L (Df(y))`, for a continuous linear map `L` and `f` of class
`C²` at `x`, evaluated at `a`, is `L` applied to the derivative of the partial derivative `∂ₐf`. -/
theorem ContDiffAt.fderiv_comp_fderiv_apply {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) (L : (E →L[ℝ] F) →L[ℝ] G)
    (a : E) :
    fderiv ℝ (fun y ↦ L (fderiv ℝ f y)) x a = L (fderiv ℝ (fun y ↦ fderiv ℝ f y a) x) := by
  -- By the symmetry of the second derivative, `D²f(x) a = D(∂ₐf)(x)`.
  have hsymm : fderiv ℝ (fderiv ℝ f) x a = fderiv ℝ (fun y ↦ fderiv ℝ f y a) x := by
    ext b
    rw [TauCeti.fderiv_fderiv_apply_comm hf (by simp) a b,
      (hf.hasFDerivAt_fderiv_apply le_rfl b).fderiv, flip_apply]
  rw [← hsymm, show (fun y ↦ L (fderiv ℝ f y)) = L ∘ fderiv ℝ f from rfl,
    (L.hasFDerivAt.comp x (hf.hasFDerivAt_fderiv le_rfl)).fderiv, comp_apply]

namespace TauCeti

section Commutator

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {v : V → W} {z : V}

/-- The derivative of `∂̄v(·) b` along `a` is `∂̄(∂ₐv) b`, for `v` of class `C²` at the point. -/
theorem fderiv_conjWirtingerDeriv_apply (hv : ContDiffAt ℝ 2 v z) (a b : V) :
    fderiv ℝ (fun w ↦ conjWirtingerDeriv v w b) z a =
      conjWirtingerDeriv (fun w ↦ fderiv ℝ v w a) z b := by
  have h := hv.fderiv_comp_fderiv_apply ((apply ℝ W b).comp complexAntilinearPartL) a
  simp only [coe_comp, Function.comp_apply, apply_apply] at h
  simp only [conjWirtingerDeriv_apply_eq_complexAntilinearPartL, h]

/-- The derivative of `∂v(·) b` along `a` is `∂(∂ₐv) b`, for `v` of class `C²` at the point. -/
theorem fderiv_wirtingerDeriv_apply (hv : ContDiffAt ℝ 2 v z) (a b : V) :
    fderiv ℝ (fun w ↦ wirtingerDeriv v w b) z a =
      wirtingerDeriv (fun w ↦ fderiv ℝ v w a) z b := by
  have hw (g : V → W) (y : V) : wirtingerDeriv g y b =
      (apply ℝ W b - (apply ℝ W b).comp complexAntilinearPartL) (fderiv ℝ g y) := by
    rw [sub_apply, comp_apply, apply_apply, apply_apply,
      ← conjWirtingerDeriv_apply_eq_complexAntilinearPartL,
      ← wirtingerDeriv_add_conjWirtingerDeriv, add_sub_cancel_right]
  simp only [hw]
  exact hv.fderiv_comp_fderiv_apply _ a

/-- **The commutator of `∂̄ + μ ∂` with a partial derivative.** If `v` is `C²` at `z` and `μ` is
differentiable there, then `P (∂ₐv) = ∂ₐ (P v) - (∂ₐμ) ∂v` at `z`, where
`P u = ∂̄u(·) b + μ ∂u(·) b`. -/
theorem conjWirtingerDeriv_fderiv_apply_add_smul_wirtingerDeriv {μ : V → ℂ}
    (hv : ContDiffAt ℝ 2 v z) (hμ : DifferentiableAt ℝ μ z) (a b : V) :
    conjWirtingerDeriv (fun w ↦ fderiv ℝ v w a) z b +
        μ z • wirtingerDeriv (fun w ↦ fderiv ℝ v w a) z b =
      fderiv ℝ (fun w ↦ conjWirtingerDeriv v w b + μ w • wirtingerDeriv v w b) z a -
        fderiv ℝ μ z a • wirtingerDeriv v z b := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hc : DifferentiableAt ℝ (fun w ↦ conjWirtingerDeriv v w b) z := by
    simp only [conjWirtingerDeriv_apply_eq_complexAntilinearPartL]
    exact (((apply ℝ W b).comp complexAntilinearPartL).differentiableAt).comp z hd
  have hw : DifferentiableAt ℝ (fun w ↦ wirtingerDeriv v w b) z := by
    have h (w : V) : wirtingerDeriv v w b = fderiv ℝ v w b - conjWirtingerDeriv v w b := by
      rw [← wirtingerDeriv_add_conjWirtingerDeriv, add_sub_cancel_right]
    simp only [h]
    exact (hd.clm_apply (differentiableAt_const b)).sub hc
  rw [(hc.hasFDerivAt.fun_add (hμ.hasFDerivAt.fun_smul hw.hasFDerivAt)).fderiv, add_apply,
    add_apply, smul_apply, smulRight_apply, fderiv_conjWirtingerDeriv_apply hv,
    fderiv_wirtingerDeriv_apply hv]
  abel

end Commutator

section Partials

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {v : ℂ → F} {n : ℕ}

/-- Pointwise, the derivative of order `n + 1` of `v` is at most the sum of the derivatives of
order `n` of the partial derivatives `∂₁v` and `∂_I v`. -/
theorem norm_iteratedFDeriv_succ_le (hv : ContDiff ℝ (n + 1) v) (x : ℂ) :
    ‖iteratedFDeriv ℝ (n + 1) v x‖ ≤ ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ v z 1) x‖ +
      ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ v z I) x‖ := by
  -- `Dⁿ(∂ₐv)(x)` is `Dⁿ(Dv)(x)` followed by evaluation at `a`.
  have h (a : ℂ) : iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ v z a) x =
      (apply ℝ F a).compContinuousMultilinearMap (iteratedFDeriv ℝ n (fderiv ℝ v) x) :=
    (apply ℝ F a).iteratedFDeriv_comp_left (hv.fderiv_right (m := n) le_rfl).contDiffAt le_rfl
  rw [← norm_iteratedFDeriv_fderiv]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  refine (opNorm_le_bound _ (by positivity) (norm_apply_le_norm_one_add_norm_I (K := ℂ) _)).trans
    ?_
  rw [RCLike.I_to_complex, add_mul]
  gcongr
  all_goals
    rw [h]
    refine le_of_eq_of_le ?_ (ContinuousMultilinearMap.le_opNorm _ m)
    rw [compContinuousMultilinearMap_coe, Function.comp_apply, apply_apply]

variable (ν : Measure ℂ) {p : ℝ≥0∞}

/-- The `Lᵖ` norm of the derivative of order `n` of `∂ₐv` is at most `‖a‖` times that of the
derivative of order `n + 1` of `v`. -/
theorem eLpNorm_iteratedFDeriv_fderiv_apply_le (hv : ContDiff ℝ (n + 1) v) (a : ℂ) (p : ℝ≥0∞) :
    eLpNorm (iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ v z a)) p ν ≤
      ENNReal.ofReal ‖a‖ * eLpNorm (iteratedFDeriv ℝ (n + 1) v) p ν :=
  eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    ((((hv.fderiv_right (m := n) le_rfl).clm_apply
      contDiff_const).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦
      (hv.norm_iteratedFDeriv_fderiv_apply_le (by simp) a x).trans_eq (mul_comm _ _)) p

/-- For `1 ≤ p`, the `Lᵖ` norm of the derivative of order `n + 1` of `v` is at most the sum of
the `Lᵖ` norms of the derivatives of order `n` of `∂₁v` and `∂_I v`. -/
theorem eLpNorm_iteratedFDeriv_succ_le (hv : ContDiff ℝ (n + 1) v) (hp : 1 ≤ p) :
    eLpNorm (iteratedFDeriv ℝ (n + 1) v) p ν ≤
      eLpNorm (iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ v z 1)) p ν +
        eLpNorm (iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ v z I)) p ν := by
  have hc (a : ℂ) : Continuous (iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ v z a)) :=
    ((hv.fderiv_right (m := n) le_rfl).clm_apply
      contDiff_const).continuous_iteratedFDeriv le_rfl
  calc eLpNorm (iteratedFDeriv ℝ (n + 1) v) p ν
      ≤ eLpNorm (fun x ↦ ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ v z 1) x‖ +
          ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ v z I) x‖) p ν :=
        eLpNorm_mono_real ((hv.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable)
          (norm_iteratedFDeriv_succ_le hv)
    _ ≤ _ := by
        refine (eLpNorm_add_le (f := fun x ↦ ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ v z 1) x‖)
          (g := fun x ↦ ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ v z I) x‖) hp).trans ?_
        rw [eLpNorm_norm, eLpNorm_norm]
        all_goals exact (hc _).aestronglyMeasurable

end Partials

section LowerOrder

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The lower-order term of the commutator.** Let `μ` be of class `C^{k+1}` on an open set `U`
containing a compact set `K`, and `1 ≤ p`. There is a constant `C` such that for every `v` of class
`C^{k+1}` with `tsupport v ⊆ K` and every `j ≤ k`, the `Lᵖ` norm of the derivative of order `j` of
`(∂ₐμ) ∂v(·) 1` is at most `C` times the sum of the `Lᵖ` norms of the derivatives of `v` of order
at most `k + 1`. -/
theorem exists_eLpNorm_iteratedFDeriv_fderiv_smul_wirtingerDeriv_le (ν : Measure ℂ)
    [IsFiniteMeasureOnCompacts ν] {p : ℝ≥0∞} (hp : 1 ≤ p) {K U : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {μ : ℂ → ℂ} {k : ℕ} (hμ : ContDiffOn ℝ (k + 1 : ℕ) μ U)
    (a : ℂ) :
    ∃ C : ℝ≥0, ∀ v : ℂ → F, ContDiff ℝ (k + 1 : ℕ) v → tsupport v ⊆ K → ∀ j ≤ k,
      eLpNorm (iteratedFDeriv ℝ j (fun z ↦ fderiv ℝ μ z a • wirtingerDeriv v z 1)) p ν ≤
        C * ∑ i ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ i v) p ν := by
  -- Replace `μ` by `ρ = χ μ`, smooth with compact support and equal to `μ` near `K`.
  obtain ⟨χ, hχ, -, hχ1, hχc, hχU⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one hU hKU
  set ρ : ℂ → ℂ := fun z ↦ χ z • μ z
  have hρ : ContDiff ℝ (k + 1 : ℕ) ρ :=
    hμ.contDiff_smul_of_tsupport_subset hU (hχ.of_le (by simp)).contDiffOn hχU
  set g : ℂ → ℂ := fun z ↦ fderiv ℝ ρ z a
  have hg : ContDiff ℝ k g :=
    (hρ.fderiv_right (m := k) le_rfl).clm_apply contDiff_const
  have hgc : HasCompactSupport g :=
    (hχc.mono fun _ hz ↦ left_ne_zero_of_smul hz : HasCompactSupport ρ).fderiv_apply (𝕜 := ℝ) a
  set B : ℂ →L[ℝ] F →L[ℝ] F := lsmul ℝ ℂ
  set M : ℝ≥0∞ := ∑ i ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ i g) (∞ : ℝ≥0∞) ν
  have hM : M ≠ ⊤ := ENNReal.sum_ne_top.2 fun i hi ↦
    (hg.memLp_iteratedFDeriv_of_hasCompactSupport
      (by exact_mod_cast Finset.mem_range_succ_iff.1 hi) hgc).eLpNorm_ne_top
  set C : ℝ≥0∞ := (k + 1) * (‖B‖ₑ * 2 ^ k * M)
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top (by simp)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top eNorm_ne_top (by simp)) hM)
  refine ⟨C.toNNReal, fun v hv hvK j hj ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hC]
  -- The coefficient may be replaced by `∂ₐρ`, since `∂v` vanishes off `K`.
  have heq : (fun z ↦ fderiv ℝ μ z a • wirtingerDeriv v z 1) =
      fun z ↦ B (g z) (wirtingerDeriv v z 1) := by
    funext z
    by_cases hz : z ∈ tsupport v
    · have h : ρ =ᶠ[𝓝 z] μ := (hχ1 z (hvK hz)).mono fun y hy ↦ by simp [ρ, hy]
      simp [B, g, h.fderiv_eq]
    · have h : v =ᶠ[𝓝 z] fun _ ↦ 0 := notMem_tsupport_iff_eventuallyEq.1 hz
      simp [h.wirtingerDeriv_eq]
  have hw : ContDiff ℝ k (fun z ↦ wirtingerDeriv v z 1) := by
    rw [wirtingerDeriv_one_eq_comp]
    exact wirtingerOne.contDiff.comp (hv.fderiv_right (m := k) (by norm_cast))
  rw [heq]
  refine (B.eLpNorm_iteratedFDeriv_le_of_bilinear hg hw (le_refl (k : WithTop ℕ∞) |>.trans' ?_)
    hp (q := fun _ ↦ (∞ : ℝ≥0∞)) (r := fun _ ↦ p) fun _ _ ↦ inferInstance).trans ?_
  · exact_mod_cast hj
  set S := ∑ i ∈ Finset.range (k + 2), eLpNorm (iteratedFDeriv ℝ i v) p ν
  calc _ ≤ ∑ _i ∈ Finset.range (j + 1), ‖B‖ₑ * 2 ^ k * M * S := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hij : i ≤ j := Finset.mem_range_succ_iff.1 hi
        gcongr
        · exact_mod_cast (Nat.choose_le_two_pow j i).trans (Nat.pow_le_pow_right two_pos hj)
        · exact Finset.single_le_sum (f := fun i ↦ eLpNorm (iteratedFDeriv ℝ i g) (∞ : ℝ≥0∞) ν)
            (fun _ _ ↦ bot_le) (Finset.mem_range_succ_iff.2 (hij.trans hj))
        · refine (eLpNorm_mono (g := iteratedFDeriv ℝ (j - i + 1) v) ((hw.continuous_iteratedFDeriv
            (by exact_mod_cast (by omega : j - i ≤ k))).aestronglyMeasurable)
            fun x ↦ ?_).trans ?_
          · rw [iteratedFDeriv_wirtingerDeriv_one
              (hv.of_le (by exact_mod_cast (by omega : j - i + 1 ≤ k + 1)))]
            exact norm_wirtingerOneCurryRight_apply_le _ _
          exact Finset.single_le_sum (f := fun i ↦ eLpNorm (iteratedFDeriv ℝ i v) p ν)
            (fun _ _ ↦ bot_le) (Finset.mem_range.2 (by omega))
    _ ≤ C * S := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
        simp only [C]
        gcongr
        exact_mod_cast (by omega : j + 1 ≤ k + 1)

end LowerOrder

end TauCeti

end
