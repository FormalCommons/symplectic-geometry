/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.IteratedFDeriv
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Partial derivatives and the operator `∂̄ + μ ∂`

Write `∂ₐv = fun z ↦ fderiv ℝ v z a` for the partial derivative of `v` along `a`. This file
proves the facts about `P v = ∂̄v + μ ∂v` that let an estimate for `P` in the plane pass from one
order to the next by applying it to the partial derivatives of `v`. The comparison of the
derivatives of `v` with those of its partials `∂₁v` and `∂_I v` is general calculus, in
`SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.FDerivApply`.

## Main results

* `TauCeti.conjWirtingerDeriv_fderiv_apply_add_smul_wirtingerDeriv`: the commutator of `P`
  with a partial derivative, `P (∂ₐv) = ∂ₐ (P v) - (∂ₐμ) ∂v`, at every point where `v` is `C²`
  and `μ` is differentiable. It rests on `TauCeti.fderiv_conjWirtingerDeriv_apply` and
  `TauCeti.fderiv_wirtingerDeriv_apply` (`∂ₐ` commutes with `∂̄` and `∂`), which follow from
  `ContDiffAt.fderiv_comp_fderiv_apply`.
* `TauCeti.conjWirtingerDeriv_add_smul_wirtingerDeriv_congr`: `P v` depends on `μ` only on the
  topological support of `v`, since `∂v` vanishes off it
  (`TauCeti.wirtingerDeriv_of_notMem_tsupport`, proved as Tau Ceti's
  `TauCeti.conjWirtingerDeriv_of_notMem_tsupport`); for the same reason the topological support
  of `P v` lies in that of `v`
  (`TauCeti.tsupport_conjWirtingerDeriv_add_smul_wirtingerDeriv_subset`).
* `ContDiff.conjWirtingerDeriv_apply` and `ContDiff.wirtingerDeriv_apply`: the Wirtinger
  derivatives of a `C^(m+1)` map, evaluated on a fixed vector, are `C^m`; the global forms of
  Tau Ceti's `ContDiffAt.conjWirtingerDeriv_apply` and `ContDiffAt.wirtingerDeriv_apply`.
* `TauCeti.eLpNorm_iteratedFDeriv_wirtingerDeriv_one_le`: the `Lᵖ` norm of `Dᵐ(∂v(·) 1)` is at
  most that of `D^{m+1} v`, from Tau Ceti's `TauCeti.iteratedFDeriv_wirtingerDeriv_one`.
* `TauCeti.exists_eLpNorm_iteratedFDeriv_fderiv_smul_wirtingerDeriv_le`: for `μ` of class
  `C^{k+1}` on an open set containing a compact `K`, the derivatives of order `j ≤ k` of
  `(∂ₐμ) ∂v` are bounded in `Lᵖ` by a constant times the sum of the `Lᵖ` norms of the derivatives
  of `v` of order at most `k + 1`, uniformly in the `C^{k+1}` maps `v` supported in `K`. The
  coefficient is first replaced by a compactly supported one that agrees with it near `K`, and
  the bound is then Tau Ceti's Leibniz rule
  `ContinuousLinearMap.eLpNorm_iteratedFDeriv_le_of_bilinear` with
  `TauCeti.eLpNorm_iteratedFDeriv_wirtingerDeriv_one_le`.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B (elliptic regularity: higher derivatives from the estimate applied to partials).
-/

public section

open MeasureTheory Complex Filter Topology ContinuousLinearMap
open scoped ENNReal NNReal ContDiff

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
  have hc := (hv.hasFDerivAt_conjWirtingerDeriv_apply b).differentiableAt
  have hw := (hv.hasFDerivAt_wirtingerDeriv_apply b).differentiableAt
  rw [(hc.hasFDerivAt.fun_add (hμ.hasFDerivAt.fun_smul hw.hasFDerivAt)).fderiv, add_apply,
    add_apply, smul_apply, smulRight_apply, fderiv_conjWirtingerDeriv_apply hv,
    fderiv_wirtingerDeriv_apply hv]
  abel

/-- The Wirtinger derivative vanishes off the topological support. -/
theorem wirtingerDeriv_of_notMem_tsupport (hz : z ∉ tsupport v) : wirtingerDeriv v z = 0 := by
  ext b
  simp [wirtingerDeriv_apply, fderiv_of_notMem_tsupport ℝ hz]

/-- The operator `∂̄ + μ ∂` does not enlarge the topological support: the topological support
of `∂̄v(·) b + μ ∂v(·) b` lies in that of `v`. -/
theorem tsupport_conjWirtingerDeriv_add_smul_wirtingerDeriv_subset (μ : V → ℂ) (b : V) :
    tsupport (fun z ↦ conjWirtingerDeriv v z b + μ z • wirtingerDeriv v z b) ⊆ tsupport v :=
  closure_minimal (fun z hz ↦ by_contra fun h ↦ hz (by
    simp [conjWirtingerDeriv_of_notMem_tsupport h, wirtingerDeriv_of_notMem_tsupport h]))
    (isClosed_tsupport v)

/-- The operator `∂̄ + μ ∂` only sees `μ` on the topological support of `v`: two coefficients
that agree there give the same `∂̄v(·) b + μ ∂v(·) b`. -/
theorem conjWirtingerDeriv_add_smul_wirtingerDeriv_congr {ρ μ : V → ℂ}
    (h : Set.EqOn ρ μ (tsupport v)) (b : V) :
    (fun z ↦ conjWirtingerDeriv v z b + ρ z • wirtingerDeriv v z b) =
      fun z ↦ conjWirtingerDeriv v z b + μ z • wirtingerDeriv v z b := by
  funext z
  by_cases hz : z ∈ tsupport v
  · rw [h hz]
  · simp [wirtingerDeriv_of_notMem_tsupport hz]

section ContDiff

variable {g : V → W} {m n : WithTop ℕ∞}

/-- The conjugate Wirtinger derivative of a `C^(m+1)` map, evaluated on a fixed vector, is
`C^m`. -/
theorem _root_.ContDiff.conjWirtingerDeriv_apply (hg : ContDiff ℝ n g) (hmn : m + 1 ≤ n)
    (v : V) : ContDiff ℝ m (fun z ↦ conjWirtingerDeriv g z v) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ hg.contDiffAt.conjWirtingerDeriv_apply hmn v

/-- The Wirtinger derivative of a `C^(m+1)` map, evaluated on a fixed vector, is `C^m`. -/
theorem _root_.ContDiff.wirtingerDeriv_apply (hg : ContDiff ℝ n g) (hmn : m + 1 ≤ n) (v : V) :
    ContDiff ℝ m (fun z ↦ wirtingerDeriv g z v) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ hg.contDiffAt.wirtingerDeriv_apply hmn v

end ContDiff

end Commutator

section LowerOrder

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The `Lᵖ` norm of the derivative of order `m` of `∂v(·) 1` is at most that of the derivative
of order `m + 1` of `v`. -/
theorem eLpNorm_iteratedFDeriv_wirtingerDeriv_one_le {v : ℂ → F} {m : ℕ}
    (hv : ContDiff ℝ (m + 1 : ℕ) v) (ν : Measure ℂ) (p : ℝ≥0∞) :
    eLpNorm (iteratedFDeriv ℝ m (fun z ↦ wirtingerDeriv v z 1)) p ν ≤
      eLpNorm (iteratedFDeriv ℝ (m + 1) v) p ν := by
  have hw : ContDiff ℝ m (fun z ↦ wirtingerDeriv v z 1) :=
    hv.wirtingerDeriv_apply (by norm_cast) 1
  refine eLpNorm_mono ((hw.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable) fun x ↦ ?_
  rw [iteratedFDeriv_wirtingerDeriv_one hv]
  exact norm_wirtingerOneCurryRight_apply_le _ _

/-- **The lower-order term of the commutator.** Let `μ` be of class `C^{k+1}` on an open set `U`
containing a compact set `K`, let `ν` be finite on compact sets, and `1 ≤ p`. There is a constant
`C` such that for every `v` of class `C^{k+1}` with `tsupport v ⊆ K` and every `j ≤ k`, the `Lᵖ(ν)`
norm of the derivative of order `j` of
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
    · simp [wirtingerDeriv_of_notMem_tsupport hz]
  have hw : ContDiff ℝ k (fun z ↦ wirtingerDeriv v z 1) :=
    hv.wirtingerDeriv_apply (by norm_cast) 1
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
        · refine (eLpNorm_iteratedFDeriv_wirtingerDeriv_one_le
            (hv.of_le (by exact_mod_cast (by omega : j - i + 1 ≤ k + 1))) ν p).trans ?_
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
