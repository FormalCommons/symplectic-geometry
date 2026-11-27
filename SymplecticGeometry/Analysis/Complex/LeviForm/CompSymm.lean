/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.Analysis.Complex.LeviForm.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Basic

import Mathlib.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.Normed.Module.RCLike.Basic

/-!
# The Levi form through a chart that is not holomorphic

Tau Ceti's `TauCeti.leviForm_comp_apply` says that the Levi form is carried by a holomorphic
change of variables. This file bounds what is lost when the change of variables `e` is only
real `C²`: the error is first order in the conjugate Wirtinger derivative `\bar∂e` of `e` and in
its derivative, against the first and second derivatives of the function.

## Main results

* `ContDiffAt.differentiableAt_conjWirtingerDeriv`,
  `ContDiffAt.fderiv_conjWirtingerDeriv_apply_apply`: for `g` real `C²` at `x`, the map
  `y ↦ \bar∂g(y)` is differentiable at `x`, with derivative
  `a ↦ (u ↦ (D²g(x)(a, u) + I • D²g(x)(a, I • u)) / 2)`.
* `ContDiffAt.norm_fderiv_fderiv_apply_add_apply_I_smul_le`: for such `g`, the vector
  `D²g(x)(v, v) + D²g(x)(I • v, I • v)` has norm at most `4 ‖D\bar∂g(x)‖ ‖v‖²`.
* `OpenPartialHomeomorph.fderiv_fderiv_symm_apply_fderiv_apply`: the second derivative of the
  inverse of a `C²` chart, `D²e⁻¹(De a, De b) = -De⁻¹(D²e(a, b))`.
* `TauCeti.le_re_leviForm_comp_symm`: for every `K` there is `C` such that, whenever the first
  derivatives of `e` and `e.symm` and the second derivative of `e` are bounded by `K`,
  `Re L(u)(p)(v, v) - C (‖\bar∂e(p)‖ ‖D²u(p)‖ + (‖\bar∂e(p)‖ + ‖D\bar∂e(p)‖) ‖Du(p)‖) ‖v‖²`
  is at most `Re L(u ∘ e⁻¹)(e p)(De_p v, De_p v)`.

## Implementation notes

The proof follows that of `TauCeti.leviForm_comp_apply`: it expands both Levi forms with
`TauCeti.re_leviForm_apply` and the second-order chain rule `fderiv_fderiv_comp_apply`. With
`ξ = De_p v` and `w = De⁻¹(I • ξ)`, the Levi form of `u ∘ e⁻¹` on `ξ` is
`(D²u(v, v) + D²u(w, w) - Du(De⁻¹(D²e(v, v) + D²e(w, w)))) / 4`; the vector `w - I • v` is
`2 De⁻¹(I • \bar∂e(v))`, and `D²e(v, v) + D²e(I • v, I • v)` is
`2 D\bar∂e(v)(v) - 2 I • D\bar∂e(I • v)(v)` by the symmetry of `D²e`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 8.12; the error term here plays the role of their bound (4.1).
-/

public section

open Complex Filter Topology

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The complex-antilinear part, as a continuous real-linear map into the complex-antilinear
operators. -/
private noncomputable def complexAntilinearPartCLM : (V →L[ℝ] W) →L[ℝ] V →L⋆[ℂ] W :=
  LinearMap.mkContinuous
    { toFun := ContinuousLinearMap.complexAntilinearPart
      map_add' := fun Ψ Φ ↦ by
        ext v
        simp only [ContinuousLinearMap.complexAntilinearPart_apply,
          _root_.add_apply]
        module
      map_smul' := fun c Ψ ↦ by
        ext v
        simp only [ContinuousLinearMap.complexAntilinearPart_apply,
          _root_.smul_apply, RingHom.id_apply]
        rw [smul_comm Complex.I c, ← smul_add, smul_comm] }
    1 fun Ψ ↦ by
      rw [one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
      have h := Ψ.le_opNorm_of_le (x := I • v) (c := ‖v‖) (by simp [norm_smul])
      have h' : ‖I • Ψ (I • v)‖ ≤ ‖Ψ‖ * ‖v‖ := by simpa [norm_smul] using h
      simpa [ContinuousLinearMap.complexAntilinearPart_apply, ← Complex.coe_smul] using
        norm_two_inv_smul_add_le (𝕜 := ℂ) (Ψ.le_opNorm v) h'

private theorem conjWirtingerDeriv_eq_complexAntilinearPartCLM (g : V → W) (x : V) :
    conjWirtingerDeriv g x = complexAntilinearPartCLM (fderiv ℝ g x) :=
  by ext v; simp [complexAntilinearPartCLM, conjWirtingerDeriv_eq_complexAntilinearPart]

variable {g : V → W} {x : V}

/-- For `g` real `C²` at `x`, the conjugate Wirtinger derivative `y ↦ \bar∂g(y)` is
differentiable at `x`. -/
theorem _root_.ContDiffAt.differentiableAt_conjWirtingerDeriv (hg : ContDiffAt ℝ 2 g x) :
    DifferentiableAt ℝ (conjWirtingerDeriv g) x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have : conjWirtingerDeriv g = fun y ↦ complexAntilinearPartCLM (fderiv ℝ g y) :=
    funext fun y ↦ conjWirtingerDeriv_eq_complexAntilinearPartCLM g y
  rw [this]
  exact complexAntilinearPartCLM.differentiableAt.comp x hD

/-- For `g` real `C²` at `x`, the derivative of `y ↦ \bar∂g(y)` at `x` in the direction `a`,
applied to `u`, is `(D²g(x)(a, u) + I • D²g(x)(a, I • u)) / 2`. -/
theorem _root_.ContDiffAt.fderiv_conjWirtingerDeriv_apply_apply (hg : ContDiffAt ℝ 2 g x)
    (a u : V) :
    fderiv ℝ (conjWirtingerDeriv g) x a u =
      (2 : ℂ)⁻¹ • (fderiv ℝ (fderiv ℝ g) x a u + I • fderiv ℝ (fderiv ℝ g) x a (I • u)) := by
  let ev : (V →L⋆[ℂ] W) →L[ℝ] W :=
    (ContinuousLinearMap.apply' W (starRingEnd ℂ) u).restrictScalars ℝ
  have h₁ : HasFDerivAt (fun y ↦ conjWirtingerDeriv g y u)
      (ev.comp (fderiv ℝ (conjWirtingerDeriv g) x)) x :=
    ev.hasFDerivAt.comp x hg.differentiableAt_conjWirtingerDeriv.hasFDerivAt
  have h := DFunLike.congr_fun (h₁.unique (hg.hasFDerivAt_conjWirtingerDeriv_apply u)) a
  simpa [ev] using h

/-- For `g` real `C²` at `x`, the vector `D²g(x)(v, v) + D²g(x)(I • v, I • v)`, which vanishes
for complex `C²` maps, is bounded by the derivative of `\bar∂g` at `x`:
it is `2 D\bar∂g(x)(v)(v) - 2 I • D\bar∂g(x)(I • v)(v)`. -/
theorem _root_.ContDiffAt.norm_fderiv_fderiv_apply_add_apply_I_smul_le (hg : ContDiffAt ℝ 2 g x)
    (v : V) :
    ‖fderiv ℝ (fderiv ℝ g) x v v + fderiv ℝ (fderiv ℝ g) x (I • v) (I • v)‖ ≤
      4 * ‖fderiv ℝ (conjWirtingerDeriv g) x‖ * ‖v‖ ^ 2 := by
  set E₂ := fderiv ℝ (fderiv ℝ g) x
  set DB := fderiv ℝ (conjWirtingerDeriv g) x
  have hDB (a b : V) : DB a b = (2 : ℂ)⁻¹ • (E₂ a b + I • E₂ a (I • b)) :=
    hg.fderiv_conjWirtingerDeriv_apply_apply a b
  have hsym : E₂ v (I • v) = E₂ (I • v) v := hg.isSymmSndFDerivAt (by simp) v (I • v)
  have hX : E₂ v v + E₂ (I • v) (I • v) = (2 : ℂ) • DB v v - (2 : ℂ) • I • DB (I • v) v := by
    rw [hDB, hDB, hsym]
    simp only [smul_add, smul_smul]
    match_scalars
    · ring
    · linear_combination I_mul_I
    · ring
  have hle (a : V) : ‖DB a v‖ ≤ ‖DB‖ * ‖a‖ * ‖v‖ := (DB a).le_of_opNorm_le (DB.le_opNorm a) v
  have h₃ := hle v
  have h₄ := hle (I • v)
  rw [norm_smul, norm_I, one_mul] at h₄
  rw [hX]
  calc ‖(2 : ℂ) • DB v v - (2 : ℂ) • I • DB (I • v) v‖
      ≤ 2 * ‖DB v v‖ + 2 * ‖DB (I • v) v‖ := by
        refine (norm_sub_le _ _).trans_eq ?_
        simp [norm_smul]
    _ ≤ 4 * ‖DB‖ * ‖v‖ ^ 2 := by linarith

/-- The second derivative of the inverse of an open partial homeomorphism `e` at `e p`, on the
images `De_p a` and `De_p b`, is `-De⁻¹(D²e_p(a, b))`, where `e` and `e.symm` are `C²`. -/
theorem _root_.OpenPartialHomeomorph.fderiv_fderiv_symm_apply_fderiv_apply {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (e : OpenPartialHomeomorph E F) {p : E}
    (hp : p ∈ e.source) (he : ContDiffAt 𝕜 2 e p) (hs : ContDiffAt 𝕜 2 e.symm (e p)) (a b : E) :
    fderiv 𝕜 (fderiv 𝕜 e.symm) (e p) (fderiv 𝕜 e p a) (fderiv 𝕜 e p b) =
      -fderiv 𝕜 e.symm (e p) (fderiv 𝕜 (fderiv 𝕜 e) p a b) := by
  have hcomp : fderiv 𝕜 (fderiv 𝕜 (e.symm ∘ e)) p = 0 := by
    have h : fderiv 𝕜 (e.symm ∘ e) =ᶠ[𝓝 p] fun _ ↦ ContinuousLinearMap.id 𝕜 E :=
      eventually_of_mem (e.open_source.mem_nhds hp) fun q hq ↦ by
        have h' : e.symm ∘ e =ᶠ[𝓝 q] id := e.eventually_left_inverse hq
        exact h'.fderiv_eq.trans fderiv_id
    rw [h.fderiv_eq]
    simp
  have h := fderiv_fderiv_comp_apply hs he a b
  rw [hcomp, zero_apply, zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The real part of the Levi form of `u ∘ e.symm` at `e p` on `De_p v`, in terms of the
derivatives of `u` and `e` at `p` and of the vector `w = De⁻¹(I • De_p v)`. -/
private theorem re_leviForm_comp_symm_apply_eq {e : OpenPartialHomeomorph V W} {p : V}
    (hp : p ∈ e.source) (he : ContDiffAt ℝ 2 e p) (hs : ContDiffAt ℝ 2 e.symm (e p))
    {u : V → ℝ} (hu : ContDiffAt ℝ 2 u p) (v : V) :
    (leviForm (u ∘ e.symm) (e p) (fderiv ℝ e p v) (fderiv ℝ e p v)).re =
      (fderiv ℝ (fderiv ℝ u) p v v +
          fderiv ℝ (fderiv ℝ u) p (fderiv ℝ e.symm (e p) (I • fderiv ℝ e p v))
            (fderiv ℝ e.symm (e p) (I • fderiv ℝ e p v)) -
        fderiv ℝ u p (fderiv ℝ e.symm (e p) (fderiv ℝ (fderiv ℝ e) p v v +
          fderiv ℝ (fderiv ℝ e) p (fderiv ℝ e.symm (e p) (I • fderiv ℝ e p v))
            (fderiv ℝ e.symm (e p) (I • fderiv ℝ e p v))))) / 4 := by
  have hfp : e.symm (e p) = p := e.left_inv hp
  have hd : DifferentiableAt ℝ e p := he.differentiableAt (by norm_num)
  have hds : DifferentiableAt ℝ e.symm (e p) := hs.differentiableAt (by norm_num)
  have hDA (a : V) : fderiv ℝ e.symm (e p) (fderiv ℝ e p a) = a :=
    e.fderiv_symm_apply_fderiv_apply_of_mem_source hp hd hds a
  have hAw : fderiv ℝ e p (fderiv ℝ e.symm (e p) (I • fderiv ℝ e p v)) = I • fderiv ℝ e p v :=
    e.fderiv_apply_fderiv_symm_apply_of_mem_source hp hd hds _
  have hg (a b : W) : fderiv ℝ (fderiv ℝ (u ∘ e.symm)) (e p) a b =
      fderiv ℝ (fderiv ℝ u) p (fderiv ℝ e.symm (e p) a) (fderiv ℝ e.symm (e p) b) +
        fderiv ℝ u p (fderiv ℝ (fderiv ℝ e.symm) (e p) a b) := by
    have h := fderiv_fderiv_comp_apply (by rwa [hfp] : ContDiffAt ℝ 2 u (e.symm (e p))) hs a b
    rwa [hfp] at h
  rw [re_leviForm_apply, hg, hg, ← hAw, e.fderiv_fderiv_symm_apply_fderiv_apply hp he hs,
    e.fderiv_fderiv_symm_apply_fderiv_apply hp he hs, hDA, hDA]
  simp only [map_add, map_neg]
  ring

/-- **The Levi form through a chart that is not holomorphic.** For every `K` there is `C` such
that for every open partial homeomorphism `e` between complex normed spaces and every `p` in its
source at which `e` is real `C²`, with `e.symm` real `C²` at `e p` and the first derivatives of
`e` and `e.symm` and the second derivative of `e` bounded by `K`, and for every `u` real `C²` at
`p` and every `v`, the real part of the Levi form of `u ∘ e.symm` at `e p` on `De_p v` is at
least that of `u` at `p` on `v`, minus
`C (‖\bar∂e(p)‖ ‖D²u(p)‖ + (‖\bar∂e(p)‖ + ‖D\bar∂e(p)‖) ‖Du(p)‖) ‖v‖²`.

For holomorphic `e` the error vanishes, and the two Levi forms agree
(`TauCeti.leviForm_comp_symm_apply_of_mem_maximalAtlas`). -/
theorem le_re_leviForm_comp_symm (K : ℝ) :
    ∃ C : ℝ, ∀ (e : OpenPartialHomeomorph V W) (p : V), p ∈ e.source →
      ContDiffAt ℝ 2 e p → ContDiffAt ℝ 2 e.symm (e p) →
      ‖fderiv ℝ e p‖ ≤ K → ‖fderiv ℝ e.symm (e p)‖ ≤ K → ‖fderiv ℝ (fderiv ℝ e) p‖ ≤ K →
      ∀ u : V → ℝ, ContDiffAt ℝ 2 u p → ∀ v : V,
        (leviForm u p v v).re - C * (‖conjWirtingerDeriv e p‖ * ‖fderiv ℝ (fderiv ℝ u) p‖ +
          (‖conjWirtingerDeriv e p‖ + ‖fderiv ℝ (conjWirtingerDeriv e) p‖) *
            ‖fderiv ℝ u p‖) * ‖v‖ ^ 2 ≤
        (leviForm (u ∘ e.symm) (e p) (fderiv ℝ e p v) (fderiv ℝ e p v)).re := by
  refine ⟨K * (K ^ 2 + 1) ^ 2, fun e p hp he hs hK₁ hK₂ hK₃ u hu v ↦ ?_⟩
  have hd : DifferentiableAt ℝ e p := he.differentiableAt (by norm_num)
  have hds : DifferentiableAt ℝ e.symm (e p) := hs.differentiableAt (by norm_num)
  have hK : 0 ≤ K := (norm_nonneg _).trans hK₁
  rw [re_leviForm_comp_symm_apply_eq hp he hs hu, re_leviForm_apply]
  set A := fderiv ℝ e p
  set D := fderiv ℝ e.symm (e p)
  set E₂ := fderiv ℝ (fderiv ℝ e) p
  set U₁ := fderiv ℝ u p
  set U₂ := fderiv ℝ (fderiv ℝ u) p
  set B := conjWirtingerDeriv e p
  set d := ‖fderiv ℝ (conjWirtingerDeriv e) p‖
  set w := D (I • A v)
  set n := ‖v‖
  -- The defect `w - I • v` of `De⁻¹ ∘ I ∘ De` from `I` on `v`.
  have hδ : w - I • v = D ((2 : ℂ) • I • B v) := by
    have h : (2 : ℂ) • I • B v = I • A v - A (I • v) := by
      simp only [B, A, conjWirtingerDeriv_apply, smul_add, smul_smul]
      match_scalars
      · ring
      · linear_combination I_mul_I
    rw [h, map_sub, e.fderiv_symm_apply_fderiv_apply_of_mem_source hp hd hds]
  have hIn : ‖I • v‖ = n := by simp [n, norm_smul]
  have hw : ‖w‖ ≤ K * K * n := by
    calc ‖w‖ ≤ K * ‖I • A v‖ := D.le_of_opNorm_le hK₂ _
      _ = K * ‖A v‖ := by simp [norm_smul]
      _ ≤ K * (K * n) := mul_le_mul_of_nonneg_left (A.le_of_opNorm_le hK₁ v) hK
      _ = K * K * n := by ring
  have hδn : ‖w - I • v‖ ≤ K * (2 * (‖B‖ * n)) := by
    rw [hδ]
    calc ‖D ((2 : ℂ) • I • B v)‖ ≤ K * ‖(2 : ℂ) • I • B v‖ := D.le_of_opNorm_le hK₂ _
      _ = K * (2 * ‖B v‖) := by simp [norm_smul]
      _ ≤ K * (2 * (‖B‖ * n)) := by gcongr; exact B.le_opNorm v
  have hH : 0 ≤ ‖U₂‖ := U₂.opNorm_nonneg
  have hG : 0 ≤ ‖U₁‖ := U₁.opNorm_nonneg
  have hn : 0 ≤ n := norm_nonneg _
  have hKn : 0 ≤ K * K * n + n := add_nonneg (mul_nonneg (mul_nonneg hK hK) hn) hn
  -- The term with the second derivative of `u`.
  have hT₁ : |U₂ w w - U₂ (I • v) (I • v)| ≤ ‖U₂‖ * (K * K * n + n) * (K * (2 * (‖B‖ * n))) := by
    rw [← Real.norm_eq_abs]
    refine (U₂.norm_apply_apply_sub_apply_apply_le w (I • v)).trans ?_
    rw [hIn]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_left hw n) hH) hδn
      (norm_nonneg _) (mul_nonneg hH hKn)
  -- The term with the first derivative of `u`.
  have hY : ‖E₂ w w - E₂ (I • v) (I • v)‖ ≤ K * (K * K * n + n) * (K * (2 * (‖B‖ * n))) := by
    refine (E₂.norm_apply_apply_sub_apply_apply_le w (I • v)).trans ?_
    rw [hIn]
    exact mul_le_mul (mul_le_mul hK₃ (add_le_add_left hw n) (by positivity) hK) hδn
      (norm_nonneg _) (mul_nonneg hK hKn)
  have hT₂ : |U₁ (D (E₂ v v + E₂ w w))| ≤
      ‖U₁‖ * (K * (4 * d * n ^ 2 + K * (K * K * n + n) * (K * (2 * (‖B‖ * n))))) := by
    rw [← Real.norm_eq_abs]
    refine (U₁.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ hG)
    refine (D.le_of_opNorm_le hK₂ _).trans (mul_le_mul_of_nonneg_left ?_ hK)
    have h : E₂ v v + E₂ w w = (E₂ v v + E₂ (I • v) (I • v)) + (E₂ w w - E₂ (I • v) (I • v)) := by
      abel
    rw [h]
    exact (norm_add_le _ _).trans
      (add_le_add (he.norm_fderiv_fderiv_apply_add_apply_I_smul_le v) hY)
  -- Comparison of the constants.
  have h1 : 1 ≤ K ^ 2 + 1 := le_add_of_nonneg_left (sq_nonneg K)
  have P : 0 ≤ K * (K ^ 2 + 1) := mul_nonneg hK (zero_le_one.trans h1)
  have hc₁ : K * (K ^ 2 + 1) / 2 ≤ K * (K ^ 2 + 1) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h1 P
    linarith
  have hc₂ : K ≤ K * (K ^ 2 + 1) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h1 hK
    have := mul_le_mul_of_nonneg_left h1 P
    linarith
  have hc₃ : K ^ 3 * (K ^ 2 + 1) / 2 ≤ K * (K ^ 2 + 1) ^ 2 := by
    have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one : K ^ 2 ≤ K ^ 2 + 1) P
    have := mul_nonneg P (sq_nonneg K)
    linarith
  have i₁ := mul_le_mul_of_nonneg_right hc₁ (by positivity : 0 ≤ ‖B‖ * ‖U₂‖ * n ^ 2)
  have i₂ := mul_le_mul_of_nonneg_right hc₂ (by positivity : 0 ≤ d * ‖U₁‖ * n ^ 2)
  have i₃ := mul_le_mul_of_nonneg_right hc₃ (by positivity : 0 ≤ ‖B‖ * ‖U₁‖ * n ^ 2)
  have a₁ := (abs_le.mp hT₁).1
  have a₂ := (abs_le.mp hT₂).2
  rw [map_add, map_add] at a₂ ⊢
  linarith

end TauCeti

end
