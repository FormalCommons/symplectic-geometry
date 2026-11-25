/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import SymplecticGeometry.Analysis.Complex.CauchyPompeiuDisc
import SymplecticGeometry.Analysis.Complex.Polydisc.CoordCauchyIntegral
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic

/-!
# Holomorphic approximation on polydiscs

On `ι → ℂ`, for a finite type `ι`, the balls of the sup norm are the polydiscs with equal radii.
This file shows that a function that is `C¹` near the closed polydisc `closedBall c ρ` and whose
conjugate Wirtinger derivatives `∂f/∂(conj z_j)` in the coordinate directions are bounded by `ε`
there is, on the closed polydisc of half the radius, within `4 (2 ^ n - 1) ρ ε` of a function that
is holomorphic on the open polydisc `ball c ρ`, where `n` is the number of coordinates.

## Main result

* `SymplecticGeometry.exists_differentiableOn_dist_le`: the approximation above.

## Proof

The holomorphic function is `h = C_{i_n} ⋯ C_{i_1} f`, where `i_1, …, i_n` lists the coordinates
and `C_i` is the Cauchy integral `SymplecticGeometry.coordCauchyIntegral` over the circle of radius
`ρ` in the `i`-th coordinate; this is the Cauchy integral of `f` over the distinguished boundary
of the polydisc. Write `g_k = C_{i_k} ⋯ C_{i_1} f`. Then:

* `g_k` is `C¹` wherever the coordinates `i_1, …, i_k` lie in the open disc and the others in the
  closed one (`SymplecticGeometry.contDiffAt_coordCauchyIntegral`);
* since `C_i` commutes with `∂/∂(conj z_j)` for `j ≠ i`
  (`SymplecticGeometry.conjWirtingerDeriv_coordCauchyIntegral_single`) and `C_i g` is holomorphic
  in `z_i` (`SymplecticGeometry.conjWirtingerDeriv_coordCauchyIntegral_single_self`), the function
  `h` has all its conjugate Wirtinger derivatives zero on the open polydisc, so it is holomorphic
  there (`TauCeti.differentiableAt_iff_forall_conjWirtingerDeriv_apply_single_eq_zero`);
* by the Cauchy–Pompeiu formula on a disc in the coordinate `i_{k+1}`
  (`SymplecticGeometry.norm_sub_two_pi_I_inv_smul_circleIntegral_le`),
  `‖g_k - g_{k+1}‖ ≤ 4 ρ sup ‖∂g_k/∂(conj z_{i_{k+1}})‖`, and
  `∂g_k/∂(conj z_{i_{k+1}}) = C_{i_k} ⋯ C_{i_1} ∂f/∂(conj z_{i_{k+1}})`;
* each `C_i` at most doubles the sup norm at points whose `i`-th coordinate lies in the disc of
  half the radius (`SymplecticGeometry.norm_coordCauchyIntegral_le`), so on the polydisc of half
  the radius `‖g_k - g_{k+1}‖ ≤ 4 ρ 2 ^ k ε`, and summing over `k` gives the bound.

The several-variable `∂̄`-equation is not needed: only first derivatives of `f` enter.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Chapter II (the Cauchy integral formula on polydiscs).
* [D. Auroux, *Symplectic 4-manifolds as branched coverings of ℂℙ²*][Auroux2000], Proposition 2
  (where the approximation by holomorphic functions on polydiscs is used).
-/

public section

open Function Metric TauCeti

namespace SymplecticGeometry

variable {ι : Type*} [DecidableEq ι] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℂ F] {c : ι → ℂ} {ρ : ℝ}

/-- The coordinate Cauchy integrals in the coordinates of `l`, applied to `f` from the last one
of `l` to the first. -/
private noncomputable def iterCauchy (c : ι → ℂ) (ρ : ℝ) (l : List ι) (f : (ι → ℂ) → F) :
    (ι → ℂ) → F :=
  l.foldr (fun i g ↦ coordCauchyIntegral i c ρ g) f

private theorem iterCauchy_nil (f : (ι → ℂ) → F) : iterCauchy c ρ [] f = f :=
  (rfl)

private theorem iterCauchy_cons (a : ι) (l : List ι) (f : (ι → ℂ) → F) :
    iterCauchy c ρ (a :: l) f = coordCauchyIntegral a c ρ (iterCauchy c ρ l f) :=
  (rfl)

/-- Changing the coordinate `a` keeps a property of the coordinates of `l` when `a ∉ l`. -/
private theorem forall_mem_update_of_notMem {R : ℝ → ℝ → Prop} {r : ℝ} {a : ι}
    {l : List ι} (ha : a ∉ l) {w : ι → ℂ} (h : ∀ k ∈ a :: l, R ‖w k - c k‖ r) (ζ : ℂ) :
    ∀ k ∈ l, R ‖update w a ζ k - c k‖ r := fun k hk ↦ by
  rw [update_of_ne (ne_of_mem_of_not_mem hk ha)]
  exact h k (List.mem_cons_of_mem a hk)

/-- Changing one coordinate to a point of the closed disc stays in the closed polydisc. -/
private theorem norm_update_sub_le {w : ι → ℂ} (hw : ∀ k, ‖w k - c k‖ ≤ ρ) {a : ι} {ζ : ℂ}
    (hζ : ‖ζ - c a‖ ≤ ρ) (k : ι) : ‖update w a ζ k - c k‖ ≤ ρ := by
  rcases eq_or_ne k a with rfl | hk
  · simpa using hζ
  · simpa [hk] using hw k

variable [Fintype ι] {f : (ι → ℂ) → F}

/-- `C_{l_1} ⋯ C_{l_m} f` is `C¹` at the points of the closed polydisc whose coordinates in `l`
lie in the open disc. -/
private theorem contDiffAt_iterCauchy (hf : ∀ y, (∀ k, ‖y k - c k‖ ≤ ρ) → ContDiffAt ℝ 1 f y)
    {l : List ι} (hl : l.Nodup) {w : ι → ℂ} (hw : ∀ k, ‖w k - c k‖ ≤ ρ)
    (hlw : ∀ k ∈ l, ‖w k - c k‖ < ρ) : ContDiffAt ℝ 1 (iterCauchy c ρ l f) w := by
  induction l generalizing w with
  | nil => exact hf w hw
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    exact contDiffAt_coordCauchyIntegral (mem_ball_iff_norm.2 (hlw a List.mem_cons_self))
      fun ζ hζ ↦ ih hl.2 (norm_update_sub_le hw (mem_sphere_iff_norm.1 hζ).le)
        (forall_mem_update_of_notMem hl.1 hlw ζ)

/-- For `j ∉ l`, `∂/∂(conj z_j)` commutes with `C_{l_1} ⋯ C_{l_m}`. -/
private theorem conjWirtingerDeriv_iterCauchy_of_notMem
    (hf : ∀ y, (∀ k, ‖y k - c k‖ ≤ ρ) → ContDiffAt ℝ 1 f y) {l : List ι} (hl : l.Nodup)
    {j : ι} (hj : j ∉ l) {w : ι → ℂ} (hw : ∀ k, ‖w k - c k‖ ≤ ρ)
    (hlw : ∀ k ∈ l, ‖w k - c k‖ < ρ) :
    conjWirtingerDeriv (iterCauchy c ρ l f) w (Pi.single j 1) =
      iterCauchy c ρ l (fun y ↦ conjWirtingerDeriv f y (Pi.single j 1)) w := by
  induction l generalizing w with
  | nil => rfl
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.mem_cons, not_or] at hj
    have hwa := hlw a List.mem_cons_self
    rw [iterCauchy_cons, iterCauchy_cons, conjWirtingerDeriv_coordCauchyIntegral_single
      (mem_ball_iff_norm.2 hwa) (fun ζ hζ ↦ contDiffAt_iterCauchy hf hl.2
        (norm_update_sub_le hw (mem_sphere_iff_norm.1 hζ).le)
        (forall_mem_update_of_notMem hl.1 hlw ζ)) hj.1]
    exact coordCauchyIntegral_congr ((norm_nonneg _).trans hwa.le) fun ζ hζ ↦ ih hl.2 hj.2
      (norm_update_sub_le hw (mem_sphere_iff_norm.1 hζ).le)
      (forall_mem_update_of_notMem hl.1 hlw ζ)

/-- For `j ∈ l`, `C_{l_1} ⋯ C_{l_m} f` is holomorphic in `z_j` at the points of the closed
polydisc whose coordinates in `l` lie in the open disc. -/
private theorem conjWirtingerDeriv_iterCauchy_of_mem
    (hf : ∀ y, (∀ k, ‖y k - c k‖ ≤ ρ) → ContDiffAt ℝ 1 f y) {l : List ι} (hl : l.Nodup)
    {j : ι} (hj : j ∈ l) {w : ι → ℂ} (hw : ∀ k, ‖w k - c k‖ ≤ ρ)
    (hlw : ∀ k ∈ l, ‖w k - c k‖ < ρ) :
    conjWirtingerDeriv (iterCauchy c ρ l f) w (Pi.single j 1) = 0 := by
  induction l generalizing w with
  | nil => simp at hj
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have hwa := hlw a List.mem_cons_self
    have hC : ∀ ζ ∈ sphere (c a) ρ, ContDiffAt ℝ 1 (iterCauchy c ρ l f) (update w a ζ) :=
      fun ζ hζ ↦ contDiffAt_iterCauchy hf hl.2
        (norm_update_sub_le hw (mem_sphere_iff_norm.1 hζ).le)
        (forall_mem_update_of_notMem hl.1 hlw ζ)
    rw [iterCauchy_cons]
    rcases eq_or_ne j a with rfl | hja
    · exact conjWirtingerDeriv_coordCauchyIntegral_single_self (mem_ball_iff_norm.2 hwa) hC
    have hjl : j ∈ l := (List.mem_cons.1 hj).resolve_left hja
    rw [conjWirtingerDeriv_coordCauchyIntegral_single (mem_ball_iff_norm.2 hwa) hC hja,
      coordCauchyIntegral_congr (g := 0) ((norm_nonneg _).trans hwa.le) fun ζ hζ ↦ ih hl.2 hjl
        (norm_update_sub_le hw (mem_sphere_iff_norm.1 hζ).le)
        (forall_mem_update_of_notMem hl.1 hlw ζ),
      coordCauchyIntegral_zero, Pi.zero_apply]

omit [Fintype ι] in
/-- Each coordinate Cauchy integral at most doubles the sup norm on the closed polydisc, at the
points whose coordinates in `l` lie in the disc of half the radius. -/
private theorem norm_iterCauchy_le {g : (ι → ℂ) → F} {M : ℝ}
    (hg : ∀ y, (∀ k, ‖y k - c k‖ ≤ ρ) → ‖g y‖ ≤ M) {l : List ι} (hl : l.Nodup) {w : ι → ℂ}
    (hw : ∀ k, ‖w k - c k‖ ≤ ρ) (hlw : ∀ k ∈ l, ‖w k - c k‖ ≤ ρ / 2) :
    ‖iterCauchy c ρ l g w‖ ≤ 2 ^ l.length * M := by
  induction l generalizing w with
  | nil => simpa [iterCauchy_nil] using hg w hw
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [iterCauchy_cons, List.length_cons, pow_succ, mul_comm _ (2 : ℝ), mul_assoc]
    exact norm_coordCauchyIntegral_le (hlw a List.mem_cons_self) fun ζ hζ ↦ ih hl.2
      (norm_update_sub_le hw (mem_sphere_iff_norm.1 hζ).le)
      (forall_mem_update_of_notMem hl.1 hlw ζ)

variable [CompleteSpace F]

/-- The estimate, by the Cauchy–Pompeiu formula in each coordinate of `l` in turn. -/
private theorem norm_sub_iterCauchy_le
    (hf : ∀ y, (∀ k, ‖y k - c k‖ ≤ ρ) → ContDiffAt ℝ 1 f y) {ε : ℝ}
    (hε : ∀ y, (∀ k, ‖y k - c k‖ ≤ ρ) → ∀ j, ‖conjWirtingerDeriv f y (Pi.single j 1)‖ ≤ ε)
    (hρ : 0 < ρ) {l : List ι} (hl : l.Nodup) {w : ι → ℂ} (hw : ∀ k, ‖w k - c k‖ ≤ ρ)
    (hlw : ∀ k ∈ l, ‖w k - c k‖ ≤ ρ / 2) :
    ‖f w - iterCauchy c ρ l f w‖ ≤ 4 * (2 ^ l.length - 1) * ρ * ε := by
  induction l generalizing w with
  | nil => simp [iterCauchy_nil]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have hlt : ∀ k ∈ l, ‖w k - c k‖ < ρ := fun k hk ↦
      (hlw k (List.mem_cons_of_mem a hk)).trans_lt (by linarith)
    -- The Cauchy–Pompeiu formula in the coordinate `a`, for `G = C_{l_1} ⋯ C_{l_m} f`
    -- restricted to the complex line through `w` along that coordinate.
    set G := iterCauchy c ρ l f
    have hupd (ζ : ℂ) (hζ : ‖ζ - c a‖ ≤ ρ) : ContDiffAt ℝ 1 G (update w a ζ) :=
      contDiffAt_iterCauchy hf hl.2 (norm_update_sub_le hw hζ)
        (forall_mem_update_of_notMem hl.1 (R := (· < ·))
          (fun k hk ↦ by
            rcases List.mem_cons.1 hk with rfl | hk
            · exact (hlw k List.mem_cons_self).trans_lt (by linarith)
            · exact hlt k hk) ζ)
    have hψ : ∀ ζ ∈ closedBall (c a) ρ, ContDiffAt ℝ 1 (fun ζ ↦ G (update w a ζ)) ζ :=
      fun ζ hζ ↦ (hupd ζ (mem_closedBall_iff_norm.1 hζ)).comp ζ
        (contDiff_update 1 w a).contDiffAt
    have hdbar : ∀ ζ ∈ ball (c a) ρ,
        ‖conjWirtingerDeriv (fun ζ ↦ G (update w a ζ)) ζ 1‖ ≤ 2 ^ l.length * ε := by
      intro ζ hζ
      have hζ' := (mem_ball_iff_norm.1 hζ).le
      rw [conjWirtingerDeriv_update_apply_one ((hupd ζ hζ').differentiableAt one_ne_zero)]
      rw [conjWirtingerDeriv_iterCauchy_of_notMem hf hl.2 hl.1 (norm_update_sub_le hw hζ')
        (forall_mem_update_of_notMem hl.1 (R := (· < ·))
          (fun k hk ↦ by
            rcases List.mem_cons.1 hk with rfl | hk
            · exact (hlw k List.mem_cons_self).trans_lt (by linarith)
            · exact hlt k hk) ζ)]
      exact norm_iterCauchy_le (fun y hy ↦ hε y hy a) hl.2 (norm_update_sub_le hw hζ')
        (forall_mem_update_of_notMem hl.1 hlw ζ)
    have hwa : w a ∈ ball (c a) ρ :=
      mem_ball_iff_norm.2 ((hlw a List.mem_cons_self).trans_lt (by linarith))
    have h₂ : ‖G w - coordCauchyIntegral a c ρ G w‖ ≤ 4 * ρ * (2 ^ l.length * ε) := by
      simpa only [update_eq_self, coordCauchyIntegral_def] using
        norm_sub_two_pi_I_inv_smul_circleIntegral_le hψ hwa hdbar
    have h₁ := ih hl.2 hw fun k hk ↦ hlw k (List.mem_cons_of_mem a hk)
    rw [iterCauchy_cons, List.length_cons]
    refine (norm_sub_le_norm_sub_add_norm_sub _ (G w) _).trans ((add_le_add h₁ h₂).trans_eq ?_)
    ring

/-- **Holomorphic approximation on polydiscs.** Let `f : (ι → ℂ) → F` be real `C¹` at every point
of the closed polydisc `closedBall c ρ` of `ι → ℂ`, for a finite type `ι`, with conjugate
Wirtinger derivatives `‖∂f/∂(conj z_j)‖ ≤ ε` there for every coordinate `j`. Then there is a
function `h`, holomorphic on the open polydisc `ball c ρ`, with `‖f z - h z‖ ≤ 4 (2 ^ n - 1) ρ ε`
on the closed polydisc of half the radius, where `n` is the number of coordinates. -/
theorem exists_differentiableOn_dist_le {ε : ℝ} (hf : ∀ z ∈ closedBall c ρ, ContDiffAt ℝ 1 f z)
    (hε : ∀ z ∈ closedBall c ρ, ∀ j, ‖conjWirtingerDeriv f z (Pi.single j 1)‖ ≤ ε) :
    ∃ h : (ι → ℂ) → F, DifferentiableOn ℂ h (ball c ρ) ∧
      ∀ z ∈ closedBall c (ρ / 2), dist (f z) (h z) ≤ 4 * (2 ^ Fintype.card ι - 1) * ρ * ε := by
  rcases lt_trichotomy ρ 0 with hρ | rfl | hρ
  · refine ⟨0, differentiableOn_const 0, fun z hz ↦ ?_⟩
    have := dist_nonneg.trans (mem_closedBall.1 hz)
    linarith
  · refine ⟨fun _ ↦ f c, differentiableOn_const _, fun z hz ↦ ?_⟩
    rw [zero_div, closedBall_zero, Set.mem_singleton_iff] at hz
    simp [hz]
  have hcb : ∀ y, y ∈ closedBall c ρ ↔ ∀ k, ‖y k - c k‖ ≤ ρ := fun y ↦ by
    simp only [mem_closedBall_iff_norm, pi_norm_le_iff_of_nonneg hρ.le, Pi.sub_apply]
  have hf' : ∀ y, (∀ k, ‖y k - c k‖ ≤ ρ) → ContDiffAt ℝ 1 f y := fun y hy ↦ hf y ((hcb y).2 hy)
  have hl := Finset.nodup_toList (Finset.univ : Finset ι)
  refine ⟨iterCauchy c ρ Finset.univ.toList f, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · have hz' : ∀ k, ‖z k - c k‖ < ρ := by
      simpa only [mem_ball_iff_norm, pi_norm_lt_iff hρ, Pi.sub_apply] using hz
    have hC := contDiffAt_iterCauchy hf' hl (fun k ↦ (hz' k).le) fun k _ ↦ hz' k
    refine (((differentiableAt_iff_forall_conjWirtingerDeriv_apply_single_eq_zero
      (hC.differentiableAt one_ne_zero)).2 fun j ↦ ?_)).differentiableWithinAt
    exact conjWirtingerDeriv_iterCauchy_of_mem hf' hl (Finset.mem_toList.2 (Finset.mem_univ j))
      (fun k ↦ (hz' k).le) fun k _ ↦ hz' k
  · have hz' : ∀ k, ‖z k - c k‖ ≤ ρ / 2 := by
      simpa only [mem_closedBall_iff_norm, pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ ρ / 2),
        Pi.sub_apply]
        using hz
    rw [dist_eq_norm, ← Finset.card_univ, ← Finset.length_toList]
    exact norm_sub_iterCauchy_le hf' (fun y hy ↦ hε y ((hcb y).2 hy)) hρ hl
      (fun k ↦ (hz' k).trans (by linarith)) fun k _ ↦ hz' k

end SymplecticGeometry

end
