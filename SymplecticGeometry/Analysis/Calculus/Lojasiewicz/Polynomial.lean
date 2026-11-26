/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
import SymplecticGeometry.Analysis.Calculus.Gradient.MvPolynomial
import Mathlib.Analysis.Calculus.Deriv.Prod
import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.Choice
import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.DerivGrowth
import SymplecticGeometry.Topology.Algebra.MvPolynomial
import TauCeti.Analysis.MvPolynomial.Jacobian
import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.Differentiable

/-!
# The Łojasiewicz gradient inequality for real polynomials

For a real polynomial `P` on Euclidean space `EuclideanSpace ℝ ι` and a point `x₀`, there are an
exponent `θ ∈ [1/2, 1)` and a constant `c > 0` such that `|P x - P x₀| ^ θ ≤ c * ‖∇P x‖` for
all `x` near `x₀` (`MvPolynomial.exists_lojasiewicz_gradient`). The norm of the gradient is
read off from the formal partial derivatives of `P` by `MvPolynomial.norm_gradient_eval`.

## Proof

We prove the bound where `P x > P x₀`; applied to `-P` it gives the bound where `P x < P x₀`.
Let `B` be the closed unit ball around `x₀` for the sup norm on `ι → ℝ`, and `Q = ∑ i, (∂ᵢ P)²`.
For each level `t > 0` that `P - P x₀` takes on `B`, the points of `B` on the level set
`P - P x₀ = t` at which `Q` is smallest form a semialgebraic family over `t`, and every such
fiber is nonempty, by the intermediate value theorem and compactness. Semialgebraic choice
(`TauCeti.IsSemialgebraic.exists_isSemialgebraicOn_sumElim_mem`) gives a semialgebraic curve
`t ↦ x t` of such minimizers. Its coordinates are bounded, so near `0⁺` they are differentiable
and their derivatives are `O(t ^ (q - 1))` for some `q > 0`
(`TauCeti.IsSemialgebraicOn.exists_pos_differentiableOn_Ioo`,
`TauCeti.IsSemialgebraicOn.exists_abs_deriv_le_mul_rpow`). Differentiating `P (x t) - P x₀ = t`
gives `1 = ∑ i, ∂ᵢ P (x t) * x'ᵢ t`, hence `t ^ (1 - q) ≤ L * √(Q (x t))`, and the minimality of
`x t` carries this bound to every point of `B` on the same level set. The exponent is
`θ = max (1/2) (1 - q)`, over both signs.

This is the curve-selection proof of the gradient inequality for definable functions, specialized
to polynomials.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, CNRS, Paris, 1963, 87–89.
* K. Kurdyka, *On gradients of functions definable in o-minimal structures*, Ann. Inst. Fourier
  (Grenoble) 48 (1998), 769–783.
* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Sections 2.5–2.6.
-/

public section

open Filter Set Topology TauCeti

namespace MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- The sum of the squares of the formal partial derivatives of `P`. -/
local notation "gsq" P => ∑ i, pderiv i P ^ 2

/-- The pairs `(t, x)` such that `x` lies in the closed unit ball around `a` (for the sup norm),
on the level set `P x - P a = t`, and minimizes `∑ i, (∂ᵢ P)²` over the points of that level set
in the ball. -/
private def minSet (P : MvPolynomial ι ℝ) (a : ι → ℝ) : Set (Fin 1 ⊕ ι → ℝ) :=
  {z | eval (z ∘ Sum.inr) P - eval a P = z (Sum.inl 0) ∧ dist (z ∘ Sum.inr) a ≤ 1 ∧
    ∀ w : ι → ℝ, eval w P - eval a P = z (Sum.inl 0) → dist w a ≤ 1 →
      eval (z ∘ Sum.inr) (gsq P) ≤ eval w (gsq P)}

/-- The family `minSet P a` is semialgebraic: it is cut out by polynomial conditions and one
universal quantifier over the points `w`. -/
private theorem isSemialgebraic_minSet (P : MvPolynomial ι ℝ) (a : ι → ℝ) :
    IsSemialgebraic (minSet P a) := by
  classical
  let A := {u : (Fin 1 ⊕ ι) ⊕ ι → ℝ | eval u (rename (Sum.inl ∘ Sum.inr) P - C (eval a P)) =
    eval u (X (Sum.inl (Sum.inl 0)))}
  let B := {u : (Fin 1 ⊕ ι) ⊕ ι → ℝ |
    dist (fun i ↦ eval u (X (Sum.inl (Sum.inr i)))) (fun i ↦ eval u (C (a i))) ≤ eval u 1}
  let A' := {u : (Fin 1 ⊕ ι) ⊕ ι → ℝ | eval u (rename Sum.inr P - C (eval a P)) =
    eval u (X (Sum.inl (Sum.inl 0)))}
  let B' := {u : (Fin 1 ⊕ ι) ⊕ ι → ℝ |
    dist (fun i ↦ eval u (X (Sum.inr i))) (fun i ↦ eval u (C (a i))) ≤ eval u 1}
  let G := {u : (Fin 1 ⊕ ι) ⊕ ι → ℝ |
    eval u (rename (Sum.inl ∘ Sum.inr) (gsq P)) ≤ eval u (rename Sum.inr (gsq P))}
  have hT : IsSemialgebraic (A ∩ B ∩ (A'ᶜ ∪ B'ᶜ ∪ G)) :=
    ((isSemialgebraic_eval_eq _ _).inter (isSemialgebraic_setOf_dist_eval_le _ _ _)).inter
      (((isSemialgebraic_eval_eq _ _).compl.union
        (isSemialgebraic_setOf_dist_eval_le _ _ _).compl).union (isSemialgebraic_eval_le _ _))
  convert hT.setOf_forall_sumElim using 1
  ext z
  simp only [minSet, Function.comp_def, Fin.isValue, map_sum, map_pow, mem_ofPred_eq, map_sub,
    eval_rename, eval_C, eval_X, map_one, mem_inter_iff, Sum.elim_inl, mem_union, mem_compl_iff,
    Sum.elim_inr, not_le, or_iff_not_imp_left, Decidable.not_not, not_imp, not_lt, and_imp, A, B,
    A', B', G]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ w ↦ ⟨⟨h₁, h₂⟩, h₃ w⟩,
    fun h ↦ ⟨(h 0).1.1, (h 0).1.2, fun w ↦ (h w).2⟩⟩

/-- Every value `t ∈ [0, P y - P a]`, for `y` in the closed unit ball around `a`, is a level
with a minimizer in `minSet P a`. -/
private theorem exists_sumElim_mem_minSet (P : MvPolynomial ι ℝ) (a y : ι → ℝ)
    (hy : y ∈ Metric.closedBall a 1) {t : ℝ} (ht : t ∈ Icc 0 (eval y P - eval a P)) :
    ∃ x, Sum.elim ![t] x ∈ minSet P a := by
  -- A point of the level set on the segment from `a` to `y`.
  have hc : Continuous fun s : ℝ ↦ eval (a + s • (y - a)) P - eval a P :=
    by fun_prop
  obtain ⟨s, hs, hst⟩ := intermediate_value_Icc zero_le_one hc.continuousOn (by simpa using ht)
  set K := {w : ι → ℝ | eval w P - eval a P = t} ∩ Metric.closedBall a 1
  have hK : IsCompact K := (isCompact_closedBall a 1).inter_left
    (isClosed_eq ((continuous_eval P).sub continuous_const) continuous_const)
  have hne : K.Nonempty := ⟨a + s • (y - a), hst,
    (convex_closedBall a 1).add_smul_sub_mem (Metric.mem_closedBall_self zero_le_one) hy hs⟩
  obtain ⟨x, hxK, hmin⟩ := hK.exists_isMinOn hne (continuous_eval (gsq P)).continuousOn
  refine ⟨x, ?_, ?_, fun w hw₁ hw₂ ↦ ?_⟩
  · simpa [Function.comp_def] using hxK.1
  · simpa [Function.comp_def] using hxK.2
  · simpa [Function.comp_def] using
      hmin (show w ∈ K from ⟨by simpa using hw₁, Metric.mem_closedBall.2 hw₂⟩)

/-- A curve `t ↦ x t` of minimizers in `minSet P a` over the levels `t ∈ (0, δ)`, whose
coordinates are differentiable near `0⁺` with `∑ i, |x'ᵢ t| ≤ L * t ^ (q - 1)`. -/
private theorem exists_curve_minSet (P : MvPolynomial ι ℝ) (a : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hD : ∀ t ∈ Ioo 0 δ, ∃ y, Sum.elim ![t] y ∈ minSet P a) :
    ∃ x : ℝ → ι → ℝ, (∀ t ∈ Ioo 0 δ, Sum.elim ![t] (x t) ∈ minSet P a) ∧
      ∃ q : ℝ, 0 < q ∧ ∃ L : ℝ, 0 < L ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (∀ i, DifferentiableAt ℝ (fun s ↦ x s i) t) ∧
        ∑ i, |deriv (fun s ↦ x s i) t| ≤ L * t ^ (q - 1) := by
  obtain ⟨f, hf, hfS⟩ := (isSemialgebraic_minSet P a).exists_isSemialgebraicOn_sumElim_mem
  have hD' : ∀ t ∈ Ioo 0 δ, ![t] ∈ {x | ∃ y, Sum.elim x y ∈ minSet P a} :=
    fun t ht ↦ mem_ofPred.2 (hD t ht)
  have hxS (t : ℝ) (ht : t ∈ Ioo 0 δ) : Sum.elim ![t] (f ![t]) ∈ minSet P a := hfS _ (hD' t ht)
  have hcoord (i : ι) := (isSemialgebraicOn_pi_iff.1 hf).2 i
  have hbound (i : ι) (t : ℝ) (ht : t ∈ Ioo 0 δ) : |f ![t] i| ≤ |a i| + 1 := by
    have h := (hxS t ht).2.1
    simp only [Sum.elim_comp_inr] at h
    have := (abs_sub_abs_le_abs_sub _ _).trans
      ((Real.dist_eq _ _).symm.le.trans ((dist_le_pi_dist _ _ i).trans h))
    linarith
  choose p hp C ε hε hC using fun i ↦
    (hcoord i).exists_abs_deriv_le_mul_rpow hδ hD' (hbound i)
  choose ε' hε' hdiff _ using fun i ↦ (hcoord i).exists_pos_differentiableOn_Ioo hδ hD'
  -- A common exponent `q ≤ p i`.
  have hqev : ∀ᶠ q in 𝓝[>] (0 : ℝ), (∀ i, q < p i) ∧ q ∈ Ioi 0 :=
    (eventually_all.2 fun i ↦ eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (hp i))).and self_mem_nhdsWithin
  obtain ⟨q, hqp, hq⟩ := hqev.exists
  refine ⟨fun t ↦ f ![t], hxS, q, hq, ∑ i, |C i| + 1, by positivity, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT one_pos, eventually_all.2 fun i ↦ Ioo_mem_nhdsGT (hε' i),
    eventually_all.2 fun i ↦ Ioo_mem_nhdsGT (hε i)] with t ht ht' ht''
  refine ⟨fun i ↦ (hdiff i t (ht' i)).differentiableAt (Ioo_mem_nhds (ht' i).1 (ht' i).2), ?_⟩
  have hpow (i : ι) : t ^ (p i - 1) ≤ t ^ (q - 1) :=
    Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le (by linarith [hqp i])
  calc ∑ i, |deriv (fun s ↦ f ![s] i) t| ≤ ∑ i, |C i| * t ^ (q - 1) :=
        Finset.sum_le_sum fun i _ ↦ (hC i t (ht'' i)).trans
          (mul_le_mul (le_abs_self _) (hpow i) (Real.rpow_nonneg ht.1.le _) (abs_nonneg _))
    _ ≤ (∑ i, |C i| + 1) * t ^ (q - 1) := by
        rw [← Finset.sum_mul]
        have := Real.rpow_nonneg ht.1.le (q - 1)
        nlinarith

/-- Along a curve `t ↦ x t` of minimizers in `minSet P a`, at a level `t` where the curve is
differentiable with `∑ i, |x'ᵢ t| ≤ M`, differentiating `P (x s) - P a = s` gives
`1 ≤ √(∑ i, (∂ᵢ P)²) (x t) * M`. -/
private theorem one_le_sqrt_mul_of_minSet (P : MvPolynomial ι ℝ) (a : ι → ℝ) {δ t M : ℝ}
    {x : ℝ → ι → ℝ} (hx : ∀ s ∈ Ioo 0 δ, Sum.elim ![s] (x s) ∈ minSet P a) (ht : t ∈ Ioo 0 δ)
    (hdx : ∀ i, DifferentiableAt ℝ (fun s ↦ x s i) t)
    (hM : ∑ i, |deriv (fun s ↦ x s i) t| ≤ M) :
    1 ≤ √(eval (x t) (gsq P)) * M := by
  have hderiv : HasDerivAt x (fun i ↦ deriv (fun s ↦ x s i) t) t :=
    hasDerivAt_pi.2 fun i ↦ (hdx i).hasDerivAt
  have h1 : 1 = ∑ i, eval (x t) (pderiv i P) * deriv (fun s ↦ x s i) t := by
    have hcomp := (P.hasFDerivAt_eval (x t)).comp_hasDerivAt t hderiv
    have hid : HasDerivAt (fun s ↦ eval (x s) P) 1 t := by
      refine ((hasDerivAt_id t).add_const (eval a P)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      have := (hx s hs).1
      simp only [Sum.elim_comp_inr, Sum.elim_inl, Matrix.cons_val_fin_one] at this
      rw [id_eq]
      linarith
    simpa using hid.unique hcomp
  have hpd (i : ι) : |eval (x t) (pderiv i P)| ≤ √(eval (x t) (gsq P)) := by
    refine Real.abs_le_sqrt ?_
    simpa using Finset.single_le_sum (f := fun j ↦ eval (x t) (pderiv j P) ^ 2)
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
  calc (1 : ℝ) = |∑ i, eval (x t) (pderiv i P) * deriv (fun s ↦ x s i) t| := by
        rw [← h1, abs_one]
    _ ≤ ∑ i, |eval (x t) (pderiv i P) * deriv (fun s ↦ x s i) t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, √(eval (x t) (gsq P)) * |deriv (fun s ↦ x s i) t| :=
        Finset.sum_le_sum fun i _ ↦ by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hpd i) (abs_nonneg _)
    _ ≤ √(eval (x t) (gsq P)) * M := by
        rw [← Finset.mul_sum]
        gcongr

/-- The one-sided form of the inequality: near `a`, where `P x > P a`, the value
`(P x - P a) ^ (1 - p)` is at most `K` times the square root of `∑ i, (∂ᵢ P x)²`. -/
private theorem exists_rpow_le_sqrt_of_pos (P : MvPolynomial ι ℝ) (a : ι → ℝ) :
    ∃ p : ℝ, 0 < p ∧ ∃ K : ℝ, 0 < K ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ y ∈ Metric.closedBall a 1, 0 < eval y P - eval a P → eval y P - eval a P < ε →
        (eval y P - eval a P) ^ (1 - p) ≤ K * √(eval y (gsq P)) := by
  by_cases h : ∃ y ∈ Metric.closedBall a 1, 0 < eval y P - eval a P
  swap
  · push Not at h
    exact ⟨1, one_pos, 1, one_pos, 1, one_pos, le_rfl, fun y hy hpos _ ↦
      absurd hpos (h y hy).not_gt⟩
  obtain ⟨y₀, hy₀, hδ⟩ := h
  obtain ⟨x, hxS, q, hq, L, hL, hev⟩ := exists_curve_minSet P a hδ fun t ht ↦
    exists_sumElim_mem_minSet P a y₀ hy₀ ⟨ht.1.le, ht.2.le⟩
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hev.and (Ioo_mem_nhdsGT hδ))
  refine ⟨q, hq, L, hL, min ε₀ 1, lt_min hε₀ one_pos, min_le_right _ _,
    fun y hy hpos hlt ↦ ?_⟩
  set t := eval y P - eval a P
  obtain ⟨⟨hdx, hM⟩, htδ⟩ := hsub ⟨hpos, hlt.trans_le (min_le_left _ _)⟩
  have hmain := one_le_sqrt_mul_of_minSet P a hxS htδ hdx hM
  have hmin := (hxS t htδ).2.2 y rfl (Metric.mem_closedBall.1 hy)
  have htq : t ^ (1 - q) = (t ^ (q - 1))⁻¹ := by
    rw [← Real.rpow_neg hpos.le, neg_sub]
  rw [htq, inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hpos _)]
  calc (1 : ℝ) ≤ √(eval (x t) (gsq P)) * (L * t ^ (q - 1)) := hmain
    _ ≤ √(eval y (gsq P)) * (L * t ^ (q - 1)) := by
      gcongr
      simpa [Function.comp_def] using hmin
    _ = _ := by ring

/-- **The Łojasiewicz gradient inequality** for a real polynomial `P` on `ℝⁿ`: near every
point `x₀` there are an exponent `θ ∈ [1/2, 1)` and a constant `c > 0` with
`|P x - P x₀| ^ θ ≤ c * ‖∇P x‖`. -/
theorem exists_lojasiewicz_gradient (P : MvPolynomial ι ℝ) (x₀ : EuclideanSpace ℝ ι) :
    ∃ θ ∈ Ico (1 / 2 : ℝ) 1, ∃ c > 0, ∀ᶠ x : EuclideanSpace ℝ ι in 𝓝 x₀,
      |eval x P - eval x₀ P| ^ θ ≤ c * ‖gradient (fun y : EuclideanSpace ℝ ι ↦ eval y P) x‖ := by
  obtain ⟨p₁, hp₁, K₁, hK₁, ε₁, hε₁, hε₁1, h₁⟩ := exists_rpow_le_sqrt_of_pos P x₀
  obtain ⟨p₂, hp₂, K₂, -, ε₂, hε₂, -, h₂⟩ := exists_rpow_le_sqrt_of_pos (-P) x₀
  set θ := max (1 / 2) (max (1 - p₁) (1 - p₂))
  have hθ : 0 < θ := lt_max_of_lt_left one_half_pos
  refine ⟨θ, ⟨le_max_left _ _, max_lt (by norm_num) (max_lt (by linarith) (by linarith))⟩,
    max K₁ K₂, lt_max_of_lt_left hK₁, ?_⟩
  have hc : Continuous fun y : EuclideanSpace ℝ ι ↦ eval y P - eval x₀ P :=
    by fun_prop
  filter_upwards [(PiLp.continuous_ofLp 2 _).continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ one_pos),
    (hc.abs.continuousAt (x := x₀)).eventually_lt (continuousAt_const (y := min ε₁ ε₂))
      (by simpa using lt_min hε₁ hε₂)]
    with x hball hxε
  have hsq₁ : eval x (gsq P) = ∑ i, eval x (pderiv i P) ^ 2 := by simp
  have hsq₂ : eval x (gsq (-P)) = ∑ i, eval x (pderiv i P) ^ 2 := by simp
  rw [norm_gradient_eval]
  set v := eval x P - eval x₀ P
  have hv1 : |v| < 1 := hxε.trans_le ((min_le_left _ _).trans hε₁1)
  -- On `(0, 1)`, a larger exponent gives a smaller power.
  have hpow {r : ℝ} (hr : r ≤ θ) (hv : 0 < |v|) : |v| ^ θ ≤ |v| ^ r :=
    Real.rpow_le_rpow_of_exponent_ge hv hv1.le hr
  rcases lt_trichotomy v 0 with hv | hv | hv
  · have h := h₂ x hball (by simp; linarith) (by simp; linarith [neg_abs_le v,
      (lt_min_iff.1 hxε).2])
    rw [hsq₂] at h
    have hv' : |v| = eval x (-P) - eval x₀ (-P) := by simp [abs_of_neg hv, v]; ring
    rw [← hv'] at h
    calc |v| ^ θ ≤ |v| ^ (1 - p₂) := hpow ((le_max_right _ _).trans (le_max_right _ _))
          (abs_pos.2 hv.ne)
      _ ≤ K₂ * √(∑ i, eval x (pderiv i P) ^ 2) := h
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · rw [hv, abs_zero, Real.zero_rpow hθ.ne']
    positivity
  · have h : v ^ (1 - p₁) ≤ K₁ * √(eval x (gsq P)) :=
      h₁ x hball hv (by linarith [le_abs_self v, (lt_min_iff.1 hxε).1])
    rw [← abs_of_pos hv, hsq₁] at h
    calc |v| ^ θ ≤ |v| ^ (1 - p₁) := hpow ((le_max_left _ _).trans (le_max_right _ _))
          (abs_pos.2 hv.ne')
      _ ≤ K₁ * √(∑ i, eval x (pderiv i P) ^ 2) := h
      _ ≤ _ := by gcongr; exact le_max_left _ _

end MvPolynomial
