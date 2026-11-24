/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Polynomial.Puiseux.Laurent.Factorization
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import SymplecticGeometry.Topology.Algebra.Polynomial
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.Topology.Connected.FiniteFamily

/-!
# Growth of a continuous real root branch near `0⁺`

Let `P` be a polynomial whose coefficients are real polynomials in a parameter `t`, with nonzero
discriminant and nonzero constant coefficient (both over `ℝ[X]`). If `g` is continuous on an
interval `(0, ε)` and `g t` is a root of `P (t, ·)` there, then `g` grows like a rational power
of `t`: `g t / t ^ q` tends to a nonzero real number as `t → 0⁺`
(`Polynomial.exists_tendsto_div_rpow_of_continuousOn_isRoot`).

The proof complexifies the coefficients and applies Tau Ceti's nonmonic Puiseux Laurent
factorization `TauCeti.Polynomial.exists_analyticOnNhd_nonmonic_laurent`, with a trivial
parameter space. After the substitution `t = s ^ d!`, `d` the degree, every complex root is
`s ^ e i * w i s` with `w i` continuous and nonzero at `0`. Off `s = 0` the roots are distinct
and continuous, so a continuous real root `g (s ^ d!)` follows a single label `i` on the whole
interval, by Tau Ceti's `TauCeti.eq_of_continuous_mem_range`; then
`g t / t ^ (e i / d!) = w i (t ^ (1 / d!))` tends to `w i 0`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), §4.
* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Sections 2.5–2.6.
-/

public section

open Filter Function Metric Set Topology

namespace Polynomial

/-- The complex Puiseux roots of `P`, along the line of parameters `(0, s)`. -/
private theorem exists_puiseux_roots {P : ℝ[X][X]} (hdiscr : P.discr ≠ 0)
    (hconst : P.coeff 0 ≠ 0) :
    ∃ R > (0 : ℝ), ∃ ρ ω : Fin P.natDegree → ℂ → ℂ, ∃ e : Fin P.natDegree → ℤ,
      (∀ i, ContinuousOn (ρ i) (ball 0 R \ {0})) ∧
      (∀ i, ContinuousAt (ω i) 0 ∧ ω i 0 ≠ 0) ∧
      ∀ s ∈ ball (0 : ℂ) R \ {0}, Injective (fun i ↦ ρ i s) ∧
        (∀ z, ((P.map (mapRingHom (algebraMap ℝ ℂ))).map
          (evalRingHom (s ^ P.natDegree.factorial))).IsRoot z → ∃ i, ρ i s = z) ∧
        ∀ i, ρ i s = s ^ e i * ω i s := by
  set d := P.natDegree
  set Pc := P.map (mapRingHom (algebraMap ℝ ℂ))
  have hinj : Injective (mapRingHom (algebraMap ℝ ℂ)) :=
    map_injective _ (algebraMap ℝ ℂ).injective
  have hP0 : P ≠ 0 := fun h ↦ hconst (by simp [h])
  have hdeg : Pc.natDegree = d := natDegree_map_eq_of_injective hinj P
  have hlc : Pc.leadingCoeff ≠ 0 := by
    rw [leadingCoeff_map_of_injective hinj]
    exact (map_ne_zero_iff _ hinj).2 (leadingCoeff_ne_zero.2 hP0)
  have hc0 : Pc.coeff 0 ≠ 0 := by
    rw [coeff_map]
    exact (map_ne_zero_iff _ hinj).2 hconst
  have hD : Pc.discr ≠ 0 := by
    rw [discr_map_of_natDegree_eq _ hdeg]
    exact (map_ne_zero_iff _ hinj).2 hdiscr
  obtain ⟨a, u, hu, hu0⟩ := exists_eq_X_sub_C_pow_mul_eventually_eval_ne_zero hlc 0
  obtain ⟨c, v, hv, hv0⟩ := exists_eq_X_sub_C_pow_mul_eventually_eval_ne_zero hc0 0
  obtain ⟨k, D, hDk, hD0⟩ := exists_eq_X_sub_C_pow_mul_eventually_eval_ne_zero hD 0
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hu0.and (hv0.and hD0))
  replace hu (z : ℂ) : Pc.leadingCoeff.eval z = z ^ a * u.eval z := by simp [hu]
  replace hv (z : ℂ) : (Pc.coeff 0).eval z = z ^ c * v.eval z := by simp [hv]
  replace hDk (z : ℂ) : Pc.discr.eval z = z ^ k * D.eval z := by simp [hDk]
  replace hu0 (z : ℂ) (hz : z ∈ ball 0 R) : u.eval z ≠ 0 := (hball z hz).1
  replace hv0 (z : ℂ) (hz : z ∈ ball 0 R) : v.eval z ≠ 0 := (hball z hz).2.1
  replace hD0 (z : ℂ) (hz : z ∈ ball 0 R) : D.eval z ≠ 0 := (hball z hz).2.2
  let F : ℂ × ℂ → ℂ[X] := fun b ↦ Pc.map (evalRingHom b.2)
  have hFc (b : ℂ × ℂ) (i : ℕ) : (F b).coeff i = (Pc.coeff i).eval b.2 := by
    simp [F, coeff_map]
  have hlead (b : ℂ × ℂ) : (F b).coeff d = b.2 ^ a * u.eval b.2 := by
    rw [hFc, ← hdeg, coeff_natDegree, hu]
  have hFdeg (b : ℂ × ℂ) (hb : b.2 ∈ ball (0 : ℂ) R \ {0}) : (F b).natDegree = d := by
    rw [← hdeg]
    refine natDegree_map_of_leadingCoeff_ne_zero _ ?_
    rw [coe_evalRingHom, hu]
    exact mul_ne_zero (pow_ne_zero _ hb.2) (hu0 _ hb.1)
  let : ContractibleSpace (ball (0 : ℂ) 1) :=
    (convex_ball _ _).contractibleSpace ⟨_, mem_ball_self one_pos⟩
  let : SimplyConnectedSpace (ball (0 : ℂ) 1) := SimplyConnectedSpace.ofContractible _
  have han (p : ℂ[X]) : AnalyticOnNhd ℂ (fun b : ℂ × ℂ ↦ p.eval b.2) (ball 0 1 ×ˢ ball 0 R) := by
    simpa only [aeval_def, eval₂_eq_eval_map, Algebra.algebraMap_self, map_id] using
      AnalyticOnNhd.aeval_polynomial (A := ℂ) (f := fun b : ℂ × ℂ ↦ b.2)
        (fun _ _ ↦ analyticAt_snd) p
  obtain ⟨R', hR', hfit, r, -, hra, -, hsplit, e, w, -, hw, hw0, hform⟩ :=
    TauCeti.Polynomial.exists_analyticOnNhd_nonmonic_laurent (F := F) (d := d)
      (u := fun b ↦ u.eval b.2) (v := fun b ↦ v.eval b.2) isOpen_ball hR
      (fun i _ ↦ by simpa only [hFc] using han (Pc.coeff i))
      (fun b hb ↦ hFdeg b hb.2)
      (fun b hb ↦ by
        -- `F b` is, by its local definition, `Pc` with coefficients evaluated at `b.2`.
        rw [show F b = Pc.map (evalRingHom b.2) from rfl,
          discr_map_of_natDegree_eq _ ((hFdeg b hb.2).trans hdeg.symm), coe_evalRingHom, hDk]
        exact mul_ne_zero (pow_ne_zero _ hb.2.2) (hD0 _ hb.2.1))
      (han u) (fun b hb ↦ hu0 _ hb.2) (han v) (fun b hb ↦ hv0 _ hb.2)
      (fun b _ ↦ hlead b) (fun b _ ↦ by rw [hFc, ← hv])
  have hmem {s : ℂ} (hs : s ∈ ball (0 : ℂ) R' \ {0}) :
      ((0 : ℂ), s) ∈ ball (0 : ℂ) 1 ×ˢ (ball 0 R' \ {0}) := ⟨mem_ball_self one_pos, hs⟩
  have h0 : ((0 : ℂ), (0 : ℂ)) ∈ ball (0 : ℂ) 1 ×ˢ ball 0 R' :=
    ⟨mem_ball_self one_pos, mem_ball_self hR'⟩
  refine ⟨R', hR', fun i s ↦ r i (0, s), fun i s ↦ w i (0, s), e, fun i s hs ↦ ?_,
    fun i ↦ ⟨((hw i _ h0).continuousAt).comp (Continuous.prodMk_right 0).continuousAt,
      hw0 i _ h0⟩, fun s hs ↦ ⟨(hsplit _ (hmem hs)).1, fun z hz ↦ ?_, hform _ (hmem hs)⟩⟩
  · exact ((hra i _ (hmem hs)).continuousAt.comp
      (Continuous.prodMk_right 0).continuousAt).continuousWithinAt
  · have hsplit' := (hsplit _ (hmem hs)).2
    -- `hz` is the same statement, with the local definition of `F` unfolded.
    have hz' : (F (0, s ^ d.factorial)).IsRoot z := hz
    rw [hsplit', IsRoot, eval_mul, eval_C, eval_prod, mul_eq_zero,
      Finset.prod_eq_zero_iff] at hz'
    rcases hz' with hz' | ⟨i, -, hi⟩
    · exact absurd hz' (by
        rw [hlead]
        exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hs.2))
          (hu0 _ (TauCeti.mapsTo_pow_ball_zero d.factorial_ne_zero hfit hs.1)))
    · exact ⟨i, (by simpa [sub_eq_zero] using hi : z = _).symm⟩

/-- **Growth of a real root branch.** Let `P` be a polynomial whose coefficients are real
polynomials in `t`, with nonzero discriminant and nonzero constant coefficient over `ℝ[X]`. If
`g` is continuous on `(0, ε)` and `g t` is a root of `P (t, ·)` for each `t` there, then there are
a rational `q` and a real `a ≠ 0` with `g t / t ^ q → a` as `t → 0⁺`. -/
theorem exists_tendsto_div_rpow_of_continuousOn_isRoot {P : ℝ[X][X]} (hdiscr : P.discr ≠ 0)
    (hconst : P.coeff 0 ≠ 0) {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (hg : ContinuousOn g (Ioo 0 ε))
    (hroot : ∀ t ∈ Ioo 0 ε, (P.map (evalRingHom t)).IsRoot (g t)) :
    ∃ q : ℚ, ∃ a : ℝ, a ≠ 0 ∧ Tendsto (fun t ↦ g t / t ^ (q : ℝ)) (𝓝[>] 0) (𝓝 a) := by
  obtain ⟨R, hR, ρ, ω, e, hρ, hω, hsplit⟩ := exists_puiseux_roots hdiscr hconst
  set n := P.natDegree.factorial
  have hn : n ≠ 0 := Nat.factorial_ne_zero _
  set δ := min R (min ε 1)
  have hδ : 0 < δ := lt_min hR (lt_min hε one_pos)
  have hδn : δ ^ n ≤ ε :=
    (pow_le_of_le_one hδ.le ((min_le_right _ _).trans (min_le_right _ _)) hn).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hs {s : ℝ} (hs : s ∈ Ioo 0 δ) : (s : ℂ) ∈ ball (0 : ℂ) R \ {0} :=
    ⟨by simpa [abs_of_pos hs.1] using hs.2.trans_le (min_le_left _ _),
      by simpa using hs.1.ne'⟩
  have hsn {s : ℝ} (hs : s ∈ Ioo 0 δ) : s ^ n ∈ Ioo 0 ε :=
    ⟨pow_pos hs.1 n, (pow_lt_pow_left₀ hs.2 hs.1.le hn).trans_le hδn⟩
  -- Each value `g (s ^ n)` is one of the complex roots `ρ i s`.
  have hlabel {s : ℝ} (h : s ∈ Ioo 0 δ) : ∃ i, ρ i s = g (s ^ n) := by
    refine (hsplit _ (hs h)).2.1 _ ?_
    have hmap : (P.map (evalRingHom (s ^ n))).map (algebraMap ℝ ℂ) =
        (P.map (mapRingHom (algebraMap ℝ ℂ))).map (evalRingHom ((s : ℂ) ^ n)) := by
      rw [map_map, map_map]
      congr 1
      ext <;> simp
    have := (hroot _ (hsn h)).map (f := algebraMap ℝ ℂ)
    rwa [hmap, Complex.coe_algebraMap] at this
  -- By Tau Ceti's `eq_of_continuous_mem_range`, it is the same root `ρ i₀ s` for all
  -- `s ∈ (0, δ)`.
  obtain ⟨i₀, hi₀⟩ := hlabel (s := δ / 2) ⟨half_pos hδ, half_lt_self hδ⟩
  have hconstant : ∀ s ∈ Ioo 0 δ, ρ i₀ s = g (s ^ n) := by
    have : PreconnectedSpace (Ioo 0 δ) := Subtype.preconnectedSpace isPreconnected_Ioo
    have h := TauCeti.eq_of_continuous_mem_range (B := Ioo 0 δ)
      (r := fun i (x : Ioo 0 δ) ↦ ρ i (x : ℝ)) (f := fun x ↦ (g ((x : ℝ) ^ n) : ℂ))
      (b₀ := ⟨δ / 2, half_pos hδ, half_lt_self hδ⟩)
      (fun i ↦ (hρ i).comp_continuous (Complex.continuous_ofReal.comp continuous_subtypeVal)
        fun x ↦ hs x.property)
      (Complex.continuous_ofReal.comp
        (hg.comp_continuous (continuous_subtypeVal.pow n) fun x ↦ hsn x.property))
      (fun x _ hj ↦ (hsplit _ (hs x.property)).1 hj) (fun x ↦ hlabel x.property) hi₀
    exact fun s hs ↦ congrFun h ⟨s, hs⟩
  -- Then `g t / t ^ (e i₀ / n) = ω i₀ (t ^ (1 / n))`, which tends to `ω i₀ 0`.
  set c := ω i₀ 0
  have hroot0 : Tendsto (fun t : ℝ ↦ ((t ^ (n⁻¹ : ℝ) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (n⁻¹ : ℝ)
      (Or.inr (by positivity))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rw [Real.zero_rpow (by positivity)] at h
    exact (Complex.ofReal_zero ▸ Complex.continuous_ofReal.tendsto 0).comp h
  have hlim : Tendsto (fun t : ℝ ↦ ((g t / t ^ (((e i₀ : ℚ) / n : ℚ) : ℝ) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 c) := by
    refine ((hω i₀).1.tendsto.comp hroot0).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (pow_pos hδ n)] with t ht
    set s := t ^ (n⁻¹ : ℝ)
    have hsI : s ∈ Ioo 0 δ := by
      refine ⟨Real.rpow_pos_of_pos ht.1 _, ?_⟩
      rw [← Real.pow_rpow_inv_natCast hδ.le hn]
      exact Real.rpow_lt_rpow ht.1.le ht.2 (by positivity)
    have hst : s ^ n = t := Real.rpow_inv_natCast_pow ht.1.le hn
    have hgt : (g t : ℂ) = (s : ℂ) ^ e i₀ * ω i₀ s := by
      rw [← hst, ← hconstant s hsI, (hsplit _ (hs hsI)).2.2 i₀]
    have hpow : t ^ (((e i₀ : ℚ) / n : ℚ) : ℝ) = s ^ e i₀ := by
      rw [show (((e i₀ : ℚ) / n : ℚ) : ℝ) = (n⁻¹ : ℝ) * (e i₀ : ℝ) by push_cast; ring,
        Real.rpow_mul ht.1.le, Real.rpow_intCast]
    have hs0 : (s : ℂ) ^ e i₀ ≠ 0 := zpow_ne_zero _ (hs hsI).2
    rw [comp_apply, hpow, Complex.ofReal_div, Complex.ofReal_zpow, hgt,
      mul_div_cancel_left₀ _ hs0]
  have him : c.im = 0 :=
    tendsto_nhds_unique ((Complex.continuous_im.tendsto c).comp hlim)
      (by simp [comp_def])
  refine ⟨(e i₀ : ℚ) / n, c.re, fun h ↦ (hω i₀).2 (Complex.ext (by simpa using h) him), ?_⟩
  simpa [comp_def] using (Complex.continuous_re.tendsto c).comp hlim

end Polynomial

end
