/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Calculus.Deriv.FinOne
public import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.RootBranch
public import SymplecticGeometry.Topology.Constructions.FinOne
public import TauCeti.Geometry.RealAlgebraic.Nash.Implicit
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Derivative

/-!
# A one-variable semialgebraic function is analytic near a point

Let `f` be a real function of one variable, semialgebraic on a set containing the points `![t]`,
`t > a` close to `a`. Then `t ↦ f ![t]` is analytic, so differentiable, at every `t > a` close to
`a`, and its derivative is again semialgebraic there.

* `TauCeti.isNashAt_of_eventually_isRoot`: a continuous function whose values are roots of a
  polynomial `P (t, ·)` that is separable at the base point is a Nash germ there.
* `TauCeti.IsSemialgebraicOn.eventually_analyticAt_nhdsGT`: analyticity just to the right of `a`.
* `TauCeti.IsSemialgebraicOn.deriv`: the derivative of a one-variable semialgebraic function
  that is differentiable on an open set is semialgebraic there.
* `TauCeti.IsSemialgebraicOn.exists_pos_differentiableOn_Ioo`: both together, on an interval
  `(0, ε)`, in the form that `TauCeti.IsSemialgebraicOn.exists_tendsto_div_rpow_nhdsGT` takes.

The proof of analyticity: if `f` vanishes on some interval `(a, b)` there is nothing to
show. Otherwise, to the right of `a`, `f` is a continuous root branch of a polynomial
`P : ℝ[X][X]` with nonzero discriminant
(`TauCeti.IsSemialgebraicOn.exists_polynomial_eventually_isRoot_nhdsGT`). Away from the finitely
many `t` at which the discriminant or the leading coefficient of `P` vanishes, `P (t, ·)` is
separable (Tau Ceti's `Polynomial.separable_map_iff_map_discr_ne_zero`), so `f t` is a simple
root, and Tau Ceti's Nash implicit function theorem `TauCeti.IsNashAt.implicit` makes `f` a Nash
germ, hence analytic, at `t`. The derivative is then semialgebraic by Tau Ceti's
`TauCeti.IsSemialgebraicOn.fderiv_apply`.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Sections 2.5–2.6
  and 8.1.
* L. van den Dries, *Tame Topology and o-minimal Structures*, Cambridge University Press, 1998,
  Chapter 7.
-/

public section

open Filter Set Topology

namespace TauCeti
open _root_.Polynomial

/-- A real function `f` of one variable, continuous at `x`, whose value `f y` is a root of
`P (y 0, ·)` for every `y` near `x`, is a Nash germ at `x` when `P (x 0, ·)` is separable. -/
theorem isNashAt_of_eventually_isRoot {f : (Fin 1 → ℝ) → ℝ} {P : ℝ[X][X]} {x : Fin 1 → ℝ}
    (hcont : ContinuousAt f x)
    (hroot : ∀ᶠ y in 𝓝 x, (P.map (evalRingHom (y 0))).IsRoot (f y))
    (hsep : (P.map (evalRingHom (x 0))).Separable) :
    IsNashAt f x := by
  -- The equation `P (t, y) = 0` as a polynomial function of `(t, y)`.
  set F : (Fin 1 ⊕ Unit → ℝ) → ℝ :=
    fun p ↦ (P.map (evalRingHom (p (.inl 0)))).eval (p (.inr ()))
  have hF : F = fun p ↦ MvPolynomial.eval p
      (P.eval₂ (aeval (MvPolynomial.X (.inl 0))).toRingHom (MvPolynomial.X (.inr ()))) := by
    ext p
    rw [Polynomial.hom_eval₂, ← eval_map]
    simp only [F, MvPolynomial.eval_X]
    congr 2
    ext <;> simp
  have hFN : IsNashAt F (Sum.elim x fun _ ↦ f x) := by
    rw [hF]
    exact MvPolynomial.isNashAt_eval _
  -- The root `f x` of `P (x 0, ·)` is simple.
  have hd : deriv (fun y ↦ F (Sum.elim x fun _ ↦ y)) (f x) ≠ 0 := by
    simp only [F, Sum.elim_inl, Sum.elim_inr, Polynomial.deriv]
    have := hsep.aeval_derivative_ne_zero (x := f x)
      (by simpa [aeval_def] using hroot.self_of_nhds)
    simpa [aeval_def] using this
  exact hFN.implicit hcont hroot hd

/-- A real function `f` of one variable that is semialgebraic on a set containing the points
`![t]`, `t > a` close to `a`, is analytic at every `t > a` close to `a`, as the function
`t ↦ f ![t]`. -/
theorem IsSemialgebraicOn.eventually_analyticAt_nhdsGT {f : (Fin 1 → ℝ) → ℝ}
    {s : Set (Fin 1 → ℝ)} (hf : IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s) {a : ℝ}
    (hs : ∀ᶠ t in 𝓝[>] a, ![t] ∈ s) :
    ∀ᶠ t in 𝓝[>] a, AnalyticAt ℝ (fun t ↦ f ![t]) t := by
  by_cases hne : ∃ᶠ t in 𝓝[>] a, f ![t] ≠ 0
  swap
  · -- `f` vanishes on an interval `(a, b)`.
    obtain ⟨b, hab, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (not_frequently.1 hne)
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    refine (analyticAt_const (v := (0 : ℝ))).congr ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact (by simpa using hb hu : f ![u] = 0).symm
  obtain ⟨P, hdisc, hc0, hev⟩ := hf.exists_polynomial_eventually_isRoot_nhdsGT hs hne
  have hP : P ≠ 0 := fun h ↦ hc0 (by simp [h])
  -- Away from the zeros of the discriminant and of the leading coefficient of `P`.
  have hD : ∀ᶠ t in 𝓝[>] a, (P.discr * P.leadingCoeff).eval t ≠ 0 :=
    ((eventually_eval_ne_zero_codiscrete
      (mul_ne_zero hdisc (leadingCoeff_ne_zero.2 hP))).filter_mono (nhdsNE_le_codiscrete a))
      |>.filter_mono (nhdsWithin_mono _ fun _ ht ↦ ne_of_gt ht)
  obtain ⟨b, hab, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hev.and hD)
  filter_upwards [Ioo_mem_nhdsGT hab] with t ht
  obtain ⟨⟨hcont, -⟩, hDt⟩ := hb ht
  rw [eval_mul, mul_ne_zero_iff] at hDt
  have hroots : ∀ᶠ y in 𝓝 ![t], (P.map (evalRingHom (y 0))).IsRoot (f y) := by
    filter_upwards [(continuous_apply 0).continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds ht.1 ht.2)] with y hy
    rw [← show ![y 0] = y from FinVec.etaExpand_eq y]
    exact (hb hy).1.2
  have hN : IsNashAt f ![t] :=
    isNashAt_of_eventually_isRoot (continuousAt_iff_continuousAt_vecCons_fin_one.2 hcont) hroots
      ((separable_map_iff_map_discr_ne_zero P (evalRingHom t) hDt.2).2 hDt.1)
  have hv : AnalyticAt ℝ (fun s : ℝ ↦ ![s]) t := by
    simp only [Matrix.vec_single_eq_const]
    exact (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.toContinuousLinearMap.analyticAt t
  exact hN.analyticAt.comp (f := fun s : ℝ ↦ ![s]) hv

/-- The derivative of a real function `f` of one variable that is semialgebraic on the points
`![t]`, `t ∈ u`, of an open set `u` and differentiable on `u`, as the function `t ↦ f ![t]`, is
semialgebraic on these points. -/
theorem IsSemialgebraicOn.deriv {f : (Fin 1 → ℝ) → ℝ} {u : Set ℝ}
    (hf : IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) {x : Fin 1 → ℝ | x 0 ∈ u})
    (hu : IsOpen u)
    (hd : DifferentiableOn ℝ (fun t ↦ f ![t]) u) :
    IsSemialgebraicOn (fun x (_ : Unit) ↦ _root_.deriv (fun t ↦ f ![t]) (x 0))
      {x : Fin 1 → ℝ | x 0 ∈ u} := by
  have hU : IsOpen {x : Fin 1 → ℝ | x 0 ∈ u} := hu.preimage (continuous_apply 0)
  have hdU : ∀ x ∈ {x : Fin 1 → ℝ | x 0 ∈ u}, DifferentiableAt ℝ f x := fun x hx ↦
    differentiableAt_iff_differentiableAt_vecCons_fin_one.2
      ((hd _ hx).differentiableAt (hu.mem_nhds hx))
  refine (hf.fderiv_apply hU (fun x hx ↦ (hdU x hx).differentiableWithinAt) ![1]).congr
    fun x hx ↦ funext fun _ ↦ ?_
  have hx : HasFDerivAt f (fderiv ℝ f x) ![x 0] := by
    rw [show ![x 0] = x from FinVec.etaExpand_eq x]
    exact (hdU x hx).hasFDerivAt
  exact ((hx.comp_hasDerivAt (x 0) (hasDerivAt_vecCons_fin_one (x 0))).deriv).symm

/-- A real function `f` of one variable that is semialgebraic on a set containing the points
`![t]`, `0 < t < ε₀`, is differentiable on some interval `(0, ε)`, as the function
`t ↦ f ![t]`, and its derivative is semialgebraic on the points `![t]`, `0 < t < ε`. -/
theorem IsSemialgebraicOn.exists_pos_differentiableOn_Ioo {f : (Fin 1 → ℝ) → ℝ}
    {s : Set (Fin 1 → ℝ)} (hf : IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hs : ∀ t ∈ Ioo 0 ε₀, ![t] ∈ s) :
    ∃ ε > 0, DifferentiableOn ℝ (fun t ↦ f ![t]) (Ioo 0 ε) ∧
      IsSemialgebraicOn (fun x (_ : Unit) ↦ _root_.deriv (fun t ↦ f ![t]) (x 0))
        {x : Fin 1 → ℝ | x 0 ∈ Ioo 0 ε} := by
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hf.eventually_analyticAt_nhdsGT (eventually_of_mem (Ioo_mem_nhdsGT hε₀) hs))
  set ε := min b ε₀
  have hd : DifferentiableOn ℝ (fun t ↦ f ![t]) (Ioo 0 ε) := fun t ht ↦
    (hsub (Ioo_subset_Ioo_right (min_le_left _ _) ht)).differentiableAt.differentiableWithinAt
  have hI : IsSemialgebraic {x : Fin 1 → ℝ | x 0 ∈ Ioo 0 ε} := by
    have h : {x : Fin 1 → ℝ | x 0 ∈ Ioo 0 ε} = {x | MvPolynomial.eval x (MvPolynomial.C 0) <
        MvPolynomial.eval x (MvPolynomial.X 0)} ∩
        {x | MvPolynomial.eval x (MvPolynomial.X 0) < MvPolynomial.eval x (MvPolynomial.C ε)} := by
      ext x; simp
    exact h ▸ (isSemialgebraic_eval_lt _ _).inter (isSemialgebraic_eval_lt _ _)
  refine ⟨ε, lt_min hb hε₀, hd, (hf.mono hI fun x hx ↦ ?_).deriv isOpen_Ioo hd⟩
  rw [← show ![x 0] = x from FinVec.etaExpand_eq x]
  exact hs _ (Ioo_subset_Ioo_right (min_le_right _ _) hx)

end TauCeti

end
