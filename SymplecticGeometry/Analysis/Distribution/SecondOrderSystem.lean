/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Distribution.Coordinates
public import SymplecticGeometry.Analysis.Distribution.EllipticSystem
public import SymplecticGeometry.Analysis.Distribution.SmulLeft
import Mathlib.Analysis.InnerProductSpace.Dual
import SymplecticGeometry.Analysis.Distribution.NegativeSobolev
import SymplecticGeometry.MeasureTheory.Function.LpSeminorm.LinearEquiv
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Smoothness
import TauCeti.MeasureTheory.Function.LocalRepresentative

/-!
# Regularity for second-order systems with a scalar elliptic principal part

This file proves interior regularity for second-order systems whose principal part is one scalar
operator times the identity, for distributions and in weak form.

* `Distribution.IsLocallySobolevAt.of_secondOrderSystem` and
  `Distribution.singularSupport_eq_empty_of_secondOrderSystem`: a system of distributions
  `T : κ → 𝓓'(Ω, ℂ)` on an open set `Ω ⊆ CoordinateSpace n`, written with the multiplications
  inside the derivatives,
  `∑ i j, ∂_{v i} ∂_{v j} (g i j T a) + ∑ b i, ∂_{v i} (β a b i T b) + ∑ b, γ a b T b`,
  with smooth real coefficients, and the symbol `∑ i j, g i j x ⟪v i, ξ⟫ ⟪v j, ξ⟫` vanishing at
  no `ξ ≠ 0`. If every left side is `H^s` near `x`, every `T a` is `H^(s + 2)` near `x`; if every
  left side is smooth on `Ω` and the symbol condition holds on `Ω`, every `T a` is smooth on `Ω`.
  The Leibniz rule `Distribution.lineDerivOp_smulLeftCLM` moves the coefficients outside the
  derivatives, and the result is then `Distribution.IsLocallySobolevAt.of_ellipticSystem`.
* `SymplecticGeometry.secondOrderSystem_coordOfFun_apply` and
  `SymplecticGeometry.exists_secondOrderSystem_coordOfFun`: the link with weak forms, on an
  open set `U` of a finite-dimensional real space `E` with a basis `b`. Let
  `P a = -∑ i j, A i j ∂_{b j} ∂_{b i} a + ∑ i, B i (∂_{b i} a) + C a` act on maps `a : E → F`,
  with `A i j : E → ℝ` and `B i, C : E → F →L[ℝ] F` smooth on `U`, and the quadratic form
  `∑ i j, A i j y ξ i ξ j` nonzero at every `ξ ≠ 0`, for every `y ∈ U`. Near each point of `U`,
  with the coefficients extended to the whole space by a cutoff and read in coordinates
  `e : E ≃L[ℝ] CoordinateSpace n`, the system above, elliptic there and applied to the coordinate
  distributions (`Distribution.coordOfFun`, in the dual basis of a basis `f` of `F`) of any `w`
  locally integrable there, is the distribution `φ ↦ ∫ w (P ((φ ∘ e) • f k)) dμ`, for any
  measure `μ`.
* `SymplecticGeometry.exists_contDiffOn_ae_eq_of_forall_integral_apply_eq`: if
  `w : E → F →L[ℝ] ℝ` is locally integrable on `U`, `h` is smooth on `U`, and
  `∫ w (P a) dμ = ∫ h a dμ` for every smooth `a` with compact support in `U`, for an additive
  Haar measure `μ`, then `w` agrees almost everywhere on `U` with a function smooth on `U`. This
  is the operator of `SymplecticGeometry.exists_mpullback_symm_hodgeLaplacian_eq`, the Hodge
  Laplacian in a chart.
* `SymplecticGeometry.isLocallySobolevAt_one_coordOfFun_of_abs_integral_le`: the `H^{-1}` case.
  If `w` is locally integrable on `U` and, for each compact `K ⊆ U`, `|∫ w (P a) dμ|` is at most
  a constant times `‖a‖_{L²} + ∑ i, ‖∂_{b i} a‖_{L²}` for smooth `a` supported in `K`, then the
  coordinate distributions of `w` are `H^1` near every point of any open `Ω` with
  `e⁻¹ '' Ω ⊆ U`.

For the smoothness of weak solutions, the weak equation says, by
`exists_secondOrderSystem_coordOfFun`, that the coordinate distributions of `w` solve the
system with the coordinate distributions of `h`, which are smooth, as right sides. The regular
representatives (`Distribution.exists_contDiffOn_ae_eq_of_singularSupport_coordOfFun_eq_empty`)
are glued by Tau Ceti's `TauCeti.exists_contDiffOn_ae_eq_of_locally`.

For the `H^{-1}` case, near a point the system of the coordinate distributions is again the weak
form, restricted (`Distribution.restrictCLM_coordOfFun`) to where the coefficients agree. Its
right sides are bounded by the `W^{1,2}` norm of `φ ∘ e`, which a change of variables
(`MeasureTheory.eLpNorm_comp_continuousLinearEquiv_eq_addHaarScalarFactor_rpow_mul`) turns into
that of `φ` along the vectors `e (b i)`. So they are `H^{-1}` near the point
(`Distribution.isLocallySobolevAt_neg_one_of_norm_le`), and the first result with `s = -1` gives
`H^1`.

## Main results

* `Distribution.IsLocallySobolevAt.of_secondOrderSystem`.
* `Distribution.singularSupport_eq_empty_of_secondOrderSystem`.
* `SymplecticGeometry.secondOrderSystem_coordOfFun_apply`.
* `SymplecticGeometry.exists_secondOrderSystem_coordOfFun`.
* `SymplecticGeometry.exists_contDiffOn_ae_eq_of_forall_integral_apply_eq`.
* `SymplecticGeometry.isLocallySobolevAt_one_coordOfFun_of_abs_integral_le`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6 (weak solutions of elliptic equations and their regularity).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1 (the transpose
  of a differential operator and the Leibniz rule).
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (`H_{-1}` as the dual of `H_1`, and `H_1` as the `L²` functions with first derivatives in
  `L²`).
-/

public section

open TopologicalSpace TauCeti
open scoped ContDiff Distributions LineDeriv InnerProductSpace

namespace Distribution

variable {n : ℕ} {Ω : Opens (CoordinateSpace n)} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Interior regularity for second-order systems with a scalar elliptic principal part.** Let
`T : κ → 𝓓'(Ω, ℂ)` and let the coefficients `g i j`, `β a b i` and `γ a b` be smooth real
functions such that `∑ i j, g i j x ⟪v i, ξ⟫ ⟪v j, ξ⟫ ≠ 0` for every `ξ ≠ 0`. If every
`∑ i j, ∂_{v i} ∂_{v j} (g i j T a) + ∑ b i, ∂_{v i} (β a b i T b) + ∑ b, γ a b T b` is `H^s`
near `x`, then every `T a` is `H^(s + 2)` near `x`. -/
theorem IsLocallySobolevAt.of_secondOrderSystem (v : ι → CoordinateSpace n)
    {g : ι → ι → CoordinateSpace n → ℝ} {β : κ → κ → ι → CoordinateSpace n → ℝ}
    {γ : κ → κ → CoordinateSpace n → ℝ} (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hβ : ∀ a b i, ContDiff ℝ ∞ (β a b i)) (hγ : ∀ a b, ContDiff ℝ ∞ (γ a b))
    {x : CoordinateSpace n}
    (hσ : ∀ ξ, ξ ≠ 0 → ∑ i, ∑ j, g i j x * ⟪v i, ξ⟫_ℝ * ⟪v j, ξ⟫_ℝ ≠ 0)
    {T : κ → 𝓓'(Ω, ℂ)} {s : ℝ}
    (hT : ∀ a, IsLocallySobolevAt s
      (∑ i, ∑ j, ∂_{v i} (∂_{v j} (Distribution.smulLeftCLM (hg i j) (T a))) +
        ∑ b, ∑ i, ∂_{v i} (Distribution.smulLeftCLM (hβ a b i) (T b)) +
        ∑ b, Distribution.smulLeftCLM (hγ a b) (T b)) x)
    (a : κ) : (T a).IsLocallySobolevAt (s + 2) x := by
  classical
  /- The Leibniz rule turns the system into one of the form of `EllipticSystem.lean`. Its
  coupling terms are indexed by the first-order terms `J₁ = (ι × ι × Bool) ⊕ ι`, from the
  second-order part and from the `β`, and the zeroth-order terms `J₀ = (ι × ι) ⊕ ι ⊕ Unit`, from
  the second-order part, the `β` and the `γ`. The terms from the second-order part act on `T a`
  alone. -/
  let k' : ((ι × ι × Bool) ⊕ ι) ⊕ ((ι × ι) ⊕ ι ⊕ Unit) → ℕ := Sum.elim (fun _ ↦ 1) fun _ ↦ 0
  let d : (ι × ι × Bool) ⊕ ι → CoordinateSpace n :=
    Sum.elim (fun p ↦ bif p.2.2 then v p.2.1 else v p.1) v
  let m' : ∀ j, Fin (k' j) → CoordinateSpace n := fun j ↦
    Sum.rec (motive := fun j ↦ Fin (k' j) → CoordinateSpace n) (fun p ↦ ![d p]) (fun _ ↦ ![]) j
  let h : κ → κ → ((ι × ι × Bool) ⊕ ι) ⊕ ((ι × ι) ⊕ ι ⊕ Unit) → CoordinateSpace n → ℝ :=
    fun a b ↦
      Sum.elim (Sum.elim (fun p x ↦ fderiv ℝ (g p.1 p.2.1) x (bif p.2.2 then v p.1 else v p.2.1))
        (β a b))
        (Sum.elim (fun p x ↦ fderiv ℝ (fun y ↦ fderiv ℝ (g p.1 p.2) y (v p.2)) x (v p.1))
          (Sum.elim (fun i x ↦ fderiv ℝ (β a b i) x (v i)) fun _ ↦ γ a b))
  let c' : κ → κ → ((ι × ι × Bool) ⊕ ι) ⊕ ((ι × ι) ⊕ ι ⊕ Unit) → ℂ := fun a b ↦
    Sum.elim (Sum.elim (fun _ ↦ if b = a then 1 else 0) fun _ ↦ 1)
      (Sum.elim (fun _ ↦ if b = a then 1 else 0) fun _ ↦ 1)
  have hh : ∀ a b j, ContDiff ℝ ∞ (h a b j) := by
    rintro a b ((⟨i, j, _ | _⟩ | i) | (⟨i, j⟩ | i | _))
    · exact (hg i j).fderiv_apply_const le_rfl _
    · exact (hg i j).fderiv_apply_const le_rfl _
    · exact hβ a b i
    · exact ((hg i j).fderiv_apply_const le_rfl _).fderiv_apply_const le_rfl _
    · exact (hβ a b i).fderiv_apply_const le_rfl _
    · exact hγ a b
  have hT' := IsLocallySobolevAt.of_ellipticSystem (s := s) (x := x) (T := T)
    (t := Finset.univ) (c := fun _ ↦ 1)
    (g := fun p : ι × ι ↦ g p.1 p.2) (k := fun _ ↦ 2) (m := fun p ↦ ![v p.1, v p.2])
    (t' := Finset.univ) (c' := c') (h := h) (k' := k') (m' := m')
    (fun p ↦ hg p.1 p.2) hh (M := 2) (fun _ _ ↦ le_rfl) ?_ ?_ ?_ a
  · exact_mod_cast hT'
  · rintro (_ | _) - <;> simp [k']
  · intro ξ hξ
    simp only [one_mul, constCoeffPrincipalSymbol_def, Finset.filter_true, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fintype.sum_prod_type]
    exact_mod_cast (by simpa only [mul_assoc] using hσ ξ hξ)
  · intro a
    convert hT a using 1
    simp only [lineDerivOp_smulLeftCLM, LineDeriv.lineDerivOp_add, Finset.sum_add_distrib]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, k', m', h, c', d,
      Sum.elim_inl, Sum.elim_inr, LineDeriv.iteratedLineDerivOp_succ_left,
      LineDeriv.iteratedLineDerivOp_fin_zero, ite_smul, one_smul,
      Finset.sum_ite_irrel,
      Finset.sum_add_distrib, Bool.cond_true, Bool.cond_false]
    simp only [Fin.tail, Matrix.cons_val_zero, Matrix.cons_val_succ, Fintype.sum_unique]
    have h0 : ∀ X : 𝓓'(Ω, ℂ), (0 : ℂ) • X = 0 := fun X ↦ zero_smul ℂ X
    simp only [h0, Finset.sum_const_zero, add_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    abel

/-- **Regularity for second-order systems with a scalar elliptic principal part.** Let
`T : κ → 𝓓'(Ω, ℂ)` and let the coefficients `g i j`, `β a b i` and `γ a b` be smooth real
functions. If, at every `x ∈ Ω`, `∑ i j, g i j x ⟪v i, ξ⟫ ⟪v j, ξ⟫ ≠ 0` for every `ξ ≠ 0`, and
every `∑ i j, ∂_{v i} ∂_{v j} (g i j T a) + ∑ b i, ∂_{v i} (β a b i T b) + ∑ b, γ a b T b` is
smooth on `Ω`, then every `T a` is smooth on `Ω`. -/
theorem singularSupport_eq_empty_of_secondOrderSystem (v : ι → CoordinateSpace n)
    {g : ι → ι → CoordinateSpace n → ℝ} {β : κ → κ → ι → CoordinateSpace n → ℝ}
    {γ : κ → κ → CoordinateSpace n → ℝ} (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hβ : ∀ a b i, ContDiff ℝ ∞ (β a b i)) (hγ : ∀ a b, ContDiff ℝ ∞ (γ a b))
    (hσ : ∀ x ∈ Ω, ∀ ξ, ξ ≠ 0 → ∑ i, ∑ j, g i j x * ⟪v i, ξ⟫_ℝ * ⟪v j, ξ⟫_ℝ ≠ 0)
    {T : κ → 𝓓'(Ω, ℂ)}
    (hT : ∀ a, singularSupport (∑ i, ∑ j, ∂_{v i} (∂_{v j} (smulLeftCLM (hg i j) (T a))) +
      ∑ b, ∑ i, ∂_{v i} (smulLeftCLM (hβ a b i) (T b)) + ∑ b, smulLeftCLM (hγ a b) (T b)) = ∅)
    (a : κ) : (T a).singularSupport = ∅ :=
  singularSupport_eq_empty_of_forall_isLocallySobolevAt hT fun x hx _ hs ↦
    IsLocallySobolevAt.of_secondOrderSystem v hg hβ hγ (hσ x hx) hs a

end Distribution

namespace SymplecticGeometry

open MeasureTheory Set Filter Distribution
open scoped Topology

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Fintype ι]

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- **The coordinate distributions of `w` under a second-order operator.** Let
`P a = -∑ i j, A i j ∂_{b j} ∂_{b i} a + ∑ i, B i (∂_{b i} a) + C a`, let `w` be locally integrable
on an open set `V`, and let `e : E ≃L[ℝ] CoordinateSpace n`. Let `g`, `β`, `γ` be smooth, with
`g i j (e y) = -A i j y`, `β k l i (e y) = -bF.repr (B i y (bF k)) l` and
`γ k l (e y) = bF.repr (C y (bF k)) l` for `y ∈ V`. Applied to the coordinate distributions of
`w` in the dual basis `bD` of `bF`, the system of
`Distribution.singularSupport_eq_empty_of_secondOrderSystem` with these coefficients is the
distribution `φ ↦ ∫ y, w y (P ((φ ∘ e) • bF k) y) ∂μ` on `Ω`. -/
theorem secondOrderSystem_coordOfFun_apply (b : Module.Basis ι ℝ E)
    {A : ι → ι → E → ℝ} {B : ι → E → F →L[ℝ] F} {C : E → F →L[ℝ] F} {w : E → F →L[ℝ] ℝ}
    {V : TopologicalSpace.Opens E} (hwV : LocallyIntegrableOn w V μ) {n : ℕ}
    (e : E ≃L[ℝ] CoordinateSpace n) {Ω : TopologicalSpace.Opens (CoordinateSpace n)}
    (hΩ : MapsTo e.symm Ω V) {κ : Type*} [Fintype κ] (bF : Module.Basis κ ℝ F)
    (bD : Module.Basis κ ℝ (F →L[ℝ] ℝ)) (hbD : ∀ L l, bD.repr L l = L (bF l))
    {g : ι → ι → CoordinateSpace n → ℝ} {β : κ → κ → ι → CoordinateSpace n → ℝ}
    {γ : κ → κ → CoordinateSpace n → ℝ} (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hβ : ∀ k l i, ContDiff ℝ ∞ (β k l i)) (hγ : ∀ k l, ContDiff ℝ ∞ (γ k l))
    (hgA : ∀ i j, ∀ y ∈ V, g i j (e y) = -A i j y)
    (hβB : ∀ k l i, ∀ y ∈ V, β k l i (e y) = -bF.repr (B i y (bF k)) l)
    (hγC : ∀ k l, ∀ y ∈ V, γ k l (e y) = bF.repr (C y (bF k)) l) (k : κ) (φ : 𝓓(Ω, ℝ)) :
    (∑ i, ∑ j, ∂_{e (b i)} (∂_{e (b j)} (smulLeftCLM (hg i j) (coordOfFun e hΩ bD w μ k))) +
      ∑ l, ∑ i, ∂_{e (b i)} (smulLeftCLM (hβ k l i) (coordOfFun e hΩ bD w μ l)) +
      ∑ l, smulLeftCLM (hγ k l) (coordOfFun e hΩ bD w μ l)) φ =
      ∫ y, ((w y (-∑ i, ∑ j, A i j y •
          fderiv ℝ (fun z ↦ fderiv ℝ (fun y ↦ φ (e y) • bF k) z (b i)) y (b j) +
        ∑ i, B i y (fderiv ℝ (fun y ↦ φ (e y) • bF k) y (b i)) + C y (φ (e y) • bF k)) : ℝ) : ℂ)
        ∂μ := by
  classical
  have hwbF (y : E) (u : F) : w y u = ∑ l, bF.repr u l * w y (bF l) := by
    calc w y u = w y (∑ l, bF.repr u l • bF l) := by rw [bF.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  have hde (ψ : 𝓓(Ω, ℝ)) (u : F) (y z : E) :
      fderiv ℝ (fun y ↦ ψ (e y) • u) y z = ∂_{e z} ψ (e y) • u := by
    simpa using TestFunction.fderiv_comp_smul_const_apply (e : E →L[ℝ] _) ψ u y z
  simp only [hde]
  -- Integrability of the pairings of the coordinates of `w` with test functions.
  have hint (ψ : 𝓓(Ω, ℝ)) (l) : Integrable (fun y ↦ ψ (e y) • (bD.repr (w y) l : ℂ)) μ := by
    simpa using (e.symm.transportTestFunction hΩ ψ).integrable_smul
      (hwV.ofReal_basis_repr bD l)
  -- The left side pairs `φ` with the coordinates of `w` through test functions `Ψ l`.
  let Ψ : κ → 𝓓(Ω, ℝ) := fun l ↦
    (if l = k then ∑ i, ∑ j, TestFunction.smulLeftCLM (hg i j) (∂_{e (b j)} (∂_{e (b i)} φ))
      else 0) +
      ∑ i, TestFunction.smulLeftCLM (hβ k l i) (-∂_{e (b i)} φ) +
      TestFunction.smulLeftCLM (hγ k l) φ
  have h₁ : (∑ i, ∑ j, ∂_{e (b i)} (∂_{e (b j)} (smulLeftCLM (hg i j) (coordOfFun e hΩ bD w μ k))) +
      ∑ l, ∑ i, ∂_{e (b i)} (smulLeftCLM (hβ k l i) (coordOfFun e hΩ bD w μ l)) +
      ∑ l, smulLeftCLM (hγ k l) (coordOfFun e hΩ bD w μ l)) φ =
      ∑ l, coordOfFun e hΩ bD w μ l (Ψ l) := by
    simp only [add_apply, sum_apply,
      lineDerivOp_apply_apply, Distribution.smulLeftCLM_apply, LineDeriv.lineDerivOp_neg,
      neg_neg, Ψ, map_add, map_sum, apply_ite, map_zero, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [h₁]
  simp only [coordOfFun_apply e hΩ bD hwV]
  rw [← integral_finsetSum _ fun l _ ↦ hint _ l]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  have hwB (i : ι) : w y (B i y (bF k)) = ∑ l, bF.repr (B i y (bF k)) l * w y (bF l) :=
    hwbF y _
  have hwC : w y (C y (bF k)) = ∑ l, bF.repr (C y (bF k)) l * w y (bF l) := hwbF y _
  simp only [map_add, map_neg, map_sum, map_smul, smul_eq_mul, hwB, hwC]
  by_cases hy : y ∈ V
  · simp only [smul_eq_mul, map_neg, Finset.sum_neg_distrib, add_apply, apply_ite,
      FunLike.coe_zero, ite_apply, sum_apply, TestFunction.smulLeftCLM_apply,
      hgA _ _ y hy, hβB _ _ _ y hy, hγC _ _ y hy,
      TestFunction.lineDerivOp_apply,
      neg_mul, Pi.zero_apply, neg_apply, neg_neg, hbD, Complex.real_smul, Complex.ofReal_add,
      Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_zero, add_mul,
      ite_mul, Finset.sum_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, Finset.mul_sum, Ψ]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (by simp only [mul_assoc]) ?_)
      (Finset.sum_congr rfl fun _ _ ↦ by ring)
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  · have hz (ψ : 𝓓(Ω, ℝ)) : ψ (e y) = 0 :=
      ψ.zero_on_compl fun hy' ↦ hy (by simpa using hΩ hy')
    simp [hz]

omit [μ.IsAddHaarMeasure] in
/-- **The coordinate distributions of a weak solution satisfy an elliptic system.** Let
`P a = -∑ i j, A i j ∂_{b j} ∂_{b i} a + ∑ i, B i (∂_{b i} a) + C a` have coefficients smooth on an
open set `U`, with `∑ i j, A i j y ξ i ξ j ≠ 0` for every `y ∈ U` and `ξ ≠ 0`, and let
`e : E ≃L[ℝ] CoordinateSpace n`. Every `x ∈ U` has an open neighbourhood `V ⊆ U` with smooth
coefficients `g`, `β`, `γ` on `CoordinateSpace n`, whose principal symbol
`∑ i j, g i j z ⟪e (b i), ξ⟫ ⟪e (b j), ξ⟫` vanishes at no `ξ ≠ 0` for `z ∈ e '' V`, such that for
every `w` locally integrable on `V` the system of
`Distribution.singularSupport_eq_empty_of_secondOrderSystem` with these coefficients, applied to
the coordinate distributions of `w` in the dual basis `bD` of `bF`, is the distribution
`φ ↦ ∫ y, w y (P ((φ ∘ e) • bF k) y) ∂μ`. -/
theorem exists_secondOrderSystem_coordOfFun {U : Set E} (hU : IsOpen U)
    (b : Module.Basis ι ℝ E) {A : ι → ι → E → ℝ} {B : ι → E → F →L[ℝ] F} {C : E → F →L[ℝ] F}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (A i j) U) (hB : ∀ i, ContDiffOn ℝ ∞ (B i) U)
    (hC : ContDiffOn ℝ ∞ C U)
    (hAell : ∀ y ∈ U, ∀ ξ : ι → ℝ, ξ ≠ 0 → ∑ i, ∑ j, A i j y * ξ i * ξ j ≠ 0)
    {n : ℕ} (e : E ≃L[ℝ] CoordinateSpace n) {κ : Type*} [Fintype κ] (bF : Module.Basis κ ℝ F)
    (bD : Module.Basis κ ℝ (F →L[ℝ] ℝ)) (hbD : ∀ L l, bD.repr L l = L (bF l)) {x : E}
    (hx : x ∈ U) :
    ∃ V : TopologicalSpace.Opens E, x ∈ V ∧ (V : Set E) ⊆ U ∧
      ∃ (g : ι → ι → CoordinateSpace n → ℝ) (β : κ → κ → ι → CoordinateSpace n → ℝ)
        (γ : κ → κ → CoordinateSpace n → ℝ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
        (hβ : ∀ k l i, ContDiff ℝ ∞ (β k l i)) (hγ : ∀ k l, ContDiff ℝ ∞ (γ k l)),
        (∀ z, e.symm z ∈ V → ∀ ξ, ξ ≠ 0 →
          ∑ i, ∑ j, g i j z * ⟪e (b i), ξ⟫_ℝ * ⟪e (b j), ξ⟫_ℝ ≠ 0) ∧
        ∀ {Ω : TopologicalSpace.Opens (CoordinateSpace n)} (hΩ : MapsTo e.symm Ω V)
          {w : E → F →L[ℝ] ℝ}, LocallyIntegrableOn w V μ → ∀ (k : κ) (φ : 𝓓(Ω, ℝ)),
          (∑ i, ∑ j, ∂_{e (b i)} (∂_{e (b j)} (smulLeftCLM (hg i j) (coordOfFun e hΩ bD w μ k))) +
            ∑ l, ∑ i, ∂_{e (b i)} (smulLeftCLM (hβ k l i) (coordOfFun e hΩ bD w μ l)) +
            ∑ l, smulLeftCLM (hγ k l) (coordOfFun e hΩ bD w μ l)) φ =
          ∫ y, ((w y (-∑ i, ∑ j, A i j y •
              fderiv ℝ (fun z ↦ fderiv ℝ (fun y ↦ φ (e y) • bF k) z (b i)) y (b j) +
            ∑ i, B i y (fderiv ℝ (fun y ↦ φ (e y) • bF k) y (b i)) + C y (φ (e y) • bF k)) : ℝ) :
              ℂ) ∂μ := by
  -- A cutoff `χ` equal to `1` on an open neighbourhood `V ⊆ U` of `x`.
  obtain ⟨χ, hχ, -, hχ1, -, hχU⟩ :=
    isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one hU (singleton_subset_iff.2 hx)
  obtain ⟨t, ht1, ht, hxt⟩ := eventually_nhds_iff.1 (hχ1 x rfl)
  let V : TopologicalSpace.Opens E := ⟨t ∩ U, ht.inter hU⟩
  have hVU : (V : Set E) ⊆ U := inter_subset_right
  -- The coefficients, extended by the cutoff and read in the coordinates.
  have hext (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) :
      ContDiff ℝ ∞ fun z ↦ χ (e.symm z) • f (e.symm z) :=
    (hf.contDiff_smul_of_tsupport_subset hU hχ.contDiffOn hχU).comp e.symm.contDiff
  have hrepr {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (l : κ) :
      ContDiffOn ℝ ∞ (fun y ↦ bF.repr (f y) l) U := by
    simpa [Function.comp_def] using (bF.coord l).toContinuousLinearMap.contDiff.comp_contDiffOn hf
  have hg (i j : ι) : ContDiff ℝ ∞ fun z ↦ -(χ (e.symm z) • A i j (e.symm z)) :=
    (hext _ (hA i j)).neg
  have hβ (k l : κ) (i : ι) :
      ContDiff ℝ ∞ fun z ↦ -(χ (e.symm z) • bF.repr (B i (e.symm z) (bF k)) l) :=
    (hext _ (hrepr ((hB i).clm_apply contDiffOn_const) l)).neg
  have hγ (k l : κ) : ContDiff ℝ ∞ fun z ↦ χ (e.symm z) • bF.repr (C (e.symm z) (bF k)) l :=
    hext _ (hrepr (hC.clm_apply contDiffOn_const) l)
  refine ⟨V, ⟨hxt, hx⟩, hVU, _, _, _, hg, hβ, hγ, ?_, fun hΩ _ hwV k φ ↦
    secondOrderSystem_coordOfFun_apply b hwV e hΩ bF bD hbD hg hβ hγ
      (fun _ _ y hy ↦ by simp [ht1 y hy.1]) (fun _ _ _ y hy ↦ by simp [ht1 y hy.1])
      (fun _ _ y hy ↦ by simp [ht1 y hy.1]) k φ⟩
  -- Ellipticity: `ξ ≠ 0` has a nonzero coordinate `⟪e (b i), ξ⟫`.
  intro z hzV ξ hξ
  have hη : (fun i ↦ ⟪e (b i), ξ⟫_ℝ) ≠ 0 := by
    intro hη
    exact hξ (InnerProductSpace.ext_inner_left_basis (b.map e.toLinearEquiv) fun i ↦ by
      simpa using congrFun hη i)
  have := hAell _ (hVU hzV) _ hη
  simp only [ht1 _ hzV.1, one_smul]
  simpa [neg_mul, Finset.sum_neg_distrib] using this

/-- The local step of `exists_contDiffOn_ae_eq_of_forall_integral_apply_eq`. -/
private theorem exists_contDiffOn_ae_eq_nhds {U : Set E} (hU : IsOpen U)
    (b : Module.Basis ι ℝ E) {A : ι → ι → E → ℝ} {B : ι → E → F →L[ℝ] F} {C : E → F →L[ℝ] F}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (A i j) U) (hB : ∀ i, ContDiffOn ℝ ∞ (B i) U)
    (hC : ContDiffOn ℝ ∞ C U)
    (hAell : ∀ y ∈ U, ∀ ξ : ι → ℝ, ξ ≠ 0 → ∑ i, ∑ j, A i j y * ξ i * ξ j ≠ 0)
    {w h : E → F →L[ℝ] ℝ} (hw : LocallyIntegrableOn w U μ) (hh : ContDiffOn ℝ ∞ h U)
    (hwh : ∀ a : E → F, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ U →
      ∫ y, w y (-∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (b i)) y (b j) +
        ∑ i, B i y (fderiv ℝ a y (b i)) + C y (a y)) ∂μ = ∫ y, h y (a y) ∂μ)
    {x : E} (hx : x ∈ U) :
    ∃ N ∈ 𝓝 x, ∃ g : E → F →L[ℝ] ℝ, ContDiffOn ℝ ∞ g N ∧ w =ᵐ[μ.restrict N] g := by
  -- Coordinates on `E`, and a basis of `F` with its dual basis.
  let e : E ≃L[ℝ] CoordinateSpace (Module.finrank ℝ E) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let bF := Module.finBasis ℝ F
  let bD : Module.Basis (Fin (Module.finrank ℝ F)) ℝ (F →L[ℝ] ℝ) :=
    bF.dualBasis.map LinearMap.toContinuousLinearMap
  have hbD (L : F →L[ℝ] ℝ) (l : Fin (Module.finrank ℝ F)) : bD.repr L l = L (bF l) := by
    simp [bD]
  obtain ⟨V, hxV, hVU, g, β, γ, hg, hβ, hγ, hσ, hP⟩ :=
    exists_secondOrderSystem_coordOfFun (μ := μ) hU b hA hB hC hAell e bF bD hbD hx
  have hwV : LocallyIntegrableOn w V μ := hw.mono_set hVU
  have hhV : LocallyIntegrableOn h V μ :=
    hh.continuousOn.locallyIntegrableOn hU.measurableSet |>.mono_set hVU
  let Ω : TopologicalSpace.Opens (CoordinateSpace (Module.finrank ℝ E)) :=
    ⟨e.symm ⁻¹' V, V.isOpen.preimage e.symm.continuous⟩
  have hΩ : MapsTo e.symm Ω V := fun z hz ↦ hz
  have hVΩ : MapsTo e V Ω := fun y hy ↦ by simpa [Ω] using hy
  -- The weak equation says that the system has the coordinate distributions of `h` as right side.
  have hT := singularSupport_eq_empty_of_secondOrderSystem (fun i ↦ e (b i)) hg hβ hγ
    (fun z hz ↦ hσ z hz) (T := coordOfFun e hΩ bD w μ) fun k ↦ by
      convert singularSupport_coordOfFun_eq_empty (μ := μ) e hΩ bD (hh.mono hVU) k using 2
      ext φ
      set θ : 𝓓(V, ℝ) := e.symm.transportTestFunction hΩ φ
      have hθ : (fun y ↦ θ y • bF k) = fun y ↦ φ (e y) • bF k := funext fun y ↦ by simp [θ]
      rw [hP hΩ hwV k φ, integral_complex_ofReal,
        hwh _ (hθ ▸ θ.contDiff.smul contDiff_const) (hθ ▸ θ.hasCompactSupport.smul_right)
          (hθ ▸ (tsupport_smul_subset_left _ _).trans (θ.tsupport_subset.trans hVU)),
        coordOfFun_apply e hΩ bD hhV, ← integral_complex_ofReal]
      exact integral_congr_ae (ae_of_all _ fun y ↦ by simp [hbD, Complex.real_smul])
  obtain ⟨g, hg, hwg⟩ :=
    exists_contDiffOn_ae_eq_of_singularSupport_coordOfFun_eq_empty e hΩ bD hVΩ hwV hT
  exact ⟨V, V.isOpen.mem_nhds hxV, g, hg, hwg⟩

/-- **Regularity of weak solutions of a system with a scalar elliptic principal part.** Let `U`
be an open subset of `E`, `b` a basis of `E`, and
`P a = -∑ i j, A i j ∂_{b j} ∂_{b i} a + ∑ i, B i (∂_{b i} a) + C a` an operator on maps
`a : E → F` with coefficients `A i j : E → ℝ` and `B i, C : E → F →L[ℝ] F` smooth on `U`, such
that `∑ i j, A i j y ξ i ξ j ≠ 0` for every `y ∈ U` and `ξ ≠ 0`. Let `w : E → F →L[ℝ] ℝ` be
locally integrable on `U` and `h : E → F →L[ℝ] ℝ` smooth on `U`, for an additive Haar measure `μ`.
If `∫ w (P a) dμ = ∫ h a dμ` for every smooth `a` with compact support in `U`, then `w` agrees
almost everywhere on `U` with a function smooth on `U`. -/
theorem exists_contDiffOn_ae_eq_of_forall_integral_apply_eq {U : Set E} (hU : IsOpen U)
    (b : Module.Basis ι ℝ E) {A : ι → ι → E → ℝ} {B : ι → E → F →L[ℝ] F} {C : E → F →L[ℝ] F}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (A i j) U) (hB : ∀ i, ContDiffOn ℝ ∞ (B i) U)
    (hC : ContDiffOn ℝ ∞ C U)
    (hAell : ∀ y ∈ U, ∀ ξ : ι → ℝ, ξ ≠ 0 → ∑ i, ∑ j, A i j y * ξ i * ξ j ≠ 0)
    {w h : E → F →L[ℝ] ℝ} (hw : LocallyIntegrableOn w U μ) (hh : ContDiffOn ℝ ∞ h U)
    (hwh : ∀ a : E → F, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ U →
      ∫ y, w y (-∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (b i)) y (b j) +
        ∑ i, B i y (fderiv ℝ a y (b i)) + C y (a y)) ∂μ = ∫ y, h y (a y) ∂μ) :
    ∃ g : E → F →L[ℝ] ℝ, ContDiffOn ℝ ∞ g U ∧ w =ᵐ[μ.restrict U] g :=
  TauCeti.exists_contDiffOn_ae_eq_of_locally fun _ hx ↦
    exists_contDiffOn_ae_eq_nhds hU b hA hB hC hAell hw hh hwh hx


/-- **Weak solutions whose right side is bounded in `W^{1,2}` are locally `H^1`.** Let `U` be
an open subset of `E`, `b` a basis of `E`, and
`P a = -∑ i j, A i j ∂_{b j} ∂_{b i} a + ∑ i, B i (∂_{b i} a) + C a` an operator on maps
`a : E → F` with coefficients `A i j : E → ℝ` and `B i, C : E → F →L[ℝ] F` smooth on `U`, such
that `∑ i j, A i j y ξ i ξ j ≠ 0` for every `y ∈ U` and `ξ ≠ 0`. Let `w : E → F →L[ℝ] ℝ` be
locally integrable on `U`, for an additive Haar measure `μ`, and suppose that for every compact
`K ⊆ U` there is `c` with
`|∫ w (P a) dμ| ≤ c * (‖a‖_{L²(μ)} + ∑ i, ‖∂_{b i} a‖_{L²(μ)})` for every smooth `a` supported
in `K`. Then, in coordinates `e : E ≃L[ℝ] CoordinateSpace n` on any open `Ω` with
`e⁻¹ '' Ω ⊆ U`, the coordinate distributions of `w` in the dual basis `bD` of a basis `bF` of
`F` are `H^1` near every point of `Ω`. -/
theorem isLocallySobolevAt_one_coordOfFun_of_abs_integral_le {U : TopologicalSpace.Opens E}
    (b : Module.Basis ι ℝ E) {A : ι → ι → E → ℝ} {B : ι → E → F →L[ℝ] F} {C : E → F →L[ℝ] F}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (A i j) U) (hB : ∀ i, ContDiffOn ℝ ∞ (B i) U)
    (hC : ContDiffOn ℝ ∞ C U)
    (hAell : ∀ y ∈ U, ∀ ξ : ι → ℝ, ξ ≠ 0 → ∑ i, ∑ j, A i j y * ξ i * ξ j ≠ 0)
    {w : E → F →L[ℝ] ℝ} (hw : LocallyIntegrableOn w U μ)
    (hwP : ∀ K : Set E, IsCompact K → K ⊆ U → ∃ c : ℝ, ∀ a : E → F, ContDiff ℝ ∞ a →
      tsupport a ⊆ K →
      |∫ y, w y (-∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (b i)) y (b j) +
        ∑ i, B i y (fderiv ℝ a y (b i)) + C y (a y)) ∂μ| ≤
        c * ((eLpNorm a 2 μ).toReal + ∑ i, (eLpNorm (fun y ↦ fderiv ℝ a y (b i)) 2 μ).toReal))
    {n : ℕ} (e : E ≃L[ℝ] CoordinateSpace n) {Ω : TopologicalSpace.Opens (CoordinateSpace n)}
    (hΩ : MapsTo e.symm Ω U) {κ : Type*} [Finite κ] (bF : Module.Basis κ ℝ F)
    (bD : Module.Basis κ ℝ (F →L[ℝ] ℝ)) (hbD : ∀ L l, bD.repr L l = L (bF l)) (k : κ)
    {z : CoordinateSpace n} (hz : z ∈ Ω) :
    (coordOfFun e hΩ bD w μ k).IsLocallySobolevAt 1 z := by
  have := Fintype.ofFinite κ
  obtain ⟨V, hxV, hVU, g, β, γ, hg, hβ, hγ, hσ, hP⟩ :=
    exists_secondOrderSystem_coordOfFun (μ := μ) U.isOpen b hA hB hC hAell e bF bD hbD (hΩ hz)
  have hwV : LocallyIntegrableOn w V μ := hw.mono_set hVU
  -- A compact neighbourhood `K ⊆ V` of `e⁻¹ z`, and the constant of the hypothesis for it.
  obtain ⟨K, hK, hxK, hKV⟩ := exists_compact_subset V.isOpen hxV
  obtain ⟨c, hc⟩ := hwP K hK (hKV.trans hVU)
  -- Restrict to the open set `Ω'` where the system of `exists_secondOrderSystem_coordOfFun` holds.
  let Ω' : TopologicalSpace.Opens (CoordinateSpace n) :=
    Ω ⊓ ⟨e.symm ⁻¹' V, V.isOpen.preimage e.symm.continuous⟩
  have hΩ' : MapsTo e.symm Ω' V := fun _ h ↦ h.2
  have hzΩ' : z ∈ Ω' := ⟨hz, hxV⟩
  rw [← isLocallySobolevAt_restrictCLM_iff (inf_le_left : Ω' ≤ Ω) hzΩ',
    restrictCLM_coordOfFun e hΩ bD hΩ' inf_le_left hw hwV]
  have h := IsLocallySobolevAt.of_secondOrderSystem (s := -1) (fun i ↦ e (b i)) hg hβ hγ
    (hσ z hxV) (T := coordOfFun e hΩ' bD w μ) ?_ k
  · norm_num at h
    exact h
  -- Each right side is `H^{-1}` near `z`, by the bound of the hypothesis.
  intro l
  -- The `L²` norm of `ψ ∘ e • bF l` for `μ` is a constant multiple of that of `ψ`.
  set m : ℝ := ‖bF l‖ * ((μ.map e).addHaarScalarFactor volume : ℝ) ^ (2 : ℝ)⁻¹
  have hL (ψ : 𝓓(Ω', ℝ)) :
      (eLpNorm (fun y ↦ ψ (e y) • bF l) 2 μ).toReal =
        m * (eLpNorm (ψ : _ → ℝ) 2 volume).toReal := by
    have h₁ : eLpNorm (fun y ↦ ψ (e y) • bF l) 2 μ = eLpNorm (‖bF l‖ • (ψ ∘ e)) 2 μ :=
      eLpNorm_congr_norm_ae
        ((ψ.continuous.comp e.continuous).smul continuous_const).aestronglyMeasurable
        (continuous_const.smul (ψ.continuous.comp e.continuous)).aestronglyMeasurable
        (ae_of_all _ fun y ↦ by simp [norm_smul, mul_comm])
    rw [h₁, eLpNorm_const_smul,
      eLpNorm_comp_continuousLinearEquiv_eq_addHaarScalarFactor_rpow_mul μ volume e,
      ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_eNorm, norm_norm, ← ENNReal.toReal_rpow,
      ENNReal.coe_toReal]
    norm_num [m, mul_assoc]
  have hde (ψ : 𝓓(Ω', ℝ)) (y v : E) :
      fderiv ℝ (fun y ↦ ψ (e y) • bF l) y v = ∂_{e v} ψ (e y) • bF l := by
    simpa using TestFunction.fderiv_comp_smul_const_apply (e : E →L[ℝ] _) ψ (bF l) y v
  refine isLocallySobolevAt_neg_one_of_norm_le hzΩ' (fun i ↦ e (b i))
    ((isOpen_interior.preimage e.symm.continuous).mem_nhds hxK) (C := max c 0 * m)
    fun φ hφ ↦ ?_
  have hsupp : tsupport (fun y ↦ φ (e y) • bF l) ⊆ K := by
    refine (tsupport_smul_subset_left _ _).trans fun y hy ↦ ?_
    have : e y ∈ tsupport φ := by
      simpa [Function.comp_def] using
        (tsupport_comp_subset_preimage (φ : _ → ℝ) e.continuous) hy
    simpa using interior_subset (hφ this)
  rw [hP hΩ' hwV l φ, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs]
  refine (hc (fun y ↦ φ (e y) • bF l) ((φ.contDiff.comp e.contDiff).smul contDiff_const)
    hsupp).trans ?_
  simp only [hde, hL, ← Finset.mul_sum, ← mul_add]
  exact (mul_le_mul_of_nonneg_right (le_max_left c 0) (by positivity)).trans_eq (by ring)

end SymplecticGeometry

end
