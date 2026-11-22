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
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.MeasureTheory.Function.LocalRepresentative

/-!
# Regularity for second-order systems with a scalar elliptic principal part

This file proves interior regularity for second-order systems whose principal part is one scalar
operator times the identity, in two forms.

* `Distribution.singularSupport_eq_empty_of_secondOrderSystem`: a system of distributions
  `T : κ → 𝓓'(Ω, ℂ)` on an open set `Ω ⊆ CoordinateSpace n`, written with the multiplications
  inside the derivatives,
  `∑ i j, ∂_{v i} ∂_{v j} (g i j T a) + ∑ b i, ∂_{v i} (β a b i T b) + ∑ b, γ a b T b`,
  with smooth real coefficients. If every left side is smooth on `Ω` and the symbol
  `∑ i j, g i j x ⟪v i, ξ⟫ ⟪v j, ξ⟫` vanishes at no `ξ ≠ 0`, for `x ∈ Ω`, then every `T a` is
  smooth on `Ω`. The Leibniz rule `Distribution.lineDerivOp_smulLeftCLM` moves the coefficients
  outside the derivatives, and the result is then
  `Distribution.singularSupport_eq_empty_of_ellipticSystem`.
* `SymplecticGeometry.exists_contDiffOn_ae_eq_of_forall_integral_apply_eq`: the weak form, on an
  open set `U` of a finite-dimensional real space `E` with a basis `b`. Let
  `P a = -∑ i j, A i j ∂_{b j} ∂_{b i} a + ∑ i, B i (∂_{b i} a) + C a` act on maps `a : E → F`,
  with `A i j : E → ℝ` and `B i, C : E → F →L[ℝ] F` smooth on `U`, and the quadratic form
  `∑ i j, A i j y ξ i ξ j` nondegenerate at every `y ∈ U`. If `w : E → F →L[ℝ] ℝ` is locally
  integrable on `U`, `h` is smooth on `U`, and `∫ w (P a) dμ = ∫ h a dμ` for every smooth `a` with
  compact support in `U`, for an additive Haar measure `μ`, then `w` agrees almost everywhere on
  `U` with a function smooth on `U`. This is the operator of
  `SymplecticGeometry.exists_mpullback_symm_hodgeLaplacian_eq`, the Hodge Laplacian in a chart.

For the weak form, near each point of `U` the coefficients are extended to the whole space by a
cutoff and read in coordinates `e : E ≃L[ℝ] CoordinateSpace n`. Pairing the weak equation with
`a = (φ ∘ e) • f k`, for a test function `φ` and a basis `f` of `F`, shows that the coordinate
distributions of `w` (`Distribution.coordOfFun`, in the dual basis) solve a system of the first
kind whose right sides are the coordinate distributions of `h`, which are smooth. The regular
representatives (`Distribution.exists_contDiffOn_ae_eq_of_singularSupport_coordOfFun_eq_empty`)
are glued by Tau Ceti's `TauCeti.exists_contDiffOn_ae_eq_of_locally`.

## Main results

* `TestFunction.fderiv_comp_smul_const_apply`: the derivative of `z ↦ ψ (L z) • v`.
* `Distribution.singularSupport_eq_empty_of_secondOrderSystem`.
* `SymplecticGeometry.exists_contDiffOn_ae_eq_of_forall_integral_apply_eq`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §6 (weak solutions of elliptic equations and their regularity).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1 (the transpose
  of a differential operator and the Leibniz rule).
-/

public section

open TopologicalSpace TauCeti
open scoped ContDiff Distributions LineDeriv InnerProductSpace

namespace TestFunction

/-- The derivative along `u` of `z ↦ ψ (L z) • v`, for a real test function `ψ` and a continuous
linear map `L`, is `(∂_{L u} ψ) (L y) • v`. -/
theorem fderiv_comp_smul_const_apply {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Opens E'} (L : E →L[ℝ] E') (ψ : 𝓓(Ω, ℝ)) (v : F) (y u : E) :
    fderiv ℝ (fun z ↦ ψ (L z) • v) y u = ∂_{L u} ψ (L y) • v := by
  have hψ : DifferentiableAt ℝ ψ (L y) := ψ.contDiff.differentiable (by simp) _
  have hd : HasFDerivAt (fun z ↦ ψ (L z) • v) _ y :=
    (hψ.hasFDerivAt.comp y L.hasFDerivAt).smul_const v
  rw [hd.fderiv, lineDerivOp_apply_eq_fderiv]
  simp

end TestFunction

namespace Distribution

variable {n : ℕ} {Ω : Opens (CoordinateSpace n)} {ι κ : Type*} [Fintype ι] [Fintype κ]

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
    (a : κ) : (T a).singularSupport = ∅ := by
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
    · exact (hg i j).fderiv_apply_const _
    · exact (hg i j).fderiv_apply_const _
    · exact hβ a b i
    · exact ((hg i j).fderiv_apply_const _).fderiv_apply_const _
    · exact (hβ a b i).fderiv_apply_const _
    · exact hγ a b
  refine singularSupport_eq_empty_of_ellipticSystem (t := Finset.univ) (c := fun _ ↦ 1)
    (g := fun p : ι × ι ↦ g p.1 p.2) (k := fun _ ↦ 2) (m := fun p ↦ ![v p.1, v p.2])
    (t' := Finset.univ) (c' := c') (h := h) (k' := k') (m' := m')
    (fun p ↦ hg p.1 p.2) hh (M := 2) (fun _ _ ↦ le_rfl) ?_ ?_ ?_ a
  · rintro (_ | _) - <;> simp [k']
  · intro x hx ξ hξ
    simp only [one_mul, constCoeffPrincipalSymbol_def, Finset.filter_true, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fintype.sum_prod_type]
    exact_mod_cast (by simpa only [mul_assoc] using hσ x hx ξ hξ)
  · intro a
    convert hT a using 2
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

end Distribution

namespace SymplecticGeometry

open MeasureTheory Set Filter Distribution
open scoped Topology

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Fintype ι]

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- The weak equation, paired with `a = (φ ∘ e) • bF k`, says that the coordinate distributions of
`w` in the dual basis `bD` of `bF` solve a system of the form of
`Distribution.singularSupport_eq_empty_of_secondOrderSystem`, with the coefficients extended by a
cutoff `χ` equal to `1` on `V`, and right sides those of `h`. -/
private theorem secondOrderSystem_coordOfFun_eq {U : Set E} (b : Module.Basis ι ℝ E)
    {A : ι → ι → E → ℝ} {B : ι → E → F →L[ℝ] F} {C : E → F →L[ℝ] F} {w h : E → F →L[ℝ] ℝ}
    (hwh : ∀ a : E → F, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ U →
      ∫ y, w y (-∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (b i)) y (b j) +
        ∑ i, B i y (fderiv ℝ a y (b i)) + C y (a y)) ∂μ = ∫ y, h y (a y) ∂μ)
    {V : TopologicalSpace.Opens E} (hVU : (V : Set E) ⊆ U) (hwV : LocallyIntegrableOn w V μ)
    (hhV : LocallyIntegrableOn h V μ) {χ : E → ℝ} (hχV : ∀ y ∈ V, χ y = 1) {n : ℕ}
    (e : E ≃L[ℝ] CoordinateSpace n) {Ω : TopologicalSpace.Opens (CoordinateSpace n)}
    (hΩ : MapsTo e.symm Ω V) {κ : Type*} [Fintype κ] (bF : Module.Basis κ ℝ F)
    (bD : Module.Basis κ ℝ (F →L[ℝ] ℝ)) (hbD : ∀ L l, bD.repr L l = L (bF l))
    (hg : ∀ i j, ContDiff ℝ ∞ fun z ↦ -(χ (e.symm z) • A i j (e.symm z)))
    (hβ : ∀ k l i, ContDiff ℝ ∞ fun z ↦ -(χ (e.symm z) • bF.repr (B i (e.symm z) (bF k)) l))
    (hγ : ∀ k l, ContDiff ℝ ∞ fun z ↦ χ (e.symm z) • bF.repr (C (e.symm z) (bF k)) l) (k : κ) :
    ∑ i, ∑ j, ∂_{e (b i)} (∂_{e (b j)} (smulLeftCLM (hg i j) (coordOfFun e hΩ bD w μ k))) +
      ∑ l, ∑ i, ∂_{e (b i)} (smulLeftCLM (hβ k l i) (coordOfFun e hΩ bD w μ l)) +
      ∑ l, smulLeftCLM (hγ k l) (coordOfFun e hΩ bD w μ l) = coordOfFun e hΩ bD h μ k := by
  classical
  have hwbF (y : E) (u : F) : w y u = ∑ l, bF.repr u l * w y (bF l) := by
    calc w y u = w y (∑ l, bF.repr u l • bF l) := by rw [bF.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  ext φ
  -- The test vector field `a = (φ ∘ e) • bF k` and its derivatives.
  set θ : 𝓓(V, ℝ) := e.symm.transportTestFunction hΩ φ
  have hθ (y : E) : θ y = φ (e y) := by simp [θ]
  let a : E → F := fun y ↦ φ (e y) • bF k
  have ha : (fun y ↦ θ y • bF k) = a := funext fun y ↦ by rw [hθ]
  have hwa := hwh a (ha ▸ θ.contDiff.smul contDiff_const)
    (ha ▸ θ.hasCompactSupport.smul_right)
    (ha ▸ (tsupport_smul_subset_left _ _).trans (θ.tsupport_subset.trans hVU))
  have hde (ψ : 𝓓(Ω, ℝ)) (u : F) (y z : E) :
      fderiv ℝ (fun y ↦ ψ (e y) • u) y z = ∂_{e z} ψ (e y) • u := by
    simpa using TestFunction.fderiv_comp_smul_const_apply (e : E →L[ℝ] _) ψ u y z
  simp only [a, hde] at hwa
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
  simp only [coordOfFun_apply e hΩ bD hwV, coordOfFun_apply e hΩ bD hhV]
  rw [← integral_finsetSum _ fun l _ ↦ hint _ l]
  have hP (y : E) : ∑ l, Ψ l (e y) • (bD.repr (w y) l : ℂ) =
      ((w y (-∑ i, ∑ j, A i j y • ∂_{e (b j)} (∂_{e (b i)} φ) (e y) • bF k +
        ∑ i, B i y (∂_{e (b i)} φ (e y) • bF k) + C y (φ (e y) • bF k)) : ℝ) : ℂ) := by
    have hwB (i : ι) : w y (B i y (bF k)) = ∑ l, bF.repr (B i y (bF k)) l * w y (bF l) :=
      hwbF y _
    have hwC : w y (C y (bF k)) = ∑ l, bF.repr (C y (bF k)) l * w y (bF l) := hwbF y _
    simp only [map_add, map_neg, map_sum, map_smul, smul_eq_mul, hwB, hwC]
    by_cases hy : y ∈ V
    · simp only [smul_eq_mul, map_neg, Finset.sum_neg_distrib, add_apply, apply_ite,
        FunLike.coe_zero, ite_apply, sum_apply, TestFunction.smulLeftCLM_apply,
        ContinuousLinearEquiv.symm_apply_apply, hχV y hy, one_mul, TestFunction.lineDerivOp_apply,
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
  calc _ = ∫ y, ((w y (-∑ i, ∑ j, A i j y • ∂_{e (b j)} (∂_{e (b i)} φ) (e y) • bF k +
        ∑ i, B i y (∂_{e (b i)} φ (e y) • bF k) + C y (φ (e y) • bF k)) : ℝ) : ℂ) ∂μ :=
        integral_congr_ae (ae_of_all _ hP)
    _ = ∫ y, ((h y (φ (e y) • bF k) : ℝ) : ℂ) ∂μ := by
      rw [integral_complex_ofReal, integral_complex_ofReal, hwa]
    _ = _ := integral_congr_ae (ae_of_all _ fun y ↦ by simp [hbD, Complex.real_smul])

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
  classical
  -- A cutoff `χ` equal to `1` on an open neighbourhood `V ⊆ U` of `x`.
  obtain ⟨χ, hχ, -, hχ1, -, hχU⟩ :=
    isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one hU (singleton_subset_iff.2 hx)
  obtain ⟨t, ht1, ht, hxt⟩ := eventually_nhds_iff.1 (hχ1 x rfl)
  let V : TopologicalSpace.Opens E := ⟨t ∩ U, ht.inter hU⟩
  have hVU : (V : Set E) ⊆ U := inter_subset_right
  have hwV : LocallyIntegrableOn w V μ := hw.mono_set hVU
  -- Coordinates on `E`, and a basis of `F` with its dual basis.
  let e : E ≃L[ℝ] CoordinateSpace (Module.finrank ℝ E) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let Ω : TopologicalSpace.Opens (CoordinateSpace (Module.finrank ℝ E)) :=
    ⟨e.symm ⁻¹' V, V.isOpen.preimage e.symm.continuous⟩
  have hΩ : MapsTo e.symm Ω V := fun z hz ↦ hz
  have hVΩ : MapsTo e V Ω := fun y hy ↦ by simpa [Ω] using hy
  let bF := Module.finBasis ℝ F
  let bD : Module.Basis (Fin (Module.finrank ℝ F)) ℝ (F →L[ℝ] ℝ) :=
    bF.dualBasis.map LinearMap.toContinuousLinearMap
  have hbD (L : F →L[ℝ] ℝ) (l : Fin (Module.finrank ℝ F)) : bD.repr L l = L (bF l) := by
    simp [bD]
  -- The coefficients, extended by the cutoff and read in the coordinates.
  have hext (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) :
      ContDiff ℝ ∞ fun z ↦ χ (e.symm z) • f (e.symm z) :=
    (hf.contDiff_smul_of_tsupport_subset hU hχ.contDiffOn hχU).comp e.symm.contDiff
  have hrepr {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (l : Fin (Module.finrank ℝ F)) :
      ContDiffOn ℝ ∞ (fun y ↦ bF.repr (f y) l) U := by
    simpa [Function.comp_def] using (bF.coord l).toContinuousLinearMap.contDiff.comp_contDiffOn hf
  let v : ι → CoordinateSpace (Module.finrank ℝ E) := fun i ↦ e (b i)
  let g : ι → ι → CoordinateSpace (Module.finrank ℝ E) → ℝ := fun i j z ↦
    -(χ (e.symm z) • A i j (e.symm z))
  let β : Fin (Module.finrank ℝ F) → Fin (Module.finrank ℝ F) → ι →
      CoordinateSpace (Module.finrank ℝ E) → ℝ := fun k l i z ↦
    -(χ (e.symm z) • bF.repr (B i (e.symm z) (bF k)) l)
  let γ : Fin (Module.finrank ℝ F) → Fin (Module.finrank ℝ F) →
      CoordinateSpace (Module.finrank ℝ E) → ℝ := fun k l z ↦
    χ (e.symm z) • bF.repr (C (e.symm z) (bF k)) l
  have hg (i j : ι) : ContDiff ℝ ∞ (g i j) := (hext _ (hA i j)).neg
  have hβ (k l i) : ContDiff ℝ ∞ (β k l i) :=
    (hext _ (hrepr ((hB i).clm_apply contDiffOn_const) l)).neg
  have hγ (k l) : ContDiff ℝ ∞ (γ k l) := hext _ (hrepr (hC.clm_apply contDiffOn_const) l)
  -- The weak equation is a second-order system for the coordinate distributions of `w`.
  have hT := singularSupport_eq_empty_of_secondOrderSystem v hg hβ hγ ?_
    (T := coordOfFun e hΩ bD w μ) fun k ↦ by
      rw [secondOrderSystem_coordOfFun_eq b hwh hVU hwV
        (hh.continuousOn.locallyIntegrableOn hU.measurableSet |>.mono_set hVU)
        (fun y hy ↦ ht1 y hy.1) e hΩ bF bD hbD hg hβ hγ k]
      exact singularSupport_coordOfFun_eq_empty e hΩ bD (hh.mono hVU) k
  · obtain ⟨g, hg, hwg⟩ :=
      exists_contDiffOn_ae_eq_of_singularSupport_coordOfFun_eq_empty e hΩ bD hVΩ hwV hT
    exact ⟨V, V.isOpen.mem_nhds ⟨hxt, hx⟩, g, hg, hwg⟩
  · -- Ellipticity: `ξ ≠ 0` has a nonzero coordinate `⟪e (b i), ξ⟫`.
    intro z hz ξ hξ
    have hzV : e.symm z ∈ V := hz
    have hη : (fun i ↦ ⟪v i, ξ⟫_ℝ) ≠ 0 := by
      intro hη
      exact hξ (InnerProductSpace.ext_inner_left_basis (b.map e.toLinearEquiv) fun i ↦ by
        simpa [v] using congrFun hη i)
    have := hAell _ (hVU hzV) _ hη
    simp only [g, ht1 _ hzV.1, one_smul]
    simpa [neg_mul, Finset.sum_neg_distrib] using this

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

end SymplecticGeometry

end
