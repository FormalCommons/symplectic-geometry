/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.CubeCompression
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.ProdFiberContraction
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.NormedSpace
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.HomotopyOperator
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Module
import TauCeti.Topology.UnitInterval

/-!
# The handle-core lemma for a one-dimensional core

Let `D = (Fin 1 → ℝ) × F` with the sup norm, `F` finite-dimensional, with the cube
`Q = closedBall 0 1` and the attaching faces `A = sphere 0 1 ×ˢ closedBall 0 1`. Let `τ` be a
smooth family of two-forms on `D`, over a parameter space `L`, nondegenerate on `Q` for the
parameters of a compact `K ⊆ L`, and exact on a fixed open neighbourhood `W` of `A` for those
parameters. `SymplecticGeometry.exists_homotopy_exact_of_exact_near_attaching_fin_one` deforms
`τ`, smoothly in the parameter and in time, through forms nondegenerate on `Q` and fixed near `A`,
to forms exact on all of `D`; parameters for which `τ` is already exact near `Q` stay exact near
`Q`. This is the case `m = 1` of the handle-core lemma (McDuff–Salamon, Lemma 7.3.2).

## The construction

Write `Φ ((u, v), s) = (u, s • v)` for the fibrewise contraction onto the core and `h` for the
homotopy operator. Since the core is one-dimensional, `τ' := d (h (Φ^* τ))` equals
`τ - h (Φ^* dτ)` (`SymplecticGeometry.mextDerivₗ_homotopyOperator_mpullback_prodFiberContraction`),
so `τ'` is exact on `D`, and differs from `τ` by a term that

* vanishes at the points whose fibre segment to the core stays in `W`, where `τ` is closed, which
  is the case on an open neighbourhood `T` of `A`, and so on the part of `Q` next to `A`;
* is at most `‖v‖ · sup ‖dτ‖` at `(u, v) ∈ Q`
  (`SymplecticGeometry.norm_homotopyOperator_mpullback_prodFiberContraction_apply_le`).

Let `r` be a nondegeneracy margin of `τ` over `K × Q`
(`SymplecticGeometry.IsSmoothFamily.exists_pos_forall_nondegenerate`). The compression
`c s` of `SymplecticGeometry.exists_cubeCompression` squeezes `Q` into the union of the part next to
`A` and a tube `‖v‖ < δ` so thin that there `‖τ' - τ‖ < r`. The homotopy is
`σ (λ, t) = (c (a t))^* ((1 - b t) • τ λ + b t • τ' λ)` for smooth steps `a` and `b`, with `b`
starting once `a` has reached `1`: first the cube is compressed, then `τ` is moved to `τ'` on the
compressed cube. Every `c s` is a diffeomorphism fixing a neighbourhood of `A`, so the forms stay
nondegenerate on `Q` and equal to `τ` near `A`; and `σ (λ, 1) = c 1 ^* d (h (Φ^* τ λ))` is exact.

This differs from McDuff–Salamon's proof, which patches the primitives given near the two ends of
the core across a band around it, and lengthens the band by a zig-zag
(here `SymplecticGeometry.exists_wiggling_diffeotopy`) to make the error small. The contraction
along the fibres gives one primitive, on all of `D`, of a form close to `τ` near the core, so no
patching and no zig-zag are needed: the compression of the cube replaces them. The primitive of
the final form is `c 1 ^* h (Φ^* τ λ)`, which depends smoothly on `λ`.

The primitives of `τ` near `A` are only used through the closedness of `τ` on `W`; they need not
depend smoothly on the parameter.

## Main results

* `SymplecticGeometry.exists_homotopy_exact_of_exact_near_attaching_fin_one`

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 7.3.2.
-/

public section

open Set Metric Filter TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {F L : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup L] [NormedSpace ℝ L]

/-- A neighbourhood `T` of the attaching faces contains the part of the cube where the core
coordinate has norm above `1 - ε`, for some `0 < ε < 1`. -/
private theorem exists_forall_closedBall_mem_of_sphere_prod_subset
    {T : Set ((Fin 1 → ℝ) × F)} (hT : IsOpen T)
    (hAT : sphere (0 : Fin 1 → ℝ) 1 ×ˢ closedBall (0 : F) 1 ⊆ T) :
    ∃ ε, 0 < ε ∧ ε < 1 ∧
      ∀ x ∈ closedBall (0 : (Fin 1 → ℝ) × F) 1, 1 - ε < ‖x.1‖ → x ∈ T := by
  have hS : IsCompact (closedBall (0 : (Fin 1 → ℝ) × F) 1 \ T) :=
    (isCompact_closedBall _ _).diff hT
  rcases (closedBall (0 : (Fin 1 → ℝ) × F) 1 \ T).eq_empty_or_nonempty with he | hne
  · refine ⟨1 / 2, by norm_num, by norm_num, fun x hx _ ↦ ?_⟩
    by_contra hxT
    exact (he ▸ (⟨hx, hxT⟩ : x ∈ closedBall (0 : (Fin 1 → ℝ) × F) 1 \ T) : x ∈ (∅ : Set _))
  obtain ⟨x₀, ⟨hx₀Q, hx₀T⟩, hmax⟩ :=
    hS.exists_isMaxOn hne (continuous_norm.comp continuous_fst).continuousOn
  rw [mem_closedBall_zero_iff] at hx₀Q
  have hx₀ : ‖x₀.1‖ < 1 := by
    refine lt_of_le_of_ne ((norm_fst_le x₀).trans hx₀Q) fun h ↦ hx₀T (hAT ⟨?_, ?_⟩)
    · rwa [mem_sphere_zero_iff_norm]
    · exact mem_closedBall_zero_iff.2 ((norm_snd_le x₀).trans hx₀Q)
  refine ⟨min (1 / 2) (1 - ‖x₀.1‖), lt_min (by norm_num) (by linarith),
    (min_le_left _ _).trans_lt (by norm_num), fun x hx hx₁ ↦ ?_⟩
  by_contra hxT
  have : ‖x.1‖ ≤ ‖x₀.1‖ := hmax ⟨hx, hxT⟩
  have : min (1 / 2) (1 - ‖x₀.1‖) ≤ 1 - ‖x₀.1‖ := min_le_right _ _
  linarith

/-- **The handle-core lemma for a one-dimensional core.** On `D = (Fin 1 → ℝ) × F` with the sup
norm, `F` finite-dimensional, let `Q = closedBall 0 1` be the cube and
`A = sphere 0 1 ×ˢ closedBall 0 1` its attaching faces. Let `τ` be a smooth family of two-forms on
`D` over a normed space `L`, and `K ⊆ L` compact, such that for `λ ∈ K` the form `τ λ` is
nondegenerate on `Q` and has a primitive on the open set `W ⊇ A`. Then there is a smooth family
`σ` of two-forms over `L × [0, 1]` with `σ (λ, 0) = τ λ` such that:

* `σ (λ, t)` is nondegenerate on `Q` for `λ ∈ K` and every `t`;
* `σ (λ, t) = τ λ` on a neighbourhood `W'` of `A`, the same for all `λ ∈ K` and all `t`;
* `σ (λ, 1)` has a primitive on a neighbourhood of `Q`, the same for all `λ`;
* if `τ λ` has a primitive on a neighbourhood of `Q`, then so does every `σ (λ, t)`. -/
theorem exists_homotopy_exact_of_exact_near_attaching_fin_one {K : Set L} (hK : IsCompact K)
    {τ : L → SmoothTwoForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F)}
    (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hnd : ∀ l ∈ K, ∀ x ∈ closedBall (0 : (Fin 1 → ℝ) × F) 1,
      ((τ l).bilinFormAt x).Nondegenerate)
    {W : Set ((Fin 1 → ℝ) × F)} (hW : IsOpen W)
    (hAW : sphere (0 : Fin 1 → ℝ) 1 ×ˢ closedBall (0 : F) 1 ⊆ W)
    (hτβ : ∀ l ∈ K, ∃ β : SmoothForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F) ℝ 1,
      ∀ x ∈ W, (mextDerivₗ 𝓘(ℝ, (Fin 1 → ℝ) × F) 1 β).val x = (τ l).val x) :
    ∃ σ : L × unitInterval → SmoothTwoForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F),
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) σ ∧
      (∀ l, σ (l, 0) = τ l) ∧
      (∀ l ∈ K, ∀ t, ∀ x ∈ closedBall (0 : (Fin 1 → ℝ) × F) 1,
        ((σ (l, t)).bilinFormAt x).Nondegenerate) ∧
      (∃ W' ∈ 𝓝ˢ (sphere (0 : Fin 1 → ℝ) 1 ×ˢ closedBall (0 : F) 1), ∀ l ∈ K, ∀ t,
        ∀ x ∈ W', (σ (l, t)).val x = (τ l).val x) ∧
      (∃ V ∈ 𝓝ˢ (closedBall (0 : (Fin 1 → ℝ) × F) 1), ∀ l,
        ∃ γ : SmoothForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F) ℝ 1,
          ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (Fin 1 → ℝ) × F) 1 γ).val x = (σ (l, 1)).val x) ∧
      ∀ l, (∃ V ∈ 𝓝ˢ (closedBall (0 : (Fin 1 → ℝ) × F) 1),
          ∃ γ : SmoothForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F) ℝ 1,
            ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (Fin 1 → ℝ) × F) 1 γ).val x = (τ l).val x) →
        ∀ t, ∃ V ∈ 𝓝ˢ (closedBall (0 : (Fin 1 → ℝ) × F) 1),
          ∃ γ : SmoothForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F) ℝ 1,
            ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (Fin 1 → ℝ) × F) 1 γ).val x = (σ (l, t)).val x := by
  have hΦ := contMDiff_prodFiberContraction (Fin 1 → ℝ) F
  -- `τ' l = d (h (Φ^* τ l))` is exact, and equals `τ l - η l` with `η l = h (Φ^* d (τ l))`.
  set τ' : L → SmoothTwoForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F) := fun l ↦
    mextDerivₗ _ 1 (SmoothForm.homotopyOperator (SmoothForm.mpullback _ hΦ (τ l))) with hτ'def
  set η : L → SmoothTwoForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F) := fun l ↦
    SmoothForm.homotopyOperator (SmoothForm.mpullback _ hΦ (mextDerivₗ _ 2 (τ l))) with hηdef
  have hτη (l : L) : τ' l = τ l - η l :=
    mextDerivₗ_homotopyOperator_mpullback_prodFiberContraction (k := 1) (by simp) (τ l)
  have hτ' : IsSmoothFamily 𝓘(ℝ, L) τ' :=
    ((hτ.mpullback _ hΦ).homotopyOperator).mextDeriv
  -- The points whose fibre segment to the core stays in `W` form an open neighbourhood of `A`.
  set T : Set ((Fin 1 → ℝ) × F) := {x | ∀ s : unitInterval, (x.1, (s : ℝ) • x.2) ∈ W} with hTdef
  have hT : IsOpen T := by
    have hc : Continuous fun p : ((Fin 1 → ℝ) × F) × unitInterval ↦ (p.1.1, (p.2 : ℝ) • p.1.2) :=
      by fun_prop
    have hTc : Tᶜ = Prod.fst '' ((fun p : ((Fin 1 → ℝ) × F) × unitInterval ↦
        (p.1.1, (p.2 : ℝ) • p.1.2)) ⁻¹' Wᶜ) := by
      ext x
      simp [hTdef, and_assoc]
    rw [← isClosed_compl_iff, hTc]
    exact isClosedMap_fst_of_compactSpace _ (hW.isClosed_compl.preimage hc)
  have hAT : sphere (0 : Fin 1 → ℝ) 1 ×ˢ closedBall (0 : F) 1 ⊆ T := fun x hx s ↦ by
    refine hAW ⟨hx.1, mem_closedBall_zero_iff.2 ?_⟩
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (unitInterval.abs_coe_le_one s)).trans
      (mem_closedBall_zero_iff.1 hx.2)
  -- On `T`, the error term `η` vanishes, since `τ` is closed on `W`.
  have hηT : ∀ l ∈ K, ∀ x ∈ T, (η l).val x = 0 := by
    intro l hl x hx
    obtain ⟨β, hβ⟩ := hτβ l hl
    simp only [hηdef, SmoothForm.coe_homotopyOperator, SmoothForm.coe_mpullback]
    refine homotopyOperator_mpullback_prodFiberContraction_apply_eq_zero fun s ↦ ?_
    exact SmoothForm.mextDerivₗ_apply_eq_zero_of_eventuallyEq_mextDerivₗ (β := β)
      (eventually_of_mem (hW.mem_nhds (hx s)) fun z hz ↦ (hβ z hz).symm)
  obtain ⟨ε, hε, hε₁, hεT⟩ := exists_forall_closedBall_mem_of_sphere_prod_subset hT hAT
  -- On the cube, the error term is bounded by `‖v‖ * C`.
  obtain ⟨C, hC⟩ := hτ.mextDeriv.exists_norm_val_le hK (isCompact_closedBall (0 : _) 1)
  have hηQ : ∀ l ∈ K, ∀ y ∈ closedBall (0 : (Fin 1 → ℝ) × F) 1,
      @norm (((Fin 1 → ℝ) × F) [⋀^Fin 2]→L[ℝ] ℝ) _ ((η l).val y) ≤ ‖y.2‖ * C := by
    intro l hl y hy
    simp only [hηdef, SmoothForm.coe_homotopyOperator, SmoothForm.coe_mpullback]
    refine norm_homotopyOperator_mpullback_prodFiberContraction_apply_le _ y fun s ↦ hC l hl _ ?_
    rw [mem_closedBall_zero_iff] at hy ⊢
    refine max_le ((norm_fst_le y).trans hy) ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (unitInterval.abs_coe_le_one s)).trans
      ((norm_snd_le y).trans hy)
  -- The nondegeneracy margin, and the width of the tube.
  obtain ⟨r, hr, hnd'⟩ := hτ.exists_pos_forall_nondegenerate hK (isCompact_closedBall _ _) hnd
  have hC₁ : 0 < |C| + 1 := by positivity
  set δ := r / (|C| + 1) with hδdef
  have hδ : 0 < δ := div_pos hr hC₁
  obtain ⟨ψ, hψ, hψpos, hψ0, hψA, hψQ, hψ1⟩ := exists_cubeCompression (F := F) hε hε₁ hδ
  -- The smooth steps in time.
  set a : unitInterval → ℝ := fun t ↦ Real.smoothTransition (2 * (t : ℝ))
  set b : unitInterval → ℝ := fun t ↦ Real.smoothTransition (2 * (t : ℝ) - 1)
  have ha : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ a :=
    (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)).contMDiff.comp
      contMDiff_subtypeVal_Icc
  have hb : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ b :=
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub
      contDiff_const)).contMDiff.comp contMDiff_subtypeVal_Icc
  have hab (t : unitInterval) (h : b t ≠ 0) : a t = 1 := by
    have : ¬ 2 * (t : ℝ) - 1 ≤ 0 := fun h' ↦ h (Real.smoothTransition.zero_of_nonpos h')
    exact Real.smoothTransition.one_of_one_le (by linarith)
  have hb₁ (t : unitInterval) : |b t| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  -- The compressions, as one smooth map of the parameter and the point.
  set f : (L × unitInterval) × ((Fin 1 → ℝ) × F) → (Fin 1 → ℝ) × F :=
    fun q ↦ prodFiberScaling (fun u ↦ ψ (a q.1.2, u)) q.2 with hfdef
  have hf : ContMDiff ((𝓘(ℝ, L).prod (𝓡∂ 1)).prod 𝓘(ℝ, (Fin 1 → ℝ) × F))
      𝓘(ℝ, (Fin 1 → ℝ) × F) ∞ f :=
    contMDiff_prodFiberScaling_family (ψ := fun q : (L × unitInterval) × (Fin 1 → ℝ) ↦
      ψ (a q.1.2, q.2)) (hψ.contMDiff.comp
        ((ha.comp (contMDiff_snd.comp contMDiff_fst)).prodMk_space contMDiff_snd))
  have hfp (p : L × unitInterval) :
      ContMDiff 𝓘(ℝ, (Fin 1 → ℝ) × F) 𝓘(ℝ, (Fin 1 → ℝ) × F) ∞ fun x ↦ f (p, x) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  -- The forms moved from `τ` to `τ'`, before the compression.
  set ν : L × unitInterval → SmoothTwoForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F) :=
    fun p ↦ (1 - b p.2) • τ p.1 + b p.2 • τ' p.1 with hνdef
  have hν : IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) ν :=
    ((hτ.comp Prod.fst contMDiff_fst).fun_smul
        (contMDiff_const.sub (hb.comp contMDiff_snd))).add
      ((hτ'.comp Prod.fst contMDiff_fst).fun_smul (hb.comp contMDiff_snd))
  have hνval (p : L × unitInterval) (x : (Fin 1 → ℝ) × F) :
      (ν p).val x = (τ p.1).val x - b p.2 • (η p.1).val x := by
    simp only [hνdef, hτη, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub,
      Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
    module
  -- Pullback along a map that is the identity near `x` does not change the value at `x`.
  have hid (p : L × unitInterval) (θ : SmoothTwoForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F))
      {x : (Fin 1 → ℝ) × F} (hx : (fun y ↦ f (p, y)) =ᶠ[𝓝 x] id) :
      (SmoothForm.mpullback _ (hfp p) θ).val x = θ.val x := by
    rw [SmoothForm.coe_mpullback, hx.mpullback_eq, TauCeti.mpullback_id]
  refine ⟨fun p ↦ SmoothForm.mpullback _ (hfp p) (ν p), hν.mpullback_family hf, fun l ↦ ?_,
    fun l hl t x hx ↦ ?_, ⟨T ∩ {x | 1 - ε / 2 < ‖x.1‖}, ?_, fun l hl t x hx ↦ ?_⟩,
    ⟨univ, univ_mem, fun l ↦ ?_⟩, fun l ⟨V, hV, γ, hγ⟩ t ↦ ?_⟩
  · -- At time `0` nothing moves.
    have hb0 : b 0 = 0 := Real.smoothTransition.zero_of_nonpos (by simp)
    have ha0 : a 0 = 0 := Real.smoothTransition.zero_of_nonpos (by simp)
    refine Subtype.ext (funext fun x ↦ ?_)
    rw [hid (l, 0) _ (Eventually.of_forall fun y ↦ by simp [hfdef, ha0, hψ0]), hνval, hb0,
      zero_smul, sub_zero]
  · -- Nondegeneracy on the cube.
    set y := f ((l, t), x) with hydef
    have hyQ : y ∈ closedBall (0 : (Fin 1 → ℝ) × F) 1 := hψQ (a t) hx
    have hdf : (mfderiv 𝓘(ℝ, (Fin 1 → ℝ) × F) 𝓘(ℝ, (Fin 1 → ℝ) × F)
        (fun x ↦ f ((l, t), x)) x).IsInvertible :=
      (isLocalDiffeomorph_prodFiberScaling (hψ.comp (contDiff_const.prodMk contDiff_id))
        (fun u ↦ (hψpos _).1.ne')).isInvertible_mfderiv (by simp) x
    have hpull : mpullback 𝓘(ℝ, (Fin 1 → ℝ) × F) 𝓘(ℝ, (Fin 1 → ℝ) × F)
        (fun x ↦ f ((l, t), x)) (ν (l, t)).val x =
        (SmoothForm.mpullback _ (hfp (l, t)) (ν (l, t))).val x := by
      rw [SmoothForm.coe_mpullback]
    refine (SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv hdf hpull).1 ?_
    refine hnd' l hl y hyQ _ ?_
    have hnorm : @norm (((Fin 1 → ℝ) × F) [⋀^Fin 2]→L[ℝ] ℝ) _
        ((ν (l, t)).val y - (τ l).val y) ≤
        |b t| * @norm (((Fin 1 → ℝ) × F) [⋀^Fin 2]→L[ℝ] ℝ) _ ((η l).val y) := by
      erw [hνval, sub_sub_cancel_left, norm_neg, ← Real.norm_eq_abs]
      exact norm_smul_le (β := ((Fin 1 → ℝ) × F) [⋀^Fin 2]→L[ℝ] ℝ) (b t) _
    refine hnorm.trans_lt ?_
    rcases eq_or_ne (b t) 0 with h0 | h0
    · rw [h0, abs_zero, zero_mul]
      exact hr
    have hy1 : y = prodFiberScaling (fun u ↦ ψ (1, u)) x := by
      simp only [hydef, hfdef, hab t h0]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hb₁ t)).trans_lt ?_
    rcases hy1 ▸ hψ1 hx with htube | hslab
    · calc _ ≤ ‖y.2‖ * C := hηQ l hl y hyQ
        _ ≤ ‖y.2‖ * (|C| + 1) :=
          mul_le_mul_of_nonneg_left ((le_abs_self C).trans (by linarith)) (norm_nonneg _)
        _ < δ * (|C| + 1) := mul_lt_mul_of_pos_right (hy1 ▸ htube) hC₁
        _ = r := by rw [hδdef, div_mul_cancel₀ _ hC₁.ne']
    · rw [hηT l hl y (hεT y hyQ (hy1 ▸ hslab))]
      exact (norm_zero (E := ((Fin 1 → ℝ) × F) [⋀^Fin 2]→L[ℝ] ℝ)).trans_lt hr
  · -- A fixed neighbourhood of the faces.
    refine (hT.inter (isOpen_lt continuous_const (continuous_norm.comp continuous_fst))).mem_nhdsSet
      |>.2 fun x hx ↦ ⟨hAT hx, ?_⟩
    have : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.1 hx.1
    change 1 - ε / 2 < ‖x.1‖
    rw [this]
    linarith
  · have hnear : (fun y ↦ f ((l, t), y)) =ᶠ[𝓝 x] id :=
      eventually_of_mem ((isOpen_lt continuous_const
        (continuous_norm.comp continuous_fst)).mem_nhds hx.2) fun y hy ↦ hψA _ y hy
    rw [hid (l, t) _ hnear, hνval, hηT l hl x hx.1, smul_zero, sub_zero]
  · -- At time `1` the form is exact.
    have hb1 : b 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
    refine ⟨SmoothForm.mpullback _ (hfp (l, 1))
      (SmoothForm.homotopyOperator (SmoothForm.mpullback _ hΦ (τ l))), fun x _ ↦ ?_⟩
    rw [SmoothForm.mextDerivₗ_mpullback]
    simp only [hνdef, hb1, sub_self, zero_smul, one_smul, zero_add, hτ'def]
  · -- Forms exact near the cube stay exact near the cube.
    have hνγ : ∀ y ∈ V, (mextDerivₗ 𝓘(ℝ, (Fin 1 → ℝ) × F) 1 ((1 - b t) • γ + b t •
        SmoothForm.homotopyOperator (SmoothForm.mpullback _ hΦ (τ l)))).val y =
        (ν (l, t)).val y := fun y hy ↦ by
      simp only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
        Pi.smul_apply, hγ y hy, hνdef, hτ'def]
    obtain ⟨V', hV', h'⟩ :=
      SmoothForm.exists_mem_nhdsSet_mextDerivₗ_mpullback_eq (hfp (l, t)) (hψQ (a t)) hV hνγ
    exact ⟨V', hV', _, h'⟩

end SymplecticGeometry

end
