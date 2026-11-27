/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import Mathlib.Tactic.Module
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.SmoothTransition
import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Topology.UnitInterval

/-!
# The homotopy of the handle-core lemmas

Both handle-core lemmas, for a one-dimensional core
(`SymplecticGeometry.exists_homotopy_exact_of_closed_near_attaching_fin_one`) and for a core of
any dimension (`SymplecticGeometry.exists_homotopy_exact_of_exact_near_attaching`), end with the
same construction, which this file proves once.

Let `τ` be a smooth family of two-forms on a normed space `E` over a parameter space `L`, with a
margin `r > 0` of nondegeneracy over `K × Q`: a two-form within `r` of `τ l` at a point `x ∈ Q`,
`l ∈ K`, is nondegenerate at `x`. Let `β'` be a smooth family of one-forms, and `e` a smooth
family of isotopies of `E` with invertible differentials, starting at the identity, preserving
`Q`, and fixing an open set `U ⊇ A` on which `dβ' l = τ l` for `l ∈ K`. If `e (l, 1)` moves `Q`
into the region where `dβ' l` is within `r` of `τ l`, then

  `σ (l, t) = (e (l, a t))^* ((1 - b t) • τ l + b t • dβ' l)`,

with the smooth time steps `a = TauCeti.collaredFirstHalf` and `b = TauCeti.collaredSecondHalf`
(`b` leaves `0` only once `a` has reached `1`), is a homotopy from `τ` through forms nondegenerate
on `Q` and equal to `τ` on `U`, ending at the exact forms `d ((e (l, 1))^* β' l)`
(`SymplecticGeometry.exists_homotopy_exact_of_isotopy`). This is the compression step of
Eliashberg–Mishachev (§10.2): first squeeze `Q` into the region of approximation, then
interpolate there.

## Main results

* `SymplecticGeometry.exists_homotopy_exact_of_isotopy`

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2.
-/

public section

open Set Filter TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup L] [NormedSpace ℝ L]

/-- **The homotopy of the handle-core lemmas.** Let `τ` be a smooth family of two-forms on `E`
over `L`, `K ⊆ L` and `Q ⊆ E`, and `r > 0` such that for `l ∈ K` and `x ∈ Q` every two-form within
`r` of `τ l` at `x` is nondegenerate at `x`. Let `β'` be a smooth family of one-forms, and
`e : (L × [0, 1]) × E → E` smooth, with every slice `e (p, ·)` of invertible differential and
mapping `Q` into `Q`, `e ((l, 0), ·)` the identity, and every slice the identity on an open set
`U ⊇ A` on which `dβ' l = τ l` for `l ∈ K`. Suppose that for `l ∈ K` and `x ∈ Q`, `dβ' l` is within
`r` of `τ l` at `e ((l, 1), x)`. Then there is a smooth family `σ` of two-forms over `L × [0, 1]`
with `σ (l, 0) = τ l` such that:

* `σ (l, t)` is nondegenerate on `Q` for `l ∈ K` and every `t`;
* `σ (l, t) = τ l` on a neighbourhood `W'` of `A`, the same for all `l ∈ K` and all `t`;
* `σ (l, 1)` is exact on `E`, for every `l`;
* if `τ l` has a primitive on a neighbourhood of `Q`, then so does every `σ (l, t)`. -/
theorem exists_homotopy_exact_of_isotopy {τ : L → SmoothTwoForm 𝓘(ℝ, E) E}
    (hτ : IsSmoothFamily 𝓘(ℝ, L) τ) {K : Set L} {Q A U : Set E} {r : ℝ} (hr : 0 < r)
    (hnd : ∀ l ∈ K, ∀ x ∈ Q, ∀ σ : SmoothTwoForm 𝓘(ℝ, E) E,
      @norm (E [⋀^Fin 2]→L[ℝ] ℝ) _ (σ.val x - (τ l).val x) < r →
        (σ.bilinFormAt x).Nondegenerate)
    {β' : L → SmoothForm 𝓘(ℝ, E) E ℝ 1} (hβ' : IsSmoothFamily 𝓘(ℝ, L) β')
    {e : (L × unitInterval) × E → E}
    (he : ContMDiff ((𝓘(ℝ, L).prod (𝓡∂ 1)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ e)
    (hinv : ∀ p x, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x ↦ e (p, x)) x).IsInvertible)
    (he0 : ∀ l x, e ((l, 0), x) = x) (heQ : ∀ p, MapsTo (fun x ↦ e (p, x)) Q Q)
    (hU : IsOpen U) (hAU : A ⊆ U) (heU : ∀ p, ∀ x ∈ U, e (p, x) = x)
    (hβ'U : ∀ l ∈ K, ∀ x ∈ U, (mextDerivₗ 𝓘(ℝ, E) 1 (β' l)).val x = (τ l).val x)
    (hβ'Q : ∀ l ∈ K, ∀ x ∈ Q, @norm (E [⋀^Fin 2]→L[ℝ] ℝ) _
      ((mextDerivₗ 𝓘(ℝ, E) 1 (β' l)).val (e ((l, 1), x)) - (τ l).val (e ((l, 1), x))) < r) :
    ∃ σ : L × unitInterval → SmoothTwoForm 𝓘(ℝ, E) E,
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) σ ∧
      (∀ l, σ (l, 0) = τ l) ∧
      (∀ l ∈ K, ∀ t, ∀ x ∈ Q, ((σ (l, t)).bilinFormAt x).Nondegenerate) ∧
      (∃ W' ∈ 𝓝ˢ A, ∀ l ∈ K, ∀ t, ∀ x ∈ W', (σ (l, t)).val x = (τ l).val x) ∧
      (∀ l, ∃ γ : SmoothForm 𝓘(ℝ, E) E ℝ 1, mextDerivₗ 𝓘(ℝ, E) 1 γ = σ (l, 1)) ∧
      ∀ l, (∃ V ∈ 𝓝ˢ Q, ∃ γ : SmoothForm 𝓘(ℝ, E) E ℝ 1,
            ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, E) 1 γ).val x = (τ l).val x) →
        ∀ t, ∃ V ∈ 𝓝ˢ Q, ∃ γ : SmoothForm 𝓘(ℝ, E) E ℝ 1,
            ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, E) 1 γ).val x = (σ (l, t)).val x := by
  -- The smooth steps in time: `b` leaves `0` only once `a` has reached `1`.
  set a := collaredFirstHalf (n := ∞) le_rfl
  set c := collaredSecondHalf (n := ∞) le_rfl
  set b : unitInterval → ℝ := fun t ↦ (c t : ℝ) with hbdef
  have hb : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ b := contMDiff_subtypeVal_Icc.comp c.contMDiff
  have hab (t : unitInterval) (h : b t ≠ 0) : a t = 1 :=
    collaredFirstHalf_eq_one_of_collaredSecondHalf_ne_zero le_rfl fun (hc : c t = 0) ↦
      h (by simp only [hbdef, hc, Set.Icc.coe_zero])
  have hb₁ (t : unitInterval) : |b t| ≤ 1 := unitInterval.abs_coe_le_one (c t)
  -- The isotopies, run at the speed `a`, as one smooth map of the parameter and the point.
  set f : (L × unitInterval) × E → E := fun q ↦ e ((q.1.1, a q.1.2), q.2) with hfdef
  have hf : ContMDiff ((𝓘(ℝ, L).prod (𝓡∂ 1)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ f :=
    he.comp (((contMDiff_fst.comp contMDiff_fst).prodMk
      (a.contMDiff.comp (contMDiff_snd.comp contMDiff_fst))).prodMk contMDiff_snd)
  have hfp (p : L × unitInterval) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ fun x ↦ f (p, x) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  -- The forms moved from `τ` to `dβ'`, before the isotopy.
  set ν : L × unitInterval → SmoothTwoForm 𝓘(ℝ, E) E :=
    fun p ↦ (1 - b p.2) • τ p.1 + b p.2 • mextDerivₗ _ 1 (β' p.1) with hνdef
  have hν : IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) ν :=
    ((hτ.comp Prod.fst contMDiff_fst).fun_smul
        (contMDiff_const.sub (hb.comp contMDiff_snd))).add
      ((hβ'.mextDeriv.comp Prod.fst contMDiff_fst).fun_smul (hb.comp contMDiff_snd))
  have hνval (p : L × unitInterval) (x : E) :
      (ν p).val x = (τ p.1).val x + b p.2 •
        ((mextDerivₗ 𝓘(ℝ, E) 1 (β' p.1)).val x - (τ p.1).val x) := by
    simp only [hνdef, SmoothBundleForm.add_apply, SmoothBundleForm.smul_apply]
    module
  refine ⟨fun p ↦ SmoothForm.mpullback _ (hfp p) (ν p), hν.mpullback_family hf, fun l ↦ ?_,
    fun l hl t x hx ↦ ?_, ⟨U, hU.mem_nhdsSet.2 hAU, fun l hl t x hx ↦ ?_⟩,
    fun l ↦ ?_, fun l ⟨V, hV, γ, hγ⟩ t ↦ ?_⟩
  · -- At time `0` nothing moves.
    have hc0 : c 0 = 0 := collaredSecondHalf_zero le_rfl
    have ha0 : a 0 = 0 := collaredFirstHalf_zero le_rfl
    have hb0 : b 0 = 0 := by simp only [hbdef, hc0, Set.Icc.coe_zero]
    refine Subtype.ext (funext fun x ↦ ?_)
    rw [SmoothForm.mpullback_apply_eq_self_of_eventuallyEq_id _
        (Eventually.of_forall fun y ↦ by simp only [hfdef, ha0, he0, id]), hνval, hb0,
      zero_smul, add_zero]
  · -- Nondegeneracy on `Q`.
    set y := f ((l, t), x)
    have hyQ : y ∈ Q := heQ (l, a t) hx
    have hpull : mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x ↦ f ((l, t), x)) (ν (l, t)).val x =
        (SmoothForm.mpullback _ (hfp (l, t)) (ν (l, t))).val x := by
      rw [SmoothForm.coe_mpullback]
    refine (SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv
      (hinv (l, a t) x) hpull).1 ?_
    refine hnd l hl y hyQ _ ?_
    -- Stated in `E [⋀^Fin 2]→L[ℝ] ℝ`, whose instances give the norm, rather than in the tangent
    -- space that `hνval` is stated in, so that `rw` finds them; the two types agree by definition.
    have hsub {u v w : E [⋀^Fin 2]→L[ℝ] ℝ} {c : ℝ} (h : u = v + c • w) :
        ‖u - v‖ ≤ |c| * ‖w‖ := by
      rw [h, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    refine (hsub (hνval (l, t) y)).trans_lt ?_
    rcases eq_or_ne (b t) 0 with h0 | h0
    · rw [h0, abs_zero, zero_mul]
      exact hr
    refine (mul_le_of_le_one_left (norm_nonneg _) (hb₁ t)).trans_lt ?_
    have hy : y = e ((l, 1), x) := by simp only [y, hfdef, hab t h0]
    rw [hy]
    exact hβ'Q l hl x hx
  · -- `U` is a fixed neighbourhood of `A`.
    have hnear : (fun y ↦ f ((l, t), y)) =ᶠ[𝓝 x] id :=
      eventually_of_mem (hU.mem_nhds hx) fun y hy ↦ heU _ y hy
    rw [SmoothForm.mpullback_apply_eq_self_of_eventuallyEq_id _ hnear, hνval, hβ'U l hl x hx,
      sub_self, smul_zero, add_zero]
  · -- At time `1` the form is exact.
    have hc1 : c 1 = 1 := collaredSecondHalf_one le_rfl
    have hb1 : b 1 = 1 := by simp only [hbdef, hc1, Set.Icc.coe_one]
    refine ⟨SmoothForm.mpullback _ (hfp (l, 1)) (β' l), ?_⟩
    rw [SmoothForm.mextDerivₗ_mpullback]
    simp only [hνdef, hb1, sub_self, zero_smul, one_smul, zero_add]
  · -- Forms exact near `Q` stay exact near `Q`.
    have hνγ : ∀ y ∈ V, (mextDerivₗ 𝓘(ℝ, E) 1 ((1 - b t) • γ + b t • β' l)).val y =
        (ν (l, t)).val y := fun y hy ↦ by
      simp only [map_add, map_smul, SmoothBundleForm.add_apply, SmoothBundleForm.smul_apply,
        hγ y hy, hνdef]
    obtain ⟨V', hV', h'⟩ :=
      SmoothForm.exists_mem_nhdsSet_mextDerivₗ_mpullback_eq (hfp (l, t)) (heQ (l, a t)) hV hνγ
    exact ⟨V', hV', _, h'⟩

end SymplecticGeometry

end
