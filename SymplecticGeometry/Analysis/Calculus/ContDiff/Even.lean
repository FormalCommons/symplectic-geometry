/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.SpecialFunctions.Sqrt
import SymplecticGeometry.Analysis.Calculus.ContDiff.Seeley.Extension
import TauCeti.Analysis.Calculus.Deriv.Parity
import TauCeti.Analysis.Calculus.Hadamard

/-!
# Smooth even and odd functions of one real variable

Whitney's theorem: a smooth even function `f : ℝ → ℝ` is `g (t ^ 2)` for a smooth `g`, and a
smooth odd one is `t * g (t ^ 2)`. Hence `v ↦ f ‖v‖` is smooth on a real inner product space
for every smooth even `f`.

A smooth odd `f` is `t * k t` with `k` smooth and even, by Tau Ceti's Hadamard lemma
(`ContDiff.sub_eq_hadamardFactor_apply`, `ContDiff.contDiff_hadamardFactor`). For a smooth
even `f`, applying this to the odd function `deriv f` gives a smooth even `k` with
`deriv f t = t * k t`, so that `s ↦ f (√s)` has derivative `s ↦ k (√s) / 2` on `[0, ∞)`
(at `0` by `hasDerivWithinAt_Ici_of_tendsto_deriv`). By induction on the order,
`s ↦ f (√s)` is smooth on `[0, ∞)`, and Seeley's extension
(`SymplecticGeometry.contDiff_seeleyExtend`) gives a smooth function on `ℝ` that agrees
with it there.

## Main results

* `Function.Odd.exists_contDiff_even_mul`: a smooth odd function is `t * k t` with `k` smooth
  and even.
* `Function.Even.contDiffOn_comp_sqrt`: for a smooth even `f`, `s ↦ f (√s)` is smooth on
  `[0, ∞)`.
* `Function.Even.exists_contDiff_comp_sq`: a smooth even `f` is `g (t ^ 2)` with `g` smooth.
* `Function.Odd.exists_contDiff_mul_comp_sq`: a smooth odd `f` is `t * g (t ^ 2)` with `g`
  smooth.
* `Function.Even.contDiff_comp_norm`: for a smooth even `f`, `v ↦ f ‖v‖` is smooth.

## References

* H. Whitney, *Differentiable even functions*, Duke Math. J. 10 (1943), 159–160.
-/

public section

open Set Filter
open scoped ContDiff Topology

namespace Function

/-- A smooth odd function `f : ℝ → ℝ` is `t * k t` for a smooth even function `k`. -/
theorem Odd.exists_contDiff_even_mul {f : ℝ → ℝ} (hf : f.Odd) (hc : ContDiff ℝ ∞ f) :
    ∃ k : ℝ → ℝ, ContDiff ℝ ∞ k ∧ k.Even ∧ ∀ t, f t = t * k t := by
  set k : ℝ → ℝ := fun t ↦ hadamardFactor f 0 t 1
  have hk : ∀ t, f t = t * k t := fun t ↦ by
    have h := ContDiff.sub_eq_hadamardFactor_apply f (hc.of_le (by simp)) 0 t
    rw [hf.map_zero, sub_zero, sub_zero] at h
    rw [h, show t = t • (1 : ℝ) by simp, ContinuousLinearMap.map_smul, smul_eq_mul]
    simp [k]
  refine ⟨k, ((hc.contDiff_hadamardFactor f 0).clm_apply contDiff_const), fun t ↦ ?_, hk⟩
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have h := hf t
    rw [hk, hk, neg_mul, neg_inj] at h
    exact mul_left_cancel₀ (neg_ne_zero.2 ht) (by linarith)

/-- If `f` is smooth and `deriv f t = t * k t` with `k` continuous, then `s ↦ f (√s)` has
derivative `k (√s) / 2` within `[0, ∞)` at each `s ≥ 0`. -/
private theorem hasDerivWithinAt_comp_sqrt_of_deriv_eq_mul {f k : ℝ → ℝ} (hc : ContDiff ℝ ∞ f)
    (hck : Continuous k) (hk : ∀ t, _root_.deriv f t = t * k t) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun s ↦ f √s) (k √s / 2) (Ici 0) s := by
  have hd : Differentiable ℝ f := hc.differentiable (by simp)
  have hpos : ∀ x, 0 < x → HasDerivAt (fun s ↦ f √s) (k √x / 2) x := fun x hx ↦ by
    have hx' : √x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    refine ((hd _).hasDerivAt.comp x (Real.hasDerivAt_sqrt hx.ne')).congr_deriv ?_
    rw [hk]
    field_simp
  rcases hs.lt_or_eq with hs | rfl
  · exact (hpos s hs).hasDerivWithinAt
  · refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
      (fun x hx ↦ (hpos x hx).differentiableAt.differentiableWithinAt)
      (hd.continuous.comp Real.continuous_sqrt).continuousWithinAt self_mem_nhdsWithin ?_
    refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun x hx ↦ (hpos x hx).deriv.symm) ?_
    exact (((hck.comp Real.continuous_sqrt).div_const 2).tendsto 0).mono_left nhdsWithin_le_nhds

/-- For a smooth even `f : ℝ → ℝ`, the function `s ↦ f (√s)` is smooth on `[0, ∞)`. -/
theorem Even.contDiffOn_comp_sqrt {f : ℝ → ℝ} (hf : f.Even) (hc : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (fun s ↦ f √s) (Ici 0) := by
  suffices h : ∀ n : ℕ, ∀ f : ℝ → ℝ, f.Even → ContDiff ℝ ∞ f →
      ContDiffOn ℝ n (fun s ↦ f √s) (Ici 0) from contDiffOn_infty.2 fun n ↦ h n f hf hc
  intro n
  induction n with
  | zero =>
    intro f _ hc
    exact contDiffOn_zero.2 (hc.continuous.comp Real.continuous_sqrt).continuousOn
  | succ n ih =>
    intro f hf hc
    have hc' := (contDiff_infty_iff_deriv.1 hc).2
    have hd : (deriv f).Odd := fun t ↦
      TauCeti.deriv_neg_eq_neg_of_eventually_even (.of_forall hf)
    obtain ⟨k, hck, hke, hk⟩ := hd.exists_contDiff_even_mul hc'
    have hder : ∀ s ∈ Ici (0 : ℝ),
        HasDerivWithinAt (fun s ↦ f √s) (k √s / 2) (Ici 0) s := fun s hs ↦
      hasDerivWithinAt_comp_sqrt_of_deriv_eq_mul hc hck.continuous hk hs
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
    refine ⟨fun s hs ↦ (hder s hs).differentiableWithinAt, by simp, ?_⟩
    refine (ih (fun t ↦ k t / 2) (fun t ↦ by simp [hke t]) (hck.div_const 2)).congr
      fun s hs ↦ ?_
    exact (hder s hs).derivWithin (uniqueDiffOn_Ici 0 s hs)

/-- **Whitney's theorem.** A smooth even function `f : ℝ → ℝ` is `g (t ^ 2)` for a smooth
function `g : ℝ → ℝ`. -/
theorem Even.exists_contDiff_comp_sq {f : ℝ → ℝ} (hf : f.Even)
    (hc : ContDiff ℝ ∞ f) : ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ ∀ t, f t = g (t ^ 2) := by
  refine ⟨_, SymplecticGeometry.contDiff_seeleyExtend (hf.contDiffOn_comp_sqrt hc),
    fun t ↦ ?_⟩
  rw [SymplecticGeometry.seeleyExtend_of_nonneg _ (sq_nonneg t), Real.sqrt_sq_eq_abs]
  rcases abs_choice t with h | h <;> simp [h, hf t]

/-- **Whitney's theorem**, odd case. A smooth odd function `f : ℝ → ℝ` is `t * g (t ^ 2)` for
a smooth function `g : ℝ → ℝ`. -/
theorem Odd.exists_contDiff_mul_comp_sq {f : ℝ → ℝ} (hf : f.Odd)
    (hc : ContDiff ℝ ∞ f) : ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ ∀ t, f t = t * g (t ^ 2) := by
  obtain ⟨k, hkc, hke, hk⟩ := hf.exists_contDiff_even_mul hc
  obtain ⟨g, hg, hkg⟩ := hke.exists_contDiff_comp_sq hkc
  exact ⟨g, hg, fun t ↦ by rw [hk, hkg]⟩

/-- For a smooth even function `f : ℝ → ℝ`, the function `v ↦ f ‖v‖` is smooth on a real
inner product space. -/
theorem Even.contDiff_comp_norm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {f : ℝ → ℝ} (hf : f.Even) (hc : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun v : V ↦ f ‖v‖ := by
  obtain ⟨g, hg, hfg⟩ := hf.exists_contDiff_comp_sq hc
  rw [show (fun v : V ↦ f ‖v‖) = g ∘ fun v ↦ ‖v‖ ^ 2 from funext fun v ↦ hfg _]
  exact hg.comp (contDiff_norm_sq ℝ)

end Function

end
