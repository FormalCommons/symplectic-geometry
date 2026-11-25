/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Topology.UnitInterval
public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition

/-!
# Clipping a cube onto its attaching faces

Let `D = (ι → ℝ) × (κ → ℝ)` with the sup norms, `Q` its closed unit ball (a cube), and
`A = sphere 0 1 ×ˢ closedBall 0 1` the attaching faces of `Q` seen as a handle. This file builds a
smooth homotopy `Φ : D × [0, 1] → D` from a map that retracts a thin collar of `A` onto `A` to
the identity, which preserves `A`, `Q` and the collar at every time
(`SymplecticGeometry.exists_contMDiff_cubeClipping`). It is the homotopy that the homotopy
operator `TauCeti.SmoothForm.homotopyOperator` is applied to, through
`TauCeti.SmoothForm.mextDerivₗ_homotopyOperator_mpullback`, in the handle-core lemma of
McDuff–Salamon, Lemma 7.3.2.

The sup norm is not smooth at the corners of `A`, so the homotopy is built coordinatewise: for a
smooth odd `f : ℝ → ℝ` that is the identity on `[-(1 - 2δ), 1 - 2δ]`, `±1` beyond `1 - δ`, and
moves each point of `[-1, 1]` towards the end of its sign
(`SymplecticGeometry.exists_contDiff_odd_clip`), the homotopy is the straight line from the map
`F` that applies `f` to every coordinate to the identity. At every time each coordinate `y` of the
image of `x` satisfies `min |x| 1 ≤ |y| ≤ max |x| 1`, and so does the norm of each factor
(`min_norm_le_pi_norm_of_forall`), which gives the invariance of `A`, `Q` and the collar.

## Main results

* `min_norm_le_pi_norm_of_forall`: a coordinatewise lower bound `min ‖a i‖ c ≤ ‖b i‖` for the
  sup norm gives `min ‖a‖ c ≤ ‖b‖`.
* `SymplecticGeometry.exists_contMDiff_cubeClipping`: the clipping homotopy.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 7.3.2.
-/

public section

open Set Metric
open scoped Manifold ContDiff

/-- A coordinatewise lower bound `min ‖a i‖ c ≤ ‖b i‖` gives the same lower bound
`min ‖a‖ c ≤ ‖b‖` for the sup norms. -/
theorem min_norm_le_pi_norm_of_forall {ι : Type*} [Fintype ι] {E F : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] [∀ i, SeminormedAddGroup (F i)] {a : ∀ i, E i}
    {b : ∀ i, F i} {c : ℝ} (h : ∀ i, min ‖a i‖ c ≤ ‖b i‖) : min ‖a‖ c ≤ ‖b‖ := by
  by_contra! hb
  -- Every coordinate of `b` is below `c`, so it bounds that of `a`, and then `‖a‖ ≤ ‖b‖`.
  have : ‖a‖ ≤ ‖b‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg b)).2 fun i ↦ by
    have hi := (norm_le_pi_norm b i).trans_lt (hb.trans_le (min_le_right _ _))
    have := h i
    rw [min_le_iff] at this
    rcases this with h' | h'
    · exact h'.trans (norm_le_pi_norm b i)
    · exact absurd hi h'.not_gt
  exact this.not_gt (hb.trans_le (min_le_left _ _))

namespace SymplecticGeometry

variable {f : ℝ → ℝ}

/-- One coordinate of the clipping homotopy, at a point `s ≥ 0`, lies between `s` and `1`. -/
private theorem clip_bounds_of_nonneg (hf1 : ∀ s, |f s| ≤ 1) (hf : ∀ s ∈ Icc (0 : ℝ) 1, s ≤ f s)
    (hfR : ∀ s, 1 ≤ s → f s = 1) {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : 0 ≤ s) :
    min s 1 ≤ (1 - t) * f s + t * s ∧ (1 - t) * f s + t * s ≤ max s 1 := by
  obtain ⟨ht₀, ht₁⟩ := ht
  have hf1' := (abs_le.1 (hf1 s)).2
  rcases le_total s 1 with hs₁ | hs₁
  · have := hf s ⟨hs, hs₁⟩
    rw [min_eq_left hs₁, max_eq_right hs₁]
    constructor <;> nlinarith
  · rw [hfR s hs₁, min_eq_right hs₁, max_eq_left hs₁]
    constructor <;> nlinarith

/-- One coordinate `y` of the clipping homotopy at a point `s` satisfies
`min |s| 1 ≤ |y| ≤ max |s| 1`. -/
private theorem clip_abs_bounds (hodd : Function.Odd f) (hf1 : ∀ s, |f s| ≤ 1)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, s ≤ f s) (hfR : ∀ s, 1 ≤ s → f s = 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (s : ℝ) :
    min |s| 1 ≤ |(1 - t) * f s + t * s| ∧ |(1 - t) * f s + t * s| ≤ max |s| 1 := by
  rcases le_total 0 s with hs | hs
  · obtain ⟨h₁, h₂⟩ := clip_bounds_of_nonneg hf1 hf hfR ht hs
    have : 0 ≤ (1 - t) * f s + t * s := (le_min hs zero_le_one).trans h₁
    rw [abs_of_nonneg hs, abs_of_nonneg this]
    exact ⟨h₁, h₂⟩
  · obtain ⟨h₁, h₂⟩ := clip_bounds_of_nonneg hf1 hf hfR ht (neg_nonneg.2 hs)
    have he : (1 - t) * f (-s) + t * -s = -((1 - t) * f s + t * s) := by rw [hodd]; ring
    rw [he] at h₁ h₂
    have : 0 ≤ -((1 - t) * f s + t * s) := (le_min (neg_nonneg.2 hs) zero_le_one).trans h₁
    rw [abs_of_nonpos hs, ← abs_neg, abs_of_nonneg this]
    exact ⟨h₁, h₂⟩

/-- The straight line from the coordinatewise application of `f` to the identity, on one factor
`ι → ℝ`. -/
private theorem pi_clip_norm_bounds {ι : Type*} [Fintype ι] (hodd : Function.Odd f)
    (hf1 : ∀ s, |f s| ≤ 1) (hf : ∀ s ∈ Icc (0 : ℝ) 1, s ≤ f s) (hfR : ∀ s, 1 ≤ s → f s = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : ι → ℝ) :
    min ‖u‖ 1 ≤ ‖fun i ↦ (1 - t) * f (u i) + t * u i‖ ∧
      ‖fun i ↦ (1 - t) * f (u i) + t * u i‖ ≤ max ‖u‖ 1 := by
  refine ⟨min_norm_le_pi_norm_of_forall fun i ↦ ?_,
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_⟩
  · simpa only [Real.norm_eq_abs] using (clip_abs_bounds hodd hf1 hf hfR ht (u i)).1
  · simp only [Real.norm_eq_abs]
    exact (clip_abs_bounds hodd hf1 hf hfR ht (u i)).2.trans
      (max_le_max_right _ (by simpa using norm_le_pi_norm u i))

/-- If `f` is `±1` beyond `R ∈ (0, 1]` and bounded by `1`, then applying it to every coordinate
of a point of norm greater than `R` gives a point of norm `1`. -/
private theorem norm_comp_eq_one {ι : Type*} [Fintype ι] (hodd : Function.Odd f)
    (hf1 : ∀ s, |f s| ≤ 1) {R : ℝ} (hR : 0 < R) (hfR : ∀ s, R ≤ s → f s = 1) {u : ι → ℝ}
    (hu : R ≤ ‖u‖) : ‖fun i ↦ f (u i)‖ = 1 := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ hf1 _) ?_
  by_contra! h
  refine hu.not_gt ((pi_norm_lt_iff hR).2 fun i ↦ ?_)
  have hi : |f (u i)| < 1 := by simpa using (norm_le_pi_norm (fun i ↦ f (u i)) i).trans_lt h
  rw [Real.norm_eq_abs]
  by_contra! hRi
  rcases le_total 0 (u i) with hs | hs
  · rw [abs_of_nonneg hs] at hRi
    simp [hfR _ hRi] at hi
  · rw [abs_of_nonpos hs] at hRi
    have := hfR _ hRi
    rw [hodd] at this
    simp [neg_eq_iff_eq_neg.1 this] at hi

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The clipping homotopy of the cube onto its attaching faces.** Let `D = (ι → ℝ) × (κ → ℝ)`
with the sup norms, `Q = closedBall 0 1` and `A = sphere 0 1 ×ˢ closedBall 0 1`. For
`0 < δ ≤ 1/2` there is a smooth homotopy `Φ : D × [0, 1] → D` such that
* `Φ (·, 1)` is the identity, and every `Φ (·, t)` is the identity on `closedBall 0 (1 - 2δ)`;
* every `Φ (·, t)` maps `A` into `A`, `Q` into `Q`, and each collar
  `{x | |‖x.1‖ - 1| < ε ∧ ‖x.2‖ < 1 + ε}` into itself;
* `Φ (·, 0)` maps each such collar with `ε ≤ δ` into `A`. -/
theorem exists_contMDiff_cubeClipping {δ : ℝ} (hδ : 0 < δ) (hδ₂ : δ ≤ 1 / 2) :
    ∃ Φ : ((ι → ℝ) × (κ → ℝ)) × unitInterval → (ι → ℝ) × (κ → ℝ),
      ContMDiff (𝓘(ℝ, (ι → ℝ) × (κ → ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ∞ Φ ∧
      (∀ x, Φ (x, 1) = x) ∧ (∀ x t, ‖x‖ ≤ 1 - 2 * δ → Φ (x, t) = x) ∧
      (∀ t, MapsTo (fun x ↦ Φ (x, t)) (sphere 0 1 ×ˢ closedBall 0 1)
        (sphere 0 1 ×ˢ closedBall 0 1)) ∧
      (∀ t, MapsTo (fun x ↦ Φ (x, t)) (closedBall 0 1) (closedBall 0 1)) ∧
      (∀ ε t, MapsTo (fun x ↦ Φ (x, t)) {x | |‖x.1‖ - 1| < ε ∧ ‖x.2‖ < 1 + ε}
        {x | |‖x.1‖ - 1| < ε ∧ ‖x.2‖ < 1 + ε}) ∧
      ∀ ε ≤ δ, MapsTo (fun x ↦ Φ (x, 0)) {x | |‖x.1‖ - 1| < ε ∧ ‖x.2‖ < 1 + ε}
        (sphere 0 1 ×ˢ closedBall 0 1) := by
  obtain ⟨f, hf, hodd, hid, hfR, hf1, hfI⟩ :=
    exists_contDiff_odd_clip (r := 1 - 2 * δ) (R := 1 - δ) (by linarith) (by linarith)
      (by linarith)
  have hfR1 (s : ℝ) (hs : 1 ≤ s) : f s = 1 := hfR s (by linarith)
  -- The coordinatewise application of `f`, and the straight line from it to the identity.
  let F : (ι → ℝ) × (κ → ℝ) → (ι → ℝ) × (κ → ℝ) := fun x ↦ (fun i ↦ f (x.1 i), fun j ↦ f (x.2 j))
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_pi.2 fun i ↦ hf.comp (by fun_prop)).prodMk
      (contDiff_pi.2 fun j ↦ hf.comp (by fun_prop))
  let Φ : ((ι → ℝ) × (κ → ℝ)) × unitInterval → (ι → ℝ) × (κ → ℝ) :=
    fun p ↦ (1 - (p.2 : ℝ)) • F p.1 + (p.2 : ℝ) • p.1
  have hΦ (x : (ι → ℝ) × (κ → ℝ)) (t : unitInterval) : Φ (x, t) =
      ((fun i ↦ (1 - (t : ℝ)) * f (x.1 i) + t * x.1 i),
        (fun j ↦ (1 - (t : ℝ)) * f (x.2 j) + t * x.2 j)) := by
    ext i <;> simp [Φ, F]
  refine ⟨Φ, ?_, fun x ↦ by simp [Φ], fun x t hx ↦ ?_, fun t x hx ↦ ?_, fun t x hx ↦ ?_,
    fun ε t x hx ↦ ?_, fun ε hε x hx ↦ ?_⟩
  · have ht : ContMDiff (𝓘(ℝ, (ι → ℝ) × (κ → ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : ((ι → ℝ) × (κ → ℝ)) × unitInterval ↦ (p.2 : ℝ)) :=
      contMDiff_subtypeVal_Icc.comp contMDiff_snd
    have ht' : ContMDiff (𝓘(ℝ, (ι → ℝ) × (κ → ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
        (fun p : ((ι → ℝ) × (κ → ℝ)) × unitInterval ↦ 1 - (p.2 : ℝ)) :=
      (contDiff_const.sub contDiff_id).contMDiff.comp ht
    exact (ht'.smul (hF.contMDiff.comp contMDiff_fst)).add
      (ht.smul contMDiff_fst)
  · -- Every coordinate of `x` lies in `[-(1 - 2δ), 1 - 2δ]`, where `f` is the identity.
    have hx₁ := (pi_norm_le_iff_of_nonneg (by linarith)).1 ((norm_fst_le x).trans hx)
    have hx₂ := (pi_norm_le_iff_of_nonneg (by linarith)).1 ((norm_snd_le x).trans hx)
    rw [hΦ]
    ext i
    · simp only [hid _ (by simpa using hx₁ i)]; ring
    · simp only [hid _ (by simpa using hx₂ i)]; ring
  · obtain ⟨hu, hv⟩ := hx
    rw [mem_sphere_zero_iff_norm] at hu
    rw [mem_closedBall_zero_iff] at hv
    obtain ⟨hu₁, hu₂⟩ := pi_clip_norm_bounds hodd hf1 hfI hfR1 t.property x.1
    obtain ⟨-, hv₂⟩ := pi_clip_norm_bounds hodd hf1 hfI hfR1 t.property x.2
    dsimp only
    rw [hΦ]
    refine ⟨?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm]
      rw [hu] at hu₁ hu₂
      simp only [min_self, max_self] at hu₁ hu₂
      exact le_antisymm hu₂ hu₁
    · rw [mem_closedBall_zero_iff]
      exact hv₂.trans (max_le hv le_rfl)
  · rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff] at hx ⊢
    obtain ⟨-, hu₂⟩ := pi_clip_norm_bounds hodd hf1 hfI hfR1 t.property x.1
    obtain ⟨-, hv₂⟩ := pi_clip_norm_bounds hodd hf1 hfI hfR1 t.property x.2
    dsimp only
    rw [hΦ]
    exact ⟨hu₂.trans (max_le hx.1 le_rfl), hv₂.trans (max_le hx.2 le_rfl)⟩
  · obtain ⟨hu, hv⟩ := hx
    obtain ⟨hu₁, hu₂⟩ := pi_clip_norm_bounds hodd hf1 hfI hfR1 t.property x.1
    obtain ⟨-, hv₂⟩ := pi_clip_norm_bounds hodd hf1 hfI hfR1 t.property x.2
    dsimp only
    rw [hΦ]
    refine ⟨?_, hv₂.trans_lt (max_lt hv (by linarith [abs_nonneg (‖x.1‖ - 1)]))⟩
    rw [abs_lt] at hu ⊢
    rw [min_le_iff] at hu₁
    rw [le_max_iff] at hu₂
    constructor
    · rcases hu₁ with h | h <;> linarith
    · rcases hu₂ with h | h <;> linarith
  · obtain ⟨hu, -⟩ := hx
    dsimp only
    rw [hΦ]
    simp only [Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
    refine ⟨?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm]
      refine norm_comp_eq_one hodd hf1 (by linarith) hfR ?_
      linarith [(abs_lt.1 hu).1]
    · rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j ↦ hf1 _

end SymplecticGeometry

end
