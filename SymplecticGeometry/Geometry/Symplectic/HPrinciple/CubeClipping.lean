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
public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.AttachingCollar
public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.HomotopyOperator
import Mathlib.Analysis.Calculus.MeanValue
import SymplecticGeometry.Analysis.Normed.Group.Pi
import SymplecticGeometry.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Clipping a cube onto its attaching faces

Let `D = (ι → ℝ) × (κ → ℝ)` with the sup norms, `Q` its closed unit ball (a cube), and
`A = sphere 0 1 ×ˢ closedBall 0 1` the attaching faces of `Q` seen as a handle. This file builds a
smooth homotopy `Φ : D × [0, 1] → D`, affine in time, from a map that sends a thin collar of `A`
into `A` to the identity, which preserves `A`, `Q` and the collar at every time, moves no point
of `Q` by more than `2δ`, and whose stages have derivative of norm at most `5`, whatever `δ` is
(`SymplecticGeometry.exists_contMDiff_cubeClipping`). It is the homotopy that the homotopy
operator `TauCeti.SmoothForm.homotopyOperator` is applied to, through
`TauCeti.SmoothForm.mextDerivₗ_homotopyOperator_mpullback`, in the handle-core lemma of
McDuff–Salamon, Lemma 7.3.2.

The sup norm is not smooth at the corners of `A`, so the homotopy is built coordinatewise: for a
smooth odd `f : ℝ → ℝ` that is the identity on `[-(1 - 2δ), 1 - 2δ]`, `±1` beyond `1 - δ`,
moves each point of `[-1, 1]` towards the end of its sign, and has derivative bounded by `5`
(`SymplecticGeometry.exists_contDiff_odd_clip`), the homotopy is the straight line from the map
`F` that applies `f` to every coordinate to the identity. At every time each coordinate `y` of the
image of `x` satisfies `min |x| 1 ≤ |y| ≤ max |x| 1`, and so does the norm of each factor
(`min_norm_le_pi_norm_of_forall`), which gives the invariance of `A`, `Q` and the collar.

Since the homotopy is affine in time, its time derivative at `(x, t)` is the displacement
`x - Φ (x, 0)`, and its derivative on spatial vectors is that of the stage `Φ (·, t)`. With the
bound for the homotopy operator of a pullback,
`TauCeti.norm_homotopyOperator_mpullback_apply_le`, this bounds `h (Φ^* φ)` on an invariant set
by the displacement, the `k`-th power of the bound on the stages' derivatives, and the bound on
the `(k + 1)`-form `φ` (`SymplecticGeometry.norm_homotopyOperator_mpullback_apply_le_of_affine`).
For the clipping homotopy on `Q` this is `2 * δ * 5 ^ k * C`, small with `δ`.

## Main results

* `SymplecticGeometry.exists_contMDiff_cubeClipping`: the clipping homotopy.
* `SymplecticGeometry.norm_homotopyOperator_mpullback_apply_le_of_affine`: the homotopy operator
  of the pullback of a form along an affine-in-time homotopy is bounded by its displacement.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 7.3.2.
-/

public section

open Set Metric
open scoped Manifold ContDiff

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

/-- One coordinate of the clipping homotopy moves a point `s ∈ [-1, 1]` by at most `1 - r`, if
`f` is the identity on `[-r, r]`. -/
private theorem abs_clip_sub_le (hodd : Function.Odd f) (hf1 : ∀ s, |f s| ≤ 1)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, s ≤ f s) {r : ℝ} (hr : r ≤ 1) (hid : ∀ s, |s| ≤ r → f s = s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {s : ℝ} (hs : |s| ≤ 1) :
    |(1 - t) * f s + t * s - s| ≤ 1 - r := by
  have key (s : ℝ) (h₀ : 0 ≤ s) (h₁ : s ≤ 1) : |f s - s| ≤ 1 - r := by
    rcases le_total s r with hsr | hsr
    · rw [hid s (by rwa [abs_of_nonneg h₀]), sub_self, abs_zero]
      linarith
    · have := hf s ⟨h₀, h₁⟩
      rw [abs_of_nonneg (by linarith)]
      linarith [(abs_le.1 (hf1 s)).2]
  have hs' : |f s - s| ≤ 1 - r := by
    rcases le_total 0 s with h₀ | h₀
    · exact key s h₀ (abs_le.1 hs).2
    · have := key (-s) (by linarith) (by linarith [(abs_le.1 hs).1])
      rwa [hodd, ← neg_add', abs_neg, ← sub_eq_add_neg] at this
  rw [show (1 - t) * f s + t * s - s = (1 - t) * (f s - s) by ring, abs_mul,
    abs_of_nonneg (by linarith [ht.2])]
  nlinarith [ht.1, abs_nonneg (f s - s)]

/-- One coordinate of the clipping homotopy is `C`-Lipschitz if `f` is, for `C ≥ 1`. -/
private theorem abs_clip_sub_clip_le {C : ℝ} (hC : 1 ≤ C)
    (hfC : ∀ a b, |f a - f b| ≤ C * |a - b|) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (a b : ℝ) :
    |(1 - t) * f a + t * a - ((1 - t) * f b + t * b)| ≤ C * |a - b| := by
  obtain ⟨ht₀, ht₁⟩ := ht
  rw [show (1 - t) * f a + t * a - ((1 - t) * f b + t * b) =
    (1 - t) * (f a - f b) + t * (a - b) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - t), abs_of_nonneg ht₀]
  calc (1 - t) * |f a - f b| + t * |a - b| ≤ (1 - t) * (C * |a - b|) + t * (C * |a - b|) :=
        add_le_add (mul_le_mul_of_nonneg_left (hfC a b) (by linarith))
          (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (abs_nonneg _) hC) ht₀)
    _ = C * |a - b| := by ring

/-- The clipping homotopy on one factor `ι → ℝ` moves no point of the closed unit ball by more
than `1 - r`, if `f` is the identity on `[-r, r]`. -/
private theorem pi_clip_sub_norm_le {ι : Type*} [Fintype ι] (hodd : Function.Odd f)
    (hf1 : ∀ s, |f s| ≤ 1) (hf : ∀ s ∈ Icc (0 : ℝ) 1, s ≤ f s) {r : ℝ} (hr : r ≤ 1)
    (hid : ∀ s, |s| ≤ r → f s = s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {u : ι → ℝ}
    (hu : ‖u‖ ≤ 1) : ‖(fun i ↦ (1 - t) * f (u i) + t * u i) - u‖ ≤ 1 - r :=
  (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i ↦ by
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact abs_clip_sub_le hodd hf1 hf hr hid ht (by simpa using (norm_le_pi_norm u i).trans hu)

/-- The clipping homotopy on one factor `ι → ℝ` is `C`-Lipschitz if `f` is, for `C ≥ 1`. -/
private theorem pi_clip_sub_clip_norm_le {ι : Type*} [Fintype ι] {C : ℝ} (hC : 1 ≤ C)
    (hfC : ∀ a b, |f a - f b| ≤ C * |a - b|) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u w : ι → ℝ) :
    ‖(fun i ↦ (1 - t) * f (u i) + t * u i) - fun i ↦ (1 - t) * f (w i) + t * w i‖ ≤
      C * ‖u - w‖ :=
  (pi_norm_le_iff_of_nonneg (by have := norm_nonneg (u - w); positivity)).2 fun i ↦ by
    rw [Pi.sub_apply, Real.norm_eq_abs]
    refine (abs_clip_sub_clip_le hC hfC ht (u i) (w i)).trans
      (mul_le_mul_of_nonneg_left ?_ (by linarith))
    simpa using norm_le_pi_norm (u - w) i

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The straight line from the coordinatewise application of a smooth `f` to the identity is
smooth on `D × [0, 1]`. -/
private theorem contMDiff_clip (hf : ContDiff ℝ ∞ f) :
    ContMDiff (𝓘(ℝ, (ι → ℝ) × (κ → ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ∞
      fun p : ((ι → ℝ) × (κ → ℝ)) × unitInterval ↦
        (1 - (p.2 : ℝ)) • ((fun i ↦ f (p.1.1 i)), fun j ↦ f (p.1.2 j)) + (p.2 : ℝ) • p.1 := by
  have hF : ContDiff ℝ ∞ fun x : (ι → ℝ) × (κ → ℝ) ↦ ((fun i ↦ f (x.1 i)), fun j ↦ f (x.2 j)) :=
    (contDiff_pi.2 fun i ↦ hf.comp (by fun_prop)).prodMk
      (contDiff_pi.2 fun j ↦ hf.comp (by fun_prop))
  have ht : ContMDiff (𝓘(ℝ, (ι → ℝ) × (κ → ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : ((ι → ℝ) × (κ → ℝ)) × unitInterval ↦ (p.2 : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_snd
  have ht' : ContMDiff (𝓘(ℝ, (ι → ℝ) × (κ → ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : ((ι → ℝ) × (κ → ℝ)) × unitInterval ↦ 1 - (p.2 : ℝ)) :=
    (contDiff_const.sub contDiff_id).contMDiff.comp ht
  exact (ht'.smul (hF.contMDiff.comp contMDiff_fst)).add (ht.smul contMDiff_fst)

/-- If `f` is `±1` beyond `R ∈ (0, 1]` and bounded by `1`, applying it to every coordinate sends
each product collar `attachingCollar ι κ ε` with `ε ≤ 1 - R` into
`sphere 0 1 ×ˢ closedBall 0 1`. -/
private theorem mapsTo_clip_collar (hodd : Function.Odd f) (hf1 : ∀ s, |f s| ≤ 1) {R : ℝ}
    (hR : 0 < R) (hfR : ∀ s, R ≤ s → f s = 1) {ε : ℝ} (hε : ε ≤ 1 - R) :
    MapsTo (fun x : (ι → ℝ) × (κ → ℝ) ↦ ((fun i ↦ f (x.1 i)), fun j ↦ f (x.2 j)))
      (attachingCollar ι κ ε) (sphere 0 1 ×ˢ closedBall 0 1) := fun x hx ↦
  ⟨mem_sphere_zero_iff_norm.2 <|
      norm_comp_eq_one hodd hf1 hR hfR
        (by linarith [(abs_lt.1 (mem_attachingCollar_iff.1 hx).1).1]),
    mem_closedBall_zero_iff.2 <| (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j ↦ hf1 _⟩

/-- **The clipping homotopy of the cube onto its attaching faces.** Let `D = (ι → ℝ) × (κ → ℝ)`
with the sup norms, `Q = closedBall 0 1` and `A = sphere 0 1 ×ˢ closedBall 0 1`. For
`0 < δ ≤ 1/2` there is a smooth homotopy `Φ : D × [0, 1] → D` such that
* `Φ (x, t) = (1 - t) • Φ (x, 0) + t • x`: each point moves along the segment from its image
  under `Φ (·, 0)` to itself;
* `Φ (·, 1)` is the identity, and every `Φ (·, t)` is the identity on `closedBall 0 (1 - 2δ)`;
* every `Φ (·, t)` maps `A` into `A`, `Q` into `Q`, and each product collar
  `attachingCollar ι κ ε` into itself;
* `Φ (·, 0)` maps each such collar with `ε ≤ δ` into `A`;
* every `Φ (·, t)` moves no point of `Q` by more than `2δ`, and its derivative has norm at most
  `5` everywhere, a bound that does not depend on `δ`. -/
theorem exists_contMDiff_cubeClipping {δ : ℝ} (hδ : 0 < δ) (hδ₂ : δ ≤ 1 / 2) :
    ∃ Φ : ((ι → ℝ) × (κ → ℝ)) × unitInterval → (ι → ℝ) × (κ → ℝ),
      ContMDiff (𝓘(ℝ, (ι → ℝ) × (κ → ℝ)).prod (𝓡∂ 1)) 𝓘(ℝ, (ι → ℝ) × (κ → ℝ)) ∞ Φ ∧
      (∀ x t, Φ (x, t) = (1 - (t : ℝ)) • Φ (x, 0) + (t : ℝ) • x) ∧ (∀ x, Φ (x, 1) = x) ∧
      (∀ x t, ‖x‖ ≤ 1 - 2 * δ → Φ (x, t) = x) ∧
      (∀ t, MapsTo (fun x ↦ Φ (x, t)) (sphere 0 1 ×ˢ closedBall 0 1)
        (sphere 0 1 ×ˢ closedBall 0 1)) ∧
      (∀ t, MapsTo (fun x ↦ Φ (x, t)) (closedBall 0 1) (closedBall 0 1)) ∧
      (∀ ε t, MapsTo (fun x ↦ Φ (x, t)) (attachingCollar ι κ ε) (attachingCollar ι κ ε)) ∧
      (∀ ε ≤ δ, MapsTo (fun x ↦ Φ (x, 0)) (attachingCollar ι κ ε)
        (sphere 0 1 ×ˢ closedBall 0 1)) ∧
      (∀ t, ∀ x ∈ closedBall 0 1, ‖Φ (x, t) - x‖ ≤ 2 * δ) ∧
      ∀ t x, ‖fderiv ℝ (fun x ↦ Φ (x, t)) x‖ ≤ 5 := by
  obtain ⟨f, hf, hodd, hid, hfR, hf1, hfI, hf'⟩ :=
    exists_contDiff_odd_clip (r := 1 - 2 * δ) (R := 1 - δ) (by linarith) (by linarith)
      (by linarith)
  have hfR1 (s : ℝ) (hs : 1 ≤ s) : f s = 1 := hfR s (by linarith)
  -- With these radii the bound on the derivative of `f` is `5`, so `f` is `5`-Lipschitz.
  have hfC (a b : ℝ) : |f a - f b| ≤ 5 * |a - b| := by
    have h5 : 1 + 2 * (1 - (1 - 2 * δ)) / (1 - δ - (1 - 2 * δ)) = 5 := by
      rw [show 1 - δ - (1 - 2 * δ) = δ by ring, show 2 * (1 - (1 - 2 * δ)) = 4 * δ by ring,
        mul_div_assoc, div_self hδ.ne']
      norm_num
    simpa only [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun s _ ↦ hf.differentiable (by simp) s)
      (fun s _ ↦ (Real.norm_eq_abs _).trans_le ((hf' s).trans_eq h5)) (mem_univ b) (mem_univ a)
  -- The straight line from the coordinatewise application of `f` to the identity.
  let Φ : ((ι → ℝ) × (κ → ℝ)) × unitInterval → (ι → ℝ) × (κ → ℝ) :=
    fun p ↦ (1 - (p.2 : ℝ)) • ((fun i ↦ f (p.1.1 i)), fun j ↦ f (p.1.2 j)) + (p.2 : ℝ) • p.1
  have hΦ (x : (ι → ℝ) × (κ → ℝ)) (t : unitInterval) : Φ (x, t) =
      ((fun i ↦ (1 - (t : ℝ)) * f (x.1 i) + t * x.1 i),
        (fun j ↦ (1 - (t : ℝ)) * f (x.2 j) + t * x.2 j)) := by
    ext i <;> simp [Φ]
  -- The bounds on the norms of the two factors, from which the invariance statements follow.
  have hb (x : (ι → ℝ) × (κ → ℝ)) (t : unitInterval) : min ‖x.1‖ 1 ≤ ‖(Φ (x, t)).1‖ ∧
      ‖(Φ (x, t)).1‖ ≤ max ‖x.1‖ 1 ∧ ‖(Φ (x, t)).2‖ ≤ max ‖x.2‖ 1 := by
    rw [hΦ]
    exact ⟨(pi_clip_norm_bounds hodd hf1 hfI hfR1 t.property x.1).1,
      (pi_clip_norm_bounds hodd hf1 hfI hfR1 t.property x.1).2,
      (pi_clip_norm_bounds hodd hf1 hfI hfR1 t.property x.2).2⟩
  refine ⟨Φ, contMDiff_clip hf, fun x t ↦ by simp [Φ], fun x ↦ by simp [Φ], fun x t hx ↦ ?_,
    fun t x hx ↦ ?_, fun t x hx ↦ ?_, fun ε t x hx ↦ ?_, fun ε hε x hx ↦ ?_, fun t x hx ↦ ?_,
    fun t x ↦ ?_⟩
  · -- Every coordinate of `x` lies in `[-(1 - 2δ), 1 - 2δ]`, where `f` is the identity.
    have hx₁ := (pi_norm_le_iff_of_nonneg (by linarith)).1 ((norm_fst_le x).trans hx)
    have hx₂ := (pi_norm_le_iff_of_nonneg (by linarith)).1 ((norm_snd_le x).trans hx)
    rw [hΦ]
    ext i
    · simp only [hid _ (by simpa using hx₁ i)]; ring
    · simp only [hid _ (by simpa using hx₂ i)]; ring
  · obtain ⟨hu, hv⟩ := hx
    obtain ⟨hu₁, hu₂, hv₂⟩ := hb x t
    rw [mem_sphere_zero_iff_norm] at hu
    rw [mem_closedBall_zero_iff] at hv
    simp only [hu, min_self, max_self] at hu₁ hu₂
    exact ⟨mem_sphere_zero_iff_norm.2 (le_antisymm hu₂ hu₁),
      mem_closedBall_zero_iff.2 (hv₂.trans (max_le hv le_rfl))⟩
  · obtain ⟨-, hu₂, hv₂⟩ := hb x t
    simp only [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff] at hx ⊢
    exact ⟨hu₂.trans (max_le hx.1 le_rfl), hv₂.trans (max_le hx.2 le_rfl)⟩
  · obtain ⟨hu, hv⟩ := mem_attachingCollar_iff.1 hx
    obtain ⟨hu₁, hu₂, hv₂⟩ := hb x t
    refine mem_attachingCollar_iff.2
      ⟨?_, hv₂.trans_lt (max_lt hv (by linarith [abs_nonneg (‖x.1‖ - 1)]))⟩
    rw [abs_lt] at hu ⊢
    rw [min_le_iff] at hu₁
    rw [le_max_iff] at hu₂
    constructor
    · rcases hu₁ with h | h <;> linarith
    · rcases hu₂ with h | h <;> linarith
  · simpa [Φ] using mapsTo_clip_collar hodd hf1 (by linarith) hfR (by linarith) hx
  · simp only [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff] at hx
    rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, hΦ]
    have h : 1 - (1 - 2 * δ) = 2 * δ := by ring
    exact max_le
      ((pi_clip_sub_norm_le hodd hf1 hfI (by linarith) hid t.property hx.1).trans_eq h)
      ((pi_clip_sub_norm_le hodd hf1 hfI (by linarith) hid t.property hx.2).trans_eq h)
  · refine norm_fderiv_le_of_lip' ℝ (by norm_num) (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, hΦ]
    rw [mul_max_of_nonneg _ _ (by norm_num)]
    exact max_le_max (pi_clip_sub_clip_norm_le (by norm_num) hfC t.property y.1 x.1)
      (pi_clip_sub_clip_norm_le (by norm_num) hfC t.property y.2 x.2)

section HomotopyOperator

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The homotopy operator of an affine homotopy is small.** Let `Φ : E × [0, 1] → E` be a `C¹`
homotopy, affine in time, `Φ (x, t) = (1 - t) • Φ (x, 0) + t • x`, whose stages `Φ (·, t)` map a
set `s` into itself, have derivative of norm at most `L` on `s`, and with `Φ (·, 0)` moving no
point of `s` by more than `d`. If a `(k + 1)`-form `φ` on `E` has norm at most `C` on `s`, then the
homotopy operator of `Φ^* φ` has norm at most `d * L ^ k * C` at every point of `s`.

For the clipping homotopy of `SymplecticGeometry.exists_contMDiff_cubeClipping` and
`s = closedBall 0 1`, this gives the bound `2 * δ * 5 ^ k * C`. -/
theorem norm_homotopyOperator_mpullback_apply_le_of_affine {Φ : E × unitInterval → E}
    (hΦ : ContMDiff (𝓘(ℝ, E).prod (𝓡∂ 1)) 𝓘(ℝ, E) 1 Φ)
    (haff : ∀ x t, Φ (x, t) = (1 - (t : ℝ)) • Φ (x, 0) + (t : ℝ) • x) {s : Set E}
    (hmaps : ∀ t, MapsTo (fun x ↦ Φ (x, t)) s s) {d L C : ℝ}
    (hd : ∀ x ∈ s, ‖Φ (x, 0) - x‖ ≤ d)
    (hL : ∀ t, ∀ x ∈ s, ‖fderiv ℝ (fun x ↦ Φ (x, t)) x‖ ≤ L)
    {k : ℕ} (φ : TauCeti.RoughForm 𝓘(ℝ, E) E F (k + 1))
    (hφ : ∀ y ∈ s, @norm (E [⋀^Fin (k + 1)]→L[ℝ] F) _ (φ y) ≤ C) {x : E} (hx : x ∈ s) :
    @norm (E [⋀^Fin k]→L[ℝ] F) _
        (TauCeti.homotopyOperator (TauCeti.mpullback (𝓘(ℝ, E).prod (𝓡∂ 1)) 𝓘(ℝ, E) Φ φ) x) ≤
      d * L ^ k * C := by
  refine TauCeti.norm_homotopyOperator_mpullback_apply_le Φ φ x fun t ↦ ?_
  have hΦt : MDifferentiableAt (𝓘(ℝ, E).prod (𝓡∂ 1)) 𝓘(ℝ, E) Φ (x, t) :=
    hΦ.mdifferentiableAt one_ne_zero
  -- The time derivative is the displacement `x - Φ (x, 0)`.
  have htime : mfderiv (𝓘(ℝ, E).prod (𝓡∂ 1)) 𝓘(ℝ, E) Φ (x, t)
      ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) = x - Φ (x, 0) :=
    mfderiv_apply_zero_one_of_eq_add_smul hΦt fun s ↦ by
      rw [haff, smul_sub, sub_smul, one_smul]
      abel
  -- The spatial derivative is the derivative of the stage `Φ (·, t)`.
  have hspace : (mfderiv (𝓘(ℝ, E).prod (𝓡∂ 1)) 𝓘(ℝ, E) Φ (x, t)).comp
      (.inl ℝ E (EuclideanSpace ℝ (Fin 1))) = fderiv ℝ (fun y ↦ Φ (y, t)) x :=
    (TauCeti.mvfderiv_curry_left x t hΦt).symm.trans mvfderiv_eq_fderiv
  have hC : 0 ≤ C := (norm_nonneg _).trans (hφ x hx)
  have hd₀ : 0 ≤ d := (norm_nonneg _).trans (hd x hx)
  have h₁ := hφ _ (hmaps t hx)
  have h₂ : ‖x - Φ (x, 0)‖ ≤ d := norm_sub_rev x _ ▸ hd x hx
  have h₃ := pow_le_pow_left₀ (norm_nonneg _) (hL t x hx) k
  rw [htime, hspace]
  calc _ ≤ C * d * L ^ k := by gcongr
    _ = d * L ^ k * C := by ring

end HomotopyOperator

end SymplecticGeometry

end
