/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Liouville.Completion
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import SymplecticGeometry.Geometry.Symplectic.Liouville.Domain
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The completion of a Weinstein domain: its function

Let `(W, σ, Y, f)` be a compact Weinstein domain with top level `c`
(`SymplecticGeometry.IsWeinsteinDomain`), and `Ŵ` the completion of its Liouville domain
(`SymplecticGeometry.IsStrongFilling.Completion`), whose end `[0, ∞) × ∂W` is parametrized by the
Liouville time `s`. Following McDuff–Salamon (Remark 7.4.6), this file builds a smooth function
`F : Ŵ → ℝ` that is `f` on `W` away from a thin collar of `∂W`, is `c + ε (eˢ − 1)` on the end,
increases strictly along the Liouville field `Ŷ` of the completion on a collar of `∂W` and on the
end, and is proper and bounded below.

## Main results

* `SymplecticGeometry.IsWeinsteinDomain.exists_completion_function`: such an `F` exists.

## Implementation notes

The derivative `df(Y)` is continuous (`TauCeti.ContMDiff.contMDiff_mvfderiv_apply`) and positive
on the compact boundary, so it is at least some `a > 0` on the image of `[-2δ, 0] × ∂W` under the
collar map `Φ`, for a small `δ`: the inclusion of the compact `W` in its completion is a closed
embedding, and the tube lemma `IsCompact.eventually_forall_of_forall_eventually` applies to the
end map. Along the lines of `Φ`, which are integral curves of `Y`, `g (s, x) = f (Φ (s, x))` then
has `∂_s g ≥ a`, so `g (s, x) ≤ c + a s ≤ c + ε (eˢ − 1)` for `0 < ε ≤ a`. With a smooth
nondecreasing cutoff `ρ` made from `Real.smoothTransition`, `0` for `s ≤ -δ` and `1` for
`s ≥ -δ / 2`, the function `(1 − ρ) g + ρ (c + ε (eˢ − 1))` on the end, and `f` elsewhere, is the
required `F`. Its smoothness and its derivative along `Ŷ` are read on the two pieces of the
completion, through the local diffeomorphisms `IsStrongFilling.isLocalDiffeomorphOn_completionEnd`
and `IsStrongFilling.isLocalDiffeomorphAt_toCompletion` and the integral curves
`IsStrongFilling.isMIntegralCurveOn_completionEnd` of `Ŷ`, as for the function cutting out `W` in
`SymplecticGeometry.Geometry.Symplectic.Liouville.Domain`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Remark 7.4.6
-/

public section

open Bundle Set Function TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  [IsManifold (𝓡∂ (n + 1)) ∞ W] [T2Space W] [CompactSpace ((𝓡∂ (n + 1)).boundary W)]

variable {σ : SmoothTwoForm (𝓡∂ (n + 1)) W} {Y : (x : W) → TangentSpace (𝓡∂ (n + 1)) x}
  {f : W → ℝ} {c : ℝ}

namespace IsWeinsteinDomain

/-! ### The cutoff and the function on the end -/

/-- The cutoff in the Liouville time: `0` for `s ≤ -δ` and `1` for `s ≥ -δ / 2`. -/
private noncomputable def cutoff (δ s : ℝ) : ℝ := Real.smoothTransition ((s + δ) / (δ / 2))

private theorem cutoff_of_le {δ s : ℝ} (hδ : 0 < δ) (hs : s ≤ -δ) : cutoff δ s = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

private theorem cutoff_of_ge {δ s : ℝ} (hδ : 0 < δ) (hs : -δ / 2 ≤ s) : cutoff δ s = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)

private theorem contDiff_cutoff (δ : ℝ) : ContDiff ℝ ∞ (cutoff δ) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

private theorem monotone_cutoff {δ : ℝ} (hδ : 0 < δ) : Monotone (cutoff δ) :=
  Real.smoothTransition.monotone.comp fun _ _ hst ↦
    div_le_div_of_nonneg_right (by linarith) (by linarith)

variable (h : IsStrongFilling σ univ Y)

/-- The function on the end: `f ∘ Φ` joined to `c + ε (eˢ − 1)` by the cutoff. Its values for
`s ≤ -ε₀`, outside the collar, are junk. -/
private noncomputable def endFunction (f : W → ℝ) (c ε δ : ℝ)
    (q : ℝ × (𝓡∂ (n + 1)).boundary W) : ℝ :=
  (1 - cutoff δ q.1) * f (h.collarFlow q) + cutoff δ q.1 * (c + ε * (Real.exp q.1 - 1))

open scoped Classical in
/-- The function on the completion: `endFunction` on the image of `(-2δ, ∞) × ∂W`, and `f`
elsewhere. -/
private noncomputable def completionFunction (f : W → ℝ) (c ε δ : ℝ) (z : h.Completion) : ℝ :=
  if hz : ∃ q ∈ Ioi (-(2 * δ)) ×ˢ univ, h.completionEnd q = z then
    endFunction h f c ε δ hz.choose
  else if hz' : ∃ p, h.toCompletion p = z then f hz'.choose else 0

variable {h} {ε δ : ℝ}

private theorem endFunction_of_ge (hδ : 0 < δ) {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : -δ / 2 ≤ q.1) : endFunction h f c ε δ q = c + ε * (Real.exp q.1 - 1) := by
  rw [endFunction, cutoff_of_ge hδ hq]
  ring

private theorem completionFunction_completionEnd (hδ : 2 * δ < h.collarWidth)
    {q : ℝ × (𝓡∂ (n + 1)).boundary W} (hq : q ∈ Ioi (-(2 * δ)) ×ˢ univ) :
    completionFunction h f c ε δ (h.completionEnd q) = endFunction h f c ε δ q := by
  have hz : ∃ q' ∈ Ioi (-(2 * δ)) ×ˢ univ, h.completionEnd q' = h.completionEnd q := ⟨q, hq, rfl⟩
  have hsub : Ioi (-(2 * δ)) ×ˢ (univ : Set ((𝓡∂ (n + 1)).boundary W)) ⊆
      Ioi (-h.collarWidth) ×ˢ univ :=
    prod_mono (Ioi_subset_Ioi (by linarith)) subset_rfl
  simp only [completionFunction, dite_eq_left hz]
  rw [
    h.injOn_completionEnd (hsub hz.choose_spec.1) (hsub hq) hz.choose_spec.2]

private theorem completionFunction_toCompletion_of_not {p : W}
    (hz : ¬∃ q ∈ Ioi (-(2 * δ)) ×ˢ univ, h.completionEnd q = h.toCompletion p) :
    completionFunction h f c ε δ (h.toCompletion p) = f p := by
  have hz' : ∃ p', h.toCompletion p' = h.toCompletion p := ⟨p, rfl⟩
  simp only [completionFunction, dite_eq_right hz, dite_eq_left hz']
  rw [ h.injective_toCompletion hz'.choose_spec]

/-- Away from the image of `(-δ, 0] × ∂W` under `Φ`, the function is `f` on `W`. -/
private theorem completionFunction_toCompletion (hδ0 : 0 < δ) (hδ : 2 * δ < h.collarWidth)
    {p : W} (hp : p ∉ h.collarFlow '' (Ioc (-δ) 0 ×ˢ univ)) :
    completionFunction h f c ε δ (h.toCompletion p) = f p := by
  by_cases hz : ∃ q ∈ Ioi (-(2 * δ)) ×ˢ univ, h.completionEnd q = h.toCompletion p
  · obtain ⟨q, hq, hqp⟩ := hz
    have hq0 : q.1 ≤ 0 := le_of_not_gt fun hq0 ↦ disjoint_left.1
      h.disjoint_range_toCompletion_completionEnd_image ⟨p, rfl⟩ ⟨q, ⟨hq0, trivial⟩, hqp⟩
    have hpΦ : p = h.collarFlow q := h.injective_toCompletion <| hqp.symm.trans <|
      h.completionEnd_eq_toCompletion ⟨by linarith [show -(2 * δ) < q.1 from hq.1], hq0⟩ q.2
    have hqδ : q.1 ≤ -δ := le_of_not_gt fun hqδ ↦ hp ⟨q, ⟨⟨hqδ, hq0⟩, trivial⟩, hpΦ.symm⟩
    rw [← hqp, completionFunction_completionEnd hδ hq, endFunction, cutoff_of_le hδ0 hqδ, ← hpΦ]
    ring
  · exact completionFunction_toCompletion_of_not hz

/-! ### The derivative of `f` along the collar -/

omit [T2Space W] [CompactSpace ((𝓡∂ (n + 1)).boundary W)] in
/-- The derivative `df(Y)` is continuous on `W`. -/
private theorem continuous_mvfderiv_apply (hW : IsWeinsteinDomain σ Y f c) :
    Continuous fun p ↦ mvfderiv (𝓡∂ (n + 1)) f p (Y p) :=
  (hW.contMDiff.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp
    hW.isStrongFilling.isOutwardPointingField.contMDiff.continuous

/-- Along the lines of `Φ`, the function `f` has derivative `df(Y)`. -/
private theorem hasDerivAt_comp_collarFlow (hW : IsWeinsteinDomain σ Y f c) {s : ℝ}
    (hs : s ∈ Ioo (-hW.isStrongFilling.collarWidth) 0) (x : (𝓡∂ (n + 1)).boundary W) :
    HasDerivAt (fun t ↦ f (hW.isStrongFilling.collarFlow (t, x)))
      (mvfderiv (𝓡∂ (n + 1)) f (hW.isStrongFilling.collarFlow (s, x))
        (Y (hW.isStrongFilling.collarFlow (s, x)))) s :=
  Manifold.hasDerivAt_comp_curve ((hW.contMDiff _).mdifferentiableAt (by simp))
    ((hW.isStrongFilling.isMIntegralCurveOn_collarFlow x s ⟨hs.1, hs.2.le⟩).hasMFDerivAt
      (Ioc_mem_nhds hs.1 hs.2))

/-- On a thin collar `[-2δ, 0] × ∂W`, the derivative `df(Y)` along the lines of `Φ` is bounded
below by a positive constant. -/
private theorem exists_lt_mvfderiv [CompactSpace W] (hW : IsWeinsteinDomain σ Y f c) :
    ∃ a > 0, ∃ δ > 0, 2 * δ < hW.isStrongFilling.collarWidth ∧
      ∀ s ∈ Icc (-(2 * δ)) 0, ∀ x, a < mvfderiv (𝓡∂ (n + 1)) f (hW.isStrongFilling.collarFlow (s, x))
        (Y (hW.isStrongFilling.collarFlow (s, x))) := by
  set h := hW.isStrongFilling
  have hD := hW.continuous_mvfderiv_apply
  -- A positive lower bound on the compact boundary.
  obtain ⟨a, ha, hab⟩ : ∃ a > 0, ∀ x : (𝓡∂ (n + 1)).boundary W,
      a < mvfderiv (𝓡∂ (n + 1)) f x (Y x) := by
    rcases isEmpty_or_nonempty ((𝓡∂ (n + 1)).boundary W) with hb | hb
    · exact ⟨1, one_pos, fun x ↦ isEmptyElim x⟩
    obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn (s := (univ : Set ((𝓡∂ (n + 1)).boundary W)))
      univ_nonempty (hD.comp continuous_subtypeVal).continuousOn
    have h₀ := hW.mvfderiv_pos x₀ x₀.2
    exact ⟨_, half_pos h₀, fun x ↦ (half_lt_self h₀).trans_le (hx₀ (mem_univ x))⟩
  -- The set where `df(Y) > a` is the trace of an open set of the completion.
  obtain ⟨O, hO, hOp⟩ := (h.contMDiff_toCompletion.continuous.isClosedEmbedding
    h.injective_toCompletion).isInducing.isOpen_iff.1 (isOpen_lt continuous_const hD)
  -- By the tube lemma, the end map sends a uniform neighbourhood of `{0} × ∂W` into it.
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ (univ : Set ((𝓡∂ (n + 1)).boundary W)),
      h.completionEnd (s, x) ∈ O := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun x _ ↦ ?_
    have hq : ((0 : ℝ), x) ∈ Ioi (-h.collarWidth) ×ˢ (univ : Set ((𝓡∂ (n + 1)).boundary W)) :=
      ⟨neg_lt_zero.2 h.collarWidth_pos, trivial⟩
    have hc := h.contMDiffOn_completionEnd.continuousOn.continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds hq)
    refine hc.preimage_mem_nhds (hO.mem_nhds ?_)
    rw [h.completionEnd_zero, ← mem_preimage, hOp]
    exact hab x
  obtain ⟨η, hη, hηO⟩ := Metric.eventually_nhds_iff.1 hev
  have hε := h.collarWidth_pos
  refine ⟨a, ha, min η h.collarWidth / 4, by positivity, by
    linarith [min_le_right η h.collarWidth], fun s hs x ↦ ?_⟩
  have hsη : dist s 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_nonpos hs.2]
    linarith [hs.1, min_le_left η h.collarWidth]
  have hsε : s ∈ Ioc (-h.collarWidth) 0 := ⟨by linarith [hs.1, min_le_right η h.collarWidth], hs.2⟩
  have := hηO hsη x (mem_univ x)
  rw [h.completionEnd_eq_toCompletion hsε, ← mem_preimage, hOp] at this
  exact this

/-- On the thin collar, `f ∘ Φ` lies below `c + a s`. -/
private theorem comp_collarFlow_le (hW : IsWeinsteinDomain σ Y f c) {a δ : ℝ}
    (hδ : 2 * δ < hW.isStrongFilling.collarWidth)
    (ha : ∀ s ∈ Icc (-(2 * δ)) 0, ∀ x, a < mvfderiv (𝓡∂ (n + 1)) f
      (hW.isStrongFilling.collarFlow (s, x)) (Y (hW.isStrongFilling.collarFlow (s, x))))
    {s : ℝ} (hs : s ∈ Icc (-(2 * δ)) 0) (x : (𝓡∂ (n + 1)).boundary W) :
    f (hW.isStrongFilling.collarFlow (s, x)) ≤ c + a * s := by
  set h := hW.isStrongFilling
  have hsub : Icc (-(2 * δ)) 0 ⊆ Ioc (-h.collarWidth) 0 := fun t ht ↦ ⟨by linarith [ht.1], ht.2⟩
  have hcont : ContinuousOn (fun t ↦ f (h.collarFlow (t, x)) - a * t) (Icc (-(2 * δ)) 0) := by
    refine ContinuousOn.sub (fun t ht ↦ ?_) (by fun_prop)
    exact hW.contMDiff.continuous.continuousAt.comp_continuousWithinAt
      ((h.isMIntegralCurveOn_collarFlow x t (hsub ht)).continuousWithinAt.mono hsub)
  have hderiv : ∀ t ∈ interior (Icc (-(2 * δ)) 0), HasDerivAt
      (fun t ↦ f (h.collarFlow (t, x)) - a * t)
      (mvfderiv (𝓡∂ (n + 1)) f (h.collarFlow (t, x)) (Y (h.collarFlow (t, x))) - a) t := by
    intro t ht
    rw [interior_Icc] at ht
    exact (hW.hasDerivAt_comp_collarFlow ⟨by linarith [ht.1], ht.2⟩ x).sub
      (by simpa using (hasDerivAt_id t).const_mul a)
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont
    (fun t ht ↦ (hderiv t ht).differentiableAt.differentiableWithinAt) fun t ht ↦ by
      rw [(hderiv t ht).deriv]
      exact sub_nonneg.2 (ha t (interior_subset ht) x).le
  have := hmono hs ⟨by linarith [hs.1, hs.2], le_rfl⟩ hs.2
  simp only [h.collarFlow_zero, mul_zero, sub_zero, hW.eq_of_mem_boundary x x.2] at this
  linarith

/-! ### Smoothness and the derivative of the function on the end -/

private theorem contMDiffAt_endFunction (hW : IsWeinsteinDomain σ Y f c) (hδ0 : 0 < δ)
    (hδ : 2 * δ < hW.isStrongFilling.collarWidth) {q : ℝ × (𝓡∂ (n + 1)).boundary W}
    (hq : q ∈ Ioi (-(2 * δ)) ×ˢ univ) :
    ContMDiffAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ) ∞ (endFunction hW.isStrongFilling f c ε δ) q := by
  set h := hW.isStrongFilling
  have hk : ContMDiff (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ) ∞
      fun q : ℝ × (𝓡∂ (n + 1)).boundary W ↦ c + ε * (Real.exp q.1 - 1) :=
    (contDiff_const.add (contDiff_const.mul (Real.contDiff_exp.sub contDiff_const))).contMDiff.comp
      contMDiff_fst
  rcases lt_or_ge q.1 0 with hq0 | hq0
  · -- In the collar, the formula is smooth.
    have hO : Ioo (-h.collarWidth) 0 ×ˢ (univ : Set ((𝓡∂ (n + 1)).boundary W)) ∈ 𝓝 q :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨by linarith [show -(2 * δ) < q.1 from hq.1], hq0⟩,
        trivial⟩
    have hρ : ContMDiff (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ) ∞
        fun q : ℝ × (𝓡∂ (n + 1)).boundary W ↦ cutoff δ q.1 :=
      (contDiff_cutoff δ).contMDiff.comp contMDiff_fst
    have hg : ContMDiffOn (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ) ∞ (fun q ↦ f (h.collarFlow q))
        (Ioo (-h.collarWidth) 0 ×ˢ univ) :=
      hW.contMDiff.comp_contMDiffOn h.contMDiffOn_collarFlow
    exact (((contMDiff_const.sub hρ).contMDiffAt.mul (hg.contMDiffAt hO)).add
      (hρ.contMDiffAt.mul hk.contMDiffAt))
  · -- Near the end, it is `c + ε (eˢ − 1)`.
    refine hk.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds
      (show q.1 ∈ Ioi (-δ / 2) by simp only [mem_Ioi]; linarith)] with r hr
    exact endFunction_of_ge hδ0 (le_of_lt hr)

/-- Along the end, the function on the end increases strictly on `(-2δ, ∞)`. -/
private theorem exists_hasDerivAt_endFunction (hW : IsWeinsteinDomain σ Y f c) {a : ℝ}
    (hε : 0 < ε) (hεa : ε ≤ a) (hδ0 : 0 < δ) (hδ : 2 * δ < hW.isStrongFilling.collarWidth)
    (ha : ∀ s ∈ Icc (-(2 * δ)) 0, ∀ x, a < mvfderiv (𝓡∂ (n + 1)) f
      (hW.isStrongFilling.collarFlow (s, x)) (Y (hW.isStrongFilling.collarFlow (s, x))))
    {s : ℝ} (hs : -(2 * δ) < s) (x : (𝓡∂ (n + 1)).boundary W) :
    ∃ d > 0, HasDerivAt (fun t ↦ endFunction hW.isStrongFilling f c ε δ (t, x)) d s := by
  set h := hW.isStrongFilling
  have hk : ∀ t, HasDerivAt (fun t ↦ c + ε * (Real.exp t - 1)) (ε * Real.exp t) t := fun t ↦ by
    simpa using (((Real.hasDerivAt_exp t).sub_const 1).const_mul ε).const_add c
  rcases lt_or_ge s 0 with hs0 | hs0
  · have hρd : HasDerivAt (cutoff δ) (deriv (cutoff δ) s) s :=
      ((contDiff_cutoff δ).differentiable (by simp) s).hasDerivAt
    have hg := hW.hasDerivAt_comp_collarFlow ⟨by linarith, hs0⟩ x
    have hd := ((hρd.const_sub 1).mul hg).add (hρd.mul (hk s))
    refine ⟨_, ?_, hd⟩
    have hρ0 := Real.smoothTransition.nonneg ((s + δ) / (δ / 2))
    have hρ1 := Real.smoothTransition.le_one ((s + δ) / (δ / 2))
    have hρ' : 0 ≤ deriv (cutoff δ) s := (monotone_cutoff hδ0).deriv_nonneg
    have hD := ha s ⟨hs.le, hs0.le⟩ x
    have hgk := hW.comp_collarFlow_le hδ ha ⟨hs.le, hs0.le⟩ x
    have hexp := Real.add_one_le_exp s
    have hexp1 : Real.exp s < 1 := Real.exp_lt_one_iff.2 hs0
    have hexp0 := Real.exp_pos s
    change 0 < -deriv (cutoff δ) s * f (h.collarFlow (s, x)) + (1 - cutoff δ s) *
      mvfderiv (𝓡∂ (n + 1)) f (h.collarFlow (s, x)) (Y (h.collarFlow (s, x))) +
      (deriv (cutoff δ) s * (c + ε * (Real.exp s - 1)) + cutoff δ s * (ε * Real.exp s))
    unfold cutoff at *
    nlinarith [mul_nonneg hρ' (show 0 ≤ c + ε * (Real.exp s - 1) - f (h.collarFlow (s, x)) by
        nlinarith), mul_nonneg (sub_nonneg.2 hρ1)
        (show 0 ≤ mvfderiv (𝓡∂ (n + 1)) f (h.collarFlow (s, x)) (Y (h.collarFlow (s, x))) -
          ε * Real.exp s by nlinarith), mul_pos hε hexp0]
  · refine ⟨_, mul_pos hε (Real.exp_pos s), (hk s).congr_of_eventuallyEq ?_⟩
    filter_upwards [isOpen_Ioi.mem_nhds (show s ∈ Ioi (-δ / 2) by simp only [mem_Ioi]; linarith)]
      with t ht
    exact endFunction_of_ge hδ0 (le_of_lt ht)

end IsWeinsteinDomain

end SymplecticGeometry

end
