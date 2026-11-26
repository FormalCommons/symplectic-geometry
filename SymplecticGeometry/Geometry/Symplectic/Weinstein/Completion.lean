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
on the compact boundary, so it is greater than some `a > 0` on the image of `[-2δ, 0] × ∂W`
under the collar map `Φ`, for a small `δ`: the inclusion of the compact `W` in its completion is
a closed embedding, and the tube lemma `IsCompact.eventually_forall_of_forall_eventually` applies
to the end map. Along the lines of `Φ`, which are integral curves of `Y`, `g (s, x) = f (Φ (s, x))`
then has `∂_s g > a`, so by the mean value theorem `g (s, x) ≤ c + a s ≤ c + ε (eˢ − 1)` for
`0 < ε ≤ a`. With a smooth
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

private theorem cutoff_nonneg (δ s : ℝ) : 0 ≤ cutoff δ s :=
  Real.smoothTransition.nonneg _

private theorem cutoff_le_one (δ s : ℝ) : cutoff δ s ≤ 1 :=
  Real.smoothTransition.le_one _

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
  rw [h.injOn_completionEnd (hsub hz.choose_spec.1) (hsub hq) hz.choose_spec.2]

private theorem completionFunction_toCompletion_of_not {p : W}
    (hz : ¬∃ q ∈ Ioi (-(2 * δ)) ×ˢ univ, h.completionEnd q = h.toCompletion p) :
    completionFunction h f c ε δ (h.toCompletion p) = f p := by
  have hz' : ∃ p', h.toCompletion p' = h.toCompletion p := ⟨p, rfl⟩
  simp only [completionFunction, dite_eq_right hz, dite_eq_left hz']
  rw [h.injective_toCompletion hz'.choose_spec]

/-- Away from the image of `(-δ, 0] × ∂W` under `Φ`, the function is `f` on `W`. -/
private theorem completionFunction_toCompletion (hδ0 : 0 < δ) (hδ : 2 * δ < h.collarWidth)
    {p : W} (hp : p ∉ h.collarFlow '' (Ioc (-δ) 0 ×ˢ univ)) :
    completionFunction h f c ε δ (h.toCompletion p) = f p := by
  by_cases hz : ∃ q ∈ Ioi (-(2 * δ)) ×ˢ univ, h.completionEnd q = h.toCompletion p
  · obtain ⟨q, hq, hqp⟩ := hz
    obtain ⟨hq0, hpΦ⟩ := (h.completionEnd_eq_toCompletion_iff
      (by linarith [show -(2 * δ) < q.1 from hq.1])).1 hqp
    have hqδ : q.1 ≤ -δ := le_of_not_gt fun hqδ ↦ hp ⟨q, ⟨⟨hqδ, hq0⟩, trivial⟩, hpΦ.symm⟩
    rw [← hqp, completionFunction_completionEnd hδ hq, endFunction, cutoff_of_le hδ0 hqδ, ← hpΦ]
    ring
  · exact completionFunction_toCompletion_of_not hz

/-! ### The derivative of `f` along the collar -/

/-- On a thin collar `[-2δ, 0] × ∂W`, the derivative `df(Y)` along the lines of `Φ` is bounded
below by a positive constant. -/
private theorem exists_lt_mvfderiv [CompactSpace W] (hW : IsWeinsteinDomain σ Y f c) :
    ∃ a > 0, ∃ δ > 0, 2 * δ < hW.isStrongFilling.collarWidth ∧
      ∀ s ∈ Icc (-(2 * δ)) 0, ∀ x,
        a < mvfderiv (𝓡∂ (n + 1)) f (hW.isStrongFilling.collarFlow (s, x))
        (Y (hW.isStrongFilling.collarFlow (s, x))) := by
  set h := hW.isStrongFilling
  have hD : Continuous fun p ↦ mvfderiv (𝓡∂ (n + 1)) f p (Y p) :=
    (hW.contMDiff.contMDiff_mvfderiv_apply (m := 0) (by simp)).continuous.comp
      h.isOutwardPointingField.contMDiff.continuous
  -- A positive lower bound on the compact boundary.
  obtain ⟨b, hb, hbx⟩ := isCompact_univ.exists_forall_le'
    (hD.comp continuous_subtypeVal).continuousOn (a := 0) fun x _ ↦ hW.mvfderiv_pos x.val x.property
  -- The set where `df(Y) > b / 2` is the trace of an open set of the completion.
  obtain ⟨O, hO, hOp⟩ := (h.contMDiff_toCompletion.continuous.isClosedEmbedding
    h.injective_toCompletion).isInducing.isOpen_iff.1 (isOpen_lt (continuous_const (y := b / 2)) hD)
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
    exact (half_lt_self hb).trans_le (hbx x (mem_univ x))
  obtain ⟨η, hη, hηO⟩ := Metric.eventually_nhds_iff.1 hev
  have hε := h.collarWidth_pos
  refine ⟨b / 2, half_pos hb, min η h.collarWidth / 4, by positivity, by
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
  have hcont : ContinuousOn (fun t ↦ f (h.collarFlow (t, x))) (Icc (-(2 * δ)) 0) := fun t ht ↦
    hW.contMDiff.continuous.continuousAt.comp_continuousWithinAt
      ((h.isMIntegralCurveOn_collarFlow x t (hsub ht)).continuousWithinAt.mono hsub)
  have hderiv : ∀ t ∈ interior (Icc (-(2 * δ)) 0), HasDerivAt (fun t ↦ f (h.collarFlow (t, x)))
      (mvfderiv (𝓡∂ (n + 1)) f (h.collarFlow (t, x)) (Y (h.collarFlow (t, x)))) t := by
    intro t ht
    rw [interior_Icc] at ht
    exact h.hasDerivAt_comp_collarFlow ⟨by linarith [ht.1], ht.2⟩ x
      (hW.contMDiff.mdifferentiable (by simp) _)
  have := (convex_Icc _ _).mul_sub_le_image_sub_of_le_deriv hcont
    (fun t ht ↦ (hderiv t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ by rw [(hderiv t ht).deriv]; exact (ha t (interior_subset ht) x).le)
    s hs 0 ⟨by linarith [hs.1, hs.2], le_rfl⟩ hs.2
  rw [h.collarFlow_zero, hW.eq_of_mem_boundary x x.property] at this
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
    have hg := h.hasDerivAt_comp_collarFlow ⟨by linarith, hs0⟩ x
      (hW.contMDiff.mdifferentiable (by simp) _)
    have hd := ((hρd.const_sub 1).mul hg).add (hρd.mul (hk s))
    refine ⟨_, ?_, hd⟩
    have hρ1 := cutoff_le_one δ s
    have hρ' : 0 ≤ deriv (cutoff δ) s := (monotone_cutoff hδ0).deriv_nonneg
    have hD := ha s ⟨hs.le, hs0.le⟩ x
    have hgk := hW.comp_collarFlow_le hδ ha ⟨hs.le, hs0.le⟩ x
    have hexp := Real.add_one_le_exp s
    have hexp1 : Real.exp s < 1 := Real.exp_lt_one_iff.2 hs0
    have hexp0 := Real.exp_pos s
    nlinarith [mul_nonneg hρ' (show 0 ≤ c + ε * (Real.exp s - 1) - f (h.collarFlow (s, x)) by
        nlinarith), mul_nonneg (sub_nonneg.2 hρ1)
        (show 0 ≤ mvfderiv (𝓡∂ (n + 1)) f (h.collarFlow (s, x)) (Y (h.collarFlow (s, x))) -
          ε * Real.exp s by nlinarith), mul_pos hε hexp0]
  · refine ⟨_, mul_pos hε (Real.exp_pos s), (hk s).congr_of_eventuallyEq ?_⟩
    filter_upwards [isOpen_Ioi.mem_nhds (show s ∈ Ioi (-δ / 2) by simp only [mem_Ioi]; linarith)]
      with t ht
    exact endFunction_of_ge hδ0 (le_of_lt ht)

/-! ### The function on the completion -/

private theorem contMDiff_completionFunction (hW : IsWeinsteinDomain σ Y f c) (hδ0 : 0 < δ)
    (hδ : 2 * δ < hW.isStrongFilling.collarWidth) :
    ContMDiff (𝓡 (n + 1)) 𝓘(ℝ) ∞ (completionFunction hW.isStrongFilling f c ε δ) := by
  set h := hW.isStrongFilling
  intro z
  by_cases hz : ∃ q ∈ Ioi (-(2 * δ)) ×ˢ univ, h.completionEnd q = z
  · obtain ⟨q, hq, rfl⟩ := hz
    have hq' : q ∈ Ioi (-h.collarWidth) ×ˢ (univ : Set ((𝓡∂ (n + 1)).boundary W)) :=
      ⟨lt_trans (by linarith) hq.1, trivial⟩
    refine ((h.isLocalDiffeomorphOn_completionEnd ⟨q, hq'⟩).contMDiffAt_comp_iff le_rfl).1 ?_
    refine (hW.contMDiffAt_endFunction (ε := ε) hδ0 hδ hq).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_Ioi.prod isOpen_univ).mem_nhds hq] with r hr
    exact completionFunction_completionEnd hδ hr
  obtain ⟨p, hp, rfl⟩ := h.exists_mem_interior_toCompletion_eq (by positivity) hz
  -- Off the compact image `K` of `[-δ, 0] × ∂W`, the function is `f` read through the inclusion.
  set K := h.completionEnd '' (Icc (-δ) 0 ×ˢ univ)
  have hKc : IsClosed K := (h.isCompact_completionEnd_image_Icc (by linarith)).isClosed
  have hpK : h.toCompletion p ∉ K := by
    rintro ⟨r, hr, hrp⟩
    exact hz ⟨r, ⟨by simp only [mem_Ioi]; linarith [hr.1.1], trivial⟩, hrp⟩
  have heq : completionFunction h f c ε δ ∘ h.toCompletion =ᶠ[𝓝 p] f := by
    filter_upwards [h.contMDiff_toCompletion.continuous.continuousAt.preimage_mem_nhds
      (hKc.isOpen_compl.mem_nhds hpK)] with p' hp'
    refine completionFunction_toCompletion hδ0 hδ fun ⟨r, hr, hrp⟩ ↦ hp' ?_
    rw [← hrp, ← h.completionEnd_eq_toCompletion ⟨by linarith [hr.1.1], hr.1.2⟩ r.2]
    exact ⟨r, ⟨⟨hr.1.1.le, hr.1.2⟩, trivial⟩, rfl⟩
  exact ((h.isLocalDiffeomorphAt_toCompletion hp).contMDiffAt_comp_iff le_rfl).1
    ((hW.contMDiff p).congr_of_eventuallyEq heq)

private theorem mvfderiv_completionFunction_pos (hW : IsWeinsteinDomain σ Y f c) {a : ℝ}
    (hε : 0 < ε) (hεa : ε ≤ a) (hδ0 : 0 < δ) (hδ : 2 * δ < hW.isStrongFilling.collarWidth)
    (ha : ∀ s ∈ Icc (-(2 * δ)) 0, ∀ x, a < mvfderiv (𝓡∂ (n + 1)) f
      (hW.isStrongFilling.collarFlow (s, x)) (Y (hW.isStrongFilling.collarFlow (s, x))))
    {z : hW.isStrongFilling.Completion}
    (hz : z ∈ hW.isStrongFilling.completionEnd '' (Ioi (-(2 * δ)) ×ˢ univ)) :
    0 < mvfderiv (𝓡 (n + 1)) (completionFunction hW.isStrongFilling f c ε δ) z
      (hW.isStrongFilling.completionField z) := by
  set h := hW.isStrongFilling
  obtain ⟨⟨s, x⟩, hq, rfl⟩ := hz
  have hs : s ∈ Ioi (-h.collarWidth) := lt_trans (by linarith) hq.1
  obtain ⟨d, hd, hd'⟩ := hW.exists_hasDerivAt_endFunction hε hεa hδ0 hδ ha hq.1 x
  -- Along the integral curve `t ↦ (t, x)` of the field, the function is the function on the end.
  have hγ := (h.isMIntegralCurveOn_completionEnd x s hs).hasMFDerivAt (isOpen_Ioi.mem_nhds hs)
  have hF := Manifold.hasDerivAt_comp_curve
    ((hW.contMDiff_completionFunction (ε := ε) hδ0 hδ _).mdifferentiableAt (by simp)) hγ
  have heq : completionFunction h f c ε δ ∘ (fun t ↦ h.completionEnd (t, x)) =ᶠ[𝓝 s]
      fun t ↦ endFunction h f c ε δ (t, x) := by
    filter_upwards [isOpen_Ioi.mem_nhds hq.1] with t ht
    exact completionFunction_completionEnd hδ ⟨ht, trivial⟩
  rwa [(hF.congr_of_eventuallyEq heq.symm).unique hd']

/-- The function on the completion is bounded below by the minimum of `f` and `c - ε`. -/
private theorem le_completionFunction (hε : 0 < ε) (hδ0 : 0 < δ) (hδ : 2 * δ < h.collarWidth)
    {m : ℝ} (hm : ∀ p, m ≤ f p) (z : h.Completion) :
    min m (c - ε) ≤ completionFunction h f c ε δ z := by
  by_cases hz : ∃ q ∈ Ioi (-(2 * δ)) ×ˢ univ, h.completionEnd q = z
  · obtain ⟨q, hq, hqz⟩ := hz
    rw [← hqz, completionFunction_completionEnd hδ hq, endFunction]
    have hρ0 := cutoff_nonneg δ q.1
    have hρ1 := cutoff_le_one δ q.1
    have h1 : min m (c - ε) ≤ f (h.collarFlow q) := (min_le_left _ _).trans (hm _)
    have h2 : min m (c - ε) ≤ c + ε * (Real.exp q.1 - 1) :=
      (min_le_right _ _).trans (by nlinarith [Real.exp_pos q.1])
    nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hρ1), mul_le_mul_of_nonneg_left h2 hρ0]
  · obtain ⟨p, -, hpz⟩ := h.exists_mem_interior_toCompletion_eq (by positivity) hz
    subst hpz
    rw [completionFunction_toCompletion_of_not hz]
    exact (min_le_left _ _).trans (hm p)

/-- The sublevels of the function on the completion are compact. -/
private theorem isCompact_preimage_Iic_completionFunction [CompactSpace W]
    (hW : IsWeinsteinDomain σ Y f c) (hε : 0 < ε) (hδ0 : 0 < δ)
    (hδ : 2 * δ < hW.isStrongFilling.collarWidth) (b : ℝ) :
    IsCompact (completionFunction hW.isStrongFilling f c ε δ ⁻¹' Iic b) := by
  set h := hW.isStrongFilling
  set T := max 0 ((b - c) / ε)
  have hT : 0 ≤ T := le_max_left _ _
  -- The sublevel lies in `W` and the image of `[0, T] × ∂W`.
  have hC : IsCompact (range h.toCompletion ∪ h.completionEnd '' (Icc 0 T ×ˢ univ)) :=
    (isCompact_range h.contMDiff_toCompletion.continuous).union
      (h.isCompact_completionEnd_image_Icc (neg_lt_zero.2 h.collarWidth_pos))
  refine hC.of_isClosed_subset (isClosed_Iic.preimage
    (hW.contMDiff_completionFunction hδ0 hδ).continuous) fun z hz ↦ ?_
  rcases (h.range_toCompletion_union ▸ mem_univ z :
      z ∈ range h.toCompletion ∪ h.completionEnd '' (Ioi 0 ×ˢ univ)) with hz' | ⟨q, hq, rfl⟩
  · exact Or.inl hz'
  refine Or.inr ⟨q, ⟨⟨hq.1.le, le_of_not_gt fun hqT ↦ ?_⟩, trivial⟩, rfl⟩
  have hq' : q ∈ Ioi (-(2 * δ)) ×ˢ (univ : Set ((𝓡∂ (n + 1)).boundary W)) :=
    ⟨lt_trans (by linarith) hq.1, trivial⟩
  rw [mem_preimage, completionFunction_completionEnd hδ hq', endFunction_of_ge hδ0
    (by linarith [show (0 : ℝ) < q.1 from hq.1]), mem_Iic] at hz
  have hexp := Real.add_one_le_exp q.1
  have hbT : (b - c) / ε < q.1 := lt_of_le_of_lt (le_max_right _ _) hqT
  rw [div_lt_iff₀ hε] at hbT
  nlinarith

/-! ### The function of the completion -/

/-- **The function of the completion of a Weinstein domain.** Let `(W, σ, Y, f)` be a compact
Weinstein domain with top level `c`, and `Ŵ` the completion of its Liouville domain, whose end
is parametrized by the Liouville time `s`, with Liouville field `Ŷ`. There are `ε > 0` and
`δ > 0` with `2δ` less than the width of the collar of `Ŵ`, and a smooth function `F : Ŵ → ℝ`,
proper and bounded below, such that

* `F` is `f` on `W` away from the image of `(-δ, 0] × ∂W` under the collar map;
* `F (s, x) = c + ε (eˢ − 1)` on the end `s ≥ 0`;
* `dF(Ŷ) > 0` on the image of `(-2δ, ∞) × ∂W`. -/
theorem exists_completion_function [CompactSpace W] (hW : IsWeinsteinDomain σ Y f c) :
    ∃ ε > 0, ∃ δ > 0, 2 * δ < hW.isStrongFilling.collarWidth ∧
      ∃ F : hW.isStrongFilling.Completion → ℝ, ContMDiff (𝓡 (n + 1)) 𝓘(ℝ) ∞ F ∧
        (∀ p ∉ hW.isStrongFilling.collarFlow '' (Ioc (-δ) 0 ×ˢ univ),
          F (hW.isStrongFilling.toCompletion p) = f p) ∧
        (∀ s ≥ 0, ∀ x, F (hW.isStrongFilling.completionEnd (s, x)) = c + ε * (Real.exp s - 1)) ∧
        (∀ z ∈ hW.isStrongFilling.completionEnd '' (Ioi (-(2 * δ)) ×ˢ univ),
          0 < mvfderiv (𝓡 (n + 1)) F z (hW.isStrongFilling.completionField z)) ∧
        IsProperMap F ∧ BddBelow (range F) := by
  obtain ⟨a, ha0, δ, hδ0, hδ, ha⟩ := hW.exists_lt_mvfderiv
  obtain ⟨m, hm⟩ := (isCompact_range hW.contMDiff.continuous).bddBelow
  have hFc := hW.contMDiff_completionFunction (ε := a / 2) hδ0 hδ
  refine ⟨a / 2, half_pos ha0, δ, hδ0, hδ, completionFunction hW.isStrongFilling f c (a / 2) δ,
    hFc, fun p hp ↦ completionFunction_toCompletion hδ0 hδ hp, fun s hs x ↦ ?_,
    fun z hz ↦ hW.mvfderiv_completionFunction_pos (half_pos ha0) (half_le_self ha0.le) hδ0 hδ ha hz,
    ?_, ⟨_, forall_mem_range.2 (le_completionFunction (half_pos ha0) hδ0 hδ
      fun p ↦ hm ⟨p, rfl⟩)⟩⟩
  · rw [completionFunction_completionEnd (q := (s, x)) hδ ⟨show -(2 * δ) < s by linarith, trivial⟩,
      endFunction_of_ge hδ0 (show -δ / 2 ≤ s by linarith)]
  · refine isProperMap_iff_isCompact_preimage.2 ⟨hFc.continuous, fun K hK ↦ ?_⟩
    obtain ⟨b, hb⟩ := hK.bddAbove
    exact (hW.isCompact_preimage_Iic_completionFunction (half_pos ha0) hδ0 hδ b).of_isClosed_subset
      (hK.isClosed.preimage hFc.continuous) fun z hz ↦ hb hz

end IsWeinsteinDomain

end SymplecticGeometry

end
