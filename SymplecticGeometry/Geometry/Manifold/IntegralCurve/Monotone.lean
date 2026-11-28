/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Monotone

/-!
# Integral curves defined for all times meet a level at most once

Two results on how an integral curve `γ` of a vector field `v`, defined for all times, meets a
level `{f = c}` of a real function `f`.

If `f` decreases along `γ` (weakly) and the level is transverse to `v` wherever `γ` meets it,
then `γ` meets it at most once (`IsMIntegralCurve.subsingleton_setOfPred_apply_eq`): two meetings
would make `f` constant along `γ` between them, so `df(v)` would vanish at a meeting point, by
Tau Ceti's `IsMIntegralCurveAt.mfderiv_apply_eq_zero_of_eventuallyEq_const`.

If instead `df(v) > 0` at the points of `γ` on the level, and off it only the continuity of
`f ∘ γ` is known, then `γ` crosses the level only from `{f < c}` to `{f > c}`, hence at most once
(`IsMIntegralCurve.subsingleton_setOfPred_apply_eq_of_mvfderiv_pos`). The crossing statements
`IsMIntegralCurve.lt_apply_of_le_apply` and `IsMIntegralCurve.apply_lt_of_apply_le` are Tau
Ceti's `IsMIntegralCurveOn.lt_apply_of_le_apply` and `IsMIntegralCurveOn.apply_lt_of_apply_le`
on the set of all times.

## Main results

* `IsMIntegralCurve.subsingleton_setOfPred_apply_eq`: an integral curve along which `f` is antitone
  meets a level transverse to it at most once.
* `IsMIntegralCurve.lt_apply_of_le_apply`, `IsMIntegralCurve.apply_lt_of_apply_le`: an integral
  curve crosses a level on which `df(v) > 0` only upwards.
* `IsMIntegralCurve.subsingleton_setOfPred_apply_eq_of_mvfderiv_pos`: so it meets that level at most
  once.
-/

public section

open Filter
open scoped Manifold Topology

/-- **A transverse level is met at most once along an antitone orbit.** Let `γ` be an integral
curve of `v` along which `f` is differentiable and `f ∘ γ` is antitone. If `df(v) ≠ 0` at each
point of `γ` on the level `{f = c}`, then `γ` meets that level at most once. -/
theorem IsMIntegralCurve.subsingleton_setOfPred_apply_eq {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {v : (x : M) → TangentSpace I x} {γ : ℝ → M} {f : M → ℝ} {c : ℝ}
    (hγ : IsMIntegralCurve γ v) (hf : ∀ t, MDifferentiableAt I 𝓘(ℝ) f (γ t))
    (hanti : Antitone (f ∘ γ)) (hc : ∀ t, f (γ t) = c → mvfderiv I f (γ t) (v (γ t)) ≠ 0) :
    {t | f (γ t) = c}.Subsingleton := by
  intro s hs t ht
  by_contra hne
  wlog hst : s < t generalizing s t
  · exact this ht hs (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hst) (Ne.symm hne))
  -- Between the two meetings `f ∘ γ` is constant, so its derivative vanishes on the level.
  have hconst : f ∘ γ =ᶠ[𝓝 ((s + t) / 2)] fun _ ↦ c := by
    filter_upwards [Ioo_mem_nhds (show s < (s + t) / 2 by linarith)
      (show (s + t) / 2 < t by linarith)] with u hu
    exact le_antisymm (hs ▸ hanti hu.1.le) (ht ▸ hanti hu.2.le)
  exact hc _ hconst.eq_of_nhds
    ((hγ.isMIntegralCurveAt _).mfderiv_apply_eq_zero_of_eventuallyEq_const (hf _) hconst)

namespace IsMIntegralCurve

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x} {γ : ℝ → M} {f : M → ℝ} {c : ℝ}

/-- **An integral curve crosses an upward level only upwards.** Let `γ` be an integral curve of
`v` with `f ∘ γ` continuous, and let `f` be differentiable with `df(v) > 0` at every point of `γ`
on the level `{f = c}`. If `c ≤ f (γ s)`, then `c < f (γ t)` for every `t > s`. -/
theorem lt_apply_of_le_apply (hγ : IsMIntegralCurve γ v) (hf : Continuous (f ∘ γ))
    (hvf : ∀ t, f (γ t) = c → MDifferentiableAt I 𝓘(ℝ) f (γ t) ∧
      0 < mvfderiv I f (γ t) (v (γ t)))
    {s t : ℝ} (hs : c ≤ f (γ s)) (hst : s < t) : c < f (γ t) :=
  (hγ.isMIntegralCurveOn Set.univ).lt_apply_of_le_apply isOpen_univ (Set.subset_univ _)
    hf.continuousOn (fun u _ ↦ hvf u) hs ⟨hst, le_rfl⟩

/-- **An integral curve crosses an upward level only upwards, looking backwards.** Let `γ` be an
integral curve of `v` with `f ∘ γ` continuous, and let `f` be differentiable with `df(v) > 0` at
every point of `γ` on the level `{f = c}`. If `f (γ t) ≤ c`, then `f (γ s) < c` for every
`s < t`. -/
theorem apply_lt_of_apply_le (hγ : IsMIntegralCurve γ v) (hf : Continuous (f ∘ γ))
    (hvf : ∀ t, f (γ t) = c → MDifferentiableAt I 𝓘(ℝ) f (γ t) ∧
      0 < mvfderiv I f (γ t) (v (γ t)))
    {s t : ℝ} (ht : f (γ t) ≤ c) (hst : s < t) : f (γ s) < c :=
  (hγ.isMIntegralCurveOn Set.univ).apply_lt_of_apply_le isOpen_univ (Set.subset_univ _)
    hf.continuousOn (fun u _ ↦ hvf u) ht ⟨le_rfl, hst⟩

/-- **An upward level is met at most once.** Let `γ` be an integral curve of `v` with `f ∘ γ`
continuous, and let `f` be differentiable with `df(v) > 0` at every point of `γ` on the level
`{f = c}`. Then `γ` meets that level at most once. Off the level, only the continuity of `f ∘ γ`
is assumed. -/
theorem subsingleton_setOfPred_apply_eq_of_mvfderiv_pos (hγ : IsMIntegralCurve γ v)
    (hf : Continuous (f ∘ γ))
    (hvf : ∀ t, f (γ t) = c → MDifferentiableAt I 𝓘(ℝ) f (γ t) ∧
      0 < mvfderiv I f (γ t) (v (γ t))) :
    {t | f (γ t) = c}.Subsingleton := by
  intro s (hs : f (γ s) = c) t (ht : f (γ t) = c)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact (hγ.lt_apply_of_le_apply hf hvf hs.ge hst).ne' ht
  · exact (hγ.lt_apply_of_le_apply hf hvf ht.ge hts).ne' hs

end IsMIntegralCurve

end
