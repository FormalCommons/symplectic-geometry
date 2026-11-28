/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.SingularSupport
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Smoothness

/-!
# Smoothness from a uniform gain of local Sobolev regularity

A distribution has empty singular support exactly when it is `H^s` near every point for every
`s` (Tau Ceti's `Distribution.singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty`).
This file uses that criterion to turn a regularity estimate with a fixed gain of `M` orders into
smoothness.

## Main results

* `Distribution.singularSupport_eq_empty_of_forall_isLocallySobolevAt`: let the `S b` be smooth
  distributions on `Ω`. If at every point of `Ω`, for every `s`, `T` is `H^(s + M)` near the
  point as soon as every `S b` is `H^s` near it, then `T` is smooth on `Ω`. With
  `Distribution.IsLocallySobolevAt.of_ellipticSystem` it gives the smoothness of solutions of
  elliptic systems with smooth right sides.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-- Let `T` and the `S b` be distributions on `Ω`, with every `S b` smooth on `Ω`. If, at every
`x ∈ Ω` and for every `s`, `T` is `H^(s + M)` near `x` whenever every `S b` is `H^s` near `x`,
then `T` is smooth on `Ω`. -/
theorem singularSupport_eq_empty_of_forall_isLocallySobolevAt {κ : Type*} {S : κ → 𝓓'(Ω, ℂ)}
    {T : 𝓓'(Ω, ℂ)} {M : ℝ} (hS : ∀ b, (S b).singularSupport = ∅)
    (h : ∀ x ∈ Ω, ∀ s, (∀ b, (S b).IsLocallySobolevAt s x) → T.IsLocallySobolevAt (s + M) x) :
    T.singularSupport = ∅ := by
  refine singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty.2 fun s ↦
    Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
  have hxΩ := (mem_sobolevSingularSupport_iff.1 hx).1
  refine (notMem_sobolevSingularSupport_iff hxΩ).2 ?_ hx
  have h := h x hxΩ (s - M) fun b ↦ (notMem_sobolevSingularSupport_iff hxΩ).1 <| by
    rw [singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty.1 (hS b)]
    exact Set.notMem_empty x
  rwa [sub_add_cancel] at h

end Distribution

end
