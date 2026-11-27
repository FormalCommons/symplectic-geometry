/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Gluing Taylor series

`HasFTaylorSeriesUpToOn.union`: a Taylor series of `f` on `s` and on `t` is one on `s ∪ t`
when each of `s` and `t` is closed relative to `s ∪ t`. Two sets closed in the whole space,
as in Tau Ceti's `HasFTaylorSeriesUpToOn.union_of_isClosed`, are a special case; the proof
adapts that one, splitting at each point of the union according to whether it lies in the closure
of each set.

`Set.EqOn.iteratedFDeriv_of_isOpen`: functions that agree on an open set have iterated
derivatives that agree there, as Mathlib's `Set.EqOn.iteratedDeriv_of_isOpen` says for
`iteratedDeriv`.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞} {f : E → F}
  {p : E → FormalMultilinearSeries 𝕜 E F} {s t : Set E}

/-- Taylor series on two sets glue to their union when each set is closed relative to the
union. -/
theorem HasFTaylorSeriesUpToOn.union (hs : HasFTaylorSeriesUpToOn n f p s)
    (ht : HasFTaylorSeriesUpToOn n f p t) (hst : closure s ∩ t ⊆ s) (hts : closure t ∩ s ⊆ t) :
    HasFTaylorSeriesUpToOn n f p (s ∪ t) := by
  have key : ∀ x ∈ s ∪ t, (x ∈ s ∨ x ∉ closure s) ∧ (x ∈ t ∨ x ∉ closure t) := by
    rintro x (hx | hx)
    · exact ⟨.inl hx, (em (x ∈ closure t)).imp (fun h ↦ hts ⟨h, hx⟩) id⟩
    · exact ⟨(em (x ∈ closure s)).imp (fun h ↦ hst ⟨h, hx⟩) id, .inl hx⟩
  constructor
  · rintro x (hx | hx)
    exacts [hs.zero_eq x hx, ht.zero_eq x hx]
  · intro m hm x hx
    obtain ⟨h₁, h₂⟩ := key x hx
    apply HasFDerivWithinAt.union
    · rcases h₁ with h | h
      exacts [hs.fderivWithin m hm x h, .of_notMem_closure h]
    · rcases h₂ with h | h
      exacts [ht.fderivWithin m hm x h, .of_notMem_closure h]
  · intro m hm x hx
    obtain ⟨h₁, h₂⟩ := key x hx
    apply ContinuousWithinAt.union
    · rcases h₁ with h | h
      exacts [hs.cont m hm x h, continuousWithinAt_of_notMem_closure h]
    · rcases h₂ with h | h
      exacts [ht.cont m hm x h, continuousWithinAt_of_notMem_closure h]

/-- Functions that agree on an open set `s` have iterated derivatives of every order that agree
on `s`. -/
theorem Set.EqOn.iteratedFDeriv_of_isOpen {g : E → F} (hfg : Set.EqOn f g s) (hs : IsOpen s)
    (m : ℕ) : Set.EqOn (iteratedFDeriv 𝕜 m f) (iteratedFDeriv 𝕜 m g) s := fun _ hx ↦
  ((hfg.eventuallyEq_of_mem (hs.mem_nhds hx)).iteratedFDeriv 𝕜 m).eq_of_nhds

end
