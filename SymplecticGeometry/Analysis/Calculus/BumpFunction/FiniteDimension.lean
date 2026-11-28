/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth extensions agreeing near a compact set

* `ContDiffOn.exists_contDiff_eventuallyEq_nhdsSet`: a function that is `Cⁿ` on a neighbourhood
  of a compact set `K` of a finite-dimensional real vector space agrees on a neighbourhood of
  `K` with a globally `Cⁿ` function. It is Tau Ceti's
  `ContDiffOn.exists_contDiff_eventuallyEq_on_isCompact`, which gives the agreement near each
  point of `K`, stated with the neighbourhood filter `𝓝ˢ K`.
-/

public section

open Set Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function that is `Cⁿ` on a neighbourhood `U` of a compact set `K` agrees on a
neighbourhood of `K` with a globally `Cⁿ` function. -/
theorem ContDiffOn.exists_contDiff_eventuallyEq_nhdsSet {n : ℕ∞} {f : E → F} {K U : Set E}
    (hK : IsCompact K) (hU : U ∈ 𝓝ˢ K) (hf : ContDiffOn ℝ n f U) :
    ∃ g : E → F, ContDiff ℝ n g ∧ g =ᶠ[𝓝ˢ K] f := by
  obtain ⟨U', hU'o, hKU', hU'U⟩ := mem_nhdsSet_iff_exists.1 hU
  obtain ⟨g, hg, -, -, -, hgf⟩ :=
    (hf.mono hU'U).exists_contDiff_eventuallyEq_on_isCompact hK hU'o hKU'
  exact ⟨g, hg, eventually_nhdsSet_iff_forall.2 hgf⟩
