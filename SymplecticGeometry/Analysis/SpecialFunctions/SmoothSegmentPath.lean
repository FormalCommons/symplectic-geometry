/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.SpecialFunctions.SmoothSegmentPath

/-!
# The smooth path along a segment, as a function of its endpoints

Tau Ceti's `TauCeti.smoothSegmentPath x y` is the path `s ↦ x + ψ(s) (y - x)`, where `ψ` is
`Real.smoothTransition`, and Tau Ceti proves it smooth in `s` for fixed `x` and `y`. This file
adds that it is smooth jointly in the two endpoints and the time, as a composition lemma in the
style of `ContDiff.add` (`ContDiff.smoothSegmentPath`), and that linear maps commute with it
(`TauCeti.map_smoothSegmentPath`). The proof of `ContDiff.smoothSegmentPath` is that of Tau Ceti's
`TauCeti.contDiff_smoothSegmentPath`, with variable endpoints and time.
-/

public section

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If the endpoints `f x`, `g x` and the time `s x` depend smoothly on `x`, then so does the
point `TauCeti.smoothSegmentPath (f x) (g x) (s x)` of the smooth path along the segment. -/
theorem ContDiff.smoothSegmentPath {n : ℕ∞} {f g : X → E} {s : X → ℝ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (hs : ContDiff ℝ n s) :
    ContDiff ℝ n fun x ↦ TauCeti.smoothSegmentPath (f x) (g x) (s x) := by
  simp only [TauCeti.smoothSegmentPath_def]
  exact hf.add ((Real.smoothTransition.contDiff.comp hs).smul (hg.sub hf))

namespace TauCeti

/-- A linear map carries the smooth path along the segment from `x` to `y` to the smooth path
along the segment from its image of `x` to its image of `y`. -/
theorem map_smoothSegmentPath {L : Type*} [FunLike L E F] [LinearMapClass L ℝ E F] (f : L)
    (x y : E) (s : ℝ) : f (smoothSegmentPath x y s) = smoothSegmentPath (f x) (f y) s := by
  simp [smoothSegmentPath_def]

end TauCeti

end
