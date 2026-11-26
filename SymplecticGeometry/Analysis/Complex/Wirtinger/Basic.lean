/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# Basic facts of Wirtinger calculus

Facts about the Wirtinger derivatives `∂` and `\bar∂` that Tau Ceti's
`TauCeti.Analysis.Complex.Wirtinger.Basic` does not state.

## Main results

* `TauCeti.wirtingerDeriv_of_notMem_tsupport`: `∂g` vanishes off the topological support of `g`.
  The proof is that of Tau Ceti's `TauCeti.conjWirtingerDeriv_of_notMem_tsupport`, for `∂` in
  place of `\bar∂`.
* `ContDiff.conjWirtingerDeriv_apply` and `ContDiff.wirtingerDeriv_apply`: the Wirtinger
  derivatives of a `C^(m+1)` map, evaluated on a fixed vector, are `C^m`; the global forms of
  Tau Ceti's `ContDiffAt.conjWirtingerDeriv_apply` and `ContDiffAt.wirtingerDeriv_apply`.
-/

public section

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {g : V → W}

/-- The Wirtinger derivative vanishes off the topological support. -/
theorem wirtingerDeriv_of_notMem_tsupport {z : V} (hz : z ∉ tsupport g) :
    wirtingerDeriv g z = 0 := by
  ext b
  simp [wirtingerDeriv_apply, fderiv_of_notMem_tsupport ℝ hz]

section ContDiff

variable {m n : WithTop ℕ∞}

/-- The conjugate Wirtinger derivative of a `C^(m+1)` map, evaluated on a fixed vector, is
`C^m`. -/
theorem _root_.ContDiff.conjWirtingerDeriv_apply (hg : ContDiff ℝ n g) (hmn : m + 1 ≤ n)
    (v : V) : ContDiff ℝ m (fun z ↦ conjWirtingerDeriv g z v) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ hg.contDiffAt.conjWirtingerDeriv_apply hmn v

/-- The Wirtinger derivative of a `C^(m+1)` map, evaluated on a fixed vector, is `C^m`. -/
theorem _root_.ContDiff.wirtingerDeriv_apply (hg : ContDiff ℝ n g) (hmn : m + 1 ≤ n) (v : V) :
    ContDiff ℝ m (fun z ↦ wirtingerDeriv g z v) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ hg.contDiffAt.wirtingerDeriv_apply hmn v

end ContDiff

end TauCeti

end
