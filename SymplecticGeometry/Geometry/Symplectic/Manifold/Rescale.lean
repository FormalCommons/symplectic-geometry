/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Kahler

/-!
# Constant rescaling of compatible and Kähler forms

Tau Ceti's `TauCeti/Geometry/Symplectic/Manifold/Rescale.lean` shows that a nonzero constant
multiple of a nondegenerate or symplectic smooth two-form is again one
(`TauCeti.SmoothTwoForm.IsSymplectic.smul`). This file adds the same statement for the conditions
that involve a smooth almost complex structure `J`: a positive constant multiple of a form
compatible with `J`, or Kähler for `J`, is again compatible with `J`, or Kähler for `J`. Positivity
is needed, since `-σ` tames `-J` and not `J`.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.smul`: `c • σ` is compatible with `J` for `c > 0`.
* `TauCeti.SmoothTwoForm.IsKahler.smul`: `c • σ` is Kähler for `J` for `c > 0`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017]
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

/-- A positive constant multiple of a two-form compatible with `J` is compatible with `J`. -/
theorem Compatible.smul (h : σ.Compatible J) (c : ℝ) (hc : 0 < c) : (c • σ).Compatible J :=
  ⟨invariant_iff.2 fun x v w ↦ by
      simp only [SmoothForm.eval₂_smul, h.invariant.apply x v w],
    tames_iff.2 fun x v hv ↦ by
      simpa only [SmoothForm.eval₂_smul, smul_eq_mul] using
        mul_pos hc (tames_iff.1 h.tames x v hv)⟩

/-- A positive constant multiple of a Kähler form for `J` is a Kähler form for `J`. -/
theorem IsKahler.smul [FiniteDimensional ℝ E] (h : σ.IsKahler J) (c : ℝ) (hc : 0 < c) :
    (c • σ).IsKahler J :=
  ⟨h.isClosed.smul c, h.compatible.smul c hc, h.nijenhuis_eq_zero⟩

end SmoothTwoForm

end TauCeti

end
