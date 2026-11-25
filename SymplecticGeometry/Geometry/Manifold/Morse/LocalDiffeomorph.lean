/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Morse.Basic
import TauCeti.Geometry.Manifold.Morse.Hessian
import TauCeti.Geometry.Manifold.Morse.Submersion

/-!
# Nondegenerate critical points along a local diffeomorphism between different models

If `φ : M' → M` is a `C²` local diffeomorphism at `y` and `φ y` is a nondegenerate critical point
of `f : M → ℝ`, then `y` is a nondegenerate critical point of `f ∘ φ`. Here `M'` and `M` may be
modelled on different spaces, for instance a manifold and a vector space onto an open subset of
which a chart of the manifold is a diffeomorphism. Tau Ceti's
`IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp_iff` proves the equivalence for
manifolds with the same model; the proof here goes through the second-order chain rule
`TauCeti.criticalHessian_comp_apply` instead of a chart of the maximal atlas, as Tau Ceti's
`TauCeti.IsRegularPoint.ker_criticalHessian_comp` does for submersions. The Morse index along such
a map is Tau Ceti's `TauCeti.IsRegularPoint.manifoldMorseIndex_comp`.

## Main results

* `IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp`: a nondegenerate critical point
  pulls back to a nondegenerate critical point along a local diffeomorphism.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §2.
-/

public section

open Function TauCeti
open scoped Manifold

namespace IsLocalDiffeomorphAt

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [TopologicalSpace M'] [ChartedSpace H' M']
  {n : WithTop ℕ∞} {φ : M' → M} {y : M'} {f : M → ℝ}

/-- **Nondegenerate critical points along a local diffeomorphism.** If `φ : M' → M` is a `C^n`
local diffeomorphism at `y` with `2 ≤ n`, between boundaryless manifolds that may have different
models, the model of `M'` being finite-dimensional, and `φ y` is a nondegenerate critical point
of `f`, then `y` is a nondegenerate critical point of `f ∘ φ`. -/
theorem isManifoldNondegenerateCriticalPoint_comp [FiniteDimensional ℝ E']
    (hφ : IsLocalDiffeomorphAt I' I n φ y) (hn : 2 ≤ n)
    (hf : IsManifoldNondegenerateCriticalPoint I f (φ y)) :
    IsManifoldNondegenerateCriticalPoint I' (f ∘ φ) y := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hφ₂ : ContMDiffAt I' I 2 φ y := hφ.contMDiffAt.of_le hn
  have hcrit := hf.mem_criticalPoints
  have hreg : IsRegularPoint I' I φ y := hφ.isRegularPoint hn0
  have hinj : Injective (mfderiv I' I φ y) := (hφ.isInvertible_mfderiv hn0).injective
  have hinv := (isManifoldNondegenerateCriticalPoint_iff_criticalHessian.1 hf).2.2
  refine .of_nondegenerate_criticalHessian (hf.contMDiffAt.comp y hφ₂)
    ((hreg.mem_criticalPoints_comp_iff (hφ.mdifferentiableAt hn0)
      (hf.contMDiffAt.mdifferentiableAt two_ne_zero)).2 hcrit) fun a ha ↦ hinj ?_
  -- `Hess f (dφ a, ·)` vanishes on the image of `dφ`, which is everything, so `dφ a = 0`.
  rw [map_zero]
  refine hinv.injective (ContinuousLinearMap.ext fun v ↦ ?_)
  obtain ⟨b, rfl⟩ := isRegularPoint_iff.1 hreg v
  rw [← criticalHessian_comp_apply rfl hf.contMDiffAt hφ₂ hcrit, ha, map_zero,
    zero_apply]

end IsLocalDiffeomorphAt

end
