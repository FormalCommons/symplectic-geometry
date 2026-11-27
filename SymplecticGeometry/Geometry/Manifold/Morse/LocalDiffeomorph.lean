/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Morse.Basic
public import TauCeti.Geometry.Manifold.Morse.Hessian
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.Morse.Submersion

/-!
# Critical points and critical Hessians along local diffeomorphisms between different models

If `φ : M' → M` is a `C²` local diffeomorphism at `y` and `φ y` is a nondegenerate critical point
of `f : M → ℝ`, then `y` is a nondegenerate critical point of `f ∘ φ`. Here `M'` and `M` may be
modelled on different spaces, for instance a manifold and a vector space onto an open subset of
which a chart of the manifold is a diffeomorphism. Tau Ceti's
`IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp_iff` proves the equivalence for
manifolds with the same model; the proof here goes through the second-order chain rule
`TauCeti.criticalHessian_comp_apply` instead of a chart of the maximal atlas, as Tau Ceti's
`TauCeti.IsRegularPoint.ker_criticalHessian_comp` does for submersions. The Morse index along such
a map is Tau Ceti's `TauCeti.IsRegularPoint.manifoldMorseIndex_comp`.
The converse applies this to the local inverse of `φ`, after which `f` is recovered near `φ y`.

## Main results

* `IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp`: a nondegenerate critical point
  pulls back to a nondegenerate critical point along a local diffeomorphism, and
  `IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_of_comp` gives the converse.
* `PartialDiffeomorph.criticalHessian_apply_eq_fderiv_fderiv`: for a partial diffeomorphism `Φ`
  from a boundaryless manifold onto an open subset of a normed space, at a critical point `x` of
  `f` in its source, the critical Hessian of `f` is the second derivative of `f ∘ Φ.symm` at `Φ x`
  on the images of the vectors under `dΦ`, by the same chain rule. It is the form for partial
  diffeomorphisms of Tau Ceti's `TauCeti.criticalHessian_apply_eq_of_mem_maximalAtlas`, and
  `PartialDiffeomorph.contMDiffAt_of_contDiffAt_comp_symm` gives the `C²` hypothesis on `f`
  that it needs.

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
models, and `φ y` is a nondegenerate critical point of `f`, then `y` is a nondegenerate critical
point of `f ∘ φ`. -/
theorem isManifoldNondegenerateCriticalPoint_comp
    (hφ : IsLocalDiffeomorphAt I' I n φ y) (hn : 2 ≤ n)
    (hf : IsManifoldNondegenerateCriticalPoint I f (φ y)) :
    IsManifoldNondegenerateCriticalPoint I' (f ∘ φ) y := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hφ₂ : ContMDiffAt I' I 2 φ y := hφ.contMDiffAt.of_le hn
  have hcrit := hf.mem_criticalPoints
  obtain ⟨L, hL⟩ := hφ.isInvertible_mfderiv hn0
  obtain ⟨hf₂, -, hA⟩ := isManifoldNondegenerateCriticalPoint_iff_criticalHessian.1 hf
  refine isManifoldNondegenerateCriticalPoint_iff_criticalHessian.2
    ⟨hf₂.comp y hφ₂, mem_criticalPoints.1 (((hφ.isRegularPoint hn0).mem_criticalPoints_comp_iff
      (hφ.mdifferentiableAt hn0) (hf₂.mdifferentiableAt two_ne_zero)).2 hcrit), ?_⟩
  -- The critical Hessian of `f ∘ φ` is that of `f` with `dφ` applied to both arguments.
  -- Tau Ceti's `IsInvertible.bilinearComp` sees the tangent spaces through the instances of the
  -- model spaces, which agree with those of `TangentSpace` only by unfolding: `convert` splits
  -- off these instance goals, closed by `rfl`, and the last `rfl` is
  -- `ContinuousLinearMap.bilinearComp_apply`, which `rw` cannot use across that mismatch.
  convert hA.bilinearComp L L using 1
  all_goals try rfl
  refine heq_of_eq ?_
  ext u w
  rw [criticalHessian_comp_apply rfl hf₂ hφ₂ hcrit, ← hL]
  rfl

/-- **Nondegenerate critical points along a local diffeomorphism, converse.** If `φ : M' → M` is
a `C^n` local diffeomorphism at `y` with `2 ≤ n`, between boundaryless manifolds that may have
different models, and `y` is a nondegenerate critical point of `f ∘ φ`, then `φ y` is a
nondegenerate critical point of `f`. -/
theorem isManifoldNondegenerateCriticalPoint_of_comp
    (hφ : IsLocalDiffeomorphAt I' I n φ y) (hn : 2 ≤ n)
    (hf : IsManifoldNondegenerateCriticalPoint I' (f ∘ φ) y) :
    IsManifoldNondegenerateCriticalPoint I f (φ y) := by
  -- Pull `f ∘ φ` back along the local inverse `ψ` of `φ`; near `φ y`, `(f ∘ φ) ∘ ψ` is `f`.
  rw [← hφ.localInverse_left_inv hφ.localInverse_mem_target] at hf
  refine (hφ.localInverse_isLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp hn
    hf).congr_of_eventuallyEq ?_
  filter_upwards [hφ.localInverse_eventuallyEq_right] with z hz
  simp only [comp_apply, id_eq] at hz ⊢
  rw [hz]

end IsLocalDiffeomorphAt

namespace PartialDiffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n : WithTop ℕ∞} {f : M → ℝ} {x : M}

/-- If `Φ` is a `C^n` partial diffeomorphism from `M` onto an open subset of a normed space `G`,
with `2 ≤ n`, and `f ∘ Φ.symm` is `C²` at `Φ x` for a point `x` of the source, then `f` is `C²`
at `x`. -/
theorem contMDiffAt_of_contDiffAt_comp_symm (Φ : PartialDiffeomorph I 𝓘(ℝ, G) M G n)
    (hn : 2 ≤ n) (hx : x ∈ Φ.source) (hf : ContDiffAt ℝ 2 (f ∘ Φ.symm) (Φ x)) :
    ContMDiffAt I 𝓘(ℝ) 2 f x := by
  have hΦ : ContMDiffAt I 𝓘(ℝ, G) 2 Φ x :=
    (Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hx)).of_le hn
  refine (hf.contMDiffAt.comp x hΦ).congr_of_eventuallyEq ?_
  filter_upwards [Φ.open_source.mem_nhds hx] with y hy
  exact congrArg f (Φ.left_inv hy).symm

variable [I.Boundaryless]

/-- **The critical Hessian read in a partial diffeomorphism onto a normed space.** Let `Φ` be a
`C^n` partial diffeomorphism from a boundaryless manifold `M` onto an open subset of a normed
space `G`, with `2 ≤ n`, and `x` a point of its source. If `x` is a critical point of `f` and
`f ∘ Φ.symm` is `C²` at `Φ x`, the critical Hessian of `f` at `x` is the second derivative of
`f ∘ Φ.symm` at `Φ x`, evaluated on the images of the two vectors under the differential of `Φ`. -/
theorem criticalHessian_apply_eq_fderiv_fderiv (Φ : PartialDiffeomorph I 𝓘(ℝ, G) M G n)
    (hn : 2 ≤ n) (hx : x ∈ Φ.source) (hf : ContDiffAt ℝ 2 (f ∘ Φ.symm) (Φ x))
    (hcrit : x ∈ criticalPoints I f) (v w : TangentSpace I x) :
    criticalHessian I f x v w =
      fderiv ℝ (fderiv ℝ (f ∘ Φ.symm)) (Φ x) (mfderiv I 𝓘(ℝ, G) Φ x v)
        (mfderiv I 𝓘(ℝ, G) Φ x w) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hΦs : ContMDiffAt 𝓘(ℝ, G) I 2 Φ.symm (Φ x) :=
    (Φ.symm.contMDiffOn.contMDiffAt
      (Φ.open_target.mem_nhds (Φ.map_source hx))).of_le hn
  have hΦx : Φ.symm (Φ x) = x := Φ.left_inv hx
  have h := criticalHessian_comp_apply hΦx
    (Φ.contMDiffAt_of_contDiffAt_comp_symm hn hx hf) hΦs hcrit
    (mfderiv I 𝓘(ℝ, G) Φ x v) (mfderiv I 𝓘(ℝ, G) Φ x w)
  rw [Φ.mfderiv_symm_apply_mfderiv_apply hn0 hx, Φ.mfderiv_symm_apply_mfderiv_apply hn0 hx,
    criticalHessian_modelSpace] at h
  exact h.symm

end PartialDiffeomorph

end
