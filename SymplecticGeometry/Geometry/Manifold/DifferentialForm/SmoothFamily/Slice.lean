/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap

/-!
# Smooth families of forms at a fixed point and in a frame

Let `F` be a manifold and let `β p` be a rough `k`-form on `F` for each point `p` of a parameter
manifold `P`, such that `(p, y) ↦ β p y` is a `C^n` section of the bundle of `k`-forms of `F`
along the projection `(p, y) ↦ y` (the form in which Tau Ceti's
`TauCeti.contMDiff_mpullback_prodMk_form` gives the slices of a form on a product).

* `ContMDiffAt.roughForm_family_apply`: at a fixed `y₀`, the value `β p y₀` is `C^n` in `p`. The
  model space of `F` may have any dimension here; the trivialization at `y₀` of the bundle of
  `k`-forms is undone by its inverse `Trivialization.symmL` on the fibre.
* `ContMDiffAt.roughForm_family_apply_trivializationAt`: for a finite-dimensional model space,
  the values of `β p y` on the frame `e.symmL y ∘ v` of the tangent trivialization `e` of `F` at
  `y₀`, for a fixed tuple `v` of model vectors, are `C^n` in `(p, y)` at each point over `y₀`.
  This is the family version of one direction of Tau Ceti's
  `TauCeti.isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply`.

Both are statements about a `ContMDiffAt` hypothesis, so they sit in the namespace
`ContMDiffAt`, where dot notation finds them.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (integration
  along the fibre).
-/

public section

noncomputable section

open Bundle TauCeti
open scoped ContDiff Manifold

namespace ContMDiffAt

variable {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {K : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace F] [ChartedSpace H F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}

/-- **A smooth family of forms at a fixed point.** Let `β p` be a `k`-form on `F` for each
`p : P`, such that `(p, y) ↦ β p y`, as a section of the bundle of `k`-forms along
`(p, y) ↦ y`, is `C^n` at `q₀`. Then `p ↦ β p q₀.2`, a map into the alternating maps on the
model space, is `C^n` at `q₀.1`. -/
theorem roughForm_family_apply [IsManifold J 1 F] {n : WithTop ℕ∞}
    {β : P → RoughForm J F G k} {q₀ : P × F}
    (hβ : ContMDiffAt (K.prod J) (J.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G)) n
      (fun q : P × F ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] G)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin k]→L[ℝ] Trivial F G y) q.2 (β q.1 q.2)) q₀) :
    ContMDiffAt K 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G) n
      (fun p ↦ show E [⋀^Fin k]→L[ℝ] G from β p q₀.2) q₀.1 := by
  have hc := (contMDiffAt_totalSpace_iff.1 (hβ.comp q₀.1
    (contMDiffAt_id.prodMk contMDiffAt_const :
      ContMDiffAt K (K.prod J) n (fun p ↦ (p, q₀.2)) q₀.1))).2
  -- Undo the trivialization at `q₀.2` of the bundle of forms by its inverse on the fibre.
  have hb := mem_baseSet_trivializationAt (E [⋀^Fin k]→L[ℝ] G)
    (fun y : F ↦ TangentSpace J y [⋀^Fin k]→L[ℝ] Trivial F G y) q₀.2
  let L : (E [⋀^Fin k]→L[ℝ] G) →L[ℝ] E [⋀^Fin k]→L[ℝ] G :=
    (trivializationAt (E [⋀^Fin k]→L[ℝ] G)
      (fun y : F ↦ TangentSpace J y [⋀^Fin k]→L[ℝ] Trivial F G y) q₀.2).symmL ℝ q₀.2
  refine (L.contMDiff.contMDiffAt.comp q₀.1 hc).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun p ↦ ?_)
  exact ((Trivialization.symmL_apply _ hb _).trans
    (Trivialization.symm_apply_apply_mk _ hb _)).symm

variable [FiniteDimensional ℝ E]

/-- **A smooth family of forms read in a tangent trivialization.** Let `β p` be a `k`-form on
`F` for each `p : P`, such that `(p, y) ↦ β p y`, as a section of the bundle of `k`-forms along
`(p, y) ↦ y`, is `C^n` at `q₀`. For each tuple `v` of model vectors, the value of `β p y` on the
frame `e.symmL y ∘ v`, where `e` is the tangent trivialization of `F` at `q₀.2`, is `C^n` in
`(p, y)` at `q₀`. -/
theorem roughForm_family_apply_trivializationAt [IsManifold J 1 F] {n : WithTop ℕ∞}
    {β : P → RoughForm J F G k} {q₀ : P × F}
    (hβ : ContMDiffAt (K.prod J) (J.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] G)) n
      (fun q : P × F ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] G)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin k]→L[ℝ] Trivial F G y) q.2 (β q.1 q.2)) q₀)
    (v : Fin k → E) :
    ContMDiffAt (K.prod J) 𝓘(ℝ, G) n
      (fun q : P × F ↦ β q.1 q.2 ((trivializationAt E (TangentSpace J) q₀.2).symmL ℝ q.2 ∘ v))
      q₀ := by
  have h := (contMDiffAt_totalSpace_iff.1 hβ).2
  simp only [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
    contMDiffAt_continuousAlternatingMap_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
  exact h v

end ContMDiffAt

end
