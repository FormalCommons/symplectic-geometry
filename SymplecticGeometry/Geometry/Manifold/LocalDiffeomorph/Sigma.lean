/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.ContMDiff.Sigma

/-!
# The inclusion of a component of a disjoint union as a local diffeomorphism

For a family `M i` of charted spaces on a common model, the inclusion `Sigma.mk i` of the
component `M i` into the disjoint union `Σ i, M i` (Tau Ceti's `ChartedSpace.sigma`) is a `C^n`
diffeomorphism onto its open range. Its inverse there is the retraction that is the identity on
`M i` and sends the other components to a fixed point of `M i`; both maps are `C^n` by Tau Ceti's
`contMDiff_sigmaMk` and `contMDiff_sigma_iff`. In particular `Sigma.mk i` is a `C^n` local
diffeomorphism. The proof is that of Tau Ceti's `TauCeti.isLocalDiffeomorph_sumInl` for the
binary disjoint union, with an indexed family of summands.

## Main results

* `TauCeti.isLocalDiffeomorph_sigmaMk`: the inclusion of a component of a disjoint union is a
  `C^n` local diffeomorphism.
-/

public section

open Set Topology Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞} {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace H (M i)]

/-- The inclusion `Sigma.mk i` of the component `M i` into the disjoint union `Σ i, M i` is a
`C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_sigmaMk (i : ι) :
    IsLocalDiffeomorph I I n (Sigma.mk i : M i → Σ i, M i) := fun x ↦ by
  classical
  let r : (Σ j, M j) → M i := fun p ↦ if h : p.1 = i then h ▸ p.2 else x
  have hr : ContMDiff I I n r := contMDiff_sigma_iff.2 fun j ↦ by
    by_cases h : j = i
    · subst h
      exact contMDiff_id.congr fun y ↦ by simp [r]
    · exact (contMDiff_const (c := x)).congr fun y ↦ by simp [r, h]
  let Φ : PartialDiffeomorph I I (M i) (Σ j, M j) n :=
    { toFun := Sigma.mk i
      invFun := r
      source := univ
      target := range (Sigma.mk i)
      map_source' := fun y _ ↦ mem_range_self y
      map_target' := fun _ _ ↦ mem_univ _
      left_inv' := fun y _ ↦ by simp [r]
      right_inv' := by rintro _ ⟨y, rfl⟩; simp [r]
      open_source := isOpen_univ
      open_target := isOpen_range_sigmaMk
      contMDiffOn_toFun := (contMDiff_sigmaMk i).contMDiffOn
      contMDiffOn_invFun := hr.contMDiffOn }
  exact Φ.isLocalDiffeomorphAt I I n (mem_univ x)

end TauCeti

end
