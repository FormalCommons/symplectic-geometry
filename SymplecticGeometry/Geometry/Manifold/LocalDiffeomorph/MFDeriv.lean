/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Derivatives of transitions between partial diffeomorphisms

For partial diffeomorphisms `φ` and `ψ` from a manifold `M` into normed spaces, and a point `x` of
both sources, the derivative of the transition `ψ ∘ φ⁻¹` at `φ x`, composed with the differential
of `φ` at `x`, is the differential of `ψ` at `x`. This complements Tau Ceti's chain rule for
transitions, `PartialDiffeomorph.fderiv_comp_symm_eq_comp`.

## Main results

* `PartialDiffeomorph.fderiv_comp_symm_comp_mvfderiv`: `D(ψ ∘ φ⁻¹)(φ x) ∘ dφₓ = dψₓ`.
-/

public section

open Filter
open scoped Manifold Topology

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

/-- For partial diffeomorphisms `φ`, `ψ` into normed spaces and a point `x` of both sources, the
derivative of the transition `ψ ∘ φ⁻¹` at `φ x` composed with the differential of `φ` at `x` is
the differential of `ψ` at `x`. -/
theorem fderiv_comp_symm_comp_mvfderiv (ψ : PartialDiffeomorph I 𝓘(𝕜, G') M G' n)
    (φ : PartialDiffeomorph I 𝓘(𝕜, G) M G n) (hn : n ≠ 0) {x : M} (hψ : x ∈ ψ.source)
    (hφ : x ∈ φ.source) :
    (fderiv 𝕜 (fun z ↦ ψ (φ.symm z)) (φ x)).comp (mvfderiv I φ x) = mvfderiv I ψ x := by
  have heq : (fun z ↦ ψ (φ.symm z)) ∘ φ =ᶠ[𝓝 x] ψ :=
    eventually_of_mem (φ.open_source.mem_nhds hφ) fun z hz ↦ congrArg ψ (φ.left_inv hz)
  have hcomp := mvfderiv_comp x
    (ψ.differentiableAt_comp_symm φ hn hψ hφ).mdifferentiableAt (φ.mdifferentiableAt hn hφ)
  rw [heq.mvfderiv_eq] at hcomp
  rw [hcomp]
  ext v
  simp [NormedSpace.fromTangentSpace_apply]

end PartialDiffeomorph
