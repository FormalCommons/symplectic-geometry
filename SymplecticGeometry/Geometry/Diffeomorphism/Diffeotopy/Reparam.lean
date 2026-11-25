/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Reparam
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Stabilizer

/-!
# Reparametrized diffeotopies preserving a form

Let `τ` be a smooth differential form on a manifold `M` and `φ_t` a diffeotopy of `M`. The time
slices of its reparametrization `Φ.reparam ρ` along a smooth map `ρ` of the unit interval are
`φ_{ρ t} ∘ φ_{ρ 0}⁻¹` (Tau Ceti's `TauCeti.Diffeotopy.timeSlice_reparam`). So if every `φ_t`
preserves `τ`, so does every time slice of the reparametrization, as for Tau Ceti's other
operations on diffeotopies (`TauCeti.SmoothForm.timeSlice_trans_mem_diffeomorphStabilizer` and its
neighbours).

## Main results

* `TauCeti.SmoothForm.timeSlice_reparam_mem_diffeomorphStabilizer`: reparametrizing a diffeotopy
  that preserves `τ` at every time gives one that preserves `τ` at every time.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {τ : SmoothForm J M F k}

/-- If a diffeotopy preserves `τ` at every time, so does each of its reparametrizations. -/
theorem timeSlice_reparam_mem_diffeomorphStabilizer {Φ : Diffeotopy J ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer τ)
    (ρ : C^∞⟮𝓡∂ 1, unitInterval; 𝓡∂ 1, unitInterval⟯) (t : unitInterval) :
    (Φ.reparam ρ).timeSlice t ∈ diffeomorphStabilizer τ := by
  rw [Diffeotopy.timeSlice_reparam, ← Diffeomorph.inv_def, ← Diffeomorph.mul_def]
  exact (diffeomorphStabilizer τ).mul_mem (hΦ _) (inv_mem (hΦ _))

end TauCeti.SmoothForm

end
