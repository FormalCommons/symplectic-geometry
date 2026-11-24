/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Straightening a map that is a submersion in one variable

Let `F : A × B → Q` be strictly differentiable at `a`, with `A` complete and `B`, `Q`
finite-dimensional over a complete field, and with a derivative `F'` that is already onto on
`A × {0}`. Then the map `z ↦ (F z, z.2)` has onto derivative `F'.prod snd`, and Mathlib's
`HasStrictFDerivAt.implicitToOpenPartialHomeomorph` completes it to an open partial homeomorphism
of `A × B`, whose extra coordinate lies in the kernel of `F'.prod snd`. This file reorders its
coordinates.

## Main results

* `HasStrictFDerivAt.exists_openPartialHomeomorph_fst_eq_snd_snd_eq`: an open partial
  homeomorphism `Φ` of `A × B` into `Q × ker (F'.prod snd) × B` defined at `a`, whose first
  component is `F` and whose last is the projection to `B`.
-/

public section

noncomputable section

namespace HasStrictFDerivAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {A B Q : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B] [FiniteDimensional 𝕜 B]
  [NormedAddCommGroup Q] [NormedSpace 𝕜 Q] [FiniteDimensional 𝕜 Q]

/-- **Straightening a map that is a submersion in its first variable.** Let `F : A × B → Q` be
strictly differentiable at `a`, with `A` complete and `B`, `Q` finite-dimensional, and with a
derivative `F'` that is onto already on the vectors `(v, 0)`. Then there is an open partial
homeomorphism `Φ` of `A × B` into `Q × K × B`, with `K` the kernel of `(F', snd) : A × B → Q × B`,
defined at `a`, with `a ↦ (F a, 0, a.2)`, whose first component is `F` and whose last component
is the projection to `B`. -/
theorem exists_openPartialHomeomorph_fst_eq_snd_snd_eq {F : A × B → Q}
    {F' : A × B →L[𝕜] Q} {a : A × B} (hF : HasStrictFDerivAt F F' a)
    (hF' : (F'.comp (ContinuousLinearMap.inl 𝕜 A B)).range = ⊤) :
    ∃ Φ : OpenPartialHomeomorph (A × B) (Q × (F'.prod (ContinuousLinearMap.snd 𝕜 A B)).ker × B),
      a ∈ Φ.source ∧ Φ a = (F a, 0, a.2) ∧ ∀ z, (Φ z).1 = F z ∧ (Φ z).2.2 = z.2 := by
  have := FiniteDimensional.completeSpace 𝕜 B
  set Ψ' : A × B →L[𝕜] Q × B := F'.prod (ContinuousLinearMap.snd 𝕜 A B)
  have hΨ : HasStrictFDerivAt (fun z ↦ (F z, z.2)) Ψ' a := hF.prodMk (hasStrictFDerivAt_snd)
  have hrange : Ψ'.range = ⊤ := by
    refine LinearMap.range_eq_top.2 fun qb ↦ ?_
    obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 hF' (qb.1 - F' (0, qb.2))
    refine ⟨(v, qb.2), Prod.ext ?_ rfl⟩
    rw [show ((v, qb.2) : A × B) = (v, 0) + (0, qb.2) by simp, map_add]
    simp_all [Ψ']
  set Φ₀ := hΨ.implicitToOpenPartialHomeomorph _ _ hrange
  -- Reorder `((F z, z.2), w)` to `(F z, w, z.2)`.
  let r : ((Q × B) × Ψ'.ker) ≃L[𝕜] Q × Ψ'.ker × B :=
    (ContinuousLinearEquiv.prodAssoc 𝕜 Q B Ψ'.ker).trans
      ((ContinuousLinearEquiv.refl 𝕜 Q).prodCongr (ContinuousLinearEquiv.prodComm 𝕜 B Ψ'.ker))
  refine ⟨Φ₀.transHomeomorph r.toHomeomorph, ?_, ?_, fun z ↦ by simp [Φ₀, r]⟩
  · exact hΨ.mem_implicitToOpenPartialHomeomorph_source hrange
  · simp [Φ₀, r]

end HasStrictFDerivAt

end
