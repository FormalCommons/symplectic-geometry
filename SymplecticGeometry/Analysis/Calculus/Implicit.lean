/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Straightening a map that is a submersion in one variable

For `F : A × B → Q` between finite-dimensional real normed spaces, strictly differentiable at
`a` with a derivative that is already onto on `A × {0}`, the map `z ↦ (F z, z.2)` has onto
derivative, and Mathlib's `HasStrictFDerivAt.implicitToOpenPartialHomeomorph` completes it to an
open partial homeomorphism of `A × B`. This file reorders its coordinates.

## Main results

* `HasStrictFDerivAt.exists_openPartialHomeomorph_fst_eq_snd_snd_eq`: an open partial
  homeomorphism `Φ` of `A × B` into `Q × ℝᵐ × B` defined at `a`, whose first component is `F`
  and whose last is the projection to `B`.
-/

public section

noncomputable section

namespace HasStrictFDerivAt

variable {A B Q : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- **Straightening a map that is a submersion in its first variable.** Let `F : A × B → Q` be
strictly differentiable at `a`, between finite-dimensional real normed spaces, with a derivative
`F'` that is onto already on the vectors `(v, 0)`. Then there is an open partial homeomorphism
`Φ` of `A × B` onto an open subset of `Q × ℝᵐ × B`, defined at `a`, with `a ↦ (F a, 0, a.2)`,
whose first component is `F` and whose last component is the projection to `B`. -/
theorem exists_openPartialHomeomorph_fst_eq_snd_snd_eq {F : A × B → Q}
    {F' : A × B →L[ℝ] Q} {a : A × B} (hF : HasStrictFDerivAt F F' a)
    (hF' : ∀ q, ∃ v : A, F' (v, 0) = q) :
    ∃ (m : ℕ) (Φ : OpenPartialHomeomorph (A × B) (Q × EuclideanSpace ℝ (Fin m) × B)),
      a ∈ Φ.source ∧ Φ a = (F a, 0, a.2) ∧ ∀ z, (Φ z).1 = F z ∧ (Φ z).2.2 = z.2 := by
  set Ψ' : A × B →L[ℝ] Q × B := F'.prod (ContinuousLinearMap.snd ℝ A B)
  have hΨ : HasStrictFDerivAt (fun z ↦ (F z, z.2)) Ψ' a := hF.prodMk (hasStrictFDerivAt_snd)
  have hrange : Ψ'.range = ⊤ := by
    refine LinearMap.range_eq_top.2 fun qb ↦ ?_
    obtain ⟨v, hv⟩ := hF' (qb.1 - F' (0, qb.2))
    refine ⟨(v, qb.2), Prod.ext ?_ rfl⟩
    rw [show ((v, qb.2) : A × B) = (v, 0) + (0, qb.2) by simp, map_add]
    simp [Ψ', hv]
  set Φ₀ := hΨ.implicitToOpenPartialHomeomorph _ _ hrange
  let e : Ψ'.ker ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Ψ'.ker)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  -- Reorder `((F z, z.2), w)` to `(F z, e w, z.2)`.
  let r : ((Q × B) × Ψ'.ker) ≃L[ℝ] Q × EuclideanSpace ℝ (Fin (Module.finrank ℝ Ψ'.ker)) × B :=
    (ContinuousLinearEquiv.prodAssoc ℝ Q B Ψ'.ker).trans
      ((ContinuousLinearEquiv.refl ℝ Q).prodCongr
        ((ContinuousLinearEquiv.prodComm ℝ B Ψ'.ker).trans
          (e.prodCongr (ContinuousLinearEquiv.refl ℝ B))))
  refine ⟨_, Φ₀.transHomeomorph r.toHomeomorph, ?_, ?_, fun z ↦ by simp [Φ₀, r]⟩
  · exact hΨ.mem_implicitToOpenPartialHomeomorph_source hrange
  · simp [Φ₀, r]

end HasStrictFDerivAt

end
