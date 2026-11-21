/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Darboux.EuclideanBasis

/-!
# Complex linearity of the coordinates of a basis adapted to a complex structure

Tau Ceti's `Module.Basis.darbouxBasisEquiv` sends a basis `b` of `V` indexed by `Fin n × Fin 2`
to the standard basis of `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`: `b (k, 0)` goes
to `(eₖ, 0)` and `b (k, 1)` to `(0, eₖ)`. This file shows that when the basis is adapted to a
complex structure `J`, in the sense that `b (k, 1) = J (b (k, 0))` for every `k`, these
coordinates are complex linear from `J` to the product structure `(x, y) ↦ (-y, x)`.

## Main results

* `Module.Basis.isComplexLinearMap_darbouxBasisEquiv`: if `b (k, 1) = J (b (k, 0))` for all `k`,
  then `b.darbouxBasisEquiv` is complex linear from `J` to
  `TauCeti.AlmostComplexStructure.product`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.5.
-/

public section

namespace Module.Basis

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- For a basis `b` with `b (k, 1) = J (b (k, 0))`, the coordinate equivalence
`b.darbouxBasisEquiv` is complex linear from `J` to the product structure `(x, y) ↦ (-y, x)` on
`EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`. -/
theorem isComplexLinearMap_darbouxBasisEquiv {J : TauCeti.AlmostComplexStructure V} {n : ℕ}
    {b : Basis (Fin n × Fin 2) ℝ V} (hbJ : ∀ k, b (k, 1) = J (b (k, 0))) :
    TauCeti.IsComplexLinearMap J (TauCeti.AlmostComplexStructure.product _)
      b.darbouxBasisEquiv.toLinearMap := by
  have h : b.darbouxBasisEquiv.toLinearMap ∘ₗ J.toLinearMap =
      (TauCeti.AlmostComplexStructure.product _).toLinearMap ∘ₗ
        b.darbouxBasisEquiv.toLinearMap := by
    refine b.ext fun ⟨k, i⟩ ↦ ?_
    have hJ₁ : J (b (k, 1)) = -b (k, 0) := by rw [hbJ, J.apply_apply]
    fin_cases i
    · simp [← hbJ]
    · simp [hJ₁]
  exact (TauCeti.isComplexLinearMap_iff_apply _ _ _).2 (LinearMap.congr_fun h)

end Module.Basis

end
