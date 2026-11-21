/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Standard

/-!
# The Reeb field of the standard contact form

The Reeb field of Tau Ceti's standard contact form `dz - ⟪p, dq⟫` on `V × V × ℝ`
(`TauCeti.innerProductContactForm`) is the constant field `∂_z`
(`TauCeti.reebVectorField_innerProductContactForm`), as for the form `dz - x dy` on `ℝ³`
(`TauCeti.reebVectorField_standardContactForm`, whose proof this one follows).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §3.5, (3.5.2) and (3.5.3) on p. 126.
-/

public section

open scoped Manifold

namespace TauCeti

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Reeb field of the standard contact form `dz - ⟪p, dq⟫` on `V × V × ℝ` is `∂_z`. -/
@[simp]
theorem reebVectorField_innerProductContactForm (x : V × V × ℝ) :
    (innerProductContactForm V).reebVectorField x = ((0, 0, 1) : V × V × ℝ) := by
  -- The vector `∂_z`, as a tangent vector at `x`.
  obtain ⟨e, he⟩ : ∃ e : TangentSpace 𝓘(ℝ, V × V × ℝ) x, e = ((0, 0, 1) : V × V × ℝ) :=
    ⟨_, rfl⟩
  rw [← he]
  refine ((isContactForm_innerProductContactForm V).eq_reebVectorField_iff.2 ⟨?_, fun w ↦ ?_⟩).symm
  · rw [innerProductContactForm_apply, he]
    simp
  · rw [mextDeriv_innerProductContactForm_apply, he]
    simp [stdSymplecticForm_apply]

end TauCeti

end
