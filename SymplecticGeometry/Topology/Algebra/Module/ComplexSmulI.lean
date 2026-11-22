/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# Complex-linear equivalences from real-linear ones

A continuous real-linear equivalence between complex modules that commutes with multiplication by
`I` is a continuous complex-linear equivalence: `ContinuousLinearEquiv.complexOfMapISmul`, the
equivalence form of Tau Ceti's `ContinuousLinearMap.complexOfMapISmul`, which it applies to the
map and to its inverse.
-/

public section

namespace ContinuousLinearEquiv

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]
  [TopologicalSpace V] [AddCommGroup W] [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W]
  [TopologicalSpace W]

omit [IsScalarTower ℝ ℂ V] [IsScalarTower ℝ ℂ W] in
/-- The inverse of a real-linear equivalence that commutes with multiplication by `I` commutes
with it too. -/
theorem symm_map_I_smul (u : V ≃L[ℝ] W) (h : ∀ v, u (Complex.I • v) = Complex.I • u v) (w : W) :
    u.symm (Complex.I • w) = Complex.I • u.symm w :=
  u.injective <| by rw [h, apply_symm_apply, apply_symm_apply]

/-- A continuous real-linear equivalence between complex modules that commutes with
multiplication by `I`, as a continuous complex-linear equivalence. -/
noncomputable def complexOfMapISmul (u : V ≃L[ℝ] W)
    (h : ∀ v, u (Complex.I • v) = Complex.I • u v) : V ≃L[ℂ] W :=
  ofContinuousLinearMap ((u : V →L[ℝ] W).complexOfMapISmul fun v ↦ by simpa using h v)
    ((u.symm : W →L[ℝ] V).complexOfMapISmul fun w ↦ by simpa using u.symm_map_I_smul h w)
    (ContinuousLinearMap.ext fun w ↦ by simp)
    (ContinuousLinearMap.ext fun v ↦ by simp)

@[simp]
theorem coe_complexOfMapISmul (u : V ≃L[ℝ] W) (h : ∀ v, u (Complex.I • v) = Complex.I • u v) :
    ⇑(u.complexOfMapISmul h) = u := by
  funext v
  simp [complexOfMapISmul]

@[simp]
theorem coe_complexOfMapISmul_symm (u : V ≃L[ℝ] W)
    (h : ∀ v, u (Complex.I • v) = Complex.I • u v) :
    ⇑(u.complexOfMapISmul h).symm = u.symm := by
  funext w
  simp [complexOfMapISmul]

end ContinuousLinearEquiv

end
