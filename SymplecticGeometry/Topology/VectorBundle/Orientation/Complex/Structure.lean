/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars
public import TauCeti.LinearAlgebra.Orientation.Basic
public import TauCeti.Topology.VectorBundle.Complex.Orientation
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv

/-!
# The two orientations of a real bundle with a continuous complex structure

Let `J` be a continuous complex structure on a real vector bundle `V` with finite-dimensional
model fibre `F` (Tau Ceti's `TauCeti.Bundle.ContinuousComplexStructure`), and `J.Fiber` the
complex vector bundle it makes of `V`, with a complex model `G`. The real bundle `V` then carries
two orientations: Tau Ceti's complex orientation `J.orientation` of `V`, the complex orientation
of `J b` on each fibre, and the canonical orientation
`TauCeti.VectorBundleOrientation.complex G J.Fiber` of the complex bundle, that of
`(v₁, i v₁, …, vₙ, i vₙ)` for a complex basis `(v₁, …, vₙ)`. They agree.

## Main results

* `TauCeti.Bundle.ContinuousComplexStructure.map_fiberEquiv_complex`: the identification
  `J.fiberEquiv b : J.Fiber b ≃ V b` carries the canonical orientation of the complex fibre to
  the complex orientation of `J b`.
* `TauCeti.Bundle.ContinuousComplexStructure.complexEulerClass_eq_eulerClass`: hence the Euler
  class `TauCeti.complexEulerClass` of `J.Fiber` is the Euler class of `V` oriented by
  `J.orientation`, by `TauCeti.VectorBundleOrientation.eulerClass_eq_of_fiberwise`.

The second statement follows
`TauCeti.SmoothTwoForm.IsNondegenerate.complexEulerClass_eq_eulerClass`
(`SymplecticGeometry/Geometry/Symplectic/Manifold/ComplexOrientation.lean`), which compares the
Euler classes in the same way for a tamed complex structure on the tangent bundle of a surface.

## Proof

On the fibre over `b`, multiplication by `i` is `J b`
(`TauCeti.Bundle.ContinuousComplexStructure.fiberEquiv_I_smul`), so `J.fiberEquiv b` is complex
linear from the complex structure of `J.Fiber b` to `J b`, and carries the complex orientation of
the one to that of the other (`TauCeti.AlmostComplexStructure.map_orientation`). The complex
orientation of multiplication by `i` on a complex vector space is its canonical orientation
(`TauCeti.AlmostComplexStructure.orientation_ofComplexModule`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (a complex vector bundle is oriented as a real bundle, and its top Chern
  class is its Euler class).
-/

public section

open Bundle Module
open scoped VectorBundle.ComplexToReal

namespace TauCeti.Bundle.ContinuousComplexStructure

section Fiber

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (J : ContinuousComplexStructure F V)
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)]

/-- **The canonical orientation of `J.Fiber` is the complex orientation of `J`.** For a
continuous complex structure `J` on `V`, with `finrank ℝ F = k`, the identification
`J.fiberEquiv b : J.Fiber b ≃ V b` carries the canonical orientation of the complex vector space
`J.Fiber b`, reindexed by `Fin (2 * finrank ℂ G) ≃ Fin k`, to the complex orientation
`J.orientation hk b` of `V b`. -/
theorem map_fiberEquiv_complex {k : ℕ} (hk : finrank ℝ F = k) (b : B) :
    Orientation.map (Fin k) (J.fiberEquiv b).toLinearEquiv
      (VectorBundleOrientation.reindex (finCongr (hk ▸ (Fact.out : finrank ℝ F = _)).symm)
        (VectorBundleOrientation.complex G J.Fiber) b) =
      J.orientation hk b := by
  have := VectorBundle.finiteDimensional ℂ G J.Fiber b
  have := VectorBundle.finiteDimensional ℝ F V b
  have hk' : finrank ℝ (J.Fiber b) = k :=
    (J.fiberEquiv b).toLinearEquiv.finrank_eq.trans ((VectorBundle.finrank_eq ℝ F V b).trans hk)
  have he : IsComplexLinearMap (AlmostComplexStructure.ofComplexModule (J.Fiber b))
      (J.almostComplexStructureAt b) (J.fiberEquiv b).toLinearEquiv.toLinearMap :=
    (isComplexLinearMap_iff_apply _ _ _).2 fun v ↦ by
      simp [AlmostComplexStructure.ofComplexModule_apply, fiberEquiv_I_smul]
  rw [orientation_apply, VectorBundleOrientation.reindex_apply,
    VectorBundleOrientation.complex_apply, Orientation.reindex_finCongr_reindex_finCongr,
    ← AlmostComplexStructure.map_orientation he hk',
    AlmostComplexStructure.orientation_ofComplexModule]

end Fiber

section EulerClass

/-! Euler classes need the base and the fibres in one universe. -/

universe u

variable {B : Type u} [TopologicalSpace B]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type u} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (J : ContinuousComplexStructure F V)
  (G : Type u) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)]

/-- **The Euler class of `J.Fiber` is the Euler class of `V` with the complex orientation.** For
a continuous complex structure `J` on `V` with `finrank ℝ F = 2 r + 2`, so that `J.Fiber` has
complex rank `r + 1`, the Euler class of the complex bundle `J.Fiber` is the Euler class of `V`
oriented by `J.orientation`. -/
theorem complexEulerClass_eq_eulerClass {r : ℕ} (hF : finrank ℝ F = 2 * r + 2) :
    complexEulerClass G J.Fiber (r := r)
        (by have : finrank ℝ F = 2 * finrank ℂ G := Fact.out; omega) =
      (J.orientation hF).eulerClass hF := by
  rw [complexEulerClass_def]
  exact VectorBundleOrientation.eulerClass_eq_of_fiberwise _ hF _ _ (φ := J.fiberEquiv)
    ((J.totalSpaceHomeomorph G).continuous.congr fun v ↦ by simp)
    fun b ↦ J.map_fiberEquiv_complex G hF b

end EulerClass

end TauCeti.Bundle.ContinuousComplexStructure

end
