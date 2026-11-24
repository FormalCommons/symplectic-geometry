/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.CircleConnection
public import TauCeti.Geometry.Manifold.DeRham.Basic

/-!
# The real first Chern class of a principal circle bundle

Let `P` be a smooth principal `Circle`-bundle over a finite-dimensional, boundaryless, Hausdorff,
σ-compact manifold `B`. Its **real first Chern class** is the de Rham class
`-(2π)⁻¹ [F_α] ∈ H²_dR(B)` of Chern–Weil theory, where `F_α` is the curvature of a connection form
`α` on `P` (`SymplecticGeometry.IsCircleConnectionForm.curvature`). It is defined with the
connection form chosen by `SymplecticGeometry.exists_isCircleConnectionForm`, and does not depend
on that choice: two connection forms differ by the pull-back `π^* a` of a `1`-form on `B`, so
their curvatures differ by the exact form `d a`.

The connection forms of the library take the value `1` on the fundamental vector field of
`circleLieGenerator`, so `F_α` is the curvature of McDuff–Salamon divided by `i`, and the
normalization `-(2π)⁻¹` agrees with that of the first Chern number: when `P` is the bundle of
unitary frames of a Hermitian complex line bundle `V` over a closed oriented surface, the integral
of `-(2π)⁻¹ F_α` is the first Chern number of `V`
(`SymplecticGeometry.Bundle.chernNumber_eq_integral_curvature`).

## Main definitions and results

* `SymplecticGeometry.realFirstChernClass IB P`: the real first Chern class of `P`.
* `SymplecticGeometry.IsCircleConnectionForm.realFirstChernClass_eq`: the class is
  `-(2π)⁻¹` times the class of the curvature of any connection form.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 2.7.4 (the curvature integral of a circle bundle over a surface) and
  Proposition 5.1.9 (where the real first Chern class of a circle bundle appears).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6 (the Euler
  class of a circle bundle as the class of the curvature of an angular form).
-/

public section

noncomputable section

open Bundle Manifold TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  [IB.Boundaryless]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]
  {α : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}

/-- The curvature of a connection form is a closed form, as an element of the submodule
`TauCeti.closedForms`. -/
theorem IsCircleConnectionForm.curvature_mem_closedForms (hα : IsCircleConnectionForm α) :
    hα.curvature ∈ closedForms IB B 2 :=
  (mem_closedForms IB _).mpr ((SmoothForm.isClosed_def _).mp hα.isClosed_curvature)

/-- The de Rham class of the curvature of a connection form `α` does not depend on `α`. -/
theorem IsCircleConnectionForm.deRhamCohomology_mk_curvature_eq (hα : IsCircleConnectionForm α)
    {β : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}
    (hβ : IsCircleConnectionForm β) :
    deRhamCohomology.mk IB 2 ⟨hβ.curvature, hβ.curvature_mem_closedForms⟩ =
      deRhamCohomology.mk IB 2 ⟨hα.curvature, hα.curvature_mem_closedForms⟩ := by
  obtain ⟨a, rfl, -⟩ := hα.existsUnique_eq_add_mpullback hβ
  -- `hβ` and `hα.add_mpullback a` are proofs of the same proposition.
  have h : hβ.curvature = hα.curvature + mextDerivₗ IB 1 a := hα.curvature_add_mpullback a
  rw [← sub_eq_zero, ← map_sub, deRhamCohomology.mk_eq_zero_iff, Submodule.coe_sub,
    Submodule.coe_mk, Submodule.coe_mk, h, add_sub_cancel_left, exactForms_succ]
  exact LinearMap.mem_range_self _ a

variable [FiniteDimensional ℝ EB] [T2Space B] [SigmaCompactSpace B]

variable (IB P) in
/-- The **real first Chern class** of a smooth principal `Circle`-bundle `P` over `B`: the de Rham
class `-(2π)⁻¹ [F_α]` of the curvature `F_α` of a connection form `α` on `P`, here the one chosen
by `exists_isCircleConnectionForm`. By `IsCircleConnectionForm.realFirstChernClass_eq` every
connection form gives this class. -/
def realFirstChernClass : deRhamCohomology IB B 2 :=
  -(2 * Real.pi)⁻¹ • deRhamCohomology.mk IB 2
    ⟨_, (exists_isCircleConnectionForm (IB := IB) (P := P)).choose_spec.curvature_mem_closedForms⟩

variable (IB P) in
theorem realFirstChernClass_def :
    realFirstChernClass IB P = -(2 * Real.pi)⁻¹ • deRhamCohomology.mk IB 2
      ⟨_, IsCircleConnectionForm.curvature_mem_closedForms
        (exists_isCircleConnectionForm (IB := IB) (P := P)).choose_spec⟩ :=
  (rfl)

/-- The real first Chern class of `P` is `-(2π)⁻¹` times the de Rham class of the curvature of
any connection form on `P`. -/
theorem IsCircleConnectionForm.realFirstChernClass_eq (hα : IsCircleConnectionForm α) :
    realFirstChernClass IB P =
      -(2 * Real.pi)⁻¹ • deRhamCohomology.mk IB 2 ⟨hα.curvature, hα.curvature_mem_closedForms⟩ := by
  rw [realFirstChernClass_def, IsCircleConnectionForm.deRhamCohomology_mk_curvature_eq hα]

end SymplecticGeometry
