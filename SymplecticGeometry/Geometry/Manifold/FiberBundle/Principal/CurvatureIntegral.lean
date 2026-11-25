/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.CircleConnection
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
import TauCeti.Geometry.Manifold.DeRham.Integration.Bijective
import TauCeti.Geometry.Manifold.DeRham.PoincarePairing.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# Integrals of the curvature of circle connections

Let `P` be a smooth principal `Circle`-bundle over a compact, boundaryless, Hausdorff manifold `B`
with an orientation `o` of dimension `2`, so that the curvature of a connection form on `P` is a
top form. Two connection forms differ by the pull-back `π^* a` of a `1`-form, so
their curvatures differ by the exact form `d a`, whose integral vanishes by Stokes' theorem: the
integral of the curvature does not depend on the connection form. Conversely, if `B` is moreover
preconnected, a smooth top form with the same integral as the curvature differs from it by an
exact form `d a` (Poincaré duality in the top degree), so it is the curvature of the connection
form `α + π^* a`.

## Main results

* `SymplecticGeometry.IsCircleConnectionForm.integralTopForm_curvature_eq`: all connection forms
  have curvatures with the same integral.
* `SymplecticGeometry.IsCircleConnectionForm.exists_curvature_eq_of_integralTopForm_eq`: over a
  preconnected base, every top form with that integral is the curvature of a connection form.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (circle bundles, connection forms and their curvature).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §5 (top
  compactly supported cohomology) and §6 (the Euler class of a circle bundle).
-/

public section

open Bundle Manifold TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless] [TopologicalSpace B]
  [ChartedSpace HB B] [IsManifold IB ∞ B] [CompactSpace B] [T2Space B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]
  {α β : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1}

/-- Adding the pull-back of a `1`-form on the base to a connection form does not change the
integral of its curvature over a compact, boundaryless, oriented base. -/
theorem IsCircleConnectionForm.integralTopForm_curvature_add_mpullback
    (hα : IsCircleConnectionForm α) (o : Manifold.Orientation IB B (Fin 2))
    (a : SmoothForm IB B ℝ 1) :
    integralTopForm o (hα.add_mpullback a).curvature.val = integralTopForm o hα.curvature.val := by
  let : MeasurableSpace EB := borel EB
  have : BorelSpace EB := ⟨rfl⟩
  rw [hα.curvature_add_mpullback a, Submodule.coe_add,
    integralTopForm_add_of_compactSpace o (hα.curvature.isSmoothForm.of_le (by simp))
      ((mextDerivₗ IB 1 a).isSmoothForm.of_le (by simp)),
    integralTopForm_eq_zero_of_mem_exactForms (φ := mextDerivₗ IB 1 a) o (by simp), add_zero]

/-- Over a compact, boundaryless, oriented base, the curvatures of any two connection forms on a
principal `Circle`-bundle have the same integral. -/
theorem IsCircleConnectionForm.integralTopForm_curvature_eq (hα : IsCircleConnectionForm α)
    (hβ : IsCircleConnectionForm β) (o : Manifold.Orientation IB B (Fin 2)) :
    integralTopForm o hβ.curvature.val = integralTopForm o hα.curvature.val := by
  obtain ⟨a, rfl, -⟩ := hα.existsUnique_eq_add_mpullback hβ
  exact hα.integralTopForm_curvature_add_mpullback o a

/-- Over a compact, preconnected, boundaryless, oriented base, every smooth `2`-form whose
integral is that of the curvature of a connection form `α` is the curvature of a connection
form. -/
theorem IsCircleConnectionForm.exists_curvature_eq_of_integralTopForm_eq [PreconnectedSpace B]
    (hα : IsCircleConnectionForm α) (o : Manifold.Orientation IB B (Fin 2))
    {σ : SmoothForm IB B ℝ 2}
    (hσ : integralTopForm o σ.val = integralTopForm o hα.curvature.val) :
    ∃ (β : SmoothForm (IB.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1)
      (hβ : IsCircleConnectionForm β), hβ.curvature = σ := by
  let : MeasurableSpace EB := borel EB
  have : BorelSpace EB := ⟨rfl⟩
  have hint : integralTopForm o (σ - hα.curvature).val = 0 := by
    rw [Submodule.coe_sub, integralTopForm_sub_of_compactSpace o (σ.isSmoothForm.of_le (by simp))
      (hα.curvature.isSmoothForm.of_le (by simp)), hσ, sub_self]
  have hex := (mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero o
    (compactlySupportedForms_eq_top (I := IB) (M := B) 2 ▸ Submodule.mem_top)).mpr hint
  rw [exactCompactlySupportedForms_succ, Submodule.mem_map] at hex
  obtain ⟨a, -, ha⟩ := hex
  exact ⟨_, hα.add_mpullback a, by rw [hα.curvature_add_mpullback a, ha, add_sub_cancel]⟩

end SymplecticGeometry

end
