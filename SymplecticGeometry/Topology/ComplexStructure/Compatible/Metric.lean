/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Contractible
public import Mathlib.Topology.Homotopy.Equiv
public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.PolarComplexStructure.Basic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.PolarComplexStructure.Smooth
import SymplecticGeometry.Topology.ComplexStructure.Compatible.Matrix
import SymplecticGeometry.Topology.Homotopy.Affine

/-!
# Compatible complex structures and inner products

Let `ω` be a symplectic form on a finite-dimensional real normed space `V`. A compatible complex
structure `J` determines the inner product `g_J = ω(·, J ·)`, and an inner product `g` determines
the compatible structure `J_{g,ω}` (`SymplecticGeometry.metricPolarComplexStructure`). These two
continuous maps are homotopy inverse to each other: `J_{g_J,ω} = J`, and in the other order the
segment from `g_{J_{g,ω}}` to `g` stays in the convex set `innerProducts V`.

## Main definitions and results

* `SymplecticGeometry.compatibleMetric ω`: the continuous map `J ↦ g_J` from the `ω`-compatible
  complex structures to the inner products.
* `SymplecticGeometry.compatiblePolar ω`: the continuous map `g ↦ J_{g,ω}` in the other
  direction.
* `SymplecticGeometry.metricStraightHomotopy ω`: the straight-line homotopy
  `(t, g) ↦ (1 - t) • g_{J_{g,ω}} + t • g` from the composite to the identity of
  `innerProducts V`.
* `SymplecticGeometry.metricHomotopyEquiv ω`: the homotopy equivalence of the compatible
  structures with `innerProducts V`, with inverse `g ↦ J_{g,ω}`.
* `SymplecticGeometry.contractibleSpace_compatible_and_homotopyEquiv`: the compatible structures
  form a nonempty contractible space, homotopy equivalent to `innerProducts V` through these maps,
  and on `StdSpace ι` homeomorphic to the positive definite symplectic matrices through
  `J ↦ -J₀ M` and `P ↦ J₀ P`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 2.5.5 and Corollary 2.5.7.
-/

public section

namespace SymplecticGeometry

open TauCeti Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

/-- The continuous map `J ↦ g_J = ω(·, J ·)` from the `ω`-compatible complex structures to the
inner products of `V`. -/
noncomputable def compatibleMetric :
    C({J : AlmostComplexStructure V // ω.Compatible J}, innerProducts V) where
  toFun J := ⟨_, J.property.associatedBilinForm_mem_innerProducts⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    simp_rw [ω.toContinuousBilinearMap_associatedBilinForm]
    exact ((ContinuousLinearMap.compL ℝ V V ℝ).flip.continuous.clm_comp continuous_const).comp
      ((AlmostComplexStructure.continuous_iff (V := V)).1 continuous_subtypeVal)

/-- The value of `compatibleMetric ω` at `J` is the form `ω(·, J ·)`. -/
@[simp]
theorem coe_compatibleMetric_apply (J : {J : AlmostComplexStructure V // ω.Compatible J}) :
    (compatibleMetric ω J : V →L[ℝ] V →L[ℝ] ℝ) =
      (ω.associatedBilinForm J.val).toContinuousBilinearMap :=
  (rfl)

/-- The continuous map `g ↦ J_{g,ω}` from the inner products of `V` to the `ω`-compatible
complex structures. -/
noncomputable def compatiblePolar :
    C(innerProducts V, {J : AlmostComplexStructure V // ω.Compatible J}) :=
  ⟨fun g ↦ ⟨metricPolarComplexStructure g ω, compatible_metricPolarComplexStructure g ω⟩,
    (continuous_id.metricPolarComplexStructure continuous_const).subtype_mk _⟩

/-- The value of `compatiblePolar ω` at `g` is `J_{g,ω}`. -/
@[simp]
theorem coe_compatiblePolar_apply (g : innerProducts V) :
    (compatiblePolar ω g : AlmostComplexStructure V) = metricPolarComplexStructure g ω :=
  (rfl)

/-- The straight-line homotopy `(t, g) ↦ (1 - t) • g_{J_{g,ω}} + t • g` in the convex set of inner
products, from `g ↦ g_{J_{g,ω}}` to the identity. -/
noncomputable def metricStraightHomotopy :
    ((compatibleMetric ω).comp (compatiblePolar ω)).Homotopy
      (ContinuousMap.id (innerProducts V)) :=
  ContinuousMap.Homotopy.affineOfConvex (convex_innerProducts V) _ _

/-- The value of `metricStraightHomotopy ω` at `(t, g)` is `(1 - t) • g_{J_{g,ω}} + t • g`. -/
@[simp]
theorem coe_metricStraightHomotopy_apply (p : unitInterval × innerProducts V) :
    (metricStraightHomotopy ω p : V →L[ℝ] V →L[ℝ] ℝ) =
      (1 - (p.1 : ℝ)) •
        (ω.associatedBilinForm (metricPolarComplexStructure p.2 ω)).toContinuousBilinearMap +
        (p.1 : ℝ) • (p.2 : V →L[ℝ] V →L[ℝ] ℝ) :=
  (ContinuousMap.Homotopy.coe_affineOfConvex_apply _ _ _ p).trans
    (AffineMap.lineMap_apply_module _ _ _)

/-- The map `J ↦ g_J` is a homotopy equivalence from the `ω`-compatible complex structures to the
inner products of `V`, with homotopy inverse `g ↦ J_{g,ω}`. The composite on compatible
structures is the identity, and the one on inner products is homotopic to the identity by
`metricStraightHomotopy ω`. -/
noncomputable def metricHomotopyEquiv :
    ContinuousMap.HomotopyEquiv {J : AlmostComplexStructure V // ω.Compatible J}
      (innerProducts V) where
  toFun := compatibleMetric ω
  invFun := compatiblePolar ω
  left_inv := by
    have h : (compatiblePolar ω).comp (compatibleMetric ω) = ContinuousMap.id _ := by
      ext J : 2
      exact metricPolarComplexStructure_associatedBilinForm J.property
    rw [h]
  right_inv := ⟨metricStraightHomotopy ω⟩

/-- The forward map of `metricHomotopyEquiv ω` is `J ↦ g_J`. -/
@[simp]
theorem metricHomotopyEquiv_toFun : (metricHomotopyEquiv ω).toFun = compatibleMetric ω :=
  (rfl)

/-- The homotopy inverse of `metricHomotopyEquiv ω` is `g ↦ J_{g,ω}`. -/
@[simp]
theorem metricHomotopyEquiv_invFun : (metricHomotopyEquiv ω).invFun = compatiblePolar ω :=
  (rfl)

/-- The inverse of `metricHomotopyEquiv ω` sends an inner product `g` to `J_{g,ω}`, that is, to
`compatiblePolar ω g`. -/
@[simp]
theorem metricHomotopyEquiv_symm_apply (g : innerProducts V) :
    (metricHomotopyEquiv ω).symm g = compatiblePolar ω g :=
  (rfl)

/-- On a finite-dimensional symplectic vector space `(V, ω)`, the `ω`-compatible complex
structures form a nonempty contractible space. The map `J ↦ g_J = ω(·, J ·)` is a homotopy
equivalence with the space `innerProducts V` of inner products, with homotopy inverse
`g ↦ J_{g,ω}`. On the standard model `(StdSpace ι, ω₀)`, the map `J ↦ -J₀ M`, for `M` the matrix
of `J` and `J₀ = Matrix.J ι ℝ`, is a homeomorphism onto the symmetric positive definite symplectic
matrices, with inverse `P ↦ J₀ P`; both are restrictions of linear maps.

Milestone: *Contractibility of the space of compatible complex structures*. -/
theorem contractibleSpace_compatible_and_homotopyEquiv :
    (Nonempty {J : AlmostComplexStructure V // ω.Compatible J} ∧
      ContractibleSpace {J : AlmostComplexStructure V // ω.Compatible J}) ∧
    (∃ e : ContinuousMap.HomotopyEquiv {J : AlmostComplexStructure V // ω.Compatible J}
        (innerProducts V),
      (∀ J, (e J : V →L[ℝ] V →L[ℝ] ℝ) = (ω.associatedBilinForm J.val).toContinuousBilinearMap) ∧
      ∀ g, (e.symm g : AlmostComplexStructure V) = metricPolarComplexStructure g ω) ∧
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
      ∃ e : {J : AlmostComplexStructure (StdSpace ι) // (stdForm ι).Compatible J} ≃ₜ
          {P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ // P ∈ symplecticGroup ι ℝ ∧ P.PosDef},
        (∀ J, (e J : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
          -Matrix.J ι ℝ * toEuclideanLin.symm J.val.toLinearMap) ∧
        ∀ P, (e.symm P).val.toLinearMap = toEuclideanLin (Matrix.J ι ℝ * P.val) := by
  obtain ⟨J₀, h₀⟩ := ω.exists_compatible
  exact ⟨⟨⟨⟨J₀, h₀⟩⟩, inferInstance⟩, ⟨metricHomotopyEquiv ω, fun _ ↦ rfl, fun _ ↦ rfl⟩,
    fun ι _ _ ↦ ⟨compatibleEquivPosDefSymplectic ι, coe_compatibleEquivPosDefSymplectic_apply,
      compatibleEquivPosDefSymplectic_symm_apply_toLinearMap⟩⟩

end SymplecticGeometry

end
