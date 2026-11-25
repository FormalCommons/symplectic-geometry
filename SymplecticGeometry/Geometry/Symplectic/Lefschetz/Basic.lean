/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Restriction
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import SymplecticGeometry.Geometry.Manifold.Complex.Integrable
public import SymplecticGeometry.Geometry.Symplectic.Lefschetz.Model
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Lefschetz fibrations

A Lefschetz fibration of a real four-manifold `X` over `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` is a map
`π : X → ℂℙ¹` together with a two-form `ω` and an almost complex structure `J` such that `ω` tames
`J`, distinct critical points of `π` have distinct values, near each critical point `π` reads as
the quadric `z₁² + z₂²` in a `J`-holomorphic chart, and `ω` is nondegenerate on the kernel of the
derivative of `π` at each regular point. This is McDuff–Salamon's Definition 7.4.10, with the
almost complex structure part of the data.

`ℂℙ¹` is a real manifold modelled on `𝓘(ℝ, Fin 1 → ℂ)` through Tau Ceti's
`Projectivization.instIsManifoldReal`, and its complex coordinates are the affine charts
`Projectivization.affineChart i`, defined on `Projectivization.affineOpen i`.

The book asks moreover that `J` be integrable, and `π` holomorphic, near the critical points.
Here both follow from the holomorphic chart: on the source of a chart `φ` as in the definition,
the restriction of `J` is integrable (`IsLefschetzChart.isIntegrable_on`), and `π` read through
`φ⁻¹` is holomorphic (`IsLefschetzChart.mdifferentiableAt_of_mem`).

## Main definitions

* `SymplecticGeometry.criticalSet I I' f`: the critical points of a map `f` between manifolds,
  the points that are not regular points in the sense of Tau Ceti's `IsRegularPoint`.
* `SymplecticGeometry.IsLefschetzChart J π p φ i`: `φ` is a `J`-holomorphic chart of `X`
  centred at `p` into `ℂ²` in which `π`, read in the affine chart `affineChart i`, is the quadric
  `z₁² + z₂²` up to the constant `affineChart i (π p)`.
* `SymplecticGeometry.IsLefschetzFibration ω J π`: `π` is a Lefschetz fibration for `ω` and `J`.

## Main results

* `SymplecticGeometry.IsLefschetzChart.isIntegrable_on`: `J` is integrable on the source of a
  Lefschetz chart.
* `SymplecticGeometry.IsLefschetzChart.mdifferentiableAt_of_mem`: `π ∘ φ⁻¹` is holomorphic on
  the target of a Lefschetz chart `φ`.
* `SymplecticGeometry.IsLefschetzFibration.isIntegrable_on`: every critical point of a Lefschetz
  fibration has an open neighbourhood on which `J` is integrable.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Definition 7.4.10.
-/

public section

open Set Filter TopologicalSpace TauCeti Projectivization
open scoped Manifold Topology LinearAlgebra.Projectivization

namespace SymplecticGeometry

section CriticalSet

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The critical set of a map `f : M → N` between manifolds: the points at which the manifold
derivative of `f` is not surjective, the complement of the regular points of Tau Ceti's
`IsRegularPoint`. -/
def criticalSet (f : M → N) : Set M :=
  {x | ¬ IsRegularPoint I I' f x}

variable {I I'}

@[simp]
theorem mem_criticalSet_iff {f : M → N} {x : M} :
    x ∈ criticalSet I I' f ↔ ¬ IsRegularPoint I I' f x :=
  Iff.rfl

/-- The complement of the critical set is the set of regular points. -/
theorem compl_criticalSet (f : M → N) :
    (criticalSet I I' f)ᶜ = {x | IsRegularPoint I I' f x} := by
  ext x
  simp

end CriticalSet

section Lefschetz

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I (⊤ : ℕ∞) X]

/-- A *Lefschetz chart* of `π : X → ℂℙ¹` at `p`, for the almost complex structure `J`: a
partial diffeomorphism `φ` from an open neighbourhood of `p` onto an open subset of `ℂ²` with
`φ p = 0`, whose derivative carries `J` to multiplication by `i`, such that `π` maps the source
of `φ` into the affine open `affineOpen i` and, in the coordinate of the affine chart
`affineChart i`, `π x = π p + (φ x)₁² + (φ x)₂²` on the source of `φ`. -/
structure IsLefschetzChart (J : SmoothAlmostComplexStructure I X) (π : X → ℙ ℂ (Fin 2 → ℂ))
    (p : X) (φ : PartialDiffeomorph I 𝓘(ℝ, Fin 2 → ℂ) X (Fin 2 → ℂ) (⊤ : ℕ∞)) (i : Fin 2) :
    Prop where
  /-- The chart is defined at `p`. -/
  mem_source : p ∈ φ.source
  /-- The chart is centred at `p`. -/
  apply_eq_zero : φ p = 0
  /-- `π` maps the source of the chart into the affine open `affineOpen i`. -/
  source_subset : φ.source ⊆ π ⁻¹' affineOpen i
  /-- The chart is `J`-holomorphic. -/
  mfderiv_apply : ∀ y ∈ φ.source, ∀ v : TangentSpace I y,
    mfderiv I 𝓘(ℝ, Fin 2 → ℂ) φ y (J y v) =
      AlmostComplexStructure.ofComplexModule (Fin 2 → ℂ) (mfderiv I 𝓘(ℝ, Fin 2 → ℂ) φ y v)
  /-- In the chart, `π` is the quadric `z₁² + z₂²` up to the constant `π p`. -/
  affineChart_apply : ∀ x ∈ φ.source,
    affineChart i (π x) 0 = affineChart i (π p) 0 + LefschetzModel.quadric (φ x)

/-- A map `π : X → ℂℙ¹` is a *Lefschetz fibration* for the two-form `ω` and the almost
complex structure `J` when `ω` tames `J`, `π` is injective on its critical points, `π` has a
Lefschetz chart at every critical point, and at every regular point the restriction of `ω` to the
kernel of the derivative of `π` is nondegenerate. -/
structure IsLefschetzFibration (ω : SmoothTwoForm I X) (J : SmoothAlmostComplexStructure I X)
    (π : X → ℙ ℂ (Fin 2 → ℂ)) : Prop where
  /-- `ω` tames `J`. -/
  tames : ω.Tames J
  /-- Each fibre of `π` contains at most one critical point. -/
  injOn_criticalPoints : InjOn π (criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π)
  /-- At every critical point, `π` is the quadric `z₁² + z₂²` in a `J`-holomorphic chart. -/
  exists_model : ∀ p ∈ criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π, ∃ φ i, IsLefschetzChart J π p φ i
  /-- At every regular point, `ω` is nondegenerate on the kernel of the derivative of `π`. -/
  isNondegenerate_ker : ∀ x, IsRegularPoint I 𝓘(ℝ, Fin 1 → ℂ) π x →
    ((ω.bilinFormAt x).restrict
      (mfderiv I 𝓘(ℝ, Fin 1 → ℂ) π x).ker).Nondegenerate

namespace IsLefschetzChart

open scoped ContDiff

variable {J : SmoothAlmostComplexStructure I X} {π : X → ℙ ℂ (Fin 2 → ℂ)} {p : X}
  {φ : PartialDiffeomorph I 𝓘(ℝ, Fin 2 → ℂ) X (Fin 2 → ℂ) ∞} {i : Fin 2}

/-- **`J` is integrable on the source of a Lefschetz chart.** -/
theorem isIntegrable_on (h : IsLefschetzChart J π p φ i) :
    (J.restrictOpen ⟨φ.source, φ.open_source⟩).IsIntegrable := by
  set U : Opens X := ⟨φ.source, φ.open_source⟩
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  rw [SmoothAlmostComplexStructure.isIntegrable_iff_mfderiv]
  intro x
  -- The restriction of `φ` to `U` is a `J`-holomorphic chart of `U` into `ℂ²`.
  let ψ := φ.subtypeRestr U ⟨x⟩
  have hψ : (ψ : U → Fin 2 → ℂ) = φ ∘ Subtype.val := funext (φ.subtypeRestr_apply U ⟨x⟩)
  have hsource : ψ.source = univ := by
    rw [PartialDiffeomorph.subtypeRestr_source]
    exact eq_univ_of_forall fun y ↦ y.property
  have hd (y : U) (v : TangentSpace I y) : mfderiv I 𝓘(ℝ, Fin 2 → ℂ) ψ y v =
      mfderiv I 𝓘(ℝ, Fin 2 → ℂ) φ y (Manifold.tangentSpaceOpenEquiv (I := I) y v) := by
    rw [hψ, mfderiv_comp_apply y (φ.mdifferentiableAt hn y.property)
      (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero), Manifold.mfderiv_subtype_val,
      ContinuousLinearEquiv.coe_coe]
  have hJ : ∀ y ∈ ψ.source, ∀ v : TangentSpace I y,
      mfderiv I 𝓘(ℝ, Fin 2 → ℂ) ψ y (J.restrictOpen U y v) =
        AlmostComplexStructure.ofComplexModule (Fin 2 → ℂ)
          (mfderiv I 𝓘(ℝ, Fin 2 → ℂ) ψ y v) := fun y _ v ↦ by
    rw [hd, hd, SmoothAlmostComplexStructure.restrictOpen_apply,
      ContinuousLinearEquiv.apply_symm_apply, h.mfderiv_apply y y.property]
  -- A linear isomorphism `ℂ² ≃ E` brings it to the model of `X`.
  obtain ⟨e, -⟩ := φ.isInvertible_mfderiv hn x.property
  let L : (Fin 2 → ℂ) ≃L[ℝ] E := e.symm
  exact ⟨ψ.trans L.toDiffeomorph.toPartialDiffeomorph,
    (AlmostComplexStructure.ofComplexModule (Fin 2 → ℂ)).transport L.toLinearEquiv,
    by simp [hsource],
    (J.restrictOpen U).mfderiv_trans_toDiffeomorph_apply_eq_transport hJ L⟩

/-- **`π` is holomorphic in a Lefschetz chart**: on the target of `φ`, the map `π ∘ φ⁻¹` from
`ℂ²` to `ℂℙ¹` is complex differentiable. -/
theorem mdifferentiableAt_of_mem (h : IsLefschetzChart J π p φ i) {z : Fin 2 → ℂ}
    (hz : z ∈ φ.target) :
    MDifferentiableAt 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) (π ∘ φ.symm) z := by
  let g : (Fin 2 → ℂ) → Fin 1 → ℂ := fun w _ ↦ affineChart i (π p) 0 + LefschetzModel.quadric w
  have hg : ContDiff ℂ ∞ g :=
    contDiff_pi.2 fun _ ↦ contDiff_const.add LefschetzModel.contDiff_quadric
  have heq : π ∘ φ.symm =ᶠ[𝓝 z] (affineChart i).symm ∘ g := by
    filter_upwards [φ.open_target.mem_nhds hz] with w hw
    have hx : φ.symm w ∈ φ.source := φ.toPartialEquiv.map_target hw
    have hmem : π (φ.symm w) ∈ (affineChart (K := ℂ) i).source := by
      rw [affineChart_source]
      exact h.source_subset hx
    have hc : affineChart i (π (φ.symm w)) = g w := by
      funext j
      rw [Subsingleton.elim j 0, h.affineChart_apply _ hx]
      simp only [g]
      rw [show φ (φ.symm w) = w from φ.toPartialEquiv.right_inv hw]
    simp only [Function.comp_apply]
    rw [← hc, (affineChart i).left_inv hmem]
  refine MDifferentiableAt.congr_of_eventuallyEq ?_ heq
  exact ((contMDiff_affineChart_symm i ∞).mdifferentiableAt (by simp)).comp z
    (hg.contMDiff.mdifferentiableAt (by simp))

end IsLefschetzChart

namespace IsLefschetzFibration

variable {ω : SmoothTwoForm I X} {J : SmoothAlmostComplexStructure I X}
  {π : X → ℙ ℂ (Fin 2 → ℂ)}

/-- **`J` is integrable near the critical points of a Lefschetz fibration**: every critical point
has an open neighbourhood on which the restriction of `J` is integrable. -/
theorem isIntegrable_on (h : IsLefschetzFibration ω J π) {p : X}
    (hp : p ∈ criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π) :
    ∃ U : Opens X, p ∈ U ∧ (J.restrictOpen U).IsIntegrable := by
  obtain ⟨φ, i, hφ⟩ := h.exists_model p hp
  exact ⟨⟨φ.source, φ.open_source⟩, hφ.mem_source, hφ.isIntegrable_on⟩

end IsLefschetzFibration

end Lefschetz

end SymplecticGeometry

end
