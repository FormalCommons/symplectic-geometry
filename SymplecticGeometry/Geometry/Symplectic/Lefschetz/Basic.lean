/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Restriction
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import SymplecticGeometry.Geometry.Manifold.Complex.Integrable
public import SymplecticGeometry.Geometry.Manifold.RegularValue.CriticalSet
public import SymplecticGeometry.Geometry.Symplectic.Lefschetz.Model
public import TauCeti.Geometry.Manifold.RegularValue.Open
import SymplecticGeometry.Topology.Connected.Projectivization
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Lefschetz fibrations

A Lefschetz fibration of a real manifold `X` over `ℂℙ¹ = ℙ ℂ (Fin 2 → ℂ)` is a smooth map
`π : X → ℂℙ¹` together with a two-form `ω` and an almost complex structure `J` such that `ω` tames
`J`, distinct critical points of `π` have distinct values, near each critical point `π` reads as
the quadric `z₁² + z₂²` in a `J`-holomorphic chart, and `ω` is nondegenerate on the kernel of the
derivative of `π` at each regular point. This follows McDuff–Salamon's Definition 7.4.10, with
the almost complex structure part of the data, but in more generality: nothing fixes the dimension
of `X` (a chart into `ℂ²` at a critical point forces real dimension four only near that point,
and a fibration without critical points may have any dimension), and `ω` is only a two-form that
tames `J`, not assumed closed.

`ℂℙ¹` is a real manifold modelled on `𝓘(ℝ, Fin 1 → ℂ)` through Tau Ceti's
`Projectivization.instIsManifoldReal`, and its complex coordinates are the affine charts
`Projectivization.affineChart i`, defined on `Projectivization.affineOpen i`.

The book asks moreover that `J` be integrable, and `π` holomorphic, near the critical points.
Here both follow from the holomorphic chart: on the source of a chart `φ` as in the definition,
the restriction of `J` is integrable (`IsLefschetzChart.isIntegrable_on`), and `π` read through
`φ⁻¹` is holomorphic (`IsLefschetzChart.contMDiffAt_comp_symm` and
`IsLefschetzChart.mdifferentiableAt_of_mem`).

## Main definitions

* `SymplecticGeometry.IsLefschetzChart J π p φ i`: `φ` is a `J`-holomorphic chart of `X`
  centred at `p` into `ℂ²` in which `π`, read in the affine chart `affineChart i`, is the quadric
  `z₁² + z₂²` up to the constant `affineChart i (π p)`.
* `SymplecticGeometry.IsLefschetzFibration ω J π`: `π` is a Lefschetz fibration for `ω` and `J`.

## Main results

* `SymplecticGeometry.IsLefschetzChart.isIntegrable_on`: `J` is integrable on the source of a
  Lefschetz chart.
* `SymplecticGeometry.IsLefschetzChart.contMDiffAt_comp_symm` and
  `SymplecticGeometry.IsLefschetzChart.mdifferentiableAt_of_mem`: `π ∘ φ⁻¹` is holomorphic on the
  target of a Lefschetz chart `φ`.
* `SymplecticGeometry.IsLefschetzFibration.isIntegrable_on`: every critical point of a Lefschetz
  fibration has an open neighbourhood on which `J` is integrable.
* `SymplecticGeometry.IsLefschetzChart.isRegularPoint`: in the source of a Lefschetz chart `φ`,
  every point at which `φ` does not vanish is a regular point of `π`.
* `SymplecticGeometry.IsLefschetzFibration.isDiscrete_criticalSet` and
  `SymplecticGeometry.IsLefschetzFibration.finite_criticalPoints`: the critical points of a
  Lefschetz fibration are isolated, hence finitely many when `X` is compact.
* `SymplecticGeometry.IsLefschetzFibration.isOpen_regularValue` and
  `SymplecticGeometry.IsLefschetzFibration.isConnected_regularValue`: for compact `X`, the regular
  values form an open connected subset of `ℂℙ¹`, the complement of finitely many critical values
  (`Projectivization.isConnected_compl_of_countable`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Definition 7.4.10.
-/

public section

open Set Filter TopologicalSpace TauCeti Projectivization
open scoped Manifold Topology LinearAlgebra.Projectivization

namespace SymplecticGeometry

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
  /-- The chart is `J`-holomorphic, for the complex structure of `ℂ²`. -/
  isPseudoholomorphicAt : ∀ y ∈ φ.source, IsPseudoholomorphicAt J
    (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (Fin 2 → ℂ)) φ y
  /-- In the chart, `π` is the quadric `z₁² + z₂²` up to the constant `π p`. -/
  affineChart_apply : ∀ x ∈ φ.source,
    affineChart i (π x) 0 = affineChart i (π p) 0 + LefschetzModel.quadric (φ x)

/-- A map `π : X → ℂℙ¹` is a *Lefschetz fibration* for the two-form `ω` and the almost
complex structure `J` when `π` is smooth, `ω` tames `J`, `π` is injective on its critical
points, `π` has a Lefschetz chart at every critical point, and at every regular point the
restriction of `ω` to the kernel of the derivative of `π` is nondegenerate. Neither the
dimension of `X` nor the closedness of `ω` is assumed. -/
structure IsLefschetzFibration (ω : SmoothTwoForm I X) (J : SmoothAlmostComplexStructure I X)
    (π : X → ℙ ℂ (Fin 2 → ℂ)) : Prop where
  /-- `π` is smooth. -/
  contMDiff : ContMDiff I 𝓘(ℝ, Fin 1 → ℂ) (⊤ : ℕ∞) π
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

/-- The derivative of a Lefschetz chart carries `J` to multiplication by `i` on `ℂ²`. -/
theorem mfderiv_apply (h : IsLefschetzChart J π p φ i) {y : X} (hy : y ∈ φ.source)
    (v : TangentSpace I y) :
    mfderiv I 𝓘(ℝ, Fin 2 → ℂ) φ y (J y v) =
      AlmostComplexStructure.ofComplexModule (Fin 2 → ℂ) (mfderiv I 𝓘(ℝ, Fin 2 → ℂ) φ y v) := by
  exact ((h.isPseudoholomorphicAt y hy).mfderiv_apply_commute v).trans
    ((SmoothAlmostComplexStructure.ofComplexManifold_apply (E := Fin 2 → ℂ) (M := Fin 2 → ℂ) _
      _).trans (AlmostComplexStructure.ofComplexModule_apply (V := Fin 2 → ℂ) _).symm)

/-- **`J` is integrable on the source of a Lefschetz chart.** -/
theorem isIntegrable_on (h : IsLefschetzChart J π p φ i) :
    (J.restrictOpen ⟨φ.source, φ.open_source⟩).IsIntegrable :=
  J.isIntegrable_restrictOpen_source fun _ hy ↦ h.mfderiv_apply hy

/-- **`π` is holomorphic in a Lefschetz chart**: on the target of `φ`, the map `π ∘ φ⁻¹` from
`ℂ²` to `ℂℙ¹` is a smooth map of complex manifolds. -/
theorem contMDiffAt_comp_symm (h : IsLefschetzChart J π p φ i) {z : Fin 2 → ℂ}
    (hz : z ∈ φ.target) :
    ContMDiffAt 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) ∞ (π ∘ φ.symm) z := by
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
  exact ((contMDiff_affineChart_symm i ∞).contMDiffAt.comp z hg.contMDiff.contMDiffAt
    ).congr_of_eventuallyEq heq

/-- **`π` is holomorphic in a Lefschetz chart**: on the target of `φ`, the map `π ∘ φ⁻¹` from
`ℂ²` to `ℂℙ¹` is complex differentiable. -/
theorem mdifferentiableAt_of_mem (h : IsLefschetzChart J π p φ i) {z : Fin 2 → ℂ}
    (hz : z ∈ φ.target) :
    MDifferentiableAt 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) (π ∘ φ.symm) z :=
  (h.contMDiffAt_comp_symm hz).mdifferentiableAt (by simp)

/-- **Regular points in a Lefschetz chart.** A point `x` of the source of a Lefschetz
chart `φ` with `φ x ≠ 0` is a regular point of `π`: there `π` is the quadric read through `φ` and
the affine chart, and the quadric is regular away from `0`. -/
theorem isRegularPoint (h : IsLefschetzChart J π p φ i) {x : X} (hx : x ∈ φ.source)
    (hx0 : φ x ≠ 0) : IsRegularPoint I 𝓘(ℝ, Fin 1 → ℂ) π x := by
  let q : (Fin 2 → ℂ) → ℂ := fun w ↦ affineChart i (π p) 0 + LefschetzModel.quadric w
  let e := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ).symm
  have heq : π =ᶠ[𝓝 x] ((affineChart i).symm ∘ e ∘ q) ∘ φ := by
    filter_upwards [φ.open_source.mem_nhds hx] with y hy
    have hc : affineChart i (π y) = e (q (φ y)) := by
      rw [ContinuousLinearEquiv.coe_funUnique_symm]
      funext j
      rw [Subsingleton.elim j 0, h.affineChart_apply _ hy, Function.const_apply]
    have hmem : π y ∈ (affineChart (K := ℂ) i).source := by
      rw [affineChart_source]
      exact h.source_subset hy
    simp only [Function.comp_apply]
    rw [← hc, (affineChart i).left_inv hmem]
  refine IsRegularPoint.congr_of_eventuallyEq ?_ heq
  refine ((PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ φ hx).isRegularPoint_comp_iff
    (by simp)).2 ((IsRegularPoint.comp ?_ ((e.comp_isRegularPoint_iff).2 ?_)))
  · -- The inverse of an affine chart is a local diffeomorphism.
    rw [← coe_affineOpenPartialHomeomorph_symm]
    exact ((affineOpenPartialHomeomorph i).isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
      (n := 1) (affineOpenPartialHomeomorph_mem_maximalAtlas i) (by simp)).isRegularPoint
      one_ne_zero
  · rw [isRegularPoint_iff_surjective_fderiv, fderiv_const_add]
    exact LefschetzModel.surjective_fderiv_real_quadric hx0

/-- The only critical point of `π` in the source of a Lefschetz chart at `p` is `p`. -/
theorem eq_of_mem_criticalSet (h : IsLefschetzChart J π p φ i) {x : X} (hx : x ∈ φ.source)
    (hxc : x ∈ criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π) : x = p := by
  by_contra hne
  refine mem_criticalSet_iff.1 hxc (h.isRegularPoint hx fun h0 ↦ hne ?_)
  exact φ.injOn hx h.mem_source (h0.trans h.apply_eq_zero.symm)

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

/-- **The critical points of a Lefschetz fibration are isolated**: each has a neighbourhood, the
source of a Lefschetz chart, that contains no other. -/
theorem isDiscrete_criticalSet (h : IsLefschetzFibration ω J π) :
    IsDiscrete (criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π) := by
  refine isDiscrete_iff_forall_mem_exists_isOpen.2 fun p hp ↦ ?_
  obtain ⟨φ, i, hφ⟩ := h.exists_model p hp
  refine ⟨φ.source, φ.open_source,
    Subset.antisymm (fun x hx ↦ hφ.eq_of_mem_criticalSet hx.1 hx.2) ?_⟩
  rintro x rfl
  exact ⟨hφ.mem_source, hp⟩

/-- **A Lefschetz fibration on a compact manifold has finitely many critical points.** -/
theorem finite_criticalPoints [CompactSpace X] (h : IsLefschetzFibration ω J π) :
    (criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π).Finite :=
  (isClosed_criticalSet h.contMDiff (by simp)).isCompact.finite h.isDiscrete_criticalSet

/-- **The regular values of a Lefschetz fibration on a compact manifold form an open set.** -/
theorem isOpen_regularValue [CompactSpace X] (h : IsLefschetzFibration ω J π) :
    IsOpen {y | IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π y} :=
  isOpen_setOf_isRegularValue_of_isClosedMap h.contMDiff (by simp)
    h.contMDiff.continuous.isClosedMap

/-- **The regular values of a Lefschetz fibration on a compact manifold form a connected set**:
the complement in `ℂℙ¹` of the finitely many critical values. -/
theorem isConnected_regularValue [CompactSpace X] (h : IsLefschetzFibration ω J π) :
    IsConnected {y | IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π y} := by
  rw [setOf_isRegularValue_eq_compl_image, ← criticalSet_def]
  refine isConnected_compl_of_countable ?_ (h.finite_criticalPoints.image π).countable
  simp [rank_pi]

end IsLefschetzFibration

end Lefschetz

end SymplecticGeometry

end
