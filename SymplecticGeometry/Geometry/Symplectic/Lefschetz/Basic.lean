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
import SymplecticGeometry.Geometry.Manifold.Morse.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Morse.Submersion

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
* `SymplecticGeometry.IsLefschetzFibration.manifoldMorseIndex_comp`: at a critical point `p` of a
  Lefschetz fibration `π`, and for `μ : ℂℙ¹ → ℝ` with nonzero derivative at `π p`, the point `p`
  is a nondegenerate critical point of `μ ∘ π` of Morse index `2`. It is read in a Lefschetz chart
  from `SymplecticGeometry.LefschetzModel.manifoldMorseIndex_comp_quadric`, and moved to `X` by
  `IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp` and Tau Ceti's
  `TauCeti.IsRegularPoint.manifoldMorseIndex_comp`.

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

/-- On the source of a Lefschetz chart, `π` is the inverse affine chart applied to
`affineChart i (π p) + quadric ∘ φ`, written in the one coordinate of `Fin 1 → ℂ`. -/
theorem apply_eq_affineChart_symm (h : IsLefschetzChart J π p φ i) {x : X} (hx : x ∈ φ.source) :
    π x = (affineChart i).symm fun _ ↦ affineChart i (π p) 0 + LefschetzModel.quadric (φ x) := by
  have hmem : π x ∈ (affineChart (K := ℂ) i).source := by
    rw [affineChart_source]
    exact h.source_subset hx
  rw [← (affineChart i).left_inv hmem]
  congr 1
  funext j
  rw [Subsingleton.elim j 0, h.affineChart_apply _ hx]

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
    have hφw : φ (φ.symm w) = w := φ.toPartialEquiv.right_inv hw
    -- `g` is the right-hand side of `apply_eq_affineChart_symm`, as a function of `φ x`.
    exact (h.apply_eq_affineChart_symm hx).trans (by rw [hφw]; rfl)
  exact ((contMDiff_affineChart_symm i ∞).contMDiffAt.comp z hg.contMDiff.contMDiffAt
    ).congr_of_eventuallyEq heq

/-- **`π` is holomorphic in a Lefschetz chart**: on the target of `φ`, the map `π ∘ φ⁻¹` from
`ℂ²` to `ℂℙ¹` is complex differentiable. -/
theorem mdifferentiableAt_of_mem (h : IsLefschetzChart J π p φ i) {z : Fin 2 → ℂ}
    (hz : z ∈ φ.target) :
    MDifferentiableAt 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) (π ∘ φ.symm) z :=
  (h.contMDiffAt_comp_symm hz).mdifferentiableAt (by simp)

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

/-- **The Morse index of `μ ∘ π` at a critical point of a Lefschetz fibration.** If `p` is a
critical point of a Lefschetz fibration `π` and `μ : ℂℙ¹ → ℝ` is `C²` at `π p` with nonzero
derivative there, then `p` is a nondegenerate critical point of `μ ∘ π`, of Morse index `2`. -/
theorem manifoldMorseIndex_comp [I.Boundaryless]
    (h : IsLefschetzFibration ω J π) {p : X} (hp : p ∈ criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π)
    {μ : ℙ ℂ (Fin 2 → ℂ) → ℝ} (hμ : ContMDiffAt 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ) 2 μ (π p))
    (hdμ : mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ) μ (π p) ≠ 0) :
    IsManifoldNondegenerateCriticalPoint I (μ ∘ π) p ∧ manifoldMorseIndex I (μ ∘ π) p = 2 := by
  obtain ⟨φ, i, hφ⟩ := h.exists_model p hp
  -- `μ` read in the affine chart `i`, centred at `π p`, as a function on `ℂ`.
  set a := affineChart i (π p)
  set L := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ).symm
  set ν : ℂ → ℝ := fun t ↦ μ ((affineChart i).symm (a + L t))
  have hpe : π p ∈ (affineOpenPartialHomeomorph (K := ℂ) (n := 1) i).source := by
    simpa using hφ.source_subset hφ.mem_source
  have hμe : ContDiffAt ℝ 2 (μ ∘ (affineChart i).symm) a := by
    simpa [a, affineOpenPartialHomeomorph_extend_apply] using
      (contMDiffAt_iff_contDiffAt_comp_extend_symm
        (affineOpenPartialHomeomorph_mem_maximalAtlas i) hpe).1 hμ
  have hdμe : fderiv ℝ (μ ∘ (affineChart i).symm) a ≠ 0 := by
    have := mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero (I := 𝓘(ℝ, Fin 1 → ℂ))
      (f := μ) (affineOpenPartialHomeomorph_mem_maximalAtlas i) hpe
    simp only [OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm,
      CompTriple.comp_eq, coe_affineOpenPartialHomeomorph_symm,
      affineOpenPartialHomeomorph_extend_apply] at this
    exact fun h0 ↦ hdμ (mem_criticalPoints_iff_mfderiv_eq_zero.1 (mem_criticalPoints.2 (this.2 h0)))
  have hκ : HasFDerivAt (fun t ↦ a + L t) (L : ℂ →L[ℝ] Fin 1 → ℂ) 0 :=
    L.hasFDerivAt.const_add a
  have hμe' : ContDiffAt ℝ 2 (μ ∘ (affineChart i).symm) (a + L 0) := by simpa using hμe
  have hν : ContDiffAt ℝ 2 ν 0 :=
    hμe'.comp (g := μ ∘ (affineChart i).symm) 0 (contDiffAt_const.add L.contDiff.contDiffAt)
  have hdν : fderiv ℝ ν 0 ≠ 0 := by
    have hd : fderiv ℝ ν 0 =
        (fderiv ℝ (μ ∘ (affineChart i).symm) (a + L 0)).comp (L : ℂ →L[ℝ] Fin 1 → ℂ) :=
      ((hμe'.differentiableAt (by norm_num)).hasFDerivAt.comp
        (g := μ ∘ (affineChart i).symm) 0 hκ).fderiv
    rw [hd]
    intro h0
    refine hdμe (ContinuousLinearMap.ext fun v ↦ ?_)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, map_zero, add_zero, zero_apply]
      using congr($h0 (L.symm v))
  obtain ⟨hnd, hidx⟩ := LefschetzModel.manifoldMorseIndex_comp_quadric hν hdν
  -- Near `p`, `μ ∘ π` is `ν ∘ quadric` read through `φ`.
  have heq : μ ∘ π =ᶠ[𝓝 p] (ν ∘ LefschetzModel.quadric) ∘ φ := by
    filter_upwards [φ.open_source.mem_nhds hφ.mem_source] with x hx
    simp only [Function.comp_apply, ν, hφ.apply_eq_affineChart_symm hx]
    congr 2
    funext j
    simp [a, L, Subsingleton.elim j 0]
  have hloc : IsLocalDiffeomorphAt I 𝓘(ℝ, Fin 2 → ℂ) (⊤ : ℕ∞) φ p :=
    φ.isLocalDiffeomorphAt _ _ _ hφ.mem_source
  -- `X` is finite-dimensional near `p`, since `dφ` identifies its model with `ℂ²`.
  have : FiniteDimensional ℝ E :=
    (hloc.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv.symm.finiteDimensional
  have hnd₀ : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, Fin 2 → ℂ) (ν ∘ LefschetzModel.quadric)
      (φ p) := hφ.apply_eq_zero ▸ hnd
  refine ⟨(hloc.isManifoldNondegenerateCriticalPoint_comp (by simp) hnd₀).congr_of_eventuallyEq
    heq.symm, ?_⟩
  rw [manifoldMorseIndex_congr_of_eventuallyEq heq,
    (hloc.isRegularPoint (by simp)).manifoldMorseIndex_comp hnd₀.contMDiffAt
      (hloc.contMDiffAt.of_le (by simp)) hnd₀.mem_criticalPoints, hφ.apply_eq_zero, hidx]

end IsLefschetzFibration

end Lefschetz

end SymplecticGeometry

end
