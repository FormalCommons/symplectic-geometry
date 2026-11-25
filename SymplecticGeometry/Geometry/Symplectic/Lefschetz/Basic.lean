/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.Manifold.Projectivization.Map
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Restriction
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import SymplecticGeometry.Geometry.Manifold.Complex.Integrable
public import SymplecticGeometry.Geometry.Manifold.RegularValue.CriticalSet
public import SymplecticGeometry.Geometry.Symplectic.Lefschetz.Model
import SymplecticGeometry.Geometry.Manifold.Projectivization.ProjectiveLineBiholomorphism
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars

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
* `SymplecticGeometry.IsLefschetzChart.exists_isLefschetzChart_comp`: composing `π` with a
  biholomorphism of `ℂℙ¹` keeps a Lefschetz chart at `p`.
* `SymplecticGeometry.IsLefschetzFibration.comp_diffeomorph` and
  `SymplecticGeometry.IsLefschetzFibration.comp_projectivizationMap`: the composite of a Lefschetz
  fibration with a biholomorphism of `ℂℙ¹`, in particular with the map `[v] ↦ [g v]` of
  `g : GL (Fin 2) ℂ`, is a Lefschetz fibration for the same `ω` and `J`.

At a critical point, the coordinate expression of the biholomorphism in two affine charts is a
holomorphic function of one variable with nonzero derivative
(`Projectivization.deriv_affineChart_diffeomorph_affineChart_symm_ne_zero`), so the new chart is
the old one followed by the reparametrisation of the quadric of `Model.lean`.

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

/-- **Changing the base coordinate of a Lefschetz chart.** If `φ` is a Lefschetz chart of a
continuous `π` at `p`, then for every biholomorphism `Ψ` of `ℂℙ¹` the composite `Ψ ∘ π` has a
Lefschetz chart at `p`, for the same `J`. Its affine chart is one at `Ψ (π p)`, and the new chart
is `φ` followed by the change of coordinates of `ℂ²` that turns the coordinate expression of `Ψ`
into a translation on the quadric
(`LefschetzModel.exists_openPartialHomeomorph_apply_add_quadric`). -/
theorem exists_isLefschetzChart_comp (h : IsLefschetzChart J π p φ i) (hπ : Continuous π)
    (Ψ : ℙ ℂ (Fin 2 → ℂ) ≃ₘ^ω⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ)) :
    ∃ φ' j, IsLefschetzChart J (Ψ ∘ π) p φ' j := by
  obtain ⟨j, hj⟩ := exists_mem_affineOpen (Ψ (π p))
  have hpi : π p ∈ affineOpen i := h.source_subset h.mem_source
  -- The coordinate expression of `Ψ` in the charts `i` and `j` reads `Ψ` on `affineOpen i`.
  have hchart (y : ℙ ℂ (Fin 2 → ℂ)) (hy : y ∈ affineOpen i) :
      affineChart j (Ψ ((affineChart i).symm fun _ ↦ affineChart i y 0)) 0 =
        affineChart j (Ψ y) 0 := by
    rw [show (fun _ : Fin 1 ↦ affineChart i y 0) = affineChart (K := ℂ) i y from
      (eq_const_of_subsingleton _ 0).symm, (affineChart i).left_inv (by rwa [affineChart_source])]
  have h0t : (0 : Fin 2 → ℂ) ∈ φ.target :=
    h.apply_eq_zero ▸ φ.toPartialEquiv.map_source h.mem_source
  have hU : φ.target ∩ (fun w ↦ Ψ (π (φ.symm w))) ⁻¹' affineOpen j ∈ 𝓝 (0 : Fin 2 → ℂ) := by
    have hp0 : φ.symm 0 = p := h.apply_eq_zero ▸ φ.toPartialEquiv.left_inv h.mem_source
    refine inter_mem (φ.open_target.mem_nhds h0t) (ContinuousAt.preimage_mem_nhds
      (Ψ.continuous.continuousAt.comp (hπ.continuousAt.comp
        (φ.contMDiffOn_invFun.continuousOn.continuousAt (φ.open_target.mem_nhds h0t)))) ?_)
    rw [hp0]
    exact (isOpen_affineOpen j).mem_nhds hj
  obtain ⟨e, h0e, he0, heU, hea, hesa, heq⟩ :=
    LefschetzModel.exists_openPartialHomeomorph_apply_add_quadric
      (contDiffAt_affineChart_diffeomorph_affineChart_symm Ψ hpi hj).analyticAt
      (deriv_affineChart_diffeomorph_affineChart_symm_ne_zero Ψ hpi hj) hU
  -- The change of coordinates `e` of `ℂ²` is biholomorphic, hence a real partial diffeomorphism.
  let e' : PartialDiffeomorph 𝓘(ℝ, Fin 2 → ℂ) 𝓘(ℝ, Fin 2 → ℂ) (Fin 2 → ℂ) (Fin 2 → ℂ) ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun :=
        ((hea.contDiffOn e.open_source.uniqueDiffOn).restrict_scalars ℝ).contMDiffOn
      contMDiffOn_invFun :=
        ((hesa.contDiffOn e.open_target.uniqueDiffOn).restrict_scalars ℝ).contMDiffOn }
  -- Mathlib's `PartialDiffeomorph.trans` has no lemmas for its source and its values.
  have hsrc : (φ.trans e').source = φ.source ∩ φ ⁻¹' e.source := rfl
  have happ (x : X) : (φ.trans e') x = e (φ x) := rfl
  refine ⟨φ.trans e', j, ⟨?_, ?_, fun x hx ↦ ?_, fun y hy ↦ ?_, fun x hx ↦ ?_⟩⟩
  · rw [hsrc]
    exact ⟨h.mem_source, by rw [mem_preimage, h.apply_eq_zero]; exact h0e⟩
  · rw [happ, h.apply_eq_zero, he0]
  · rw [hsrc] at hx
    have hxx : φ.symm (φ x) = x := φ.toPartialEquiv.left_inv hx.1
    have hx' : Ψ (π (φ.symm (φ x))) ∈ affineOpen j := (heU hx.2).2
    rwa [hxx] at hx'
  · rw [hsrc] at hy
    have he : IsPseudoholomorphicAt
        (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (Fin 2 → ℂ))
        (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (Fin 2 → ℂ)) e (φ y) :=
      isPseudoholomorphicAt_ofComplexManifold_iff.2
        (hea _ hy.2).differentiableAt.mdifferentiableAt
    exact he.comp (h.isPseudoholomorphicAt y hy.1)
  · rw [hsrc] at hx
    rw [happ, Function.comp_apply, Function.comp_apply, ← hchart _ (h.source_subset hx.1),
      ← hchart _ hpi, h.affineChart_apply x hx.1, heq _ hx.2]

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

/-- **Composing with a biholomorphism of the base.** If `π` is a Lefschetz fibration for `ω` and
`J`, so is `Ψ ∘ π` for every biholomorphism `Ψ` of `ℂℙ¹` (here `⊤` is the analytic order `ω`). -/
theorem comp_diffeomorph (h : IsLefschetzFibration ω J π)
    (Ψ : ℙ ℂ (Fin 2 → ℂ) ≃ₘ^⊤⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ)) :
    IsLefschetzFibration ω J (Ψ ∘ π) := by
  -- `Ψ` as a smooth diffeomorphism of the underlying real manifold.
  let Φ : ℙ ℂ (Fin 2 → ℂ) ≃ₘ^(⊤ : ℕ∞)⟮𝓘(ℝ, Fin 1 → ℂ), 𝓘(ℝ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ) :=
    { toEquiv := Ψ.toEquiv
      contMDiff_toFun := ((by simpa using Ψ.contMDiff.restrictScalars ℝ :
        ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ) ⊤ Ψ)).of_le le_top
      contMDiff_invFun := ((by simpa using Ψ.symm.contMDiff.restrictScalars ℝ :
        ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ) ⊤ Ψ.symm)).of_le le_top }
  -- `Φ` has the same underlying function as `Ψ`, by construction.
  have hΦ : ⇑Φ = Ψ := rfl
  have hcrit : criticalSet I 𝓘(ℝ, Fin 1 → ℂ) (Ψ ∘ π) = criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π := by
    rw [← hΦ, Φ.criticalSet_comp (by simp)]
  refine ⟨Φ.contMDiff.comp h.contMDiff, h.tames, hcrit ▸ Ψ.injective.comp_injOn
    h.injOn_criticalPoints, hcrit ▸ fun p hp ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨φ, i, hφ⟩ := h.exists_model p hp
    exact hφ.exists_isLefschetzChart_comp h.contMDiff.continuous Ψ
  · have hπ : MDifferentiableAt I 𝓘(ℝ, Fin 1 → ℂ) π x :=
      (h.contMDiff x).mdifferentiableAt (by simp)
    have hinj : (mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ) Φ (π x)).ker = ⊥ :=
      LinearMap.ker_eq_bot.2 ((Φ.isLocalDiffeomorph _).isInvertible_mfderiv (by simp)).injective
    have hker : (mfderiv I 𝓘(ℝ, Fin 1 → ℂ) (Ψ ∘ π) x).ker =
        (mfderiv I 𝓘(ℝ, Fin 1 → ℂ) π x).ker := by
      rw [← hΦ, mfderiv_comp x (Φ.mdifferentiable (by simp) _) hπ,
        ContinuousLinearMap.toLinearMap_comp, LinearMap.ker_comp_of_ker_eq_bot _ hinj]
    rw [hker]
    exact h.isNondegenerate_ker x ((Φ.comp_isRegularPoint_iff (by simp)).1 (hΦ ▸ hx))

/-- **Composing with a projective transformation.** If `π` is a Lefschetz fibration for `ω` and
`J`, so is `x ↦ g • π x` for every `g : GL (Fin 2) ℂ`, acting on `ℂℙ¹` through its linear action
on `ℂ²`. -/
theorem comp_projectivizationMap (h : IsLefschetzFibration ω J π) (g : GL (Fin 2) ℂ) :
    IsLefschetzFibration ω J (fun x ↦ g • π x) :=
  h.comp_diffeomorph
    { toFun := (g • ·)
      invFun := (g⁻¹ • ·)
      left_inv := inv_smul_smul g
      right_inv := smul_inv_smul g
      contMDiff_toFun := contMDiff_const_smul g
      contMDiff_invFun := contMDiff_const_smul g⁻¹ }

end IsLefschetzFibration

end Lefschetz

end SymplecticGeometry

end
