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
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Submanifold
public import SymplecticGeometry.Topology.Sets.Opens.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Integrable
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Kahler
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Prod
public import SymplecticGeometry.Geometry.Manifold.RegularValue.CriticalSet
public import SymplecticGeometry.Geometry.Symplectic.Lefschetz.Model
public import TauCeti.Geometry.Manifold.RegularValue.Open
import SymplecticGeometry.Geometry.Manifold.Projectivization.ProjectiveLineBiholomorphism
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.RestrictScalars
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import SymplecticGeometry.Geometry.Manifold.Morse.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Morse.Submersion

/-!
# Lefschetz fibrations and Lefschetz pencils

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

A Lefschetz pencil with base locus a finite set `B ⊆ X` asks that `ω` tame `J` on all of `X`,
base points included, and is a map `π` from the open complement `B.complOpens` of `B` to `ℂℙ¹`
that is a Lefschetz fibration for the restrictions of `ω` and `J`
(the restriction of `ω` is its pullback `SmoothForm.mpullback` along the inclusion, that of `J` is
Tau Ceti's `SmoothAlmostComplexStructure.restrictOpen`), and that near each base point `b` reads
as `x ↦ [φ x]` for a `J`-holomorphic chart `φ` into `ℂ²` centred at `b`. Its fibre closures, the
fibres of `π` together with `B`, are closed when `π` is continuous.

The simplest example is the second projection `S × ℂℙ¹ → ℂℙ¹`, for a two-form on `S` taming an
almost complex structure, such as an area form on a closed surface: it has no critical points,
and it is a Lefschetz pencil with empty base locus. Fibrations without critical points are built
by `IsLefschetzFibration.of_isRegularPoint`: the kernel of the derivative of a pseudoholomorphic
map is invariant under the almost complex structure, so a taming two-form is nondegenerate on it
(`TauCeti.SmoothTwoForm.Tames.nondegenerate_restrict_ker_mfderiv`, in
`Geometry/Symplectic/Manifold/AlmostComplex/Submanifold.lean`, with
`TauCeti.SmoothTwoForm.Tames.restrictOpen` for the restriction to the complement of `B`).

## Main definitions

* `SymplecticGeometry.IsLefschetzChart J π p φ i`: `φ` is a `J`-holomorphic chart of `X`
  centred at `p` into `ℂ²` in which `π`, read in the affine chart `affineChart i`, is the quadric
  `z₁² + z₂²` up to the constant `affineChart i (π p)`.
* `SymplecticGeometry.IsLefschetzFibration ω J π`: `π` is a Lefschetz fibration for `ω` and `J`.
* `SymplecticGeometry.IsLefschetzPencil ω J B π`: `π`, defined off the finite set `B`, is a
  Lefschetz pencil with base locus `B` for `ω` and `J`.
* `SymplecticGeometry.fiberClosure B π t`: the fibre of `π` over `t`, together with `B`.

## Main results

* `SymplecticGeometry.IsLefschetzChart.isIntegrable_on`: `J` is integrable on the source of a
  Lefschetz chart.
* `SymplecticGeometry.IsLefschetzChart.contMDiffAt_comp_symm` and
  `SymplecticGeometry.IsLefschetzChart.mdifferentiableAt_of_mem`: `π ∘ φ⁻¹` is holomorphic on the
  target of a Lefschetz chart `φ`.
* `SymplecticGeometry.IsLefschetzFibration.isIntegrable_on`: every critical point of a Lefschetz
  fibration has an open neighbourhood on which `J` is integrable.
* `SymplecticGeometry.IsLefschetzChart.eqOn_source`: on the source of a Lefschetz chart `φ`,
  `π` is the inverse affine chart composed with the shifted quadric and with `φ`.
* `SymplecticGeometry.IsLefschetzChart.isRegularPoint`: in the source of a Lefschetz chart `φ`,
  every point at which `φ` does not vanish is a regular point of `π`.
* `SymplecticGeometry.IsLefschetzFibration.isDiscrete_criticalSet` and
  `SymplecticGeometry.IsLefschetzFibration.finite_criticalPoints`: the critical points of a
  Lefschetz fibration are isolated, hence finitely many when `X` is compact.
* `SymplecticGeometry.IsLefschetzFibration.isOpen_regularValue` and
  `SymplecticGeometry.IsLefschetzFibration.isConnected_regularValue`: for compact `X`, the regular
  values form an open connected subset of `ℂℙ¹`, the complement of finitely many critical values
  (Tau Ceti's `TauCeti.isConnected_compl_of_finite_of_one_lt_rank`).
* `SymplecticGeometry.IsLefschetzChart.exists_isLefschetzChart_comp`: composing `π` with a
  biholomorphism of `ℂℙ¹` keeps a Lefschetz chart at `p`.
* `SymplecticGeometry.IsLefschetzFibration.comp_diffeomorph` and
  `SymplecticGeometry.IsLefschetzFibration.comp_projectivizationMap`: the composite of a Lefschetz
  fibration with a biholomorphism of `ℂℙ¹`, in particular with the map `[v] ↦ [g v]` of
  `g : GL (Fin 2) ℂ`, is a Lefschetz fibration for the same `ω` and `J`.
* `SymplecticGeometry.IsLefschetzFibration.of_isRegularPoint`: a smooth pseudoholomorphic map
  without critical points is a Lefschetz fibration for every two-form taming the almost complex
  structure.
* `SymplecticGeometry.isClosed_fiberClosure`: fibre closures of a continuous map are closed.
* `SymplecticGeometry.isLefschetzFibration_snd` and `SymplecticGeometry.isLefschetzPencil_empty`:
  the product example.
* `SymplecticGeometry.IsLefschetzFibration.manifoldMorseIndex_comp`: at a critical point `p` of a
  Lefschetz fibration `π`, and for `μ : ℂℙ¹ → ℝ` with nonzero derivative at `π p`, the point `p`
  is a nondegenerate critical point of `μ ∘ π` of Morse index `2`. It is read in a Lefschetz chart
  from `SymplecticGeometry.LefschetzModel.manifoldMorseIndex_comp_quadric`, and moved to `X` by
  `IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp` and Tau Ceti's
  `TauCeti.IsRegularPoint.manifoldMorseIndex_comp`.

In `exists_isLefschetzChart_comp`, the biholomorphism read between an affine coordinate and an
affine chart is a holomorphic function of one variable with nonzero derivative
(`Projectivization.deriv_affineChart_diffeomorph_affineParam_ne_zero`), so the new chart is the
old one followed by the reparametrisation of the quadric of `Model.lean`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Definition 7.4.10 and Section 7.4.
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
    (SmoothAlmostComplexStructure.ofComplexManifold_apply_eq_ofComplexModule _ _)

/-- **`J` is integrable on the source of a Lefschetz chart.** -/
theorem isIntegrable_on (h : IsLefschetzChart J π p φ i) :
    (J.restrictOpen ⟨φ.source, φ.open_source⟩).IsIntegrable :=
  J.isIntegrable_restrictOpen_source fun _ hy ↦ h.mfderiv_apply hy

/-- **The local form of `π` in a Lefschetz chart**: on the source of `φ`, `π` is the inverse of
the affine chart `affineChart i` composed with `w ↦ affineChart i (π p) 0 + quadric w` and
with `φ`. -/
theorem eqOn_source (h : IsLefschetzChart J π p φ i) :
    EqOn π ((affineChart i).symm ∘
      (fun w _ ↦ affineChart i (π p) 0 + LefschetzModel.quadric w) ∘ φ) φ.source := by
  intro x hx
  have hmem : π x ∈ (affineChart (K := ℂ) i).source := by
    rw [affineChart_source]
    exact h.source_subset hx
  rw [Function.comp_apply, Function.comp_apply, ← (affineChart i).left_inv hmem]
  congr 1
  funext j
  rw [Subsingleton.elim j 0, h.affineChart_apply _ hx]

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
    have hw' : φ (φ.symm w) = w := φ.toPartialEquiv.right_inv hw
    simp only [Function.comp_apply]
    rw [h.eqOn_source hx, Function.comp_apply, Function.comp_apply, hw']
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
    rw [ContinuousLinearEquiv.coe_funUnique_symm]
    exact eventually_of_mem (φ.open_source.mem_nhds hx) fun y hy ↦ h.eqOn_source hy
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

/-- **Changing the base coordinate of a Lefschetz chart.** If `φ` is a Lefschetz chart of `π` at
`p`, then for every biholomorphism `Ψ` of `ℂℙ¹` the composite `Ψ ∘ π` has a Lefschetz chart at
`p`, for the same `J`. Its affine chart is one at `Ψ (π p)`, and the new chart is `φ` followed by
the change of coordinates of `ℂ²` that turns the coordinate expression of `Ψ` into a translation
on the quadric (`LefschetzModel.exists_openPartialHomeomorph_apply_add_quadric`). -/
theorem exists_isLefschetzChart_comp (h : IsLefschetzChart J π p φ i)
    (Ψ : ℙ ℂ (Fin 2 → ℂ) ≃ₘ^ω⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ)) :
    ∃ φ' j, IsLefschetzChart J (Ψ ∘ π) p φ' j := by
  obtain ⟨j, hj⟩ := exists_mem_affineOpen (Ψ (π p))
  have hpi : π p ∈ affineOpen i := h.source_subset h.mem_source
  -- On `affineOpen i`, the coordinate expression of `Ψ` in the charts `i` and `j` reads `Ψ`.
  have hchart {y : ℙ ℂ (Fin 2 → ℂ)} (hy : y ∈ affineOpen i) :
      affineChart j (Ψ (ProjectiveLine.affineParam i (affineChart i y 0))) 0 =
        affineChart j (Ψ y) 0 := by
    rw [ProjectiveLine.affineParam_affineChart hy]
  have h0t : (0 : Fin 2 → ℂ) ∈ φ.target :=
    h.apply_eq_zero ▸ φ.toPartialEquiv.map_source h.mem_source
  have hU : φ.target ∩ (fun w ↦ Ψ (π (φ.symm w))) ⁻¹' affineOpen j ∈ 𝓝 (0 : Fin 2 → ℂ) := by
    have hp0 : φ.symm 0 = p := h.apply_eq_zero ▸ φ.toPartialEquiv.left_inv h.mem_source
    refine inter_mem (φ.open_target.mem_nhds h0t) (ContinuousAt.preimage_mem_nhds
      (Ψ.continuous.continuousAt.comp (h.contMDiffAt_comp_symm h0t).continuousAt) ?_)
    rw [hp0]
    exact (isOpen_affineOpen j).mem_nhds hj
  obtain ⟨e, h0e, he0, heU, hea, hesa, heq⟩ :=
    LefschetzModel.exists_openPartialHomeomorph_apply_add_quadric
      (contDiffAt_affineChart_comp_affineParam Ψ.contMDiff.contMDiffAt hpi hj).analyticAt
      (deriv_affineChart_diffeomorph_affineParam_ne_zero Ψ (by simp) hpi hj) hU
  -- The change of coordinates `e` of `ℂ²` is biholomorphic, hence a real partial diffeomorphism.
  let e' := PartialDiffeomorph.ofOpenPartialHomeomorph (n := ∞) e
    ((hea.contDiffOn e.open_source.uniqueDiffOn).restrict_scalars ℝ)
    ((hesa.contDiffOn e.open_target.uniqueDiffOn).restrict_scalars ℝ)
  have he' : ⇑e' = e := by simp [e']
  have he's : e'.source = e.source := by simp [e']
  refine ⟨φ.trans e', j, ⟨?_, ?_, fun x hx ↦ ?_, fun y hy ↦ ?_, fun x hx ↦ ?_⟩⟩
  · rw [PartialDiffeomorph.trans_source, he's]
    exact ⟨h.mem_source, by rw [mem_preimage, h.apply_eq_zero]; exact h0e⟩
  · rw [PartialDiffeomorph.coe_trans, he', Function.comp_apply, h.apply_eq_zero, he0]
  · rw [PartialDiffeomorph.trans_source, he's] at hx
    have hxx : φ.symm (φ x) = x := φ.toPartialEquiv.left_inv hx.1
    have hx' : Ψ (π (φ.symm (φ x))) ∈ affineOpen j := (heU hx.2).2
    rwa [hxx] at hx'
  · rw [PartialDiffeomorph.trans_source, he's] at hy
    have he : IsPseudoholomorphicAt
        (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (Fin 2 → ℂ))
        (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (Fin 2 → ℂ)) e (φ y) :=
      isPseudoholomorphicAt_ofComplexManifold_iff.2
        (hea _ hy.2).differentiableAt.mdifferentiableAt
    rw [PartialDiffeomorph.coe_trans, he']
    exact he.comp (h.isPseudoholomorphicAt y hy.1)
  · rw [PartialDiffeomorph.trans_source, he's] at hx
    rw [PartialDiffeomorph.coe_trans, he', Function.comp_apply, Function.comp_apply,
      Function.comp_apply, ← hchart (h.source_subset hx.1), ← hchart hpi,
      h.affineChart_apply x hx.1, heq _ hx.2]

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
  exact isConnected_compl_of_finite_of_one_lt_rank (E := Fin 1 → ℂ) (by simp [rank_pi])
    (h.finite_criticalPoints.image π)

/-- **Composing with a biholomorphism of the base.** If `π` is a Lefschetz fibration for `ω` and
`J`, so is `Ψ ∘ π` for every biholomorphism `Ψ` of `ℂℙ¹` (here `⊤` is the analytic order `ω`). -/
theorem comp_diffeomorph (h : IsLefschetzFibration ω J π)
    (Ψ : ℙ ℂ (Fin 2 → ℂ) ≃ₘ^⊤⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ)) :
    IsLefschetzFibration ω J (Ψ ∘ π) := by
  -- `Ψ` as a diffeomorphism of the underlying real manifold, with the same underlying map.
  have hΦ := Diffeomorph.coe_restrictScalars' ℝ Ψ
  have hcrit : criticalSet I 𝓘(ℝ, Fin 1 → ℂ) (Ψ ∘ π) = criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π := by
    rw [← hΦ, Diffeomorph.criticalSet_comp _ (by simp)]
  refine ⟨hΦ ▸ ((Ψ.restrictScalars' ℝ).contMDiff.of_le le_top).comp h.contMDiff, h.tames,
    hcrit ▸ Ψ.injective.comp_injOn h.injOn_criticalPoints, hcrit ▸ fun p hp ↦ ?_,
    fun x hx ↦ ?_⟩
  · obtain ⟨φ, i, hφ⟩ := h.exists_model p hp
    exact hφ.exists_isLefschetzChart_comp Ψ
  · rw [← hΦ] at hx ⊢
    rw [((Ψ.restrictScalars' ℝ).isLocalDiffeomorph _).ker_mfderiv_comp (by simp)
      ((h.contMDiff x).mdifferentiableAt (by simp))]
    exact h.isNondegenerate_ker x ((Diffeomorph.comp_isRegularPoint_iff _ (by simp)).1 hx)

/-- **Composing with a projective transformation.** If `π` is a Lefschetz fibration for `ω` and
`J`, so is `x ↦ g • π x` for every `g : GL (Fin 2) ℂ`, acting on `ℂℙ¹` through its linear action
on `ℂ²`. -/
theorem comp_projectivizationMap (h : IsLefschetzFibration ω J π) (g : GL (Fin 2) ℂ) :
    IsLefschetzFibration ω J (fun x ↦ g • π x) := by
  simpa [Function.comp_def] using h.comp_diffeomorph (Diffeomorph.constSmul _ _ g)

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
    simp only [Function.comp_apply, ν, hφ.eqOn_source hx]
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

namespace IsLefschetzFibration

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I (⊤ : ℕ∞) X] {ω : SmoothTwoForm I X} {J : SmoothAlmostComplexStructure I X}
  {π : X → ℙ ℂ (Fin 2 → ℂ)}

/-- A smooth map `π : X → ℂℙ¹` without critical points, pseudoholomorphic for `J` and some almost
complex structure `L` of `ℂℙ¹`, is a Lefschetz fibration for every two-form `ω` taming `J`. -/
theorem of_isRegularPoint {L : SmoothAlmostComplexStructure 𝓘(ℝ, Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))}
    (hπ : ContMDiff I 𝓘(ℝ, Fin 1 → ℂ) (⊤ : ℕ∞) π) (hω : ω.Tames J)
    (hJ : IsPseudoholomorphic J L π) (hreg : ∀ x, IsRegularPoint I 𝓘(ℝ, Fin 1 → ℂ) π x) :
    IsLefschetzFibration ω J π where
  contMDiff := hπ
  tames := hω
  injOn_criticalPoints := fun x hx ↦ absurd (hreg x) (mem_criticalSet_iff.1 hx)
  exists_model := fun x hx ↦ absurd (hreg x) (mem_criticalSet_iff.1 hx)
  isNondegenerate_ker := fun x _ ↦
    hω.nondegenerate_restrict_ker_mfderiv (isPseudoholomorphic_iff.1 hJ x)

end IsLefschetzFibration

/-! ### Lefschetz pencils -/

section Pencil

variable {X : Type*} [TopologicalSpace X] [T1Space X]

/-- The *closure of a fibre* of a map `π` defined on the complement of a finite set `B`: the
fibre of `π` over `t`, seen in `X`, together with `B`. -/
def fiberClosure {Y : Type*} (B : Finset X) (π : B.complOpens → Y) (t : Y) : Set X :=
  Subtype.val '' (π ⁻¹' {t}) ∪ B

variable {Y : Type*} {B : Finset X} {π : B.complOpens → Y} {t : Y}

theorem fiberClosure_def (B : Finset X) (π : B.complOpens → Y) (t : Y) :
    fiberClosure B π t = Subtype.val '' (π ⁻¹' {t}) ∪ B :=
  (rfl)

/-- A point lies in a fibre closure when it lies in `B` or is a point of the fibre. -/
theorem mem_fiberClosure_iff {x : X} :
    x ∈ fiberClosure B π t ↔ x ∈ B ∨ ∃ hx : x ∈ B.complOpens, π ⟨x, hx⟩ = t := by
  rw [fiberClosure_def, mem_union, mem_image, Finset.mem_coe, or_comm]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

/-- The closure of a fibre of a continuous map on the complement of a finite set is closed. -/
theorem isClosed_fiberClosure [TopologicalSpace Y] [T1Space Y] (hπ : Continuous π) (t : Y) :
    IsClosed (fiberClosure B π t) := by
  have h : (fiberClosure B π t)ᶜ = Subtype.val '' (π ⁻¹' {t}ᶜ) := by
    ext x
    simp only [mem_compl_iff, mem_fiberClosure_iff, not_or, not_exists, mem_image,
      mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hxB, h⟩
      exact ⟨⟨x, Finset.mem_complOpens.2 hxB⟩, h (Finset.mem_complOpens.2 hxB), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Finset.mem_complOpens.1 y.property, fun _ ↦ hy⟩
  rw [← isOpen_compl_iff, h]
  exact B.complOpens.isOpen.isOpenMap_subtypeVal _ (isOpen_compl_singleton.preimage hπ)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H X] [IsManifold I (⊤ : ℕ∞) X]

/-- A *Lefschetz pencil* on `X`, with base locus the finite set `B`, for the two-form `ω` and the
almost complex structure `J`: `ω` tames `J` on all of `X`, and `π` is a map from the complement of
`B` to `ℂℙ¹` which, for the restrictions of `ω` and `J`, is a Lefschetz fibration, and which near
each point `b` of `B` is the map `x ↦ [φ x]` for a `J`-holomorphic chart `φ` of `X` into `ℂ²`
centred at `b`. -/
structure IsLefschetzPencil (ω : SmoothTwoForm I X) (J : SmoothAlmostComplexStructure I X)
    (B : Finset X) (π : B.complOpens → ℙ ℂ (Fin 2 → ℂ)) : Prop where
  /-- `ω` tames `J` on all of `X`, the base points included. -/
  tames : ω.Tames J
  /-- Away from `B`, `π` is a Lefschetz fibration for the restrictions of `ω` and `J`. -/
  isLefschetzFibration : IsLefschetzFibration
    (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal ω) (J.restrictOpen B.complOpens) π
  /-- Near each base point `b`, `π` is `x ↦ [φ x]` for a `J`-holomorphic chart `φ` into `ℂ²`
  with `φ b = 0`. -/
  exists_chart : ∀ b ∈ B, ∃ φ : PartialDiffeomorph I 𝓘(ℝ, Fin 2 → ℂ) X (Fin 2 → ℂ) (⊤ : ℕ∞),
    b ∈ φ.source ∧ φ b = 0 ∧
    (∀ y ∈ φ.source, IsPseudoholomorphicAt J
      (SmoothAlmostComplexStructure.ofComplexManifold (Fin 2 → ℂ) (Fin 2 → ℂ)) φ y) ∧
    ∀ x : B.complOpens, (x : X) ∈ φ.source → ∀ hx : φ x ≠ 0, π x = mk ℂ (φ x) hx

end Pencil

/-! ### The product of a surface with `ℂℙ¹` -/

section Product

variable {E H S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace S] [ChartedSpace H S]
  [IsManifold I (⊤ : ℕ∞) S] {σ : SmoothTwoForm I S} {j : SmoothAlmostComplexStructure I S}

/-- The second projection `S × ℂℙ¹ → ℂℙ¹` is a Lefschetz fibration without critical points, for
the product of a two-form `σ` taming `j` with the Fubini–Study form, and the product of `j` with
the complex structure of `ℂℙ¹`. This holds in particular for an area form on a closed surface. -/
theorem isLefschetzFibration_snd (hσ : σ.Tames j) :
    IsLefschetzFibration (σ.prod (fubiniStudyForm 1))
      (j.prod (SmoothAlmostComplexStructure.ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))))
      (Prod.snd : S × ℙ ℂ (Fin 2 → ℂ) → ℙ ℂ (Fin 2 → ℂ)) :=
  .of_isRegularPoint contMDiff_snd
    (SmoothAlmostComplexStructure.tames_prod hσ compatible_fubiniStudyForm.tames)
    SmoothAlmostComplexStructure.isPseudoholomorphic_snd_prod isRegularPoint_snd

/-- The second projection `S × ℂℙ¹ → ℂℙ¹`, as in `isLefschetzFibration_snd`, is a Lefschetz pencil
with empty base locus. -/
theorem isLefschetzPencil_empty [T1Space S] (hσ : σ.Tames j) :
    IsLefschetzPencil (σ.prod (fubiniStudyForm 1))
      (j.prod (SmoothAlmostComplexStructure.ofComplexManifold (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))))
      ∅ (fun x ↦ (x : S × ℙ ℂ (Fin 2 → ℂ)).2) :=
  have h := SmoothAlmostComplexStructure.tames_prod hσ compatible_fubiniStudyForm.tames
  { tames := h
    isLefschetzFibration :=
      .of_isRegularPoint (contMDiff_snd.comp contMDiff_subtypeVal) (h.restrictOpen _)
        (SmoothAlmostComplexStructure.isPseudoholomorphic_snd_prod.comp
          (SmoothAlmostComplexStructure.isPseudoholomorphic_subtype_val _ _))
        fun x ↦ (isRegularPoint_snd _).comp (isRegularPoint_subtype_val x)
    exists_chart := fun _ hb ↦ absurd hb (Finset.notMem_empty _) }

end Product

end SymplecticGeometry

end
