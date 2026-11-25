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
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Submanifold
public import SymplecticGeometry.Topology.Sets.Opens.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Integrable
public import SymplecticGeometry.Geometry.Manifold.Projectivization.FubiniStudy.Kahler
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Prod
public import SymplecticGeometry.Geometry.Manifold.RegularValue.CriticalSet
public import SymplecticGeometry.Geometry.Symplectic.Lefschetz.Model

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
* `SymplecticGeometry.IsLefschetzFibration.of_isRegularPoint`: a smooth pseudoholomorphic map
  without critical points is a Lefschetz fibration for every two-form taming the almost complex
  structure.
* `SymplecticGeometry.isClosed_fiberClosure`: fibre closures of a continuous map are closed.
* `SymplecticGeometry.isLefschetzFibration_snd` and `SymplecticGeometry.isLefschetzPencil_empty`:
  the product example.

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
