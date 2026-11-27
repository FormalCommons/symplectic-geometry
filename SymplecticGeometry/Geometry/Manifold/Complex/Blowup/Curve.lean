/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Chart.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Lift
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Uniqueness
import TauCeti.Geometry.Symplectic.JHolomorphic.RiemannSurface
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Complex.Chart
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# Lifts of holomorphic curves to the blowup, and the complex blowup at a point

Let `S` be a connected Riemann surface, `M` a Hausdorff complex manifold of dimension `n + 1`,
`c` a holomorphic chart of `M` centred at `p₀` (a `SymplecticGeometry.BlowupChart M p₀` in the
complex maximal atlas), and `u : S → M` a nonconstant holomorphic map. Then `u` lifts to the
blowup: there is a unique continuous map `ũ : S → Blowup c` with `π ∘ ũ = u`, where `π` is the
blowdown, and this lift is holomorphic. This is McDuff–Salamon, Lemma 7.1.3 (in the part about
curves) and Exercise 7.1.2 (iii).

The lift `SymplecticGeometry.Blowup.curveLift c u` is `inl ∘ u` off the fibre `u ⁻¹' {p₀}`. At a
point `x` of that fibre it is the model's `SymplecticGeometry.BlowupModel.curveLift` of the
coordinate expression `t ↦ c (u (φ.symm t))` of `u`, for `φ` the preferred chart of `S` at `x`,
taken at `φ x`. Since `u` is not constant, Tau Ceti's
`TauCeti.setOf_ne_mem_codiscrete_of_isPseudoholomorphic` shows that the fibre is discrete. So
near `x` the lift is the model's lift read through `φ` (`eventually_lift_curveLift`), which is
holomorphic since the coordinate expression of `u` is analytic and does not vanish identically
(`BlowupModel.contMDiffAt_curveLift`). Uniqueness holds since two continuous lifts agree off the
fibre, where the blowdown is injective, and the complement of a discrete set is dense in a
Riemann surface.

The last section collects, in one theorem, what the library proves of the complex blowup at a
point: the holomorphy of the blowdown and its biholomorphism off the exceptional divisor
(`Blowup/Basic.lean`), the lifted charts (`Blowup/Chart/Basic.lean`), the holomorphic embedding of
the divisor, the lifts of curves of this file, and the uniqueness of the complex structure
(`Blowup/Uniqueness.lean`).

## Main definitions

* `SymplecticGeometry.Blowup.curveLift c u`: the lift of `u : S → M` to `Blowup c`.

## Main results

* `SymplecticGeometry.Blowup.blowdown_curveLift`: the lift lies over `u`.
* `SymplecticGeometry.Blowup.mdifferentiable_curveLift`: the lift of a nonconstant holomorphic
  curve is holomorphic.
* `SymplecticGeometry.Blowup.curveLift_unique`: it is the only continuous map over `u`.
* `SymplecticGeometry.Blowup.contMDiff_blowdown_and_properties`: the properties of
  the complex blowup at a point, collected in one statement: the blowdown, the lifted charts, the
  exceptional divisor, the lifts of curves, and the uniqueness of the complex structure.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1, Lemma 7.1.1, Exercise 7.1.2 and Lemma 7.1.3.
-/

public section

namespace SymplecticGeometry

open Set Filter Topology Function TopologicalSpace
open scoped Manifold ContDiff

universe uS

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin (n + 1) → ℂ) M] {p₀ : M}
  (c : BlowupChart (n := n) M p₀)
  {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]

namespace Blowup

open GluedAlong (inl inr)

/-- The coordinate expression `t ↦ c (u (φ.symm t))` of `u` in the chart `c` of `M` and the
preferred chart `φ` of `S` at `x`. -/
private noncomputable def coordCurve (u : S → M) (x : S) : ℂ → Fin (n + 1) → ℂ :=
  fun t ↦ c (u ((chartAt ℂ x).symm t))

private theorem coordCurve_def (u : S → M) (x : S) :
    coordCurve c u x = fun t ↦ c (u ((chartAt ℂ x).symm t)) := (rfl)

/-- The model's lift of the coordinate expression of `u` in the preferred chart at `x`, taken at
a point `y` of the source of that chart with `u y` in the source of `c`, lies over the target
of `c`. -/
theorem modelCurveLift_mem_modelOpens {u : S → M} {x y : S} (hy : y ∈ (chartAt ℂ x).source)
    (hyc : u y ∈ c.source) :
    BlowupModel.curveLift (fun t ↦ c (u ((chartAt ℂ x).symm t))) (chartAt ℂ x y) ∈
      modelOpens c := by
  rw [mem_modelOpens, BlowupModel.blowdown_curveLift, (chartAt ℂ x).left_inv hy]
  exact c.map_source hyc

open scoped Classical in
/-- The lift of a curve `u : S → M` to the blowup `Blowup c`. At `x` with `u x ≠ p₀` it is the
point `inl (u x)` over `u x`. At `x` with `u x = p₀` it is the point of the model's
`BlowupModel.curveLift` of `t ↦ c (u (φ.symm t))` at `φ x`, for `φ` the preferred chart of `S` at
`x`: the point of the exceptional divisor on the line of the first nonvanishing derivative of
`c ∘ u` at `x`. For a nonconstant holomorphic `u` on a connected Riemann surface this is the unique
continuous lift of `u` (`curveLift_unique`), and it is holomorphic
(`mdifferentiable_curveLift`). -/
noncomputable def curveLift (u : S → M) (x : S) : Blowup c :=
  if h : u x = p₀ then
    inr (gluingHomeomorph c) ⟨BlowupModel.curveLift (fun t ↦ c (u ((chartAt ℂ x).symm t)))
      (chartAt ℂ x x),
      modelCurveLift_mem_modelOpens c (mem_chart_source ℂ x) (h ▸ c.mem_source)⟩
  else inl (gluingHomeomorph c) ⟨u x, (mem_puncturedOpens c).2 h⟩

variable {c} {u : S → M} {x : S}

/-- At a point of the fibre over `p₀`, the lift is the model's lift of the coordinate expression
of `u` in the preferred chart at that point. -/
theorem curveLift_of_eq (h : u x = p₀) :
    curveLift c u x = inr (gluingHomeomorph c)
      ⟨BlowupModel.curveLift (fun t ↦ c (u ((chartAt ℂ x).symm t))) (chartAt ℂ x x),
        modelCurveLift_mem_modelOpens c (mem_chart_source ℂ x) (h ▸ c.mem_source)⟩ :=
  dite_eq_left h

/-- Off the fibre over `p₀`, the lift is `inl ∘ u`. -/
theorem curveLift_of_ne (h : u x ≠ p₀) :
    curveLift c u x = inl (gluingHomeomorph c) ⟨u x, (mem_puncturedOpens c).2 h⟩ :=
  dite_eq_right h

/-- At a point of the fibre over `p₀`, the lift read through `Blowup.lift c` is the model's lift of
the coordinate expression of `u` in the preferred chart at that point. -/
theorem lift_curveLift_of_eq (h : u x = p₀) :
    lift c (curveLift c u x) =
      BlowupModel.curveLift (fun t ↦ c (u ((chartAt ℂ x).symm t))) (chartAt ℂ x x) := by
  rw [curveLift_of_eq h, lift_inr]

variable (c u x) in
/-- The lift of `u` lies over `u`. -/
@[simp]
theorem blowdown_curveLift : blowdown c (curveLift c u x) = u x := by
  by_cases h : u x = p₀
  · rw [curveLift_of_eq h, blowdown_inr, BlowupModel.blowdown_curveLift,
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x), h, c.map_center]
    exact c.symm_zero
  · rw [curveLift_of_ne h, blowdown_inl]

/-- The lift of `u` meets the exceptional divisor exactly over `p₀`. -/
@[simp]
theorem curveLift_mem_exceptionalDivisor_iff :
    curveLift c u x ∈ exceptionalDivisor c ↔ u x = p₀ := by
  rw [← blowdown_eq_center_iff, blowdown_curveLift]

/-! ### Holomorphy and uniqueness of the lift -/

/-- Let `ι` be a `C^r` map to `Blowup c` from an open subset `U` of a manifold `N`, and `G : S → N`
a map that is `C^r` at `x`. A map `F : S → Blowup c` such that, near `x`, `G y ∈ U` and
`F y = ι ⟨G y, _⟩` is `C^r` at `x`. -/
private theorem contMDiffAt_of_eventually_eq_comp {r : ℕ∞ω} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (Fin (n + 1) → ℂ) N] {U : Opens N} {ι : U → Blowup c}
    (hι : ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r ι) {G : S → N}
    (hG : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r G x) {F : S → Blowup c}
    (hF : ∀ᶠ y in 𝓝 x, ∃ h : G y ∈ U, F y = ι ⟨G y, h⟩) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r F x := by
  obtain ⟨g, hg, hgG⟩ := hG.exists_subtypeVal_comp_eventuallyEq hF.self_of_nhds.1
  refine (hι.contMDiffAt.comp x hg).congr_of_eventuallyEq ?_
  filter_upwards [hF, hgG] with y ⟨h, hy⟩ hgy
  rw [hy, Function.comp_apply]
  exact congrArg ι (Subtype.ext (by simpa using hgy.symm))

section Holomorphic

variable [IsManifold 𝓘(ℂ) ω S] [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]

open TauCeti SmoothAlmostComplexStructure in
open scoped TauCeti.ComplexManifold in
/-- The fibres of a nonconstant holomorphic map from a connected Riemann surface are discrete:
this is Tau Ceti's `TauCeti.setOf_ne_mem_codiscrete_of_isPseudoholomorphic` for the almost
complex structures of the two complex manifolds. -/
private theorem setOfPred_ne_mem_codiscrete [PreconnectedSpace S]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (p : M) :
    {y | u y ≠ p} ∈ codiscrete S :=
  setOf_ne_mem_codiscrete_of_isPseudoholomorphic (J := ofComplexManifold (Fin (n + 1) → ℂ) M)
    ((hu.contMDiff (n := 1)).restrictScalars' ℝ) (isPseudoholomorphic_ofComplexManifold_iff.2 hu)
    hne p

/-- Near a point `x` of the fibre over `p₀`, the points of `S` other than `x` are off the fibre,
and all are mapped by `u` into the source of `c`. -/
private theorem eventually_eq_or_ne [PreconnectedSpace S]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    (h : u x = p₀) : ∀ᶠ y in 𝓝 x, (y = x ∨ u y ≠ p₀) ∧ u y ∈ c.source := by
  have hdisc := mem_codiscrete_iff_forall_mem_nhdsNE.1 (setOfPred_ne_mem_codiscrete hu hne p₀) x
  have hsrc : ∀ᶠ y in 𝓝 x, u y ∈ c.source :=
    hu.continuous.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds (h ▸ c.mem_source))
  filter_upwards [eventually_nhdsWithin_iff.1 hdisc, hsrc] with y hy hyc
  exact ⟨(em (y = x)).imp_right hy, hyc⟩

omit [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M] in
/-- The coordinate expression of a holomorphic `u` is analytic at the point of the chart. -/
private theorem analyticAt_coordCurve
    [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hx : u x ∈ c.source) :
    AnalyticAt ℂ (coordCurve c u x) (chartAt ℂ x x) := by
  have hsrc : ∀ᶠ y in 𝓝 x, u y ∈ c.source :=
    hu.continuous.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx)
  rw [coordCurve_def]
  refine TauCeti.analyticAt_comp_chartAt_symm (g := fun y ↦ c (u y)) (hsrc.mono fun y hy ↦ ?_)
  exact ((contMDiffAt_of_mem_maximalAtlas hc.out hy).mdifferentiableAt (by simp)).comp y (hu y)

/-- The coordinate expression of `u` at a point of the fibre over `p₀` does not vanish
identically near the point of the chart, since the fibre is discrete. -/
private theorem analyticOrderAt_coordCurve_ne_top [PreconnectedSpace S]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    (h : u x = p₀) : analyticOrderAt (coordCurve c u x) (chartAt ℂ x x) ≠ ⊤ := by
  intro htop
  have hfalse : ∀ᶠ _ in 𝓝[≠] (chartAt ℂ x x), False := by
    filter_upwards [nhdsWithin_le_nhds (analyticOrderAt_eq_top.1 htop),
      TauCeti.tendsto_chartAt_symm_nhdsNE (H := ℂ) x <|
        inter_mem (mem_codiscrete_iff_forall_mem_nhdsNE.1 (setOfPred_ne_mem_codiscrete hu hne p₀) x)
          (nhdsWithin_le_nhds (hu.continuous.continuousAt.preimage_mem_nhds
            (c.open_source.mem_nhds (h ▸ c.mem_source))))] with t h0 ⟨hne', hct⟩
    exact c.apply_ne_zero hct hne' h0
  exact hfalse.exists.elim fun _ h ↦ h

/-- Near a point `x` of the fibre over `p₀`, the lift of `u` is `inr` of the model's lift of the
coordinate expression of `u` at `x`. -/
private theorem eventually_curveLift_eq_inr [PreconnectedSpace S]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    (h : u x = p₀) :
    ∀ᶠ y in 𝓝 x, ∃ hy : BlowupModel.curveLift (coordCurve c u x) (chartAt ℂ x y) ∈ modelOpens c,
      curveLift c u y = inr (gluingHomeomorph c) ⟨_, hy⟩ := by
  filter_upwards [eventually_eq_or_ne (c := c) hu hne h,
    (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y ⟨hy, hyc⟩ hys
  refine ⟨modelCurveLift_mem_modelOpens c hys hyc, ?_⟩
  rcases hy with rfl | hy
  · exact curveLift_of_eq h
  · rw [curveLift_of_ne hy, inl_eq_inr_iff]
    refine ⟨hyc, ?_⟩
    rw [BlowupModel.blowdown_curveLift, coordCurve, (chartAt ℂ x).left_inv hys]

/-- Near a point `x` of the fibre over `p₀`, the lift of a nonconstant holomorphic curve `u`, read
through `Blowup.lift c`, is the model's lift of the coordinate expression `t ↦ c (u (φ.symm t))`
of `u` in the preferred chart `φ` of `S` at `x`. -/
theorem eventually_lift_curveLift [PreconnectedSpace S]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    (h : u x = p₀) :
    ∀ᶠ y in 𝓝 x, lift c (curveLift c u y) =
      BlowupModel.curveLift (fun t ↦ c (u ((chartAt ℂ x).symm t))) (chartAt ℂ x y) :=
  (eventually_curveLift_eq_inr (c := c) hu hne h).mono fun _ hy ↦ by
    obtain ⟨_, hy⟩ := hy
    rw [hy, lift_inr, Subtype.coe_mk, coordCurve_def]

variable [T2Space M]
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

/-- The lift of a nonconstant holomorphic curve on a connected Riemann surface is `C^r` for every
`r`, analytic included. -/
theorem contMDiff_curveLift [PreconnectedSpace S] {r : ℕ∞ω}
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (curveLift c u) := by
  intro x
  by_cases h : u x = p₀
  · have hG : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r
        (fun y ↦ BlowupModel.curveLift (coordCurve c u x) (chartAt ℂ x y)) x :=
      (BlowupModel.contMDiffAt_curveLift (analyticAt_coordCurve hu (h ▸ c.mem_source))
        (analyticOrderAt_coordCurve_ne_top hu hne h)).comp x
        (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
          (mem_chart_source ℂ x))
    exact contMDiffAt_of_eventually_eq_comp (((isLocalDiffeomorph_inr c).contMDiff).of_le le_top)
      hG (eventually_curveLift_eq_inr hu hne h)
  · have hev : ∀ᶠ y in 𝓝 x, u y ≠ p₀ := hu.continuous.continuousAt.eventually_ne h
    exact contMDiffAt_of_eventually_eq_comp (((isLocalDiffeomorph_inl c).contMDiff).of_le le_top)
      ((hu.contMDiff (n := r)) x)
      (hev.mono fun y hy ↦ ⟨(mem_puncturedOpens c).2 hy, curveLift_of_ne hy⟩)

/-- **Lifts of holomorphic curves are holomorphic.** The lift of a nonconstant holomorphic curve
on a connected Riemann surface to the blowup is holomorphic. -/
theorem mdifferentiable_curveLift [PreconnectedSpace S]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (curveLift c u) :=
  (contMDiff_curveLift (r := 1) hu hne).mdifferentiable one_ne_zero

/-- **Uniqueness of lifts of holomorphic curves.** A continuous map `v : S → Blowup c` over a
nonconstant holomorphic curve `u` on a connected Riemann surface is the lift of `u`. -/
theorem curveLift_unique [PreconnectedSpace S]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    {v : S → Blowup c} (hv : Continuous v) (hvu : blowdown c ∘ v = u) : v = curveLift c u := by
  have : PerfectSpace S := ChartedSpace.perfectSpace (H := ℂ)
  refine funext fun x ↦ isOpen_univ.eqOn_of_eventuallyEq_codiscreteWithin hv.continuousOn
    (contMDiff_curveLift (r := 0) hu hne).continuous.continuousOn ?_ (mem_univ x)
  refine eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.2 fun z _ ↦ ?_
  filter_upwards [mem_codiscrete_iff_forall_mem_nhdsNE.1 (setOfPred_ne_mem_codiscrete hu hne p₀) z]
    with y hy _
  have hvy : blowdown c (v y) = u y := congrFun hvu y
  refine injOn_blowdown c ?_ ?_ (by rw [hvy, blowdown_curveLift])
  · rwa [mem_compl_iff, ← blowdown_eq_center_iff, hvy]
  · rwa [mem_compl_iff, curveLift_mem_exceptionalDivisor_iff]

end Holomorphic

/-! ### The complex blowup at a point -/

section Milestone

open Projectivization BlowupModel
open scoped LinearAlgebra.Projectivization

variable (c) [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M] [T2Space M]
  [Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]

/-- **The complex blowup at a point.** Take a holomorphic chart `c` with `c p₀ = 0` of a Hausdorff
complex manifold `M` of dimension `n + 1`. The blowup `Blowup c` of `M` at `p₀`, with its complex
structure, has the following properties.

* The blowdown `Blowup c → M` is holomorphic.
* It restricts to a biholomorphism from the complement of the exceptional divisor onto
  `M \ {p₀}` (this is `blowdownDiffeomorph c`).
* For every holomorphic chart `φ` of `M` with `φ p₀ = 0`, the lifted chart `liftChart c φ` is a
  biholomorphism from `blowdown c ⁻¹' φ.source` onto the part `BlowupModel.blowdown ⁻¹' φ.target`
  of the model blowup over the target of `φ`, and it is a chart of the complex structure of the
  blowup: followed by any chart `blowupModelChart i` of the model, it is in the maximal atlas.
  It lies over `φ`: the blowdown of `liftChart c φ z` is `φ (blowdown c z)`, which determines it
  off the exceptional divisor. Through `directionEquiv c`, it sends the point of the divisor over
  the line of a tangent vector `v ≠ 0` at `p₀` to the point of the zero section over the line of
  `mfderiv φ p₀ v`.
* The map `ofDirection c` from `ℙ ℂ ℂⁿ⁺¹` to the blowup is a holomorphic embedding, with image the
  exceptional divisor (this is `divisorEmbedding c`).
* Every nonconstant holomorphic curve `u` on a connected Riemann surface has a holomorphic lift
  `v` with `blowdown c ∘ v = u`, and every continuous map over `u` is `v` (this is
  `curveLift c u`).
* The complex structure is unique: a bijection `e : X ≃ Blowup c` from a space charted on `ℂⁿ⁺¹`
  such that `e.symm` after each of the two pieces of the gluing, the punctured manifold and the
  part of the model over the target of `c`, is a local biholomorphism, is a biholomorphism (this
  is `diffeomorphOfEquiv c`).

Milestone: *Complex blowup at a point*. -/
theorem contMDiff_blowdown_and_properties :
    ContMDiff 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (blowdown c) ∧
    (∃ e : offDivisorOpens c ≃ₘ^ω⟮𝓘(ℂ, Fin (n + 1) → ℂ), 𝓘(ℂ, Fin (n + 1) → ℂ)⟯
        puncturedOpens c, ∀ z, (e z : M) = blowdown c z) ∧
    (∀ (φ : BlowupChart (n := n) M p₀)
        [Fact (φ.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)],
      (∃ Φ : PartialDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (Blowup c)
          (BlowupModel n) ω,
        ⇑Φ = liftChart c φ ∧ Φ.source = blowdown c ⁻¹' φ.source ∧
        Φ.target = BlowupModel.blowdown ⁻¹' φ.target ∧
        ∀ i, Φ.toOpenPartialHomeomorph.trans (blowupModelChart i) ∈
          IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω (Blowup c)) ∧
      (∀ z ∈ blowdown c ⁻¹' φ.source, (liftChart c φ z).blowdown = φ (blowdown c z)) ∧
      ∀ (v : TangentSpace 𝓘(ℂ, Fin (n + 1) → ℂ) p₀) (hv : v ≠ 0),
        liftChart c φ (ofDirection c (directionEquiv c (mk ℂ v hv))) =
          zeroSection (mk ℂ (V := Fin (n + 1) → ℂ)
            (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) φ p₀ v)
            (by simpa using (φ.mfderivCenterEquiv.injective.ne_iff' (map_zero _)).2 hv))) ∧
    (∃ ι : TauCeti.SmoothEmbedding 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
        (ℙ ℂ (Fin (n + 1) → ℂ)) (Blowup c),
      ⇑ι = ofDirection c ∧ range ι = exceptionalDivisor c) ∧
    (∀ (S : Type uS) [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
        [PreconnectedSpace S] (u : S → M), MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u →
        (∃ x₁ x₂, u x₁ ≠ u x₂) →
      ∃ v : S → Blowup c, MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) v ∧ blowdown c ∘ v = u ∧
        ∀ w : S → Blowup c, Continuous w → blowdown c ∘ w = u → w = v) ∧
    (∀ (X : Type) [TopologicalSpace X] [ChartedSpace (Fin (n + 1) → ℂ) X] (e : X ≃ Blowup c),
      IsLocalDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
          (e.symm ∘ inl (gluingHomeomorph c)) →
      IsLocalDiffeomorph 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
          (e.symm ∘ inr (gluingHomeomorph c)) →
      ∃ d : X ≃ₘ^ω⟮𝓘(ℂ, Fin (n + 1) → ℂ), 𝓘(ℂ, Fin (n + 1) → ℂ)⟯ Blowup c, ⇑d = e) :=
  ⟨contMDiff_blowdown c, ⟨blowdownDiffeomorph c, coe_blowdownDiffeomorph_apply c⟩,
    fun φ _ ↦ ⟨⟨liftChartPartialDiffeomorph c φ, coe_liftChartPartialDiffeomorph c φ,
      liftChartPartialDiffeomorph_source c φ, liftChartPartialDiffeomorph_target c φ,
      liftChart_mem_maximalAtlas c φ⟩, fun _ hz ↦ blowdown_liftChart c φ hz,
      liftChart_ofDirection_directionEquiv_mk c φ⟩,
    ⟨divisorEmbedding c, coe_divisorEmbedding c, range_divisorEmbedding c⟩,
    fun _ _ _ _ _ u hu hne ↦ ⟨curveLift c u, mdifferentiable_curveLift hu hne,
      funext (blowdown_curveLift c u), fun _ hw hwu ↦ curveLift_unique hu hne hw hwu⟩,
    fun _ _ _ e hl hr ↦ ⟨diffeomorphOfEquiv c e hl hr, coe_diffeomorphOfEquiv c e hl hr⟩⟩

end Milestone

end Blowup

end SymplecticGeometry

end
