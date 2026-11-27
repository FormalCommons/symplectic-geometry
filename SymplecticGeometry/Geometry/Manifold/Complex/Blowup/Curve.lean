/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Basic
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Lift
import TauCeti.Geometry.Symplectic.JHolomorphic.RiemannSurface
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# Lifts of holomorphic curves to the blowup

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

## Main definitions

* `SymplecticGeometry.Blowup.curveLift c u`: the lift of `u : S → M` to `Blowup c`.

## Main results

* `SymplecticGeometry.Blowup.blowdown_curveLift`: the lift lies over `u`.
* `SymplecticGeometry.Blowup.mdifferentiable_curveLift`: the lift of a nonconstant holomorphic
  curve is holomorphic.
* `SymplecticGeometry.Blowup.curveLift_unique`: it is the only continuous map over `u`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1, Lemma 7.1.3 and Exercise 7.1.2 (iii).
-/

public section

namespace SymplecticGeometry

open Set Filter Topology Function TopologicalSpace
open scoped Manifold ContDiff

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
  classical
  obtain ⟨hx, -⟩ := hF.self_of_nhds
  let g : S → U := fun y ↦ if h : G y ∈ U then ⟨G y, h⟩ else ⟨G x, hx⟩
  have hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r g x :=
    (TauCeti.ContMDiffAt.subtypeVal_comp_iff U g x).1 <|
      hG.congr_of_eventuallyEq (hF.mono fun y ⟨h, _⟩ ↦ by simp [g, h])
  exact (hι.contMDiffAt.comp x hg).congr_of_eventuallyEq
    (hF.mono fun y ⟨h, hy⟩ ↦ by simp [g, h, hy])

section Holomorphic

variable [IsManifold 𝓘(ℂ) ω S] [IsManifold 𝓘(ℂ, Fin (n + 1) → ℂ) ω M]

open TauCeti SmoothAlmostComplexStructure in
open scoped TauCeti.ComplexManifold in
/-- The fibres of a nonconstant holomorphic map from a connected Riemann surface are discrete:
this is Tau Ceti's `TauCeti.setOf_ne_mem_codiscrete_of_isPseudoholomorphic` for the almost
complex structures of the two complex manifolds. -/
private theorem setOf_ne_mem_codiscrete [ConnectedSpace S]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (p : M) :
    {y | u y ≠ p} ∈ codiscrete S :=
  setOf_ne_mem_codiscrete_of_isPseudoholomorphic (J := ofComplexManifold (Fin (n + 1) → ℂ) M)
    ((hu.contMDiff (n := 1)).restrictScalars' ℝ) (isPseudoholomorphic_ofComplexManifold_iff.2 hu)
    hne p

/-- Near a point `x` of the fibre over `p₀`, the points of `S` other than `x` are off the fibre,
and all are mapped by `u` into the source of `c`. -/
private theorem eventually_eq_or_ne [ConnectedSpace S]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    (h : u x = p₀) : ∀ᶠ y in 𝓝 x, (y = x ∨ u y ≠ p₀) ∧ u y ∈ c.source := by
  have hdisc := mem_codiscrete_iff_forall_mem_nhdsNE.1 (setOf_ne_mem_codiscrete hu hne p₀) x
  have hsrc : ∀ᶠ y in 𝓝 x, u y ∈ c.source :=
    hu.continuous.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds (h ▸ c.mem_source))
  filter_upwards [eventually_nhdsWithin_iff.1 hdisc, hsrc] with y hy hyc
  exact ⟨(em (y = x)).imp_right hy, hyc⟩

/-- The coordinate expression of a holomorphic `u` is analytic at the point of the chart. -/
private theorem analyticAt_coordCurve
    [hc : Fact (c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (n + 1) → ℂ) ω M)]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hx : u x ∈ c.source) :
    AnalyticAt ℂ (coordCurve c u x) (chartAt ℂ x x) := by
  have hφ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm (chartAt ℂ x x) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ))).contMDiffAt
      ((chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))
  rw [← (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at hx
  have hc' : ContMDiffAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω c
      (u ((chartAt ℂ x).symm (chartAt ℂ x x))) :=
    (contMDiffOn_of_mem_maximalAtlas hc.out).contMDiffAt (c.open_source.mem_nhds hx)
  have hcomp := hc'.comp (chartAt ℂ x x) (((hu.contMDiff (n := ω)) _).comp (chartAt ℂ x x) hφ)
  exact (contMDiffAt_iff_contDiffAt.1 hcomp).analyticAt

/-- The coordinate expression of `u` at a point of the fibre over `p₀` does not vanish
identically near the point of the chart, since the fibre is discrete. -/
private theorem analyticOrderAt_coordCurve_ne_top [ConnectedSpace S]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    (h : u x = p₀) : analyticOrderAt (coordCurve c u x) (chartAt ℂ x x) ≠ ⊤ := by
  intro htop
  set φ := chartAt ℂ x
  have hφ : Tendsto φ.symm (𝓝 (φ x)) (𝓝 x) := by
    have := φ.continuousAt_symm (mem_chart_target ℂ x)
    rwa [ContinuousAt, φ.left_inv (mem_chart_source ℂ x)] at this
  have hfalse : ∀ᶠ _ in 𝓝[≠] (φ x), False := by
    filter_upwards [nhdsWithin_le_nhds (analyticOrderAt_eq_top.1 htop),
      nhdsWithin_le_nhds (hφ.eventually (eventually_eq_or_ne (c := c) hu hne h)),
      nhdsWithin_le_nhds (φ.open_target.mem_nhds (mem_chart_target ℂ x)),
      self_mem_nhdsWithin] with t h0 ⟨hxt, hct⟩ ht hne'
    rcases hxt with hxt | hxt
    · exact hne' (show t = φ x by rw [← hxt, φ.right_inv ht])
    · exact c.apply_ne_zero hct hxt h0
  exact hfalse.exists.elim fun _ h ↦ h

/-- Near a point `x` of the fibre over `p₀`, the lift of `u` is `inr` of the model's lift of the
coordinate expression of `u` at `x`. -/
private theorem eventually_curveLift_eq_inr [ConnectedSpace S]
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
theorem eventually_lift_curveLift [ConnectedSpace S]
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
theorem contMDiff_curveLift [ConnectedSpace S] {r : ℕ∞ω}
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r (curveLift c u) := by
  intro x
  by_cases h : u x = p₀
  · have hG : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) r
        (fun y ↦ BlowupModel.curveLift (coordCurve c u x) (chartAt ℂ x y)) x :=
      (BlowupModel.contMDiffAt_curveLift (analyticAt_coordCurve hu (h ▸ c.mem_source))
        (analyticOrderAt_coordCurve_ne_top hu hne h)).comp x
        ((contMDiffOn_chart (I := 𝓘(ℂ))).contMDiffAt
          ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)))
    exact contMDiffAt_of_eventually_eq_comp (((isLocalDiffeomorph_inr c).contMDiff).of_le le_top)
      hG (eventually_curveLift_eq_inr hu hne h)
  · have hev : ∀ᶠ y in 𝓝 x, u y ≠ p₀ := hu.continuous.continuousAt.eventually_ne h
    exact contMDiffAt_of_eventually_eq_comp (((isLocalDiffeomorph_inl c).contMDiff).of_le le_top)
      ((hu.contMDiff (n := r)) x)
      (hev.mono fun y hy ↦ ⟨(mem_puncturedOpens c).2 hy, curveLift_of_ne hy⟩)

/-- **Lifts of holomorphic curves are holomorphic.** The lift of a nonconstant holomorphic curve
on a connected Riemann surface to the blowup is holomorphic. -/
theorem mdifferentiable_curveLift [ConnectedSpace S]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) (curveLift c u) :=
  (contMDiff_curveLift (r := 1) hu hne).mdifferentiable one_ne_zero

/-- **Uniqueness of lifts of holomorphic curves.** A continuous map `v : S → Blowup c` over a
nonconstant holomorphic curve `u` on a connected Riemann surface is the lift of `u`. -/
theorem curveLift_unique [ConnectedSpace S]
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂)
    {v : S → Blowup c} (hv : Continuous v) (hvu : blowdown c ∘ v = u) : v = curveLift c u := by
  have : PerfectSpace S := ChartedSpace.perfectSpace (H := ℂ)
  refine funext fun x ↦ isOpen_univ.eqOn_of_eventuallyEq_codiscreteWithin hv.continuousOn
    (contMDiff_curveLift (r := 0) hu hne).continuous.continuousOn ?_ (mem_univ x)
  refine eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.2 fun z _ ↦ ?_
  filter_upwards [mem_codiscrete_iff_forall_mem_nhdsNE.1 (setOf_ne_mem_codiscrete hu hne p₀) z]
    with y hy _
  have hvy : blowdown c (v y) = u y := congrFun hvu y
  refine injOn_blowdown c ?_ ?_ (by rw [hvy, blowdown_curveLift])
  · rwa [mem_compl_iff, ← blowdown_eq_center_iff, hvy]
  · rwa [mem_compl_iff, curveLift_mem_exceptionalDivisor_iff]

end Holomorphic

end Blowup

end SymplecticGeometry

end
