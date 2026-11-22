/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Complex.Isothermal
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
public import TauCeti.Geometry.Symplectic.Manifold.Nijenhuis
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
import TauCeti.Geometry.Symplectic.Finrank
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Integrable almost complex structures

A smooth almost complex structure `J` on a manifold `M` modelled on `E` is *integrable*
(`TauCeti.SmoothAlmostComplexStructure.IsIntegrable`) when `M` is covered by smooth charts
`ψ : M → E` in which `J` is constant: for each chart there is a linear complex structure `J₀` of
`E` with `dψ ∘ J = J₀ ∘ dψ` on the source of `ψ`, or equivalently with Tau Ceti's pushforward
`chartPushforward` of `J` along `ψ` equal to `J₀` on its target. The charts are Mathlib's
`PartialDiffeomorph`s onto open subsets of `E`, so on a manifold with boundary they only reach
interior points. Each chart has its own `J₀`. With a single `J₀` for all charts the empty manifold
modelled on a space of odd dimension would not be integrable, although its Nijenhuis tensor
vanishes.

The structure of a complex manifold is integrable, through its holomorphic charts. Integrability
is preserved by pulling back along diffeomorphisms, and it forces the Nijenhuis tensor to vanish:
the pullbacks along a chart of the constant vector fields of `E` span every tangent space, `J`
carries them to one another, and their Lie brackets vanish, as in Tau Ceti's
`SmoothAlmostComplexStructure.nijenhuis_const`, by Mathlib's `VectorField.mpullback_mlieBracket`.
On a real surface, a structure is integrable exactly when isothermal charts of the smooth maximal
atlas cover the surface; in particular integrable structures have isothermal charts in the sense of
Tau Ceti's `SmoothAlmostComplexStructure.HasIsothermalCharts`.

A linear complex structure `J₀` of the model with which all tangent coordinate changes commute
defines a constant almost complex structure, `ofTangentCoordChange`; its construction follows Tau
Ceti's `SmoothAlmostComplexStructure.ofTangentCoordChangeISMul`, the case of multiplication by
`i`. On a manifold modelled on the vector space itself it is integrable.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.IsIntegrable`: integrability of a smooth almost complex
  structure; `isIntegrable_iff_mfderiv` states it through derivatives of charts, and
  `isIntegrable_of_forall_exists_isLocalDiffeomorphAt` accepts, in place of a chart, any map
  that is a local diffeomorphism at the point.
* `TauCeti.SmoothAlmostComplexStructure.isIntegrable_ofComplexManifold`: the almost complex
  structure of a complex manifold is integrable.
* `TauCeti.SmoothAlmostComplexStructure.ofTangentCoordChange` and
  `TauCeti.SmoothAlmostComplexStructure.isIntegrable_ofTangentCoordChange`: the constant structure
  of a complex structure of the model that commutes with the changes of coordinates, and its
  integrability.
* `TauCeti.SmoothAlmostComplexStructure.IsIntegrable.pullback`: integrability is invariant under
  pullback along a diffeomorphism.
* `TauCeti.SmoothAlmostComplexStructure.IsIntegrable.nijenhuis_eq_zero`: the Nijenhuis tensor of
  an integrable structure vanishes.
* `TauCeti.SmoothAlmostComplexStructure.isIntegrable_iff_forall_exists_isIsothermalChart` and
  `TauCeti.SmoothAlmostComplexStructure.IsIntegrable.hasIsothermalCharts`: on a surface,
  integrability is the existence of smooth isothermal charts around every point, and integrable
  structures have isothermal charts.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 4.2.
-/

public section

open Set Filter VectorField
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace SmoothAlmostComplexStructure

section Chart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (J : SmoothAlmostComplexStructure I M)

/-- A smooth almost complex structure `J` on `M` is *integrable* when every point of `M` lies in
the source of a smooth chart `ψ : M → E`, a partial diffeomorphism onto an open subset of the
model vector space, in which `J` is constant: there is a linear complex structure `J₀` of `E`
such that the pushforward `dψ ∘ J ∘ dψ⁻¹` of `J` is `J₀` at every point of the target of
`ψ`. -/
def IsIntegrable : Prop :=
  ∀ x : M, ∃ (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (J₀ : AlmostComplexStructure E),
    x ∈ ψ.source ∧
      ∀ p ∈ ψ.target, ∀ w : E, J.chartPushforward ψ.toOpenPartialHomeomorph p w = J₀ w

/-- The defining property of an integrable almost complex structure. -/
theorem isIntegrable_def : J.IsIntegrable ↔
    ∀ x : M, ∃ (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (J₀ : AlmostComplexStructure E),
      x ∈ ψ.source ∧
        ∀ p ∈ ψ.target, ∀ w : E, J.chartPushforward ψ.toOpenPartialHomeomorph p w = J₀ w :=
  Iff.rfl

/-- `J` is integrable exactly when every point of `M` lies in the source of a smooth chart whose
derivative carries `J` to a fixed linear complex structure of `E` at every point of its
source. -/
theorem isIntegrable_iff_mfderiv : J.IsIntegrable ↔
    ∀ x : M, ∃ (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (J₀ : AlmostComplexStructure E),
      x ∈ ψ.source ∧ ∀ y ∈ ψ.source, ∀ v : TangentSpace I y,
        mfderiv I 𝓘(ℝ, E) ψ y (J y v) = J₀ (mfderiv I 𝓘(ℝ, E) ψ y v) := by
  simp only [isIntegrable_def, forall_chartPushforward_apply_eq_iff]

/-- `J` is integrable when around every point `x` there are a neighbourhood `s` of `x` and a map
`φ : M → E` that is a smooth local diffeomorphism at `x` and whose derivative carries `J` to a
fixed linear complex structure of `E` at every point of `s`. -/
theorem isIntegrable_of_forall_exists_isLocalDiffeomorphAt
    (h : ∀ x : M, ∃ (φ : M → E) (s : Set M) (J₀ : AlmostComplexStructure E),
      s ∈ nhds x ∧ IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ φ x ∧
        ∀ y ∈ s, ∀ v : TangentSpace I y,
          mfderiv I 𝓘(ℝ, E) φ y (J y v) = J₀ (mfderiv I 𝓘(ℝ, E) φ y v)) :
    J.IsIntegrable := by
  rw [isIntegrable_iff_mfderiv]
  intro x
  obtain ⟨φ, s, J₀, hs, hφ, hJ⟩ := h x
  -- A partial diffeomorphism that agrees with `φ` on its source, inside `s`, is the chart.
  obtain ⟨Φ, hxΦ, hΦs, hφΦ⟩ := hφ.exists_partialDiffeomorph_source_subset hs
  refine ⟨Φ, J₀, hxΦ, fun y hy v ↦ ?_⟩
  have hd : mfderiv I 𝓘(ℝ, E) Φ y = mfderiv I 𝓘(ℝ, E) φ y :=
    Filter.EventuallyEq.mfderiv_eq <|
      Filter.eventually_of_mem (Φ.open_source.mem_nhds hy) fun z hz ↦ (hφΦ hz).symm
  rw [hd]
  exact hJ y (hΦs hy) v

/-- **The Nijenhuis tensor of an integrable structure vanishes.** -/
theorem IsIntegrable.nijenhuis_eq_zero [FiniteDimensional ℝ E]
    {J : SmoothAlmostComplexStructure I M} (hJ : J.IsIntegrable) : J.nijenhuis = 0 := by
  rw [isIntegrable_iff_mfderiv] at hJ
  funext x
  obtain ⟨ψ, J₀, hx, hψ⟩ := hJ x
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have : IsManifold I (minSmoothness ℝ 2) M := .of_le (n := ∞) (by simp)
  have hψx : ContMDiffAt I 𝓘(ℝ, E) ∞ ψ x :=
    ψ.contMDiffOn.contMDiffAt (ψ.open_source.mem_nhds hx)
  -- The pullbacks along `ψ` of the constant vector fields of `E`.
  let V : E → Π z : E, TangentSpace 𝓘(ℝ, E) z := fun u _ ↦ u
  let X : E → Π y : M, TangentSpace I y := fun u ↦ VectorField.mpullback I 𝓘(ℝ, E) ψ (V u)
  have hconst (u : E) : MDiffAt (T% (V u)) (ψ x) :=
    ((contMDiffAt_vectorSpace_iff_contDiffAt (𝕜 := ℝ) (V := V u) (x := ψ x)
      (n := 1)).mpr contDiffAt_const).mdifferentiableAt one_ne_zero
  have hX (u : E) : MDiffAt (T% (X u)) x :=
    (hconst u).mpullback_vectorField hψx (ψ.isInvertible_mfderiv hn hx) (by simp)
  -- Near `x`, `J` maps the pullback of `u` to the pullback of `J₀ u`.
  have hJX (u : E) : (fun y ↦ J y (X u y)) =ᶠ[𝓝 x] X (J₀ u) := by
    filter_upwards [ψ.open_source.mem_nhds hx] with y hy
    have hy' := ψ.isInvertible_mfderiv hn hy
    refine (hy'.inverse_apply_eq.2 ?_).symm
    exact ((hψ y hy _).trans (congrArg J₀ (hy'.self_apply_inverse u))).symm
  -- The Lie bracket of two such pullbacks vanishes at `x`.
  have hbr (u u' : E) : mlieBracket I (X u) (X u') x = 0 := by
    rw [← mpullback_mlieBracket (hconst u) (hconst u') hψx (by simp)]
    have : mlieBracket 𝓘(ℝ, E) (V u) (V u') = 0 :=
      funext fun z ↦ mlieBracket_const_model_space u u' z
    rw [this, VectorField.mpullback_zero, Pi.zero_apply]
  have hN (u u' : E) : J.nijenhuis x (X u x) (X u' x) = 0 := by
    rw [nijenhuis_apply J (hX u) (hX u'), (hJX u).mlieBracket_vectorField_eq (hJX u'),
      (hJX u).mlieBracket_vectorField_eq (EventuallyEq.refl _ (X u')),
      (EventuallyEq.refl _ (X u)).mlieBracket_vectorField_eq (hJX u'), hbr, hbr, hbr, hbr]
    simp
  have hsurj (v : TangentSpace I x) : X (mfderiv I 𝓘(ℝ, E) ψ x v) x = v :=
    (ψ.isInvertible_mfderiv hn hx).inverse_apply_self v
  ext v w
  have h := hN (mfderiv I 𝓘(ℝ, E) ψ x v) (mfderiv I 𝓘(ℝ, E) ψ x w)
  rw [hsurj, hsurj] at h
  simpa using h

/-- Following a smooth chart `ψ` into `G` whose derivative carries `J` to `J₀` by a partial
diffeomorphism `Θ` from `G` to `G'` whose derivative carries `J₀` to `J₁` at every point of its
source gives a chart whose derivative carries `J` to `J₁` at every point of its source. -/
theorem mfderiv_trans_apply_eq_of_fderiv_apply_eq {G G' : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞} {J₀ : G → G}
    (hψ : ∀ y ∈ ψ.source, ∀ v : TangentSpace I y,
      mfderiv I 𝓘(ℝ, G) ψ y (J y v) = J₀ (mfderiv I 𝓘(ℝ, G) ψ y v))
    {Θ : PartialDiffeomorph 𝓘(ℝ, G) 𝓘(ℝ, G') G G' ∞} {J₁ : G' → G'}
    (hΘ : ∀ z ∈ Θ.source, ∀ w : G, fderiv ℝ Θ z (J₀ w) = J₁ (fderiv ℝ Θ z w)) :
    ∀ y ∈ (ψ.trans Θ).source, ∀ v : TangentSpace I y,
      mfderiv I 𝓘(ℝ, G') (ψ.trans Θ) y (J y v) =
        J₁ (mfderiv I 𝓘(ℝ, G') (ψ.trans Θ) y v) := by
  intro y hy v
  rw [PartialDiffeomorph.trans_source] at hy
  have hd (u : TangentSpace I y) : mfderiv I 𝓘(ℝ, G') (ψ.trans Θ) y u =
      fderiv ℝ Θ (ψ y) (mfderiv I 𝓘(ℝ, G) ψ y u) := by
    rw [PartialDiffeomorph.coe_trans, mfderiv_comp_apply y (Θ.mdifferentiableAt (by simp) hy.2)
      (ψ.mdifferentiableAt (by simp) hy.1), mfderiv_eq_fderiv]
    -- `NormedSpace.fromTangentSpace` is the identity of `G` and of `G'`, which Mathlib states by
    -- no lemma.
    rfl
  rw [hd, hd, hψ y hy.1 v]
  exact hΘ _ hy.2 _

/-- Following a smooth chart `ψ` into `G` whose derivative carries `J` to `J₀` by a continuous
linear equivalence `L : G ≃L[ℝ] G'` gives a chart whose derivative carries `J` to the transport of
`J₀` along `L`, at every point of its source. -/
theorem mfderiv_trans_toDiffeomorph_apply_eq_transport {G G' : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞} {J₀ : AlmostComplexStructure G}
    (hψ : ∀ y ∈ ψ.source, ∀ v : TangentSpace I y,
      mfderiv I 𝓘(ℝ, G) ψ y (J y v) = J₀ (mfderiv I 𝓘(ℝ, G) ψ y v)) (L : G ≃L[ℝ] G') :
    ∀ y ∈ (ψ.trans L.toDiffeomorph.toPartialDiffeomorph).source, ∀ v : TangentSpace I y,
      mfderiv I 𝓘(ℝ, G') (ψ.trans L.toDiffeomorph.toPartialDiffeomorph) y (J y v) =
        J₀.transport L.toLinearEquiv
          (mfderiv I 𝓘(ℝ, G') (ψ.trans L.toDiffeomorph.toPartialDiffeomorph) y v) :=
  J.mfderiv_trans_apply_eq_of_fderiv_apply_eq hψ fun _ _ w ↦ by
    simp [ContinuousLinearEquiv.fderiv]

/-- **Integrability is invariant under pullback.** The pullback of an integrable almost complex
structure along a diffeomorphism is integrable. -/
theorem IsIntegrable.pullback [FiniteDimensional ℝ E] {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold I' ∞ N] (h : M ≃ₘ⟮I, I'⟯ N) {J : SmoothAlmostComplexStructure I' N}
    (hJ : J.IsIntegrable) : (pullback h J).IsIntegrable := by
  rw [isIntegrable_iff_mfderiv] at hJ ⊢
  intro x
  obtain ⟨ψ, J₀, hx, hψ⟩ := hJ (h x)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  -- The chart `ψ` read through `h` takes values in `E'`, and carries `pullback h J` to `J₀`.
  let Ψ : PartialDiffeomorph I 𝓘(ℝ, E') M E' ∞ := h.toPartialDiffeomorph.trans ψ
  have hc : (Ψ : M → E') = ψ ∘ h := by
    ext z
    simp [Ψ]
  have hΨ : ∀ y ∈ Ψ.source, ∀ v : TangentSpace I y,
      mfderiv I 𝓘(ℝ, E') Ψ y (SmoothAlmostComplexStructure.pullback h J y v) =
        J₀ (mfderiv I 𝓘(ℝ, E') Ψ y v) := by
    intro y hy v
    have hy' : h y ∈ ψ.source := by simpa [Ψ] using hy
    rw [hc, mfderiv_comp_apply y (ψ.mdifferentiableAt hn hy') (h.mdifferentiable hn y),
      mfderiv_comp_apply y (ψ.mdifferentiableAt hn hy') (h.mdifferentiable hn y),
      mfderiv_pullback_apply, hψ _ hy']
  -- A linear isomorphism `E' ≃ E` brings it back to the model of `M`.
  let L : E' ≃L[ℝ] E := (h.mfderivToContinuousLinearEquiv hn x).symm
  exact ⟨Ψ.trans L.toDiffeomorph.toPartialDiffeomorph, J₀.transport L.toLinearEquiv,
    by simpa [Ψ] using hx, mfderiv_trans_toDiffeomorph_apply_eq_transport _ hΨ L⟩

end Chart

section ModelSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- On a manifold modelled on a normed space `E` itself, `J` is integrable when every point lies
in the source of a chart of the smooth maximal atlas whose derivative carries `J` to a fixed
linear complex structure of `E` at every point of its source. -/
theorem isIntegrable_of_forall_mem_maximalAtlas {J : SmoothAlmostComplexStructure 𝓘(ℝ, E) M}
    (h : ∀ x : M, ∃ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M, x ∈ e.source ∧
      ∃ J₀ : AlmostComplexStructure E, ∀ y ∈ e.source, ∀ v : TangentSpace 𝓘(ℝ, E) y,
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y (J y v) = J₀ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y v)) :
    J.IsIntegrable :=
  isIntegrable_of_forall_exists_isLocalDiffeomorphAt J fun x ↦
    let ⟨e, he, hx, J₀, hJ⟩ := h x
    ⟨e, e.source, J₀, e.open_source.mem_nhds hx, e.isLocalDiffeomorphAt_of_mem_maximalAtlas he hx,
      hJ⟩

end ModelSpace

section Constant

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (J₀ : E →L[ℝ] E)

/-- In the tangent coordinates of the chart at `x₀`, the constant section `J₀` is `J₀` on the
whole chart domain, when the tangent coordinate changes commute with `J₀`. -/
private theorem inTangentCoordinates_const
    (h : ∀ {x y z : M}, z ∈ (chartAt H x).source ∩ (chartAt H y).source → ∀ v : E,
      tangentCoordChange I x y z (J₀ v) = J₀ (tangentCoordChange I x y z v))
    {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    inTangentCoordinates I I id id
        (fun x : M ↦ (J₀ : TangentSpace I x →L[ℝ] TangentSpace I x)) x₀ x = J₀ := by
  refine (inTangentCoordinates_eq (I := I) (I' := I) id id _ hx hx).trans
    (ContinuousLinearMap.ext fun v ↦ ?_)
  have hx' : x ∈ (extChartAt I x₀).source ∩ (extChartAt I x).source ∩
      (extChartAt I x₀).source := by
    simp [hx]
  simp only [ContinuousLinearMap.comp_apply]
  exact (h ⟨mem_chart_source H x, hx⟩ _).trans
    (congrArg J₀ ((tangentCoordChange_comp hx').trans (tangentCoordChange_self (by simp [hx]))))

/-- The constant section `J₀` of the tangent bundle, for a linear complex structure `J₀` of the
model space with which all tangent coordinate changes commute, as a smooth almost complex
structure. -/
def ofTangentCoordChange (hJ₀ : ∀ v, J₀ (J₀ v) = -v)
    (h : ∀ {x y z : M}, z ∈ (chartAt H x).source ∩ (chartAt H y).source → ∀ v : E,
      tangentCoordChange I x y z (J₀ v) = J₀ (tangentCoordChange I x y z v)) :
    SmoothAlmostComplexStructure I M where
  toEndomorphism :=
    ⟨fun _ ↦ J₀, fun x₀ ↦ by
      -- In the tangent coordinates at `x₀`, the section is constantly `J₀` near `x₀`.
      rw [contMDiffAt_hom_bundle]
      refine ⟨contMDiffAt_id, (contMDiffAt_const (c := J₀)).congr_of_eventuallyEq ?_⟩
      filter_upwards [(chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)] with x hx
      exact inTangentCoordinates_const I J₀ h hx⟩
  square_neg _ := ContinuousLinearMap.ext hJ₀

variable {I J₀}

theorem ofTangentCoordChange_apply {hJ₀ : ∀ v, J₀ (J₀ v) = -v}
    {h : ∀ {x y z : M}, z ∈ (chartAt H x).source ∩ (chartAt H y).source → ∀ v : E,
      tangentCoordChange I x y z (J₀ v) = J₀ (tangentCoordChange I x y z v)} (x : M)
    (v : TangentSpace I x) :
    ofTangentCoordChange I J₀ hJ₀ h x v = J₀ v :=
  (rfl)

/-- The almost complex structure `ofTangentCoordChange` is `J₀` on every tangent space, as an
endomorphism. -/
theorem toEndomorphism_ofTangentCoordChange {hJ₀ : ∀ v, J₀ (J₀ v) = -v}
    {h : ∀ {x y z : M}, z ∈ (chartAt H x).source ∩ (chartAt H y).source → ∀ v : E,
      tangentCoordChange I x y z (J₀ v) = J₀ (tangentCoordChange I x y z v)} (x : M) :
    (ofTangentCoordChange I J₀ hJ₀ h).toEndomorphism x =
      (J₀ : TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.ext fun v ↦ ofTangentCoordChange_apply x v

/-- In the tangent coordinates of the chart at any point `x₀`, the almost complex structure
`ofTangentCoordChange` is `J₀` on the whole chart domain. -/
theorem inTangentCoordinates_ofTangentCoordChange {hJ₀ : ∀ v, J₀ (J₀ v) = -v}
    {h : ∀ {x y z : M}, z ∈ (chartAt H x).source ∩ (chartAt H y).source → ∀ v : E,
      tangentCoordChange I x y z (J₀ v) = J₀ (tangentCoordChange I x y z v)} {x₀ x : M}
    (hx : x ∈ (chartAt H x₀).source) :
    inTangentCoordinates I I id id
        (fun x ↦ (ofTangentCoordChange I J₀ hJ₀ h).toEndomorphism x) x₀ x = J₀ :=
  inTangentCoordinates_const I J₀ h hx

/-- On a manifold modelled on `E` itself, the constant structure `J₀` is integrable: in every
chart it is `J₀`. -/
theorem isIntegrable_ofTangentCoordChange [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (hJ₀ : ∀ v, J₀ (J₀ v) = -v)
    (h : ∀ {x y z : M}, z ∈ (chartAt E x).source ∩ (chartAt E y).source → ∀ v : E,
      tangentCoordChange 𝓘(ℝ, E) x y z (J₀ v) = J₀ (tangentCoordChange 𝓘(ℝ, E) x y z v)) :
    (ofTangentCoordChange 𝓘(ℝ, E) J₀ hJ₀ h).IsIntegrable :=
  isIntegrable_of_forall_mem_maximalAtlas fun x ↦
    ⟨chartAt E x, IsManifold.chart_mem_maximalAtlas x, mem_chart_source E x,
      ⟨J₀.toLinearMap, LinearMap.ext hJ₀⟩, fun y hy v ↦ by
        rw [mfderiv_chartAt_eq_tangentCoordChange hy, ofTangentCoordChange_apply]
        exact h ⟨mem_chart_source E y, hy⟩ v⟩

end Constant

section ComplexManifold

open scoped TauCeti.ComplexManifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-- **The almost complex structure of a complex manifold is integrable**: in every holomorphic
chart it is multiplication by `i`. -/
theorem isIntegrable_ofComplexManifold : (ofComplexManifold E M).IsIntegrable :=
  isIntegrable_of_forall_mem_maximalAtlas fun x ↦
    ⟨chartAt E x, IsManifold.chart_mem_maximalAtlas x, mem_chart_source E x,
      AlmostComplexStructure.ofComplexModule E, fun y hy v ↦ by
        have h := tangentCoordChange_smul ℝ (𝕜' := ℂ) ⟨mem_chart_source E y, hy⟩ Complex.I v
        rw [← mfderiv_chartAt_eq_tangentCoordChange hy] at h
        exact (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) y)
          (ofComplexManifold_apply (E := E) y v)).trans
          (h.trans (AlmostComplexStructure.ofComplexModule_apply _).symm)⟩

end ComplexManifold

section Surface

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
  {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M}

/-- An almost complex structure on a real surface is integrable exactly when every point lies in
the source of an isothermal chart of the smooth maximal atlas. -/
theorem isIntegrable_iff_forall_exists_isIsothermalChart :
    j.IsIntegrable ↔ ∀ x : M, ∃ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ M,
      IsIsothermalChart j e ∧ x ∈ e.source := by
  refine ⟨fun hj x ↦ ?_, fun h ↦ isIntegrable_of_forall_mem_maximalAtlas fun x ↦ ?_⟩
  · rw [isIntegrable_iff_mfderiv] at hj
    obtain ⟨ψ, J₀, hx, hψ⟩ := hj x
    -- A real-linear automorphism `L` of `ℂ` carrying `J₀` to multiplication by `i`.
    obtain ⟨φ, hφ⟩ := J₀.exists_linearEquiv_I_smul (G := ℂ) (by simp)
    let L : ℂ ≃L[ℝ] ℂ := φ.symm.toContinuousLinearEquiv
    have hL (w : ℂ) : J₀.transport L.toLinearEquiv w = Complex.I • w := by
      apply φ.injective
      simpa [L] using (hφ w).symm
    let Φ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) M ℂ ∞ :=
      ψ.trans L.toDiffeomorph.toPartialDiffeomorph
    have hΦ := mfderiv_trans_toDiffeomorph_apply_eq_transport _ hψ L
    have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
    have hmem : Φ.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ M := by
      rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
      exact ⟨Φ.contMDiffOn, Φ.symm.contMDiffOn⟩
    refine ⟨Φ.toOpenPartialHomeomorph, hmem,
      ⟨IsManifold.maximalAtlas_subset_of_le (by simp) hmem, fun y hy ↦ ?_⟩,
      by simpa [Φ] using hx⟩
    refine isPseudoholomorphicAt_iff_mfderiv.2 ⟨Φ.mdifferentiableAt hn hy, fun w ↦ ?_⟩
    simp only [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]
    exact (hΦ y hy w).trans ((hL _).trans (ofComplexManifold_apply (E := ℂ) _ _).symm)
  · obtain ⟨e, he, hj, hx⟩ := h x
    exact ⟨e, he, hx, AlmostComplexStructure.ofComplexModule ℂ, fun y hy v ↦
      (hj.mfderiv_apply_commute hy v).trans ((ofComplexManifold_apply _ _).trans
        (AlmostComplexStructure.ofComplexModule_apply (V := ℂ) _).symm)⟩

/-- **An integrable structure on a real surface has isothermal charts.** -/
theorem IsIntegrable.hasIsothermalCharts (hj : j.IsIntegrable) : j.HasIsothermalCharts where
  exists_isIsothermalChart x := by
    obtain ⟨e, -, he, hx⟩ := isIntegrable_iff_forall_exists_isIsothermalChart.1 hj x
    exact ⟨e, he, hx⟩

end Surface

end SmoothAlmostComplexStructure

end TauCeti
