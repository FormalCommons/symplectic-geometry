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
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Restriction
public import TauCeti.Geometry.Symplectic.Manifold.Nijenhuis
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Coordinates
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.ModelChart
import TauCeti.Geometry.Manifold.VectorBundle.Hom

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
On a surface modelled on `𝓘(ℝ, ℂ)`, isothermal charts of the smooth maximal atlas around every
point give integrability. Every smooth almost complex structure there has such charts, by Tau
Ceti's `SmoothAlmostComplexStructure.exists_isIsothermalChart` and
`IsIsothermalChart.mem_maximalAtlas_infty`, so both conditions hold for every structure.

A linear complex structure `J₀` of the model with which all tangent coordinate changes commute
defines a constant almost complex structure, `ofTangentCoordChange`; its construction follows Tau
Ceti's `SmoothAlmostComplexStructure.ofTangentCoordChangeISMul`, the case of multiplication by
`i`. Its smoothness is Tau Ceti's `TauCeti.contMDiff_hom_bundle_of_inCoordinates_eq_const`: the
trivialization of the tangent bundle at a point has the chart's source as its base set, and there
the structure reads as `J₀` in tangent coordinates. On a manifold modelled on the vector space
itself it is integrable.

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
* `TauCeti.SmoothAlmostComplexStructure.isIntegrable_restrictOpen_source`: `J` is integrable on
  the source of a partial diffeomorphism onto an open subset of a normed space whose derivative
  carries `J` to a fixed linear complex structure.
* `TauCeti.SmoothAlmostComplexStructure.IsIntegrable.pullback`: integrability is invariant under
  pullback along a diffeomorphism.
* `TauCeti.SmoothAlmostComplexStructure.IsIntegrable.nijenhuis_eq_zero`: the Nijenhuis tensor of
  an integrable structure vanishes.
* `TauCeti.SmoothAlmostComplexStructure.isIntegrable_iff_forall_exists_isIsothermalChart`: on a
  surface modelled on `𝓘(ℝ, ℂ)`, integrability is equivalent to the existence of smooth
  isothermal charts around every point. Both hold for every structure; what the theorem adds is
  that such charts give integrability.

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
  obtain ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.1 hs
  obtain ⟨Φ, hxΦ, hΦt, hφΦ⟩ := hφ.exists_partialDiffeomorph_eqOn ht hxt
  refine ⟨Φ, J₀, hxΦ, fun y hy v ↦ ?_⟩
  have hd : mfderiv I 𝓘(ℝ, E) Φ y = mfderiv I 𝓘(ℝ, E) φ y :=
    Filter.EventuallyEq.mfderiv_eq <|
      Filter.eventually_of_mem (Φ.open_source.mem_nhds hy) fun z hz ↦ (hφΦ hz).symm
  rw [hd]
  exact hJ y (hts (hΦt hy)) v

attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField in
/-- **The Nijenhuis tensor of an integrable structure vanishes.** -/
theorem IsIntegrable.nijenhuis_eq_zero [FiniteDimensional ℝ E]
    {J : SmoothAlmostComplexStructure I M} (hJ : J.IsIntegrable) : J.nijenhuis = 0 := by
  rw [isIntegrable_iff_mfderiv] at hJ
  funext x
  obtain ⟨ψ, J₀, hx, hψ⟩ := hJ x
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hψx : ContMDiffAt I 𝓘(ℝ, E) ∞ ψ x :=
    ψ.contMDiffOn.contMDiffAt (ψ.open_source.mem_nhds hx)
  -- The pullbacks along `ψ` of the constant vector fields of `E`.
  let X : E → Π y : M, TangentSpace I y := fun u ↦
    VectorField.mpullback I 𝓘(ℝ, E) ψ (constVectorField u)
  have hconst (u : E) : MDiffAt (T% (constVectorField u)) (ψ x) :=
    mdifferentiable_constVectorField u (ψ x)
  have hX (u : E) : MDiffAt (T% (X u)) x :=
    (hconst u).mpullback_vectorField hψx (ψ.isInvertible_mfderiv hn hx) (by simp)
  -- Near `x`, `J` maps the pullback of `u` to the pullback of `J₀ u`.
  have hJX (u : E) : (fun y ↦ J y (X u y)) =ᶠ[𝓝 x] X (J₀ u) := by
    filter_upwards [ψ.open_source.mem_nhds hx] with y hy
    have hy' := ψ.isInvertible_mfderiv hn hy
    simp only [X, VectorField.mpullback_apply, constVectorField_apply,
      NormedSpace.fromTangentSpace_symm_apply]
    refine (hy'.inverse_apply_eq.2 ?_).symm
    exact ((hψ y hy _).trans (congrArg J₀ (hy'.self_apply_inverse u))).symm
  -- The Lie bracket of two such pullbacks vanishes at `x`.
  have hbr (u u' : E) : mlieBracket I (X u) (X u') x = 0 := by
    rw [← mpullback_mlieBracket (hconst u) (hconst u') hψx (by simp),
      mlieBracket_constVectorField, VectorField.mpullback_zero, Pi.zero_apply]
  have hN (u u' : E) : J.nijenhuis x (X u x) (X u' x) = 0 := by
    rw [nijenhuis_apply J (hX u) (hX u'), (hJX u).mlieBracket_vectorField_eq (hJX u'),
      (hJX u).mlieBracket_vectorField_eq (EventuallyEq.refl _ (X u')),
      (EventuallyEq.refl _ (X u)).mlieBracket_vectorField_eq (hJX u'), hbr, hbr, hbr, hbr]
    simp
  have hsurj (v : TangentSpace I x) : X (mfderiv I 𝓘(ℝ, E) ψ x v) x = v := by
    simp only [X, VectorField.mpullback_apply]
    exact (congrArg (mfderiv I 𝓘(ℝ, E) ψ x).inverse ((constVectorField_apply _ _).trans
      (NormedSpace.fromTangentSpace_symm_apply _ _))).trans
      ((ψ.isInvertible_mfderiv hn hx).inverse_apply_self v)
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
  have hd (u : TangentSpace I y) : mfderiv I 𝓘(ℝ, G') (ψ.trans Θ) y u =
      fderiv ℝ Θ (ψ y) (mfderiv I 𝓘(ℝ, G) ψ y u) := by
    rw [ψ.mfderiv_trans Θ (by simp) hy, mfderiv_eq_fderiv]
    -- `NormedSpace.fromTangentSpace` is the identity of `G` and of `G'`, and the tangent spaces at
    -- `Θ (ψ y)` and at `(ψ.trans Θ) y` are the same type, so the two sides agree by definition.
    rfl
  rw [PartialDiffeomorph.trans_source] at hy
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

/-- **A chart in which `J` is constant makes `J` integrable on its source.** If the derivative
of a partial diffeomorphism `φ` from `M` onto an open subset of a normed space `G` carries `J` to a
fixed linear complex structure `J₀` of `G` at every point of its source, then the restriction of
`J` to the source of `φ` is integrable. -/
theorem isIntegrable_restrictOpen_source {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {φ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞} {J₀ : AlmostComplexStructure G}
    (hφ : ∀ y ∈ φ.source, ∀ v : TangentSpace I y,
      mfderiv I 𝓘(ℝ, G) φ y (J y v) = J₀ (mfderiv I 𝓘(ℝ, G) φ y v)) :
    (J.restrictOpen ⟨φ.source, φ.open_source⟩).IsIntegrable := by
  set U : TopologicalSpace.Opens M := ⟨φ.source, φ.open_source⟩
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  rw [isIntegrable_iff_mfderiv]
  intro x
  -- The restriction of `φ` to `U` is a chart of `U` into `G` in which `J` is `J₀`.
  let ψ := φ.subtypeRestr U ⟨x⟩
  have hψ : (ψ : U → G) = φ ∘ Subtype.val := funext (φ.subtypeRestr_apply U ⟨x⟩)
  have hsource : ψ.source = univ := by
    rw [PartialDiffeomorph.subtypeRestr_source]
    exact eq_univ_of_forall fun y ↦ y.property
  have hd (y : U) (v : TangentSpace I y) : mfderiv I 𝓘(ℝ, G) ψ y v =
      mfderiv I 𝓘(ℝ, G) φ y (Manifold.tangentSpaceOpenEquiv (I := I) y v) := by
    rw [hψ, mfderiv_comp_apply y (φ.mdifferentiableAt hn y.property)
      (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero), Manifold.mfderiv_subtype_val,
      ContinuousLinearEquiv.coe_coe]
  have hJ : ∀ y ∈ ψ.source, ∀ v : TangentSpace I y,
      mfderiv I 𝓘(ℝ, G) ψ y (J.restrictOpen U y v) = J₀ (mfderiv I 𝓘(ℝ, G) ψ y v) :=
    fun y _ v ↦ by
      rw [hd, hd, restrictOpen_apply, ContinuousLinearEquiv.apply_symm_apply, hφ y y.property]
  -- A linear isomorphism `G ≃ E` brings it to the model of `M`.
  obtain ⟨e, -⟩ := φ.isInvertible_mfderiv hn x.property
  let L : G ≃L[ℝ] E := e.symm
  exact ⟨ψ.trans L.toDiffeomorph.toPartialDiffeomorph, J₀.transport L.toLinearEquiv,
    by simp [hsource], (J.restrictOpen U).mfderiv_trans_toDiffeomorph_apply_eq_transport hJ L⟩

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

/-- The constant section `J₀` of the tangent bundle, for a linear complex structure `J₀` of the
model space with which all tangent coordinate changes commute, as a smooth almost complex
structure. -/
def ofTangentCoordChange (hJ₀ : ∀ v, J₀ (J₀ v) = -v)
    (h : ∀ {x y z : M}, z ∈ (chartAt H x).source ∩ (chartAt H y).source → ∀ v : E,
      tangentCoordChange I x y z (J₀ v) = J₀ (tangentCoordChange I x y z v)) :
    SmoothAlmostComplexStructure I M where
  toEndomorphism :=
    ⟨fun _ ↦ J₀, TauCeti.contMDiff_hom_bundle_of_inCoordinates_eq_const
      (V := TangentSpace I) (W := TangentSpace I) (c := fun _ ↦ J₀) fun _ _ hx _ ↦ by
        rw [TangentBundle.trivializationAt_baseSet] at hx
        simpa only [inTangentCoordinates, id_eq] using
          SymplecticGeometry.inTangentCoordinates_const I J₀ hx (h ⟨mem_chart_source H _, hx⟩)⟩
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
  SymplecticGeometry.inTangentCoordinates_const I J₀ hx (h ⟨mem_chart_source H _, hx⟩)

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
        -- The chart is holomorphic, so its real derivative commutes with multiplication by `i`.
        have h := (mdifferentiableAt_atlas (I := 𝓘(ℂ, E)) (chart_mem_atlas E x)
          hy).mfderiv_ofComplexManifold_apply v
        exact h.trans ((ofComplexManifold_apply (E := E) (M := E) _ _).trans
          (AlmostComplexStructure.ofComplexModule_apply (V := E) _).symm)⟩

end ComplexManifold

section Surface

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
  {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M}

/-- On a surface modelled on `𝓘(ℝ, ℂ)`, a smooth almost complex structure is integrable if and
only if every point lies in the source of an isothermal chart of the smooth maximal atlas.

Both sides hold for every such structure: the left-hand side by `isIntegrable_of_finrank_eq_two`
(in `Complex/Isothermal.lean`), the right-hand side by Tau Ceti's `exists_isIsothermalChart` and
`IsIsothermalChart.mem_maximalAtlas_infty`. What the theorem adds
is the backward direction: isothermal charts of the smooth maximal atlas around every point make
the structure integrable. -/
theorem isIntegrable_iff_forall_exists_isIsothermalChart :
    j.IsIntegrable ↔ ∀ x : M, ∃ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ M,
      IsIsothermalChart j e ∧ x ∈ e.source := by
  refine ⟨fun _ x ↦ ?_, fun h ↦ isIntegrable_of_forall_mem_maximalAtlas fun x ↦ ?_⟩
  · -- Every point lies in a smooth isothermal chart, integrable or not.
    obtain ⟨e, he, hx⟩ := j.exists_isIsothermalChart x
    exact ⟨e, he.mem_maximalAtlas_infty, he, hx⟩
  · obtain ⟨e, he, hj, hx⟩ := h x
    exact ⟨e, he, hx, AlmostComplexStructure.ofComplexModule ℂ, fun y hy v ↦
      (hj.mfderiv_apply_commute hy v).trans ((ofComplexManifold_apply _ _).trans
        (AlmostComplexStructure.ofComplexModule_apply (V := ℂ) _).symm)⟩

end Surface

end SmoothAlmostComplexStructure

end TauCeti
