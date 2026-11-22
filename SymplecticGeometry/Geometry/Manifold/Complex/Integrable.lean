/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Complex.Isothermal
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
public import TauCeti.Geometry.Symplectic.Manifold.Nijenhuis
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
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
On a real surface, integrable structures have isothermal charts in the sense of Tau Ceti's
`SmoothAlmostComplexStructure.HasIsothermalCharts`, and smooth isothermal charts make a structure
integrable.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.IsIntegrable`: integrability of a smooth almost complex
  structure; `isIntegrable_iff_mfderiv` states it through derivatives of charts.
* `TauCeti.SmoothAlmostComplexStructure.isIntegrable_ofComplexManifold`: the almost complex
  structure of a complex manifold is integrable.
* `TauCeti.SmoothAlmostComplexStructure.IsIntegrable.pullback`: integrability is invariant under
  pullback along a diffeomorphism.
* `TauCeti.SmoothAlmostComplexStructure.IsIntegrable.nijenhuis_eq_zero`: the Nijenhuis tensor of
  an integrable structure vanishes.
* `TauCeti.SmoothAlmostComplexStructure.IsIntegrable.hasIsothermalCharts` and
  `TauCeti.SmoothAlmostComplexStructure.isIntegrable_of_forall_isIsothermalChart`: on a surface,
  integrable structures have isothermal charts, and smooth isothermal charts covering the surface
  make the structure integrable.

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

/-- A smooth chart `ψ` into a normed space carries `J` to a fixed map `J₀` on its target exactly
when its derivative intertwines `J` with `J₀` at every point of its source. -/
theorem forall_chartPushforward_apply_eq_iff {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (ψ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) (J₀ : G → G) :
    (∀ p ∈ ψ.target, ∀ w : G, J.chartPushforward ψ.toOpenPartialHomeomorph p w = J₀ w) ↔
      ∀ y ∈ ψ.source, ∀ v : TangentSpace I y,
        mfderiv I 𝓘(ℝ, G) ψ y (J y v) = J₀ (mfderiv I 𝓘(ℝ, G) ψ y v) := by
  refine ⟨fun h y hy v ↦ ?_, fun h p hp w ↦ ?_⟩
  · have h' := DFunLike.congr_fun ((J.toContMDiff ⊤).mfderiv_comp_toEndomorphism
      ψ.toOpenPartialHomeomorph hy (ψ.mdifferentiableAt (by simp) hy)
      (ψ.symm.mdifferentiableAt (by simp) (ψ.map_source hy))) v
    simp only [toContMDiff_chartPushforward, toContMDiff_toEndomorphism_apply,
      ψ.toFun'_toOpenPartialHomeomorph] at h'
    exact h'.trans (h _ (ψ.map_source hy) _)
  · rw [← toContMDiff_chartPushforward J ⊤, ContMDiffAlmostComplexStructure.chartPushforward_apply,
      toContMDiff_apply]
    exact (h _ (ψ.map_target hp) _).trans
      (congrArg J₀ (ψ.mfderiv_apply_mfderiv_symm_apply (by simp) hp w))

/-- `J` is integrable exactly when every point of `M` lies in the source of a smooth chart whose
derivative carries `J` to a fixed linear complex structure of `E` at every point of its
source. -/
theorem isIntegrable_iff_mfderiv : J.IsIntegrable ↔
    ∀ x : M, ∃ (ψ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (J₀ : AlmostComplexStructure E),
      x ∈ ψ.source ∧ ∀ y ∈ ψ.source, ∀ v : TangentSpace I y,
        mfderiv I 𝓘(ℝ, E) ψ y (J y v) = J₀ (mfderiv I 𝓘(ℝ, E) ψ y v) := by
  simp only [isIntegrable_def, forall_chartPushforward_apply_eq_iff]

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
  -- A chart of `N` read through `h` takes values in `E'`; a linear isomorphism `E' ≃ E` brings
  -- it back to the model of `M`.
  let L : E' ≃L[ℝ] E := (h.mfderivToContinuousLinearEquiv hn x).symm
  let Φ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    (h.toPartialDiffeomorph.trans ψ).trans L.toPartialDiffeomorph
  have hΦ : (Φ : M → E) = L ∘ ψ ∘ h := by
    ext y
    simp [Φ]
  have hsource : Φ.source = h ⁻¹' ψ.source := by
    ext y
    simp [Φ]
  refine ⟨Φ, J₀.transport L.toLinearEquiv, hsource ▸ hx, fun y hy v ↦ ?_⟩
  rw [hsource] at hy
  have hψy := ψ.mdifferentiableAt hn hy
  have hd (u : TangentSpace I y) : mfderiv I 𝓘(ℝ, E) Φ y u =
      L (mfderiv I' 𝓘(ℝ, E') ψ (h y) (mfderiv I I' h y u)) := by
    rw [hΦ, mfderiv_comp_apply y L.mdifferentiableAt (hψy.comp y (h.mdifferentiable hn y)),
      mfderiv_comp_apply y hψy (h.mdifferentiable hn y), L.mfderiv_eq]
    -- `L` as a continuous linear map, applied on a tangent space of `E'`, which is `E'`.
    rfl
  rw [hd, hd, mfderiv_pullback_apply, hψ _ hy, AlmostComplexStructure.transport_apply]
  exact congrArg (fun z : E' ↦ L (J₀ z)) (L.symm_apply_apply _).symm

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
    J.IsIntegrable := by
  rw [isIntegrable_iff_mfderiv]
  intro x
  obtain ⟨e, he, hx, J₀, hJ⟩ := h x
  -- A chart of the smooth maximal atlas is a smooth partial diffeomorphism to the model space.
  let ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  exact ⟨ψ, J₀, hx, hJ⟩

end ModelSpace

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

/-- An almost complex structure on a real surface is integrable when every point lies in the
source of an isothermal chart of the smooth maximal atlas. -/
theorem isIntegrable_of_forall_isIsothermalChart
    (h : ∀ x : M, ∃ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ M,
      IsIsothermalChart j e ∧ x ∈ e.source) :
    j.IsIntegrable :=
  isIntegrable_of_forall_mem_maximalAtlas fun x ↦ by
    obtain ⟨e, he, hj, hx⟩ := h x
    exact ⟨e, he, hx, AlmostComplexStructure.ofComplexModule ℂ, fun y hy v ↦
      (hj.mfderiv_apply_commute hy v).trans ((ofComplexManifold_apply _ _).trans
        (AlmostComplexStructure.ofComplexModule_apply (V := ℂ) _).symm)⟩

/-- **An integrable structure on a real surface has isothermal charts.** -/
theorem IsIntegrable.hasIsothermalCharts (hj : j.IsIntegrable) : j.HasIsothermalCharts where
  exists_isIsothermalChart x := by
    rw [isIntegrable_iff_mfderiv] at hj
    obtain ⟨ψ, J₀, hx, hψ⟩ := hj x
    -- A real-linear automorphism `L` of `ℂ` carrying `J₀` to multiplication by `i`.
    obtain ⟨φ, hφ⟩ := J₀.exists_linearEquiv_I_smul (G := ℂ) (by simp)
    let L : ℂ ≃L[ℝ] ℂ := φ.symm.toContinuousLinearEquiv
    have hL (w : ℂ) : L (J₀ w) = Complex.I • L w := by
      apply φ.injective
      simp only [L, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.apply_symm_apply]
      rw [hφ, LinearEquiv.apply_symm_apply]
    let Φ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) M ℂ ∞ := ψ.trans L.toPartialDiffeomorph
    have hΦ : (Φ : M → ℂ) = L ∘ ψ := by
      ext y
      simp [Φ]
    have hsource : Φ.source = ψ.source := by
      ext y
      simp [Φ]
    have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
    refine ⟨Φ.toOpenPartialHomeomorph, ⟨?_, fun y hy ↦ ?_⟩, hsource ▸ hx⟩
    · rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
      exact ⟨Φ.contMDiffOn.of_le (by simp), Φ.symm.contMDiffOn.of_le (by simp)⟩
    · have hy' : y ∈ ψ.source := hsource ▸ hy
      refine isPseudoholomorphicAt_iff_mfderiv.2 ⟨Φ.mdifferentiableAt hn hy, fun w ↦ ?_⟩
      have hd (u : TangentSpace 𝓘(ℝ, ℂ) y) :
          mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) Φ y u = L (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ y u) := by
        rw [hΦ, mfderiv_comp_apply y L.mdifferentiableAt (ψ.mdifferentiableAt hn hy'),
          L.mfderiv_eq]
        -- `L` as a continuous linear map, applied on a tangent space of `ℂ`, which is `ℂ`.
        rfl
      simp only [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]
      exact (hd _).trans ((congrArg L (hψ y hy' w)).trans ((hL _).trans
        ((congrArg (fun z : ℂ ↦ Complex.I • z) (hd w).symm).trans
          (ofComplexManifold_apply (E := ℂ) _ _).symm)))

end Surface

end SmoothAlmostComplexStructure

end TauCeti
