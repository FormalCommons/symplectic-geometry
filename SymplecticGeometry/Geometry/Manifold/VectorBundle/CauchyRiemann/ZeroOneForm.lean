/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.ZeroOne.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Topology
import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Topology
import SymplecticGeometry.Topology.FiberBundle.Basic

/-!
# The `(0,1)`-projection as a smooth section of a hom bundle

For an almost complex structure `j` on `M` and a complex vector bundle `V → M`, Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.zeroOnePart` is, at every point `x`, a real-linear map of
the `V`-valued one-forms at `x` to themselves. This file bundles it at `x` as a continuous
real-linear endomorphism `TauCeti.SmoothAlmostComplexStructure.zeroOnePartL j x` of the one-forms
at `x`, and shows that these endomorphisms form a smooth section of the bundle of endomorphisms
of the bundle of `V`-valued one-forms
(`TauCeti.SmoothAlmostComplexStructure.contMDiff_zeroOnePartL`). In this form the projection
can act on Sobolev sections of one-forms as a smooth coefficient.

The formula `η ↦ ½ (η + i • η ∘ T)` makes sense for every endomorphism `T` of a tangent space
(`TauCeti.SmoothAlmostComplexStructure.zeroOnePartOfEnd`), and `zeroOnePartL j x` is defined as
this formula at `T = j x`. In the preferred trivializations the formula reads as the same
formula for the coordinate expression of `T`, since the trivializations of `V` are complex
linear, so it is a smooth map of total spaces from the tangent endomorphism bundle
(`TauCeti.SmoothAlmostComplexStructure.contMDiff_totalSpace_zeroOnePartOfEnd`). The smoothness of
`zeroOnePartL j` is its composite with the smooth section `j`, and so needs no finite
dimension of `E` or `F`.

The bundled section `TauCeti.SmoothAlmostComplexStructure.zeroOnePartSection j` depends
continuously on `j` (`TauCeti.SmoothAlmostComplexStructure.continuous_zeroOnePartSection`), for
the `C^∞` topology `TauCeti.SmoothAlmostComplexStructure.frameTopology` on almost complex
structures and the compact derivative topology `ContMDiffSection.frameTopology` on sections: Tau
Ceti's `ContMDiffSection.continuous_map_frameTopology` gives the continuity of the action of
`zeroOnePartOfEnd` on sections. Here the model space `E` of `M` is finite dimensional.

## Main definitions and results

* `TauCeti.SmoothAlmostComplexStructure.zeroOnePartL`: the `(0,1)`-projection at a point.
* `TauCeti.SmoothAlmostComplexStructure.zeroOnePartOfEnd`: the same formula for any endomorphism
  of the tangent space.
* `TauCeti.SmoothAlmostComplexStructure.contMDiff_totalSpace_zeroOnePartOfEnd`: it is a smooth
  map of total spaces.
* `TauCeti.SmoothAlmostComplexStructure.contMDiff_zeroOnePartL`: `zeroOnePartL j` is a smooth
  section of the endomorphism bundle of the one-forms.
* `TauCeti.SmoothAlmostComplexStructure.zeroOnePartSection`: that smooth section, bundled.
* `TauCeti.SmoothAlmostComplexStructure.topologicalSpaceTotalSpaceOneFormEnd`: the topology of
  the total space of the endomorphism bundle of the one-forms, named as an instance.
* `TauCeti.SmoothAlmostComplexStructure.continuous_zeroOnePartSection`: it depends continuously
  on the almost complex structure.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (j : SmoothAlmostComplexStructure I M)
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)]

/-! ### The formula of the `(0,1)`-projection -/

variable (V) in
/-- The formula `η ↦ ½ (η + i • η ∘ T)` of the `(0,1)`-projection, for an arbitrary
endomorphism `T` of the tangent space at `x`. -/
def zeroOnePartOfEnd (x : M) (T : TangentSpace I x →L[ℝ] TangentSpace I x) :
    (TangentSpace I x →L[ℝ] V x) →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ + Complex.I • ContinuousLinearMap.precomp (V x) T)

omit [IsManifold I ∞ M] in
/-- `zeroOnePartOfEnd V x T` sends a one-form `η` to `½ (η + i • η ∘ T)`. -/
@[simp]
theorem zeroOnePartOfEnd_apply (x : M) (T : TangentSpace I x →L[ℝ] TangentSpace I x)
    (η : TangentSpace I x →L[ℝ] V x) :
    zeroOnePartOfEnd V x T η = (2⁻¹ : ℝ) • (η + Complex.I • η.comp T) :=
  (rfl)

/-- The `(0,1)`-projection `η ↦ ½ (η + i • η ∘ j)` of the `V`-valued one-forms at `x`, as a
continuous real-linear endomorphism: the formula `zeroOnePartOfEnd` at `T = j x`. -/
def zeroOnePartL (x : M) :
    (TangentSpace I x →L[ℝ] V x) →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  zeroOnePartOfEnd V x (j.toEndomorphism x)

/-- At `T = j x`, the formula `zeroOnePartOfEnd` is the `(0,1)`-projection `zeroOnePartL j x`. -/
@[simp]
theorem zeroOnePartOfEnd_toEndomorphism (x : M) :
    zeroOnePartOfEnd V x (j.toEndomorphism x) = j.zeroOnePartL x :=
  (rfl)

/-- `zeroOnePartL j x` is the `(0,1)`-projection of one-forms at `x`. -/
@[simp]
theorem zeroOnePartL_apply (x : M) (η : TangentSpace I x →L[ℝ] V x) :
    j.zeroOnePartL x η = j.zeroOnePart η := by
  ext v
  simp [← zeroOnePartOfEnd_toEndomorphism, zeroOnePart_apply]

variable [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [VectorBundle ℂ F V]

/-! ### Smoothness of the formula -/

/-- In the preferred trivializations at `x₀`, the formula of the `(0,1)`-projection for `T`
reads as the same formula for the coordinate expression of `T`. -/
private theorem inCoordinates_zeroOnePartOfEnd {x₀ x : M}
    (hT : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hV : x ∈ (trivializationAt F V x₀).baseSet)
    (T : TangentSpace I x →L[ℝ] TangentSpace I x) :
    ContinuousLinearMap.inCoordinates (E →L[ℝ] F) (fun x ↦ TangentSpace I x →L[ℝ] V x)
        (E →L[ℝ] F) (fun x ↦ TangentSpace I x →L[ℝ] V x) x₀ x x₀ x
        (zeroOnePartOfEnd V x T) =
      (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ + Complex.I •
        (ContinuousLinearMap.compL ℝ E E F).flip
          (ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x₀ x x₀ x
            T)) := by
  have hH : x ∈
      (trivializationAt (E →L[ℝ] F) (fun x ↦ TangentSpace I x →L[ℝ] V x) x₀).baseSet :=
    ⟨hT, hV⟩
  have h1 (ζ : TangentSpace I x →L[ℝ] V x) :
      (trivializationAt (E →L[ℝ] F) (fun x ↦ TangentSpace I x →L[ℝ] V x)
        x₀).continuousLinearMapAt ℝ x ζ =
        ContinuousLinearMap.inCoordinates E (TangentSpace I) F V x₀ x x₀ x ζ := by
    rw [Trivialization.continuousLinearMapAt_apply_of_mem _ _ hH, hom_trivializationAt_apply]
  have h2 (η : E →L[ℝ] F) :
      (trivializationAt (E →L[ℝ] F) (fun x ↦ TangentSpace I x →L[ℝ] V x) x₀).symmL ℝ x η =
        ((trivializationAt F V x₀).symmL ℝ x).comp
          (η.comp ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x)) :=
    Trivialization.continuousLinearMap_symmL _ _ x η
  -- The trivializations of `V` are complex linear on the fibres.
  have hI (w : V x) : (trivializationAt F V x₀).continuousLinearMapAt ℝ x (Complex.I • w) =
      Complex.I • (trivializationAt F V x₀).continuousLinearMapAt ℝ x w := by
    rw [Trivialization.coe_continuousLinearMapAt_eq_coe_continuousLinearMapAt ℝ ℂ]
    exact map_smul _ _ _
  ext η v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply, h1, h2]
  simp only [zeroOnePartOfEnd_apply, smul_apply, add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, map_smul, map_add, hI,
    Trivialization.continuousLinearMapAt_symmL _ hT,
    Trivialization.continuousLinearMapAt_symmL _ hV]

/-- The formula of the `(0,1)`-projection is a smooth map of total spaces from the tangent
endomorphism bundle to the endomorphism bundle of the `V`-valued one-forms. -/
theorem contMDiff_totalSpace_zeroOnePartOfEnd :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] E)) (I.prod 𝓘(ℝ, (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)) ∞
      (fun p : TotalSpace (E →L[ℝ] E) (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) ↦
        TotalSpace.mk' ((E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)
          (E := fun x ↦ (TangentSpace I x →L[ℝ] V x) →L[ℝ] TangentSpace I x →L[ℝ] V x) p.proj
          (zeroOnePartOfEnd V p.proj p.snd)) := by
  intro p₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨(Bundle.contMDiff_proj _) p₀, ?_⟩
  have hT := ((contMDiffAt_hom_bundle _).1
    (contMDiffAt_id (I := I.prod 𝓘(ℝ, E →L[ℝ] E)) (n := ∞) (x := p₀))).2
  have hg : ContDiff ℝ ∞ fun T : E →L[ℝ] E ↦
      (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ (E →L[ℝ] F) +
        Complex.I • (ContinuousLinearMap.compL ℝ E E F).flip T) := by
    fun_prop
  refine (hg.contMDiff.contMDiffAt.comp p₀ hT).congr_of_eventuallyEq ?_
  have hp : ContinuousAt (fun p : TotalSpace (E →L[ℝ] E)
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) ↦ p.proj) p₀ :=
    ((Bundle.contMDiff_proj (IB := I) (n := ∞) _) p₀).continuousAt
  filter_upwards [hp.eventually_mem_baseSet_trivializationAt E (TangentSpace I),
    hp.eventually_mem_baseSet_trivializationAt F V] with p hT hV
  exact inCoordinates_zeroOnePartOfEnd hT hV p.snd

/-! ### The `(0,1)`-projection as a smooth section -/

/-- The topology of the total space of the bundle of endomorphisms of the bundle of `V`-valued
one-forms, that of Mathlib's hom bundle. Instance search finds it for concrete bundles only within
a larger budget than it has when nested in another search, so it is named here. -/
instance topologicalSpaceTotalSpaceOneFormEnd :
    TopologicalSpace (TotalSpace ((E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)
      fun x ↦ (TangentSpace I x →L[ℝ] V x) →L[ℝ] TangentSpace I x →L[ℝ] V x) :=
  ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) _ _ _ _

/-- The `(0,1)`-projections at the points of `M` form a `C^n` section of the bundle of
endomorphisms of the bundle of `V`-valued one-forms, for every `n ≤ ∞`. -/
theorem contMDiff_zeroOnePartL {n : ℕ∞ω} (hn : n ≤ ∞) :
    ContMDiff I (I.prod 𝓘(ℝ, (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)) n fun x ↦
      TotalSpace.mk' ((E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)
        (E := fun x ↦ (TangentSpace I x →L[ℝ] V x) →L[ℝ] TangentSpace I x →L[ℝ] V x) x
        (j.zeroOnePartL x) :=
  ((contMDiff_totalSpace_zeroOnePartOfEnd (F := F) (V := V)).comp
    j.toEndomorphism.contMDiff).of_le hn

/-- The `(0,1)`-projections `x ↦ zeroOnePartL j x` as a smooth section of the bundle of
endomorphisms of the bundle of `V`-valued one-forms. -/
def zeroOnePartSection :
    Cₛ^∞⟮I; (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F,
      fun x ↦ (TangentSpace I x →L[ℝ] V x) →L[ℝ] TangentSpace I x →L[ℝ] V x⟯ :=
  ⟨fun x ↦ j.zeroOnePartL x, j.contMDiff_zeroOnePartL le_rfl⟩

/-- The value of `zeroOnePartSection j` at `x` is `zeroOnePartL j x`. -/
@[simp]
theorem zeroOnePartSection_apply (x : M) :
    j.zeroOnePartSection (F := F) (V := V) x = j.zeroOnePartL x :=
  (rfl)

/-! ### Continuous dependence on the almost complex structure -/

variable [ContMDiffVectorBundle ∞ F V I] [FiniteDimensional ℝ E]

/-- The section of `(0,1)`-projections depends continuously on the almost complex structure:
`J ↦ zeroOnePartSection J` is continuous from the `C^∞` topology on smooth almost complex
structures, in frames `e`, `U` of the tangent endomorphism bundle that cover `M`, to the
compact derivative topology on sections of the endomorphism bundle of the `V`-valued
one-forms, in any frames `e'`, `U'`. -/
theorem continuous_zeroOnePartSection {ι : Type*}
    (e : ι → Trivialization (E →L[ℝ] E)
      (π (E →L[ℝ] E) (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)))
    [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → TopologicalSpace.Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x, ∃ i, x ∈ U i) {κ : Type*}
    (e' : κ → Trivialization ((E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)
      (π ((E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)
        (fun x ↦ (TangentSpace I x →L[ℝ] V x) →L[ℝ] TangentSpace I x →L[ℝ] V x)))
    [∀ k, MemTrivializationAtlas (e' k)]
    (U' : κ → TopologicalSpace.Opens M) (hU' : ∀ k, (U' k : Set M) ⊆ (e' k).baseSet) :
    let _ := frameTopology e U hU
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞)
      (F := (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)
      (V := fun x ↦ (TangentSpace I x →L[ℝ] V x) →L[ℝ] TangentSpace I x →L[ℝ] V x) e' U' hU'
    Continuous fun J : SmoothAlmostComplexStructure I M ↦
      J.zeroOnePartSection (F := F) (V := V) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞)
    (F := (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)
    (V := fun x ↦ (TangentSpace I x →L[ℝ] V x) →L[ℝ] TangentSpace I x →L[ℝ] V x) e' U' hU'
  refine ((ContMDiffSection.continuous_map_frameTopology _ contMDiff_totalSpace_zeroOnePartOfEnd
    e U hU e' U' hU' hcover).comp
      (isEmbedding_toEndomorphism_frameTopology e U hU).continuous).congr fun J ↦ ?_
  refine ContMDiffSection.ext fun x ↦ ?_
  simp only [Function.comp_apply, ContMDiffSection.map_apply, zeroOnePartSection_apply]
  exact zeroOnePartOfEnd_toEndomorphism (V := V) J x

end TauCeti.SmoothAlmostComplexStructure
