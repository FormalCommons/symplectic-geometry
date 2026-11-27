/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.Basic
public import SymplecticGeometry.Geometry.Manifold.Distribution.TwoForm
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.RealChernClass
public import SymplecticGeometry.Geometry.Symplectic.Fibration.HorizontalDistribution
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
import SymplecticGeometry.Geometry.Symplectic.Fibration.Thurston

/-!
# The vertical bundle of a symplectic atlas and its real first Chern class

For a map `proj : M → B` with a smooth atlas, the kernels of the derivative of `proj` form a smooth
distribution, the vertical bundle of `proj`
(`TauCeti.MapFiber.Atlas.IsContMDiff.isContMDiffDistribution_ker_mfderiv`), and a smooth two-form
on `M` restricts to it (`TauCeti.IsContMDiffDistribution.restrictTwoForm`). The restriction of a
vertically nondegenerate form to it is nondegenerate, a symplectic structure on the vertical
bundle, and two forms that restrict to the same form on the fibre along the atlas have the same
vertical restriction. For a symplectic atlas for `(F, σ)`, the real first Chern class of this
symplectic vertical bundle is a class in the second de Rham cohomology of `M`, whose restriction
to every fibre is the real first Chern class of `σ`.

## Main definitions

* `TauCeti.MapFiber.Atlas.realFirstChernClass_vertical A`: the real first Chern class of the
  vertical bundle of a symplectic atlas `A`, with the restriction of a form that restricts to the
  fibre form along `A`.

## Main results

* `TauCeti.SmoothTwoForm.isNondegenerate_restrictTwoForm_ker_iff`: the vertical restriction of
  `τ` is nondegenerate exactly when `τ` is vertically nondegenerate; so a form that restricts to a
  nondegenerate form along a smooth atlas has a nondegenerate vertical restriction
  (`TauCeti.MapFiber.Atlas.RestrictsTo.isNondegenerate_restrictTwoForm`).
* `TauCeti.MapFiber.Atlas.RestrictsTo.restrictTwoForm_eq`: two forms that restrict to the same
  form along a smooth atlas have the same vertical restriction.
* `TauCeti.MapFiber.Atlas.realFirstChernClass_vertical_eq`: every form that restricts to the
  fibre form gives the class `realFirstChernClass_vertical A`.
* `TauCeti.MapFiber.Atlas.map_realFirstChernClass_vertical`: the pull-back of
  `realFirstChernClass_vertical A` along each fibre inclusion `j` of a chart is the real first
  Chern class of `σ`.
* `TauCeti.MapFiber.Atlas.map_inv_smul_realFirstChernClass_vertical`: the Chern class criterion;
  if `c₁(TF) = c • [σ]` with `c ≠ 0`, the class `c⁻¹ • realFirstChernClass_vertical A` restricts
  to `[σ]` on every fibre.
* `TauCeti.MapFiber.Atlas.exists_isSymplectic_compatible_of_realFirstChernClass_eq`: then, for
  compact `M` and a connected symplectic base, Thurston's theorem
  (`TauCeti.MapFiber.Atlas.exists_isSymplectic_restricts_mk_eq`) gives a symplectic form on `M`
  that restricts to `σ` along `A`.

## Implementation notes

The vertical bundle is taken as any smooth distribution `hD` whose spaces are the kernels of the
derivative of `proj`, with the bundle structure that `hD` gives, used as local instances. Since
this structure depends only on a proof, any two proofs that the vertical spaces form a smooth
distribution give the same bundle. The class is computed with a complex model `G` of complex
dimension half the rank `dim M - dim B` of the vertical bundle; the form that defines it is the
vertically closed form of `TauCeti.SmoothTwoForm.exists_restrictsTo_isVerticallyClosed`.

## Proofs

The proof of `map_realFirstChernClass_vertical` adapts that of
`TauCeti.SmoothTwoForm.IsNondegenerate.realFirstChernClass_mpullback`: the derivatives of the
fibre inclusion `j` are isomorphisms from `TF` onto the pull-back `j *ᵖ ker d proj`
(`Bundle.Trivialization.injective_mfderiv_fiberInclusionMap` and
`Bundle.Trivialization.range_mfderiv_fiberInclusionMap`), smooth on total spaces, which carry the
form of `σ = j^* τ` to the pull-back of the vertical restriction of `τ`. So the result follows from
`realFirstChernClass_pushforward` and `realFirstChernClass_pullback` for forms on bundles.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 (Lemma 6.1.7 and Corollary 6.1.8) and §6.3.
-/

public section

noncomputable section

open scoped Manifold ContDiff

/-! ### The vertical restriction of a two-form -/

namespace TauCeti.SmoothTwoForm

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M] {proj : M → B} {k : ℕ}

/-- **Nondegeneracy of the vertical restriction.** The restriction of a two-form `τ` to the
vertical bundle of `proj` is nondegenerate exactly when `τ` is vertically nondegenerate. -/
theorem isNondegenerate_restrictTwoForm_ker_iff {τ : SmoothTwoForm IM M}
    (hD : IsContMDiffDistribution IM ∞ k fun x ↦ (mfderiv IM IB proj x).ker) :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    (hD.restrictTwoForm τ).IsNondegenerate ↔ IsVerticallyNondegenerate IB proj τ :=
  hD.isNondegenerate_restrictTwoForm_iff.trans isVerticallyNondegenerate_iff.symm

end TauCeti.SmoothTwoForm

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M]
  {proj : M → B} {A : Atlas F proj} {σ : SmoothTwoForm IF F} {τ τ' : SmoothTwoForm IM M} {k : ℕ}

/-- **The vertical restriction is nondegenerate.** If `τ` restricts to a nondegenerate form `σ`
along a smooth atlas of `proj`, then its restriction to the vertical bundle of `proj` is
nondegenerate. -/
theorem RestrictsTo.isNondegenerate_restrictTwoForm (hA : A.IsContMDiff ∞ IB IF IM)
    (hσ : σ.IsNondegenerate) (hτ : A.RestrictsTo σ τ)
    (hD : IsContMDiffDistribution IM ∞ k fun x ↦ (mfderiv IM IB proj x).ker) :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    (hD.restrictTwoForm τ).IsNondegenerate :=
  (SmoothTwoForm.isNondegenerate_restrictTwoForm_ker_iff hD).2
    (hτ.isVerticallyNondegenerate hA hσ)

/-- **The vertical restriction does not depend on the form.** Two two-forms that restrict to the
same form `σ` along a smooth atlas of `proj` have the same restriction to the vertical bundle of
`proj`: the vertical space at each point is the image of the tangent space of the fibre. -/
theorem RestrictsTo.restrictTwoForm_eq (hA : A.IsContMDiff ∞ IB IF IM) (hτ : A.RestrictsTo σ τ)
    (hτ' : A.RestrictsTo σ τ')
    (hD : IsContMDiffDistribution IM ∞ k fun x ↦ (mfderiv IM IB proj x).ker) :
    hD.restrictTwoForm τ = hD.restrictTwoForm τ' := by
  refine hD.restrictTwoForm_eq_iff.2 fun x u hu v hv ↦ ?_
  have hb := A.mem_baseSet_trivAt (proj x)
  have h := (A.trivAt (proj x)).apply_eq_of_mpullback_fiberInclusionMap_eq
    (hA.mdifferentiable_trivAt (by simp) _) hb
    ((restrictsTo_iff.1 hτ _ _ hb).trans (restrictsTo_iff.1 hτ' _ _ hb).symm)
    (u := ![u, v]) fun i ↦ by fin_cases i <;> assumption
  simpa [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply] using h

end TauCeti.MapFiber.Atlas

/-! ### The real first Chern class of the vertical bundle -/

namespace TauCeti.MapFiber.Atlas

open _root_.Bundle _root_.Module SymplecticGeometry.Bundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*}
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] [T2Space B] [SigmaCompactSpace B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} [IM.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M] [T2Space M]
  [SigmaCompactSpace M]
  {proj : M → B} {A : Atlas F proj} {σ : SmoothTwoForm IF F} {τ : SmoothTwoForm IM M}
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ EM - finrank ℝ EB = 2 * finrank ℂ G)]

/-- The **real first Chern class of the vertical bundle** of a symplectic atlas `A` of
`proj : M → B` for `(F, σ)`: the real first Chern class, with complex model `G`, of the vertical
bundle `ker d proj` with the nondegenerate form `τ|_{ker d proj}`, for a two-form `τ` on `M` that
restricts to `σ` along `A`. Every such `τ` gives this class
(`TauCeti.MapFiber.Atlas.realFirstChernClass_vertical_eq`). -/
def realFirstChernClass_vertical (A : Atlas F proj) (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsSymplectic) :
    deRhamCohomology IM M 2 :=
  have hD := hA.isContMDiffDistribution_ker_mfderiv (m := ∞) le_rfl
  letI := hD.fiberBundle; letI := hD.vectorBundle; letI := hD.contMDiffVectorBundle
  ((SmoothTwoForm.exists_restrictsTo_isVerticallyClosed hA hH
    hσ.isClosed).choose_spec.1.isNondegenerate_restrictTwoForm hA hσ.isNondegenerate
      hD).realFirstChernClass G

theorem realFirstChernClass_vertical_def (A : Atlas F proj) (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsSymplectic) :
    have hD := hA.isContMDiffDistribution_ker_mfderiv (m := ∞) le_rfl
    letI := hD.fiberBundle; letI := hD.vectorBundle; letI := hD.contMDiffVectorBundle
    A.realFirstChernClass_vertical G hA hH hσ =
      ((SmoothTwoForm.exists_restrictsTo_isVerticallyClosed hA hH
        hσ.isClosed).choose_spec.1.isNondegenerate_restrictTwoForm hA hσ.isNondegenerate
          hD).realFirstChernClass G :=
  (rfl)

/-- **The class of the vertical bundle does not depend on the form.** For every two-form `τ`
that restricts to `σ` along a symplectic atlas `A`, the real first Chern class of the vertical
bundle with the restriction of `τ` is `realFirstChernClass_vertical A`. -/
theorem realFirstChernClass_vertical_eq (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsSymplectic)
    (hτ : A.RestrictsTo σ τ)
    (hD : IsContMDiffDistribution IM ∞ (finrank ℝ EM - finrank ℝ EB)
      fun x ↦ (mfderiv IM IB proj x).ker) :
    letI := hD.fiberBundle; letI := hD.vectorBundle; letI := hD.contMDiffVectorBundle
    A.realFirstChernClass_vertical G hA hH hσ =
      (hτ.isNondegenerate_restrictTwoForm hA hσ.isNondegenerate hD).realFirstChernClass G := by
  let := hD.fiberBundle; let := hD.vectorBundle; let := hD.contMDiffVectorBundle
  have key : ∀ {β β' : ContMDiffTwoForm IM ⊤ (Fin (finrank ℝ EM - finrank ℝ EB) → ℝ)
      (fun x ↦ (mfderiv IM IB proj x).ker)} (_ : β = β') (h : β.IsNondegenerate)
      (h' : β'.IsNondegenerate), h.realFirstChernClass G = h'.realFirstChernClass G := by
    rintro _ _ rfl _ _; rfl
  exact key (RestrictsTo.restrictTwoForm_eq hA
    (SmoothTwoForm.exists_restrictsTo_isVerticallyClosed hA hH hσ.isClosed).choose_spec.1 hτ hD)
      _ _

/-- **The class of the vertical bundle restricts to the class of the fibre.** For a symplectic
atlas `A` of `proj` for `(F, σ)`, the pull-back of `realFirstChernClass_vertical A` along the
fibre inclusion of a chart of `A` over a point of its base set is the real first Chern class of
`σ`. -/
theorem map_realFirstChernClass_vertical [FiniteDimensional ℝ EF] [IF.Boundaryless] [T2Space F]
    [SigmaCompactSpace F] (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G']
    [FiniteDimensional ℂ G'] [Fact (finrank ℝ EF = 2 * finrank ℂ G')]
    (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsSymplectic)
    {b b' : B} (hb' : b' ∈ (A.trivAt b).baseSet) :
    deRhamCohomology.map ((A.trivAt b).fiberInclusionMap hb')
        ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb') 2
        (A.realFirstChernClass_vertical G hA hH hσ) =
      hσ.isNondegenerate.realFirstChernClass G' := by
  set j := (A.trivAt b).fiberInclusionMap hb'
  have hj : ContMDiff IF IM ∞ j :=
    (A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb'
  have hdj := hA.mdifferentiable_trivAt (by simp) b
  have hD := hA.isContMDiffDistribution_ker_mfderiv (m := ∞) le_rfl
  let := hD.fiberBundle; let := hD.vectorBundle; let := hD.contMDiffVectorBundle
  let k := finrank ℝ EM - finrank ℝ EB
  let V := fun x ↦ (mfderiv IM IB proj x).ker
  have := _root_.Bundle.Pullback.contMDiffVectorBundle (F := Fin k → ℝ) (E := fun x ↦ V x) hj
  -- The derivative of `j` at `y` is an isomorphism from `T_y F` onto the vertical space at `j y`.
  let Φ (y : F) : TangentSpace IF y ≃L[ℝ] ((j : F → M) *ᵖ (fun x ↦ V x)) y :=
    ((LinearEquiv.ofInjective _ ((A.trivAt b).injective_mfderiv_fiberInclusionMap hdj hb' y)).trans
      (LinearEquiv.ofEq _ _
        ((A.trivAt b).range_mfderiv_fiberInclusionMap hdj hb' y))).toContinuousLinearEquiv
  have hΦ : ContMDiff (IF.prod 𝓘(ℝ, EF)) (IF.prod 𝓘(ℝ, Fin k → ℝ)) ∞
      (fun p : TangentBundle IF F ↦ TotalSpace.mk' (Fin k → ℝ) p.proj (Φ p.proj p.snd)) := by
    rw [_root_.Bundle.Pullback.contMDiff_iff j hj]
    exact ⟨contMDiff_proj _, fun p ↦ hD.contMDiffAt_totalSpace_mk
      (b := fun p : TangentBundle IF F ↦ j p.proj)
      (w := fun p ↦ mfderiv IF IM j p.proj p.snd) (hj.contMDiff_tangentMap (by simp) p)
      fun p ↦ (Φ p.proj p.snd).property⟩
  obtain ⟨hτ, -⟩ := (SmoothTwoForm.exists_restrictsTo_isVerticallyClosed hA hH
    hσ.isClosed).choose_spec
  have hτj := hτ.mpullback_fiberInclusionMap_eq hA hb'
  have hV := hτ.isNondegenerate_restrictTwoForm hA hσ.isNondegenerate hD
  rw [realFirstChernClass_vertical_def,
    ← ContMDiffTwoForm.IsNondegenerate.realFirstChernClass_pullback G hV j hj,
    SmoothTwoForm.IsNondegenerate.realFirstChernClass_def,
    ContMDiffTwoForm.IsNondegenerate.realFirstChernClass_pushforward G' G _ (hV.pullback j hj) Φ hΦ]
  intro y v w
  rw [ContMDiffTwoForm.bilinFormAt_pullback, IsContMDiffDistribution.bilinFormAt_restrictTwoForm,
    ContMDiffTwoForm.bilinFormAt_tangentEquiv_symm]
  conv_rhs => rw [← hτj, SmoothForm.bilinFormAt_mpullback]
  -- The fibre `(j *ᵖ V) y` is `V (j y)` only by definition, so the lemmas on `restrict` do not
  -- match; both sides are `τ_{j y} (dj v, dj w)`, by the definition of `Φ`.
  rfl

/-! ### The Chern class criterion -/

/-- **The Chern class criterion.** Let `A` be a symplectic atlas of `proj : M → B` for `(F, σ)`
such that `c₁(TF) = c • [σ]` in `H²(F; ℝ)` for a real `c ≠ 0`. Then the fibre inclusion of every
chart of `A` over every point of its base set pulls `c⁻¹ • realFirstChernClass_vertical A` back
to `[σ]`.

Milestone: *Chern class criterion for compatible symplectic forms*. -/
theorem map_inv_smul_realFirstChernClass_vertical [FiniteDimensional ℝ EF] [IF.Boundaryless]
    [T2Space F] [SigmaCompactSpace F] (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G']
    [FiniteDimensional ℂ G'] [Fact (finrank ℝ EF = 2 * finrank ℂ G')]
    (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsSymplectic)
    {c : ℝ} (hc : c ≠ 0)
    (hσc : hσ.isNondegenerate.realFirstChernClass G' =
      c • deRhamCohomology.mk IF 2 ⟨σ, hσ.isClosed.mem_closedForms⟩)
    {b b' : B} (hb' : b' ∈ (A.trivAt b).baseSet) :
    deRhamCohomology.map ((A.trivAt b).fiberInclusionMap hb')
        ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb') 2
        (c⁻¹ • A.realFirstChernClass_vertical G hA hH hσ) =
      deRhamCohomology.mk IF 2 ⟨σ, hσ.isClosed.mem_closedForms⟩ := by
  rw [map_smul, map_realFirstChernClass_vertical G G' hA hH hσ hb', hσc, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

include G in
/-- **Compatible symplectic forms from the Chern class criterion.** Let `A` be a symplectic atlas
of `proj : M → B` for `(F, σ)` such that `c₁(TF) = c • [σ]` in `H²(F; ℝ)` for a real `c ≠ 0`. If
`M` is compact and `B` is connected and has a symplectic form `β`, then some symplectic form on
`M` restricts to `σ` along `A`. Here `G` is a complex vector space whose real dimension is the
rank of the vertical bundle; it is needed only to define `realFirstChernClass_vertical A`.

This is the consequence that the milestone *Chern class criterion for compatible symplectic forms*
states, there for a compact base: Thurston's theorem applies to the class
`c⁻¹ • realFirstChernClass_vertical A`. -/
theorem exists_isSymplectic_compatible_of_realFirstChernClass_eq [FiniteDimensional ℝ EF]
    [IF.Boundaryless] [T2Space F] [SigmaCompactSpace F] [CompactSpace M] [ConnectedSpace B]
    (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
    [Fact (finrank ℝ EF = 2 * finrank ℂ G')] (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ)) (hσ : σ.IsSymplectic)
    {c : ℝ} (hc : c ≠ 0)
    (hσc : hσ.isNondegenerate.realFirstChernClass G' =
      c • deRhamCohomology.mk IF 2 ⟨σ, hσ.isClosed.mem_closedForms⟩)
    {β : SmoothTwoForm IB B} (hβ : β.IsSymplectic) :
    ∃ θ : SmoothTwoForm IM M, θ.IsSymplectic ∧ A.RestrictsTo σ θ := by
  obtain ⟨b⟩ := ‹ConnectedSpace B›.toNonempty
  obtain ⟨K₀, hK₀⟩ := exists_isSymplectic_restricts_mk_eq hA hH hσ hβ (A.mem_baseSet_trivAt b)
    (map_inv_smul_realFirstChernClass_vertical G G' hA hH hσ hc hσc (A.mem_baseSet_trivAt b))
  obtain ⟨θ, hθ, hθA, -⟩ := hK₀ K₀ le_rfl
  exact ⟨θ, hθ, hθA⟩

end TauCeti.MapFiber.Atlas

end
