/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.ComplexStructure.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.FirstChernClass
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Pullback
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Family
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.TimeExtension

/-!
# The first Chern class of a nondegenerate two-form

Consider a nondegenerate smooth two-form `σ` on a Hausdorff σ-compact manifold `M` modelled on a
finite-dimensional space. Its first Chern class `c₁(σ) ∈ H²(M; ℤ)`,
`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernClass`, is the first Chern class
`TauCeti.firstChernClass` of the complex vector bundle `(TM, J)` for an almost
complex structure `J` compatible with `σ`, chosen by Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`. This file shows that the choice does
not matter, and that the class does not change along a family of nondegenerate forms:

* `IsNondegenerate.firstChernClass_eq_of_tames`, `IsNondegenerate.firstChernClass_eq_of_compatible`:
  every almost complex structure tamed by `σ`, in particular every compatible one, gives `c₁(σ)`;
* `IsNondegenerate.firstChernClass_congr`: equal forms have equal classes, whatever the proofs of
  nondegeneracy;
* `IsNondegenerate.firstChernClass_congr_model`: the class does not depend on the complex model
  `G` of the tangent spaces;
* `firstChernClass_mpullback_prodMk_eq`: for a smooth two-form on `ℝ × M` whose slices
  `σ_t = ι_t^* σ` are nondegenerate for `t ∈ [0, 1]`, `c₁(σ₀) = c₁(σ₁)`;
* `SymplecticGeometry.IsSmoothFamily.firstChernClass_eq`: the same for a smooth family of
  nondegenerate two-forms over `[0, 1]`, which `IsSmoothFamily.exists_extend` reads over `ℝ`;
* `firstChernClass_wellDefined`: the statements for compatible and tamed structures and
  `firstChernClass_mpullback_prodMk_eq` together.

The family statement is proved over `ℝ × M`: the slices form a nondegenerate two-form on the
pull-back of `TM` along the projection `ℝ × M → M`, which is compatible with some complex
structure `J`. Its restrictions to the slices `{t} × M` are complex structures on `TM` tamed by
`σ_t`, whose classes are the pull-backs of the class of `J` along the inclusions `ι_t`. These
inclusions are homotopic, so they induce the same map on cohomology. A reparametrization by
`Real.smoothTransition` first reduces the case of nondegenerate slices for `t ∈ [0, 1]` to that
of nondegenerate slices for every `t`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §4.1
  (Definition 4.1.4) and §2.6 (Proposition 2.6.4).
-/

public section

noncomputable section

open _root_.Bundle Module Set SymplecticGeometry.Bundle TauCeti.Bundle.ContinuousComplexStructure
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E : Type} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)]

/-- The **first Chern class** `c₁(σ) ∈ H²(M; ℤ)` of a nondegenerate two-form `σ`: the first
Chern class of the complex vector bundle `(TM, J)`, with model `G`, for an almost complex
structure `J` compatible with `σ`. By `IsNondegenerate.firstChernClass_eq_of_tames`, every almost
complex structure tamed by `σ` gives this class. -/
def IsNondegenerate.firstChernClass {σ : SmoothTwoForm I M} (h : σ.IsNondegenerate) :
    (TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift ℤ)) ℤ (ModuleCat.of ℤ (ULift ℤ)) 2 :=
  TauCeti.firstChernClass G
    (h.exists_compatible.choose.toContMDiff ⊤).toContinuousComplexStructure.Fiber

theorem IsNondegenerate.firstChernClass_def {σ : SmoothTwoForm I M} (h : σ.IsNondegenerate) :
    h.firstChernClass G = TauCeti.firstChernClass G
      (h.exists_compatible.choose.toContMDiff ⊤).toContinuousComplexStructure.Fiber := (rfl)

/-- Equal nondegenerate two-forms have equal first Chern classes, whatever the proofs of their
nondegeneracy. -/
theorem IsNondegenerate.firstChernClass_congr {σ σ' : SmoothTwoForm I M} (h : σ.IsNondegenerate)
    (h' : σ'.IsNondegenerate) (he : σ = σ') : h.firstChernClass G = h'.firstChernClass G := by
  subst he
  rfl

/-- The first Chern class of a nondegenerate two-form `σ` is that of the complex bundle `(TM, J)`
for any complex structure `J` on `TM`, of any regularity, tamed by the two-form on `TM` that
corresponds to `σ`. -/
theorem IsNondegenerate.firstChernClass_eq_of_tangentEquiv_symm_tames {σ : SmoothTwoForm I M}
    (h : σ.IsNondegenerate) {m : ℕ∞}
    {J : ContMDiffComplexStructure I m E (TangentSpace I : M → Type _)}
    (hJ : (ContMDiffTwoForm.tangentEquiv.symm σ).Tames J) :
    h.firstChernClass G =
      TauCeti.firstChernClass G J.toContinuousComplexStructure.Fiber := by
  have hc := ContMDiffTwoForm.compatible_tangentEquiv_symm_iff.2 h.exists_compatible.choose_spec
  rw [firstChernClass_def,
    ← ContMDiffComplexStructure.toContinuousComplexStructure_tangentEquiv_symm]
  exact (hc.tames.firstChernClass_eq G hJ).symm

/-- **The first Chern class of a nondegenerate two-form is that of any tamed almost complex
structure.** If `σ` tames a smooth almost complex structure `J`, then `c₁(σ)` is the first Chern
class of the complex vector bundle `(TM, J)`. -/
theorem IsNondegenerate.firstChernClass_eq_of_tames {σ : SmoothTwoForm I M}
    (h : σ.IsNondegenerate) {J : SmoothAlmostComplexStructure I M} (hJ : σ.Tames J) :
    h.firstChernClass G = TauCeti.firstChernClass G
      (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber := by
  rw [h.firstChernClass_eq_of_tangentEquiv_symm_tames G
      (ContMDiffTwoForm.tames_tangentEquiv_symm_iff.2 hJ),
    ContMDiffComplexStructure.toContinuousComplexStructure_tangentEquiv_symm]

/-- **The first Chern class of a nondegenerate two-form is that of any compatible almost complex
structure.** -/
theorem IsNondegenerate.firstChernClass_eq_of_compatible {σ : SmoothTwoForm I M}
    (h : σ.IsNondegenerate) {J : SmoothAlmostComplexStructure I M} (hJ : σ.Compatible J) :
    h.firstChernClass G = TauCeti.firstChernClass G
      (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber :=
  h.firstChernClass_eq_of_tames G hJ.tames

/-- **The first Chern class of a nondegenerate two-form does not depend on the complex model** `G`
of the complex tangent bundle it is computed from. -/
theorem IsNondegenerate.firstChernClass_congr_model
    (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
    [Fact (finrank ℝ E = 2 * finrank ℂ G')] {σ : SmoothTwoForm I M} (h : σ.IsNondegenerate) :
    h.firstChernClass G' = h.firstChernClass G := by
  rw [firstChernClass_def, firstChernClass_def]
  exact TauCeti.Bundle.ContinuousComplexStructure.firstChernClass_congr_model G _ G'

/-! ### Families of nondegenerate two-forms -/

/-- The case of `firstChernClass_mpullback_prodMk_eq` in which every slice is nondegenerate. -/
private theorem firstChernClass_mpullback_prodMk_eq_of_forall
    (σ : SmoothTwoForm (𝓘(ℝ, ℝ).prod I) (ℝ × M))
    (h : ∀ t, IsNondegenerate
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ)) :
    (h 0).firstChernClass G = (h 1).firstChernClass G := by
  -- The slices, as a two-form on the pull-back of `TM` to `ℝ × M`.
  let Ω : ContMDiffTwoForm (𝓘(ℝ, ℝ).prod I) ⊤ E (verticalTangentBundle I M 𝓘(ℝ, ℝ) ℝ) :=
    ⟨fun p ↦ (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) σ).val p.2,
      (Pullback.contMDiff_continuousAlternatingMap_section_iff _ ContMDiffMap.snd.contMDiff _).2
        (SmoothForm.contMDiff_mpullback_prodMk σ)⟩
  have hΩ : Ω.IsNondegenerate := ContMDiffTwoForm.isNondegenerate_def.2 fun p ↦ by
    have hp := ContMDiffTwoForm.isNondegenerate_def.1
      (ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff.2 (h p.1)) p.2
    rw [ContMDiffTwoForm.bilinFormAt_def, ContMDiffTwoForm.tangentEquiv_symm_apply] at hp
    rw [ContMDiffTwoForm.bilinFormAt_def]
    -- `Ω p` is, by its definition, the slice at `p.1` evaluated at `p.2`.
    exact hp
  obtain ⟨J, hJ⟩ := hΩ.exists_compatible
  let ι (t : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ).prod I, ℝ × M⟯ :=
    ⟨Prod.mk t, contMDiff_const.prodMk contMDiff_id⟩
  have key (t : ℝ) : (h t).firstChernClass G =
      TopCat.singularCohomologyMap (TopCat.ofHom (ι t : C(M, ℝ × M))) 2
        (TauCeti.firstChernClass G J.toContinuousComplexStructure.Fiber) := by
    -- The pull-back of `TM` along `ι t` and then the projection is `TM`.
    let Φ : ∀ x, ((ι t : M → ℝ × M) *ᵖ (verticalTangentBundle I M 𝓘(ℝ, ℝ) ℝ)) x ≃L[ℝ]
        TangentSpace I x := fun x ↦ ContinuousLinearEquiv.refl ℝ (TangentSpace I x)
    have hΦ : ContMDiff (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : TotalSpace E ((ι t : M → ℝ × M) *ᵖ (verticalTangentBundle I M 𝓘(ℝ, ℝ) ℝ)) ↦
          TotalSpace.mk' E p.proj (Φ p.proj p.snd)) :=
      ((Pullback.contMDiff_lift _ ContMDiffMap.snd.contMDiff).comp
        (Pullback.contMDiff_lift _ (ι t).contMDiff)).congr fun p ↦
        -- Lifting along `ι t` and then along the projection returns to the base point of `p`.
        rfl
    have ht : (ContMDiffTwoForm.tangentEquiv.symm
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ)).Tames
        ((J.pullback (ι t) (ι t).contMDiff).pushforward Φ hΦ) := by
      have := (hJ.tames.pullback (ι t) (ι t).contMDiff).pushforward Φ hΦ hΦ
      have hp : ContMDiffTwoForm.pushforward Φ hΦ (Ω.pullback (ι t) (ι t).contMDiff) =
          ContMDiffTwoForm.tangentEquiv.symm
            (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) :=
        (ContMDiffTwoForm.pushforward_eq_iff Φ hΦ).2 fun x v w ↦ by
          rw [ContMDiffTwoForm.bilinFormAt_apply, ContMDiffTwoForm.bilinFormAt_apply,
            ContMDiffTwoForm.pullback_apply, ContMDiffTwoForm.tangentEquiv_symm_apply]
          -- `Ω (ι t x)` is the slice at `t` evaluated at `x`, and `Φ x` is the identity.
          rfl
      rwa [hp] at this
    rw [(h t).firstChernClass_eq_of_tangentEquiv_symm_tames G ht,
      ContMDiffComplexStructure.firstChernClass_pushforward G G Φ hΦ,
      ContMDiffComplexStructure.firstChernClass_pullback]
  -- The inclusions `ι 0` and `ι 1` are homotopic.
  -- The ends of `s ↦ (s, x)` are `ι 0 x` and `ι 1 x` by definition.
  let H : TopCat.Homotopy (TopCat.ofHom (ι 0 : C(M, ℝ × M))) (TopCat.ofHom (ι 1 : C(M, ℝ × M))) :=
    { toFun := fun q ↦ ((q.1 : ℝ), q.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl }
  rw [key 0, key 1, H.congr_singularCohomologyMap]

/-- **The first Chern class is constant along a family of nondegenerate two-forms.** For a smooth
two-form `σ` on `ℝ × M` whose slices `σ_t = ι_t^* σ`, along the inclusions `ι_t : x ↦ (t, x)`,
are nondegenerate for `t ∈ [0, 1]`, the slices `σ₀` and `σ₁` have the same first Chern class. -/
theorem firstChernClass_mpullback_prodMk_eq (σ : SmoothTwoForm (𝓘(ℝ, ℝ).prod I) (ℝ × M))
    (h : ∀ t ∈ Icc (0 : ℝ) 1, IsNondegenerate (SmoothForm.mpullback (Prod.mk t)
      (contMDiff_const.prodMk contMDiff_id) σ)) :
    (h 0 (left_mem_Icc.2 zero_le_one)).firstChernClass G =
      (h 1 (right_mem_Icc.2 zero_le_one)).firstChernClass G := by
  -- Reparametrize by a smooth map `ℝ → [0, 1]` fixing `0` and `1`.
  have hρ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    Real.smoothTransition.contDiff.contMDiff
  have hs (t : ℝ) := SmoothForm.mpullback_prodMk_mpullback_prodMap_id σ hρ t
  have h' (t : ℝ) := hs t ▸
    h _ ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  rw [IsNondegenerate.firstChernClass_congr G _ (h' 0) (by rw [hs, Real.smoothTransition.zero]),
    firstChernClass_mpullback_prodMk_eq_of_forall G _ h',
    IsNondegenerate.firstChernClass_congr G (h' 1) _ (by rw [hs, Real.smoothTransition.one])]

/-- **The first Chern class of a nondegenerate two-form.** On a Hausdorff σ-compact manifold `M`
modelled on a finite-dimensional space:

* for a nondegenerate two-form `σ`, every almost complex structure `J` compatible with `σ` gives
  the same first Chern class `c₁(TM, J)`, namely `c₁(σ)`;
* every almost complex structure tamed by `σ` gives the class `c₁(σ)` too;
* for a smooth two-form on `ℝ × M` whose slices `σ_t` are nondegenerate for `t ∈ [0, 1]`,
  `c₁(σ₀) = c₁(σ₁)`.

Milestone: *First Chern class of a nondegenerate two-form*. -/
theorem firstChernClass_wellDefined :
    (∀ {σ : SmoothTwoForm I M} (h : σ.IsNondegenerate) (J : SmoothAlmostComplexStructure I M),
      σ.Compatible J → h.firstChernClass G = TauCeti.firstChernClass G
        (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber) ∧
    (∀ {σ : SmoothTwoForm I M} (h : σ.IsNondegenerate) (J : SmoothAlmostComplexStructure I M),
      σ.Tames J → h.firstChernClass G = TauCeti.firstChernClass G
        (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber) ∧
    (∀ (σ : SmoothTwoForm (𝓘(ℝ, ℝ).prod I) (ℝ × M))
      (h : ∀ t ∈ Icc (0 : ℝ) 1, IsNondegenerate (SmoothForm.mpullback (Prod.mk t)
        (contMDiff_const.prodMk contMDiff_id) σ)),
      (h 0 (left_mem_Icc.2 zero_le_one)).firstChernClass G =
        (h 1 (right_mem_Icc.2 zero_le_one)).firstChernClass G) :=
  ⟨fun h _ hJ ↦ h.firstChernClass_eq_of_compatible G hJ,
    fun h _ hJ ↦ h.firstChernClass_eq_of_tames G hJ,
    fun σ h ↦ firstChernClass_mpullback_prodMk_eq G σ h⟩

end TauCeti.SmoothTwoForm

namespace SymplecticGeometry

open TauCeti

variable {E : Type} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)]

/-- **The first Chern class is constant along a smooth family of nondegenerate forms.** For a
smooth family `τ` over `[0, 1]` of two-forms that are all nondegenerate, `τ 0` and `τ 1` have the
same first Chern class. -/
theorem IsSmoothFamily.firstChernClass_eq {τ : unitInterval → SmoothTwoForm I M}
    (hτ : IsSmoothFamily (𝓡∂ 1) τ) (h : ∀ t, (τ t).IsNondegenerate) :
    (h 0).firstChernClass G = (h 1).firstChernClass G := by
  obtain ⟨β, hβ, hβτ⟩ := hτ.exists_extend
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.1 hβ
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω = τ ⟨t, ht⟩ :=
    (hΩ t).trans (hβτ ⟨t, ht⟩)
  have h' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := (hs t ht).symm ▸ h ⟨t, ht⟩
  have key := SmoothTwoForm.firstChernClass_mpullback_prodMk_eq G Ω h'
  -- The two ends of `key` are the classes of `τ 0` and `τ 1`, for other proofs of
  -- nondegeneracy.
  calc (h 0).firstChernClass G = (h' 0 (left_mem_Icc.2 zero_le_one)).firstChernClass G :=
        (h 0).firstChernClass_congr G _ (hs 0 _).symm
    _ = (h' 1 (right_mem_Icc.2 zero_le_one)).firstChernClass G := key
    _ = (h 1).firstChernClass G :=
        (h' 1 (right_mem_Icc.2 zero_le_one)).firstChernClass_congr G _ (hs 1 _)

end SymplecticGeometry
