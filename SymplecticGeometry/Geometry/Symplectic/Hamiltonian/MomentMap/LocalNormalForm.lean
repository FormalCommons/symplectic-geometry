/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Tube
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Nondegenerate
import SymplecticGeometry.Geometry.Symplectic.Moser.Equivariant
import SymplecticGeometry.Geometry.Manifold.GroupAction.Opens
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# The local normal form near an orbit

Let a compact Hausdorff Lie group `G` act smoothly on a manifold `M` with a closed `G`-invariant
two-form `σ`, let `x : M` with stabilizer `H = G_x`, and let `D` be data of a
local model `Y = G ×_H (A × V)` with descended form `ω`. Given a linear isomorphism
`T : T_{[1, 0]} Y ≃ T_x M` that is `H`-equivariant, sends `dπ_(1, 0, 0) (ξ, 0)` to `ξ_M(x)` and
takes `σ_x` to `ω_{[1, 0]}` (such as the one of
`SymplecticGeometry.LocalModelData.exists_linearEquiv_tangentSpace_ofPoint`), this file gives a
`G`-invariant open neighbourhood `N` of the zero section of `Y` and a smooth `G`-equivariant map
`Ψ : N → M`, a local diffeomorphism at every point, with `Ψ [g, 0] = g • x` and `Ψ^* σ = ω` on
`N`.

The proof corrects an equivariant map by the equivariant relative Moser theorem
(`SymplecticGeometry.LocalModelData.exists_mpullback_eq_descendedForm_of_isLocalDiffeomorphAt`).
Let `Ψ₀ : Y → M` be `G`-equivariant with `Ψ₀ [1, 0] = x`, a local diffeomorphism along the zero
section, whose differential at `[1, 0]` takes `σ_x` to `ω_{[1, 0]}`. On the open set `N₀` of the
points at which `Ψ₀` is a local diffeomorphism, invariant by
`SymplecticGeometry.isLocalDiffeomorphAt_smul_iff`, the forms `σ₀ = ω` and `σ₁ = Ψ₀^* σ` are closed
and invariant (`SymplecticGeometry.LocalModelData.mpullback_smul_descendedForm`,
`TauCeti.SmoothForm.mpullback_smul_mpullback`), `σ₀` is nondegenerate along the zero section
(`SymplecticGeometry.LocalModelData.nondegenerate_bilinFormAt_descendedForm_mk_zero`), and the
two agree there (`SymplecticGeometry.LocalModelData.mpullback_subtypeVal_apply_mk_zero_eq`). The
zero section `G ⧸ H → Y` is a smooth embedding with invariant image
(`TauCeti.BalancedProduct.isSmoothEmbedding_zeroSectionRightTranslation`), so
`TauCeti.SmoothEmbedding.exists_equivariant_diffeomorph_opens_le_of_eq_along` gives an
equivariant diffeomorphism `φ : U₀ ≃ U₁` between invariant open sets of `N₀` around it, fixing
it, with `φ^* σ₁ = σ₀`; then `Ψ = Ψ₀ ∘ φ` on `N = U₀`. The space `Y` is Hausdorff, as the
quotient of `G × (A × V)` by a proper action, and second countable, since `G` is compact, as
that theorem requires. The tube map of
`SymplecticGeometry.LocalModelData.exists_isLocalDiffeomorphAt`, whose differential at `[1, 0]`
is `T`, is such a `Ψ₀`.

## Main results

* `SymplecticGeometry.LocalModelData.exists_mpullback_eq_descendedForm_of_isLocalDiffeomorphAt`:
  the Moser correction of an equivariant map `Ψ₀` as above.
* `SymplecticGeometry.LocalModelData.exists_isLocalDiffeomorph_mpullback_eq_descendedForm`: the
  equivariant local diffeomorphism `Ψ` from a neighbourhood of the zero section of the local
  model to `M` that pulls `σ` back to the descended form.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open Function MulAction TauCeti TauCeti.Lie TauCeti.Manifold TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G] [T2Space G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] {x : M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [IsClosed (stabilizer G x : Set G)] [CompactSpace (stabilizer G x)]
  [ChartedSpace F (stabilizer G x)] [LieGroup 𝓘(ℝ, F) ∞ (stabilizer G x)]
  [ContMDiffSMul 𝓘(ℝ, F) I ∞ (stabilizer G x) G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) (stabilizer G x) (F := F) V A)

namespace LocalModelData

omit [FiniteDimensional ℝ E'] [I'.Boundaryless] [T2Space M] in
/-- **The Moser correction of an equivariant map near the zero section.** Let a compact Hausdorff
Lie group `G` act smoothly on `M`, let `σ` be a closed `G`-invariant two-form on `M`, and let `D`
be data of a local model `Y = G ×_H (A × V)` whose subgroup `H = G_x` is the stabilizer of `x`,
with descended form `ω`. Let `Ψ₀ : Y → M` be a `G`-equivariant map with `Ψ₀ [1, 0] = x`, a local
diffeomorphism at every point `[g, 0]` of the zero section, whose differential `dΨ₀` at `[1, 0]`
satisfies `σ_x (dΨ₀ u, dΨ₀ v) = ω_{[1, 0]} (u, v)`. Then there are a `G`-invariant open set `N`
of `Y` containing every point `[g, 0]` and a smooth map `Ψ : N → M`, `G`-equivariant, with
`Ψ [g, 0] = g • x`, a local diffeomorphism at every point of `N`, that pulls `σ` back to the
restriction of `ω` to `N`. -/
theorem exists_mpullback_eq_descendedForm_of_isLocalDiffeomorphAt :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I
      𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
      (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∀ {σ : SmoothTwoForm I' M}, σ.IsClosed → (∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
        (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ) →
    ∀ {Ψ₀ : BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V) → M},
      (∀ (g : G) y, Ψ₀ (g • y) = g • Ψ₀ y) →
      Ψ₀ (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
        ((0 : A), (0 : V))) = x →
      (∀ g : G, IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ₀
        (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation g)
          ((0 : A), (0 : V)))) →
      (∀ u v, SmoothBundleForm.eval₂ σ x
          (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
            (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
              ((0 : A), (0 : V))) u)
          (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
            (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
              ((0 : A), (0 : V))) v) =
        SmoothBundleForm.eval₂ D.descendedForm
          (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
            ((0 : A), (0 : V))) u v) →
      ∃ (N : Opens (BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V)))
        (Ψ : N → M) (hΨ : ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ),
        (∀ g : G, BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation g)
          ((0 : A), (0 : V)) ∈ N) ∧
        (∀ (g : G) y, y ∈ N → g • y ∈ N) ∧
        (∀ (g : G) (y : N) (h : g • (y : BalancedProduct _ _ _) ∈ N),
          Ψ ⟨g • (y : BalancedProduct _ _ _), h⟩ = g • Ψ y) ∧
        (∀ (g : G) (h : BalancedProduct.mk (stabilizer G x)
            ((stabilizer G x).toRightTranslation g) ((0 : A), (0 : V)) ∈ N),
          Ψ ⟨_, h⟩ = g • x) ∧
        (∀ y, IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ y) ∧
        SmoothForm.mpullback Ψ hΨ σ =
          SmoothForm.mpullback (Subtype.val : N → _) contMDiff_subtypeVal D.descendedForm := by
  intro σ hσc hσ Ψ₀ hΨ₀G hΨ1 hΨ₀d hT'
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
    (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
  have := BalancedProduct.contMDiffSMul_rightTranslation (K := stabilizer G x) (Z := A × V)
    (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
  -- The topological hypotheses of the Moser theorem on `Y`: `Y` is a quotient of
  -- `G × (A × V)` by a proper action, and `G` is a compact manifold.
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, A × V))
    (G := stabilizer G x) (M := A × V) ∞
  have : SecondCountableTopology H := I.isClosedEmbedding.isInducing.secondCountableTopology
  have := ChartedSpace.secondCountable_of_sigmaCompact H G
  have : SecondCountableTopology (stabilizer G x).RightTranslation :=
    inferInstanceAs (SecondCountableTopology G)
  have : SecondCountableTopology
      (BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V)) :=
    ContinuousConstSMul.secondCountableTopology
  have : T2Space (BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V)) :=
    t2Space_quotient_mulAction_of_properSMul
  have : ContMDiffConstSMul I' ∞ G M := ContMDiffSMul.contMDiffConstSMul I
  have : ContMDiffConstSMul 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) ∞ G
      (BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V)) :=
    ContMDiffSMul.contMDiffConstSMul I
  have hΨ₀0 (g : G) : Ψ₀ (BalancedProduct.mk (stabilizer G x)
      ((stabilizer G x).toRightTranslation g) ((0 : A), (0 : V))) = g • x := by
    have h := hΨ₀G g (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation 1)
      ((0 : A), (0 : V)))
    rwa [BalancedProduct.smul_mk_toRightTranslation, mul_one, hΨ1] at h
  -- The invariant open set `N₀` where `Ψ₀` is a local diffeomorphism.
  let N₀ : Opens (BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V)) :=
    ⟨{y | IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ₀ y},
      isOpen_iff_mem_nhds.2 fun _ hy ↦ hy.eventually⟩
  have hN₀ (y) : y ∈ N₀ ↔
      IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ₀ y := by
    rw [Opens.mem_mk, Set.mem_ofPred_eq]
  have hN₀0 (g : G) : BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation g)
      ((0 : A), (0 : V)) ∈ N₀ := (hN₀ _).2 (hΨ₀d g)
  have hN₀G (g : G) (y) (hy : y ∈ N₀) : g • y ∈ N₀ :=
    (hN₀ _).2 ((isLocalDiffeomorphAt_smul_iff hΨ₀G g).2 ((hN₀ _).1 hy))
  let : MulAction G N₀ := Opens.mulActionOfForallSMulMem hN₀G
  have hcN₀ := Opens.coe_smul_mulActionOfForallSMulMem hN₀G
  have : ContMDiffSMul I 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) ∞ G N₀ :=
    Opens.contMDiffSMul_of_coe_smul hcN₀
  have : ContMDiffConstSMul 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) ∞ G N₀ :=
    Opens.contMDiffConstSMul_of_coe_smul hcN₀
  have hΨ₀N : ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞
      (Ψ₀ ∘ (Subtype.val : N₀ → _)) := fun y ↦
    ((hN₀ _).1 y.property).contMDiffAt.comp y contMDiff_subtypeVal.contMDiffAt
  -- The zero section, a smooth embedding of `G ⧸ H` with invariant image in `N₀`.
  have hz₀ : ((0 : A), (0 : V)) ∈ MulAction.fixedPoints (stabilizer G x) (A × V) :=
    fun k ↦ smul_zero k
  let := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (stabilizer G x : Set G)›
  have := Subgroup.isManifold_quotientOfIsClosed (I := I) ‹IsClosed (stabilizer G x : Set G)›
  let f := SmoothEmbedding.ofIsSmoothEmbedding _
    (BalancedProduct.isSmoothEmbedding_zeroSectionRightTranslation (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F) hz₀)
  have hf (g : G) : f g = BalancedProduct.mk (stabilizer G x)
      ((stabilizer G x).toRightTranslation g) ((0 : A), (0 : V)) := by
    simp [f, BalancedProduct.zeroSectionRightTranslation_mk]
  have hfG (g : G) (q) : g • f q ∈ Set.range f := by
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨(g * g' : G), by rw [hf, hf, BalancedProduct.smul_mk_toRightTranslation]⟩
  have hfW : Set.range f ⊆ N₀ := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hf]
    exact hN₀0 g
  -- The forms `σ₀ = ω` and `σ₁ = Ψ₀^* σ` on `N₀`.
  obtain ⟨U₀, U₁, hU₀, hU₁, φ, hU₀G, -, hφG, hφf, hφσ⟩ :=
    SmoothEmbedding.exists_equivariant_diffeomorph_opens_le_of_eq_along I f hfG hfW hcN₀
      (D.isClosed_descendedForm.mpullback _ contMDiff_subtypeVal)
      (hσc.mpullback _ hΨ₀N)
      (fun g ↦ SmoothForm.mpullback_smul_mpullback contMDiff_subtypeVal (fun y ↦ hcN₀ g y)
        (D.mpullback_smul_descendedForm g _))
      (fun g ↦ SmoothForm.mpullback_smul_mpullback hΨ₀N
        (fun y ↦ by rw [comp_apply, comp_apply, hcN₀, hΨ₀G]) (hσ g))
      (fun q ↦ by
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        have h := D.nondegenerate_bilinFormAt_descendedForm_mk_zero g
        rw [← hf] at h
        exact (SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff _).2 h)
      (fun q ↦ by
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        have hp : (⟨f g, hfW (Set.mem_range_self _)⟩ : N₀) = ⟨_, hN₀0 g⟩ := Subtype.ext (hf g)
        rw [hp]
        exact D.mpullback_subtypeVal_apply_mk_zero_eq hσ hΨ₀G hΨ1 hT' N₀ hN₀0 hΨ₀N g)
  have hfix (g : G) (h : BalancedProduct.mk (stabilizer G x)
      ((stabilizer G x).toRightTranslation g) ((0 : A), (0 : V)) ∈ U₀) :
      (φ ⟨_, h⟩ : BalancedProduct _ _ _) = BalancedProduct.mk (stabilizer G x)
        ((stabilizer G x).toRightTranslation g) ((0 : A), (0 : V)) := by
    obtain ⟨h', hfix, -⟩ := hφf g
    have hp : (⟨_, h⟩ : U₀) = ⟨f g, h'⟩ := Subtype.ext (hf g).symm
    rw [hp, hfix, hf]
  -- `Ψ = Ψ₀ ∘ φ` on `U₀`.
  have hΨ₀U : ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞
      (Ψ₀ ∘ (Subtype.val : U₁ → _)) := fun y ↦
    ((hN₀ _).1 (hU₁ y.property)).contMDiffAt.comp y contMDiff_subtypeVal.contMDiffAt
  refine ⟨U₀, (Ψ₀ ∘ Subtype.val) ∘ φ, hΨ₀U.comp φ.contMDiff, fun g ↦ (hf g) ▸ (hφf g).1,
    hU₀G, fun g y h ↦ ?_, fun g h ↦ ?_, fun y ↦ ?_, ?_⟩
  · rw [comp_apply, comp_apply, comp_apply, comp_apply, hφG g y h, hΨ₀G]
  · rw [comp_apply, comp_apply, hfix, hΨ₀0]
  · exact IsLocalDiffeomorphAt.comp (hf := φ.isLocalDiffeomorph y)
      (hg := IsLocalDiffeomorphAt.comp (hf := isLocalDiffeomorph_subtype_val (φ y))
        (hg := (hN₀ _).1 (hU₁ (φ y).property)))
  · have h₁ : ((Ψ₀ ∘ Subtype.val) ∘ Opens.inclusion hU₁) ∘ φ = (Ψ₀ ∘ Subtype.val) ∘ φ := by
      funext y
      simp
    have h₀ : (Subtype.val : N₀ → _) ∘ Opens.inclusion hU₀ = Subtype.val := by
      funext y
      simp
    simpa only [SmoothForm.mpullback_mpullback, h₁, h₀] using hφσ



/-- **The local normal form near an orbit, as an equivariant local symplectomorphism.** Let a
compact Hausdorff Lie group `G` act smoothly on `M`, let `σ` be a closed `G`-invariant two-form
on `M`, and let `D` be data of a local model `Y = G ×_H (A × V)` whose subgroup `H = G_x` is the
stabilizer of `x`, with descended form `ω`. Let `T : T_{[1, 0]} Y ≃ T_x M` be a linear isomorphism
with `σ_x (T u, T v) = ω_{[1, 0]} (u, v)`, which intertwines the differential at `[1, 0]` of
`y ↦ k • y` with `dk_x` for each `k ∈ H`, and sends `dπ_(1, 0, 0) (ξ, 0)` to `ξ_M(x)` for each
`ξ ∈ 𝔤`. Then there are a `G`-invariant open set `N` of `Y` containing every point `[g, 0]` of
the zero section and a smooth map `Ψ : N → M`, `G`-equivariant, with `Ψ [g, 0] = g • x`, a local
diffeomorphism at every point of `N`, that pulls `σ` back to the restriction of `ω` to `N`. -/
theorem exists_isLocalDiffeomorph_mpullback_eq_descendedForm :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I
      𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
      (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∀ {σ : SmoothTwoForm I' M}, σ.IsClosed → (∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
        (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ) →
    ∀ T : TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
          ((0 : A), (0 : V))) ≃ₗ[ℝ] TangentSpace I' x,
      (∀ u v, SmoothBundleForm.eval₂ σ x (T u) (T v) =
        SmoothBundleForm.eval₂ D.descendedForm
          (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
            ((0 : A), (0 : V))) u v) →
      (∀ (k : stabilizer G x) u,
        T (D.tangentRepresentationOneZero k u) =
          tangentRepresentation (fun (g : G) _ ↦
            ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g x) k
            (T u)) →
      (∀ ξ : GroupLieAlgebra I G,
        T (D.orbitTangentMap ξ) = InfinitesimalAction.fundamental I G I' M ξ x) →
      ∃ (N : Opens (BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V)))
        (Ψ : N → M) (hΨ : ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ),
        (∀ g : G, BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation g)
          ((0 : A), (0 : V)) ∈ N) ∧
        (∀ (g : G) y, y ∈ N → g • y ∈ N) ∧
        (∀ (g : G) (y : N) (h : g • (y : BalancedProduct _ _ _) ∈ N),
          Ψ ⟨g • (y : BalancedProduct _ _ _), h⟩ = g • Ψ y) ∧
        (∀ (g : G) (h : BalancedProduct.mk (stabilizer G x)
            ((stabilizer G x).toRightTranslation g) ((0 : A), (0 : V)) ∈ N),
          Ψ ⟨_, h⟩ = g • x) ∧
        (∀ y, IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ y) ∧
        SmoothForm.mpullback Ψ hΨ σ =
          SmoothForm.mpullback (Subtype.val : N → _) contMDiff_subtypeVal D.descendedForm := by
  intro σ hσc hσ T hTσ hTk hTξ
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
    (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
  obtain ⟨Z, Ψ₀, -, hZ0, -, -, hΨ₀G, hΨ₀0, hΨ₀d, hΨ₀T⟩ := D.exists_isLocalDiffeomorphAt T hTk hTξ
  refine D.exists_mpullback_eq_descendedForm_of_isLocalDiffeomorphAt hσc hσ
    hΨ₀G ?_ (fun g ↦ ?_) (fun u v ↦ ?_)
  · rw [Prod.mk_zero_zero, hΨ₀0, one_smul]
  · rw [Prod.mk_zero_zero]
    exact hΨ₀d g hZ0
  · rw [hΨ₀T, hΨ₀T]
    exact hTσ u v
end LocalModelData

end SymplecticGeometry

end
