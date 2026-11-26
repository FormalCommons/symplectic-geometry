/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.MomentMap
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Tube
import SymplecticGeometry.Geometry.Manifold.GroupAction.Opens
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.WeaklyHamiltonian
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Nondegenerate
import SymplecticGeometry.Geometry.Symplectic.Moser.Equivariant
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable
import SymplecticGeometry.Geometry.Lie.Subgroup.BalancedProduct
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic

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

The proof corrects an equivariant map
(`SymplecticGeometry.LocalModelData.exists_mpullback_eq_descendedForm_of_isLocalDiffeomorphAt`).
Let `Ψ₀ : Y → M` be `G`-equivariant with `Ψ₀ [1, 0] = x`, a local diffeomorphism at `[1, 0]`,
whose differential at `[1, 0]` takes `σ_x` to `ω_{[1, 0]}`. By equivariance it is a local
diffeomorphism at every `[g, 0]` (`SymplecticGeometry.isLocalDiffeomorphAt_smul_iff`), and it pulls
`σ` back to `ω` at every `[g, 0]`
(`SymplecticGeometry.LocalModelData.mpullback_apply_mk_zero_eq_descendedForm`), where `ω` is
nondegenerate (`SymplecticGeometry.LocalModelData.nondegenerate_bilinFormAt_descendedForm_mk_zero`).
The zero section `G ⧸ H → Y` is a smooth embedding with invariant image
(`TauCeti.BalancedProduct.isSmoothEmbedding_zeroSectionRightTranslation`), and `Y` is Hausdorff
(Mathlib's instance `t2Space_quotient_mulAction_of_properSMul`, with Tau Ceti's `properSMul_prod`)
and second countable (`TauCeti.BalancedProduct.secondCountableTopology_rightTranslation`), so the
equivariant Moser correction
`TauCeti.SmoothEmbedding.exists_equivariant_isLocalDiffeomorph_mpullback_eq_of_eq_along` applies.
The tube map of `SymplecticGeometry.LocalModelData.exists_isLocalDiffeomorphAt`, whose
differential at `[1, 0]` is `T`, is such a `Ψ₀`.

If moreover `μ : M → 𝔤*` is a coadjoint-equivariant moment map of `σ` with `μ x = D.τ`, then `N`
can be shrunk so that also `μ ∘ Ψ` is the moment map `μ_Y` of the local model
(`SymplecticGeometry.LocalModelData.descendedMomentMap`). Give `N` the restricted action of `G`
(`TopologicalSpace.Opens.mulActionOfForallSMulMem`). Both `μ ∘ Ψ` and `μ_Y` restricted to `N` are
equivariant moment maps of `Ψ^* σ = ω|_N` (Tau Ceti's
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback`), so they differ by locally constant
functions
(`TauCeti.SmoothTwoForm.IsMomentMap.isMomentMap_iff_exists_eq_add_locallyConstant`). The set where
these vanish on a basis of `𝔤` is open, `G`-invariant since both maps are equivariant, and contains
the zero section, where both maps are `[g, 0] ↦ Ad*_g (μ x)`; restrict `Ψ` to it.

## Main results

* `SymplecticGeometry.LocalModelData.exists_mpullback_eq_descendedForm_of_isLocalDiffeomorphAt`:
  the Moser correction of an equivariant map `Ψ₀` as above.
* `SymplecticGeometry.LocalModelData.exists_isLocalDiffeomorph_mpullback_eq_descendedForm`: the
  equivariant local diffeomorphism `Ψ` from a neighbourhood of the zero section of the local
  model to `M` that pulls `σ` back to the descended form.
* `SymplecticGeometry.LocalModelData.exists_isLocalDiffeomorph_apply_eq_descendedMomentMap`:
  the same map, which moreover carries the moment map of `σ` to that of the local model.

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
diffeomorphism at `[1, 0]`, whose differential `dΨ₀` at `[1, 0]` satisfies
`σ_x (dΨ₀ u, dΨ₀ v) = ω_{[1, 0]} (u, v)`. Then there are a `G`-invariant open set `N` of `Y`
containing every point `[g, 0]` and a smooth map `Ψ : N → M`, `G`-equivariant, with
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
      IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ₀
        (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
          ((0 : A), (0 : V))) →
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
        IsLocalDiffeomorph 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ ∧
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
  -- The topological hypotheses of the Moser theorem: `Y` is Hausdorff and second countable.
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, A × V))
    (G := stabilizer G x) (M := A × V) ∞
  have := I.secondCountableTopology_of_sigmaCompact G
  have : ContMDiffConstSMul I' ∞ G M := ContMDiffSMul.contMDiffConstSMul I
  have : ContMDiffConstSMul 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) ∞ G
      (BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V)) :=
    ContMDiffSMul.contMDiffConstSMul I
  have hmk (g : G) : g • BalancedProduct.mk (stabilizer G x)
      ((stabilizer G x).toRightTranslation 1) ((0 : A), (0 : V)) = BalancedProduct.mk
        (stabilizer G x) ((stabilizer G x).toRightTranslation g) ((0 : A), (0 : V)) := by
    rw [BalancedProduct.smul_mk_toRightTranslation, mul_one]
  -- The zero section, a smooth embedding of `G ⧸ H` with invariant image.
  have hz₀ : ((0 : A), (0 : V)) ∈ MulAction.fixedPoints (stabilizer G x) (A × V) :=
    MulAction.mem_fixedPoints.2 fun k ↦ smul_zero k
  let := Subgroup.quotientChartedSpaceOfIsClosed I ‹IsClosed (stabilizer G x : Set G)›
  have := Subgroup.isManifold_quotientOfIsClosed (I := I) ‹IsClosed (stabilizer G x : Set G)›
  let f := SmoothEmbedding.ofIsSmoothEmbedding _
    (BalancedProduct.isSmoothEmbedding_zeroSectionRightTranslation (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F) hz₀)
  have hf (g : G) : f g = BalancedProduct.mk (stabilizer G x)
      ((stabilizer G x).toRightTranslation g) ((0 : A), (0 : V)) := by
    simp [f, BalancedProduct.zeroSectionRightTranslation_mk]
  obtain ⟨N, Ψ, hΨ, hfN, hNG, hΨG, hΨf, hΨd, hΨσ⟩ :=
    SmoothEmbedding.exists_equivariant_isLocalDiffeomorph_mpullback_eq_of_eq_along I f
      (fun g q ↦ ⟨g • q, by simp [f]⟩) D.isClosed_descendedForm
      (fun g ↦ D.mpullback_smul_descendedForm g _) hσc hσ hΨ₀G
      (fun q ↦ by
        induction q using QuotientGroup.induction_on with
        | H g => rw [hf, ← hmk]; exact (isLocalDiffeomorphAt_smul_iff hΨ₀G g).2 hΨ₀d)
      (fun q ↦ by
        induction q using QuotientGroup.induction_on with
        | H g => rw [hf]; exact D.nondegenerate_bilinFormAt_descendedForm_mk_zero g)
      (fun q ↦ by
        induction q using QuotientGroup.induction_on with
        | H g =>
          rw [hf]
          exact D.mpullback_apply_mk_zero_eq_descendedForm hσ hΨ₀G hΨ1
            (hΨ₀d.contMDiffAt.mdifferentiableAt (by simp)) hT' g)
  refine ⟨N, Ψ, hΨ, fun g ↦ hfN ⟨g, hf g⟩, hNG, hΨG, fun g h ↦ ?_, hΨd, hΨσ⟩
  calc Ψ ⟨_, h⟩ = Ψ ⟨f g, hfN ⟨g, rfl⟩⟩ := congrArg Ψ (Subtype.ext (hf g).symm)
    _ = g • x := by rw [hΨf, hf, ← hmk, hΨ₀G, hΨ1]

/-- **The local normal form near an orbit, as an equivariant local symplectomorphism.** Let a
compact Hausdorff Lie group `G` act smoothly on `M`, let `σ` be a closed `G`-invariant two-form
on `M`, and let `D` be data of a local model `Y = G ×_H (A × V)` whose subgroup `H = G_x` is the
stabilizer of `x`, with descended form `ω`. Let `T : T_{[1, 0]} Y ≃ T_x M` be a linear isomorphism
with `σ_x (T u, T v) = ω_{[1, 0]} (u, v)`, which intertwines the differential at `[1, 0]` of
`y ↦ k • y` with `dk_x` for each `k ∈ H`, and sends `dπ_(1, 0, 0) (ξ, 0)` to `ξ_M(x)` for each
`ξ ∈ 𝔤`. Then there are a `G`-invariant open set `N` of `Y` containing every point `[g, 0]` of
the zero section and a smooth map `Ψ : N → M`, `G`-equivariant, with `Ψ [g, 0] = g • x`, a local
diffeomorphism, that pulls `σ` back to the restriction of `ω` to `N`. -/
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
        IsLocalDiffeomorph 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ ∧
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
    hΨ₀G ?_ ?_ (fun u v ↦ ?_)
  · rw [Prod.mk_zero_zero, hΨ₀0, one_smul]
  · rw [Prod.mk_zero_zero]
    exact hΨ₀d 1 hZ0
  · rw [hΨ₀T, hΨ₀T]
    exact hTσ u v

/-- **The local normal form near an orbit, with the moment map.** In the setting of
`SymplecticGeometry.LocalModelData.exists_isLocalDiffeomorph_mpullback_eq_descendedForm`, let
moreover `μ : M → 𝔤*` be a coadjoint-equivariant moment map of `σ` whose value at `x` is the
covector `D.τ` of the local model. Then `N` and `Ψ` can be chosen with all the properties given
there and moreover `μ (Ψ y) = μ_Y y` for every `y ∈ N`, where `μ_Y` is the moment map
`D.descendedMomentMap` of the local model. -/
theorem exists_isLocalDiffeomorph_apply_eq_descendedMomentMap :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I
      𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
      (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∀ {σ : SmoothTwoForm I' M}, σ.IsClosed → (∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
        (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ) →
    ∀ {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}, σ.IsEquivariantMomentMap μ → D.τ = μ x →
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
        IsLocalDiffeomorph 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ ∧
        SmoothForm.mpullback Ψ hΨ σ =
          SmoothForm.mpullback (Subtype.val : N → _) contMDiff_subtypeVal D.descendedForm ∧
        ∀ y : N, μ (Ψ y) = D.descendedMomentMap y := by
  intro σ hσc hσ μ hμ hτ T hTσ hTk hTξ
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
    (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
  have := BalancedProduct.contMDiffSMul_rightTranslation (K := stabilizer G x) (Z := A × V)
    (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
  obtain ⟨N, Ψ, hΨ, hN0, hNG, hΨG, hΨ0, hΨd, hΨσ⟩ :=
    D.exists_isLocalDiffeomorph_mpullback_eq_descendedForm hσc hσ T hTσ hTk hTξ
  -- On `N`, with the restricted action, `μ ∘ Ψ` and `μ_Y ∘ val` are moment maps of one form.
  let : MulAction G N := Opens.mulActionOfForallSMulMem hNG
  have hcN := Opens.coe_smul_mulActionOfForallSMulMem hNG
  have : ContMDiffSMul I 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) ∞ G N :=
    Opens.contMDiffSMul_of_coe_smul hcN
  have h₁ := hμ.mpullback hΨ fun g y ↦ hΨG g y _
  rw [hΨσ] at h₁
  have h₂ := D.isEquivariantMomentMap_descendedForm.mpullback contMDiff_subtypeVal hcN
  obtain ⟨c, hc⟩ :=
    (h₂.toIsMomentMap.isMomentMap_iff_exists_eq_add_locallyConstant).1 h₁.toIsMomentMap
  -- The set where the two agree is open: it is cut out by the locally constant `c` on a basis.
  let b := Module.finBasis ℝ (GroupLieAlgebra I G)
  have hagree (y : N) : μ (Ψ y) = D.descendedMomentMap y ↔ ∀ i, c (b i) y = 0 := by
    refine ⟨fun h i ↦ ?_, fun h ↦ b.ext fun i ↦ ?_⟩
    · have := hc y (b i)
      simp only [Function.comp_apply, h] at this
      linarith
    · have := hc y (b i)
      simp only [Function.comp_apply, h i, add_zero] at this
      exact this
  let S : Set N := {y | ∀ i, c (b i) y = 0}
  have hS : IsOpen S := by
    simp only [S, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ (c (b i)).isLocallyConstant.isOpen_fiber 0
  let N' : Opens (BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V)) :=
    ⟨Subtype.val '' S, N.isOpen.isOpenMap_subtypeVal S hS⟩
  have hN'N : N' ≤ N := by
    rintro _ ⟨y, -, rfl⟩
    exact y.property
  have hmemN' (y : N) : (y : BalancedProduct _ _ _) ∈ N' ↔ y ∈ S :=
    Subtype.val_injective.mem_set_image
  have hagree' (y : N') : μ ((Ψ ∘ Opens.inclusion hN'N) y) = D.descendedMomentMap y := by
    obtain ⟨_, ⟨z, hz, rfl⟩⟩ := y
    exact (hagree z).2 hz
  -- `Ψ` restricted to `N'` keeps all the other properties.
  refine ⟨N', Ψ ∘ Opens.inclusion hN'N, hΨ.comp (contMDiff_inclusion hN'N), fun g ↦ ?_,
    fun g y hy ↦ ?_, fun g y h ↦ ?_, fun g h ↦ ?_,
    fun y ↦ (TauCeti.isLocalDiffeomorph_inclusion hN'N y).comp (hg := hΨd _), ?_, hagree'⟩
  · -- The zero section: there both maps are `Ad*_g τ`.
    refine (hmemN' ⟨_, hN0 g⟩).2 ((hagree _).1 ?_)
    rw [hΨ0, hμ.apply_smul, descendedMomentMap_mk_zero, hτ]
  · -- Invariance: both maps are equivariant.
    obtain ⟨z, hz, rfl⟩ := hy
    refine (hmemN' (g • z)).2 ((hagree _).1 ?_)
    rw [show Ψ (g • z) = g • Ψ z from hΨG g z _, hμ.apply_smul, hcN, descendedMomentMap_smul,
      (hagree z).2 hz]
  · exact hΨG g (Opens.inclusion hN'N y) (hN'N h)
  · exact hΨ0 g (hN'N h)
  · rw [← SmoothForm.mpullback_mpullback _ _ (contMDiff_inclusion hN'N) hΨ, hΨσ,
      SmoothForm.mpullback_mpullback_of_comp_eq (contMDiff_inclusion hN'N) contMDiff_subtypeVal
        contMDiff_id contMDiff_subtypeVal (Set.val_comp_inclusion hN'N),
      SmoothForm.mpullback_id, LinearMap.id_apply]

end LocalModelData

end SymplecticGeometry

end
