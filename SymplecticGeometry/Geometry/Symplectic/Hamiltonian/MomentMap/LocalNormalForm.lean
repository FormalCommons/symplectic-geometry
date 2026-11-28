/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.MomentMap
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.OfPoint
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Tube
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.NormSq
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.MvPolynomial.Basic
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.NormSq
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Slice
public import TauCeti.Topology.Algebra.ConstMulAction
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.NestedOpens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.GroupAction.Opens
import SymplecticGeometry.Topology.Algebra.GroupAction.InvariantCore
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.WeaklyHamiltonian
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Nondegenerate
import SymplecticGeometry.Geometry.Symplectic.Moser.Equivariant
import SymplecticGeometry.Geometry.Manifold.IsManifold.SecondCountable
import SymplecticGeometry.Geometry.Lie.Subgroup.BalancedProduct
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

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
(`TauCeti.CotangentBundle.balancedProductInducedMomentMap`). Give `N` the restricted action of `G`
(`TopologicalSpace.Opens.mulActionOfForallSMulMem`). Both `μ ∘ Ψ` and `μ_Y` restricted to `N` are
equivariant moment maps of `Ψ^* σ = ω|_N`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback`, from Tau Ceti), so the set where they
agree is open (`TauCeti.SmoothTwoForm.IsMomentMap.isClopen_setOfPred_eq`). It is `G`-invariant since
both maps are equivariant, and contains the zero section, where both maps are
`[g, 0] ↦ Ad*_g (μ x)`; restrict `Ψ` to it (`TopologicalSpace.Opens.imageVal`).

Finally, at any point `x` of a Hamiltonian `G`-manifold with closed nondegenerate invariant `σ`,
all the data are found. The stabilizer `G_x` is closed (`TauCeti.isClosed_stabilizer`), hence
compact, with the closed-subgroup Lie structure `TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`.
Its invariant complements `𝔪`, `𝔮` come from
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_subrepresentation_complements`, the spaces `V` and
`A` are Euclidean spaces of the dimensions of the symplectic slice and of `𝔪*`, identified with
them by `LinearEquiv.ofFinrankEq`, the data are `SymplecticGeometry.LocalModelData.ofPoint`, and
`T` is that of `SymplecticGeometry.LocalModelData.exists_linearEquiv_tangentSpace_ofPoint`.

As a consequence, for a nondegenerate `Ad`-invariant form `B` on `𝔤`, the norm square
`TauCeti.momentNormSq` of `μ` is a real polynomial in suitable coordinates around
every point, which is what the Łojasiewicz inequality for it needs. Pick a complement `𝔠` of `𝔥`
in `𝔤`. The map `s (w, p) = [exp w, p]` from `𝔠 × (A × V)` to `Y` is a local diffeomorphism at
`0` (`SymplecticGeometry.LocalModelData.isLocalDiffeomorphAt_mk_mulInvariantExp_submodule`), and so
is `Ψ` after it, with value `x` at `0`. On `Ψ (s (w, p))` the moment map is `μ_Y [exp w, p]`,
whose norm square is `B^∨ (ν p) (ν p)`
(`SymplecticGeometry.LocalModelData.dualForm_descendedMomentMap_mk`), a polynomial function of
`p` (`SymplecticGeometry.LocalModelData.dualForm_covector_mem_polynomialFunctions`). A local
inverse of `Ψ ∘ s`, followed by a linear isomorphism onto a Euclidean space, is the chart.

## Main results

* `SymplecticGeometry.LocalModelData.exists_mpullback_eq_descendedForm_of_isLocalDiffeomorphAt`:
  the Moser correction of an equivariant map `Ψ₀` as above.
* `SymplecticGeometry.LocalModelData.exists_isLocalDiffeomorph_mpullback_eq_descendedForm`: the
  equivariant local diffeomorphism `Ψ` from a neighbourhood of the zero section of the local
  model to `M` that pulls `σ` back to the descended form.
* `SymplecticGeometry.LocalModelData.exists_isLocalDiffeomorph_apply_eq_descendedMomentMap`:
  the same map, which moreover carries the moment map of `σ` to that of the local model.
* `SymplecticGeometry.LocalModelData.exists_ofPoint_isLocalDiffeomorph_apply_eq_descendedMomentMap`:
  the local normal form at a point `x` of a Hamiltonian `G`-manifold, for the local model
  `SymplecticGeometry.LocalModelData.ofPoint` at `x`.
* `SymplecticGeometry.exists_partialDiffeomorph_momentNormSq_eq_eval`: around every point, a
  smooth chart into a Euclidean space in which the norm square of `μ` is a polynomial.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign. Math. 51 (2005),
  117–127, for the norm square of the moment map in a chart.
-/

public section

open Function MulAction TauCeti TauCeti.Lie TauCeti.Manifold TopologicalSpace
  TauCeti.CotangentBundle
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
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]

section Model

variable {x : M}
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
        SmoothBundleForm.eval₂
            (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
              D.mpullback_smul_mpullback_snd_constSmooth
              D.isMomentMap_mpullback_snd_constSmooth)
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
          SmoothForm.mpullback (Subtype.val : N → _) contMDiff_subtypeVal
              (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
                D.mpullback_smul_mpullback_snd_constSmooth
                D.isMomentMap_mpullback_snd_constSmooth) := by
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
      (fun g q ↦ ⟨g • q, by simp [f]⟩) (isClosed_balancedProductInducedForm
        ((SymplecticForm.isClosed_constSmooth D.σ).mpullback _ _))
      (fun g ↦ mpullback_smul_balancedProductInducedForm g) hσc hσ hΨ₀G
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
        SmoothBundleForm.eval₂
            (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
              D.mpullback_smul_mpullback_snd_constSmooth
              D.isMomentMap_mpullback_snd_constSmooth)
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
          SmoothForm.mpullback (Subtype.val : N → _) contMDiff_subtypeVal
              (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
                D.mpullback_smul_mpullback_snd_constSmooth
                D.isMomentMap_mpullback_snd_constSmooth) := by
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
`TauCeti.CotangentBundle.balancedProductInducedMomentMap` of the local model. -/
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
        SmoothBundleForm.eval₂
            (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
              D.mpullback_smul_mpullback_snd_constSmooth
              D.isMomentMap_mpullback_snd_constSmooth)
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
          SmoothForm.mpullback (Subtype.val : N → _) contMDiff_subtypeVal
              (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
                D.mpullback_smul_mpullback_snd_constSmooth
                D.isMomentMap_mpullback_snd_constSmooth) ∧
        ∀ y : N, μ (Ψ y) = balancedProductInducedMomentMap G D.covectorCLM_smul y := by
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
  have hΨG' (g : G) (y : N) : Ψ (g • y) = g • Ψ y :=
    (congrArg Ψ (Subtype.ext (hcN g y))).trans (hΨG g y (hNG g y y.property))
  have h₁ := hμ.mpullback hΨ hΨG'
  rw [hΨσ] at h₁
  have h₂ := (isEquivariantMomentMap_balancedProductInducedForm (hf := D.contMDiff_covectorCLM)
    (hfK := D.covectorCLM_smul) (hσK := D.mpullback_smul_mpullback_snd_constSmooth)
    (hμ := D.isMomentMap_mpullback_snd_constSmooth)).mpullback contMDiff_subtypeVal hcN
  -- The set where the two agree is open and `G`-invariant; restrict `Ψ` to it.
  let V : Opens N := ⟨{y | μ (Ψ y) = balancedProductInducedMomentMap G D.covectorCLM_smul y},
    (h₁.toIsMomentMap.isClopen_setOfPred_eq h₂.toIsMomentMap).isOpen⟩
  have hVG (g : G) (y : N) (hy : y ∈ V) : g • y ∈ V := by
    simp only [V, Opens.mem_mk, Set.mem_ofPred_eq] at hy ⊢
    rw [hΨG', hμ.apply_smul, hcN, D.balancedProductInducedMomentMap_smul, hy]
  let N' := Opens.imageVal V
  have hN'N : N' ≤ N := Opens.imageVal_le V
  refine ⟨N', Ψ ∘ Opens.inclusion hN'N, hΨ.comp (contMDiff_inclusion hN'N),
    fun g ↦ Opens.mem_imageVal.2 ⟨hN0 g, ?_⟩, fun g y ↦ Opens.smul_mem_imageVal hcN hVG g,
    fun g y h ↦ hΨG g (Opens.inclusion hN'N y) (hN'N h), fun g h ↦ hΨ0 g (hN'N h),
    fun y ↦ (isLocalDiffeomorph_inclusion hN'N y).comp (hg := hΨd _), ?_,
    fun ⟨y, hy⟩ ↦ (Opens.mem_imageVal.1 hy).2⟩
  · -- The zero section: there both maps are `Ad*_g τ`.
    simp only [V, Opens.mem_mk, Set.mem_ofPred_eq]
    rw [hΨ0, hμ.apply_smul, D.balancedProductInducedMomentMap_mk_zero, hτ]
  · rw [← SmoothForm.mpullback_mpullback _ _ (contMDiff_inclusion hN'N) hΨ, hΨσ,
      SmoothForm.mpullback_inclusion_mpullback_subtypeVal]

end LocalModelData

end Model

variable {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

namespace LocalModelData

/-- **The local normal form at a point of a Hamiltonian `G`-manifold.** Let a compact Hausdorff
Lie group `G` act smoothly on `M`, let `σ` be a closed nondegenerate `G`-invariant two-form on
`M` with coadjoint-equivariant moment map `μ`, and let `x : M`. Its stabilizer `H = G_x` is
closed, and carries the closed-subgroup Lie structure
`TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed`. Then there are `H`-invariant complements
`𝔤_x ⊕ 𝔪 = 𝔤_{μ x}` and `𝔤_{μ x} ⊕ 𝔮 = 𝔤`, and linear isomorphisms `eV` from `ℝ^n`, `n` the
dimension of the symplectic slice at `x`, to that slice, and `eA` from `ℝ^m`,
`m = dim 𝔤_{μ x} - dim 𝔤_x`, to `𝔪*`, such that for the local model
`D = SymplecticGeometry.LocalModelData.ofPoint` at `x` built from them, whose covector is
`μ x` (`SymplecticGeometry.LocalModelData.ofPoint_τ`), with `Y = G ×_H (ℝ^m × ℝ^n)` and
descended form `ω`, there are a `G`-invariant open set `N` of `Y` containing every point
`[g, 0]` of the zero section and a smooth map `Ψ : N → M`, `G`-equivariant, with
`Ψ [g, 0] = g • x`, a local diffeomorphism, with `Ψ^* σ = ω` on `N`, and with `μ (Ψ y) = μ_Y y`
for every `y ∈ N`, where `μ_Y` is the moment map
`TauCeti.CotangentBundle.balancedProductInducedMomentMap` of the local model. -/
theorem exists_ofPoint_isLocalDiffeomorph_apply_eq_descendedMomentMap (hσc : σ.IsClosed)
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ)
    (hμ : σ.IsEquivariantMomentMap μ) (x : M) :
    haveI hx : IsClosed (stabilizer G x : Set G) := isClosed_stabilizer
      (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) x).continuous
    haveI : CompactSpace (stabilizer G x) := isCompact_iff_compactSpace.1 hx.isCompact
    let d := EmbeddedLieSubgroupData.ofIsClosed (I := I) hx
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ
      (hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x)))
    let A := EuclideanSpace ℝ (Fin (Module.finrank ℝ
      (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ x)).toSubmodule -
      Module.finrank ℝ ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule))
    ∃ (𝔪 𝔮 : Subrepresentation ((adjointRepresentation ℝ I G).comp (stabilizer G x).subtype))
      (h𝔪 : Disjoint ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule
        𝔪.toSubmodule)
      (h𝔪' : ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule ⊔
        𝔪.toSubmodule = (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ x)).toSubmodule)
      (h𝔮 : IsCompl (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ x)).toSubmodule 𝔮.toSubmodule)
      (eV : V ≃ₗ[ℝ] hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x)
      (eA : A ≃ₗ[ℝ] Module.Dual ℝ 𝔪.toSubmodule),
      let D := ofPoint hσ (fun g _ ↦ hσG g) hμ d h𝔪 h𝔪' h𝔮 eV eA
      letI := D.fiberDistribMulAction
      haveI := D.contMDiffSMul_fiberDistribMulAction
      letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I
        𝓘(ℝ, A × V) (Lie.lieSubalgebraOfSubgroup (I := I) (stabilizer G x)).toSubmodule
      haveI := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
        (I := I) (IZ := 𝓘(ℝ, A × V))
        (F := (Lie.lieSubalgebraOfSubgroup (I := I) (stabilizer G x)).toSubmodule)
      ∃ (N : Opens (BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V)))
        (Ψ : N → M)
        (hΨ : ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace
          (Lie.lieSubalgebraOfSubgroup (I := I) (stabilizer G x)).toSubmodule (E × (A × V)))
          I' ∞ Ψ),
        (∀ g : G, BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation g)
          ((0 : A), (0 : V)) ∈ N) ∧
        (∀ (g : G) y, y ∈ N → g • y ∈ N) ∧
        (∀ (g : G) (y : N) (h : g • (y : BalancedProduct _ _ _) ∈ N),
          Ψ ⟨_, h⟩ = g • Ψ y) ∧
        (∀ (g : G) (h : BalancedProduct.mk (stabilizer G x)
            ((stabilizer G x).toRightTranslation g) ((0 : A), (0 : V)) ∈ N),
          Ψ ⟨_, h⟩ = g • x) ∧
        IsLocalDiffeomorph 𝓘(ℝ, ProperSMul.QuotientModelSpace
          (Lie.lieSubalgebraOfSubgroup (I := I) (stabilizer G x)).toSubmodule (E × (A × V)))
          I' ∞ Ψ ∧
        SmoothForm.mpullback Ψ hΨ σ =
          SmoothForm.mpullback (Subtype.val : N → _) contMDiff_subtypeVal
              (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
                D.mpullback_smul_mpullback_snd_constSmooth
                D.isMomentMap_mpullback_snd_constSmooth) ∧
        ∀ y : N, μ (Ψ y) = balancedProductInducedMomentMap G D.covectorCLM_smul y := by
  have hx : IsClosed (stabilizer G x : Set G) := isClosed_stabilizer
    (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) x).continuous
  intro d _ _ _ V A
  obtain ⟨𝔪, 𝔮, h𝔪, h𝔪', h𝔮⟩ := hσ.exists_subrepresentation_complements (fun g _ ↦ hσG g)
    (hμ.momentCocycle_eq_zero x) hx.isCompact
  -- `dim 𝔪 = dim 𝔤_{μ x} - dim 𝔤_x`, since `𝔤_x ⊕ 𝔪 = 𝔤_{μ x}`.
  have hA := Submodule.finrank_sup_add_finrank_inf_eq
    ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule 𝔪.toSubmodule
  rw [h𝔪', h𝔪.eq_bot, finrank_bot, add_zero] at hA
  have hA' : Module.finrank ℝ A = Module.finrank ℝ (Module.Dual ℝ 𝔪.toSubmodule) := by
    rw [finrank_euclideanSpace_fin, Subspace.dual_finrank_eq]
    omega
  let eV : V ≃ₗ[ℝ] _ := LinearEquiv.ofFinrankEq _ _ finrank_euclideanSpace_fin
  let eA : A ≃ₗ[ℝ] _ := LinearEquiv.ofFinrankEq _ _ hA'
  refine ⟨𝔪, 𝔮, h𝔪, h𝔪', h𝔮, eV, eA, ?_⟩
  intro D
  obtain ⟨T, hTσ, hTk, hTξ⟩ :=
    exists_linearEquiv_tangentSpace_ofPoint hσ (fun g _ ↦ hσG g) hμ d h𝔪 h𝔪' h𝔮 eV eA
  exact D.exists_isLocalDiffeomorph_apply_eq_descendedMomentMap hσc hσG hμ
    (ofPoint_τ hσ (fun g _ ↦ hσG g) hμ d h𝔪 h𝔪' h𝔮 eV eA) T hTσ hTk hTξ

end LocalModelData

open LocalModelData

open scoped GroupLieAlgebra in
/-- **The norm square of a moment map is a polynomial in a chart.** Let a compact Hausdorff Lie
group `G` act smoothly on `M`, let `σ` be a closed nondegenerate `G`-invariant two-form on `M` with
coadjoint-equivariant moment map `μ`, and let `B` be a nondegenerate `Ad`-invariant bilinear form
on `𝔤`. Then every `x : M` lies in the source of a smooth partial diffeomorphism `e` from `M` to
a Euclidean space `ℝ^d` in which the norm square `y ↦ B^∨ (μ y) (μ y)` (`momentNormSq`) is a real
polynomial `P` in the coordinates: `momentNormSq μ (B.toDual hB).symm y = P (e y)` for every `y` in
the source of `e`. -/
theorem exists_partialDiffeomorph_momentNormSq_eq_eval (hσc : σ.IsClosed)
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ)
    (hμ : σ.IsEquivariantMomentMap μ) {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
    (hB : B.Nondegenerate)
    (hBG : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B) (x : M) :
    ∃ (d : ℕ) (e : PartialDiffeomorph I' 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) M
      (EuclideanSpace ℝ (Fin d)) ∞) (P : MvPolynomial (Fin d) ℝ),
      x ∈ e.source ∧ ∀ y ∈ e.source,
        momentNormSq μ (B.toDual hB).symm y = MvPolynomial.eval (e y) P := by
  have hx : IsClosed (stabilizer G x : Set G) := isClosed_stabilizer
    (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) x).continuous
  have : CompactSpace (stabilizer G x) := isCompact_iff_compactSpace.1 hx.isCompact
  let d := EmbeddedLieSubgroupData.ofIsClosed (I := I) hx
  let _ := d.chartedSpace
  let _ := d.lieGroup
  let _ := d.contMDiffSMul (I'' := I) (M := G)
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ
    (hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x)))
  let A := EuclideanSpace ℝ (Fin (Module.finrank ℝ
    (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ x)).toSubmodule -
    Module.finrank ℝ ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule))
  obtain ⟨𝔪, 𝔮, h𝔪, h𝔪', h𝔮, eV, eA, h⟩ :=
    exists_ofPoint_isLocalDiffeomorph_apply_eq_descendedMomentMap hσc hσ hσG hμ x
  set D := ofPoint hσ (fun g _ ↦ hσG g) hμ d h𝔪 h𝔪' h𝔮 eV eA
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I
    𝓘(ℝ, A × V) (Lie.lieSubalgebraOfSubgroup (I := I) (stabilizer G x)).toSubmodule
  obtain ⟨N, Ψ, -, hN0, -, -, hΨ0, hΨd, -, hΨμ⟩ := h
  let Q := ProperSMul.QuotientModelSpace
    (Lie.lieSubalgebraOfSubgroup (I := I) (stabilizer G x)).toSubmodule (E × (A × V))
  obtain ⟨𝔠, h𝔠⟩ := Submodule.exists_isCompl D.𝔥
  have hs := D.isLocalDiffeomorphAt_mk_mulInvariantExp_submodule h𝔠
  set s : 𝔠 × (A × V) → _ := fun p ↦ BalancedProduct.mk (stabilizer G x)
    ((stabilizer G x).toRightTranslation (mulInvariantExp (I := I) (p.1 : GroupLieAlgebra I G)))
    p.2 with hs_def
  -- The point `[1, 0]` of `N`, and a local inverse `r` of the inclusion `N → Y` there.
  have hs0 : s 0 = BalancedProduct.mk (stabilizer G x)
      ((stabilizer G x).toRightTranslation (1 : G)) ((0 : A), (0 : V)) := by
    simp [hs_def, Prod.zero_eq_mk]
  let y₀ : N := ⟨s 0, hs0 ▸ hN0 1⟩
  have hval : IsLocalDiffeomorphAt 𝓘(ℝ, Q) 𝓘(ℝ, Q) ∞ (Subtype.val : N → _) y₀ :=
    isLocalDiffeomorph_subtype_val y₀
  set r := hval.localInverse
  have hr0 : r (s 0) = y₀ := hval.localInverse_left_inv hval.localInverse_mem_target
  have hrs := IsLocalDiffeomorphAt.comp (hf := hs) (hg := hval.localInverse_isLocalDiffeomorphAt)
  have hΦ := IsLocalDiffeomorphAt.comp (hf := hrs) (hg := hΨd (r (s 0)))
  set e₀ := hΦ.localInverse
  have hΦ0 : (Ψ ∘ r ∘ s) 0 = x := by
    simp only [Function.comp_apply, hr0]
    rw [← one_smul G x, ← hΨ0 1 (hs0 ▸ hN0 1)]
    exact congrArg Ψ (Subtype.ext hs0)
  -- Shrink the source of the local inverse `e₀` of `Ψ ∘ r ∘ s` to where `r` inverts the
  -- inclusion along `s`.
  set t := interior (s ⁻¹' r.source)
  have h0t : (0 : 𝔠 × (A × V)) ∈ t := mem_interior_iff_mem_nhds.2
    (hs.contMDiffAt.continuousAt.preimage_mem_nhds
      (r.open_source.mem_nhds hval.localInverse_mem_source))
  have ht : IsOpen (e₀.source ∩ e₀ ⁻¹' t) :=
    e₀.contMDiffOn.continuousOn.isOpen_inter_preimage e₀.open_source isOpen_interior
  let L := toEuclidean (E := 𝔠 × (A × V))
  let e := (e₀.restrOpen _ ht).trans (L.toPartialDiffeomorph (n := ∞))
  have he : ∀ y, y ∈ e.source ↔ y ∈ e₀.source ∧ e₀ y ∈ t := fun y ↦ by
    rw [PartialDiffeomorph.trans_toPartialDiffeomorph_source, PartialDiffeomorph.restrOpen_source,
      ← Set.inter_assoc, Set.inter_self, Set.mem_inter_iff, Set.mem_preimage]
  have he_apply (y : M) : e y = L (e₀ y) := by
    simp [e]
  -- The norm square read in the coordinates `z = L w` is a polynomial function of `z`.
  obtain ⟨P, hP⟩ := (EuclideanSpace.basisFun (Fin _) ℝ).toBasis.mem_polynomialFunctions_iff.1
    (Module.comp_linearMap_mem_polynomialFunctions
      (LinearMap.snd ℝ 𝔠 (A × V) ∘ₗ L.symm.toLinearMap)
      (D.dualForm_covector_mem_polynomialFunctions hB))
  have hx₀ := hΦ.localInverse_mem_source
  have hex := hΦ.localInverse_left_inv hΦ.localInverse_mem_target
  rw [hΦ0] at hx₀ hex
  refine ⟨_, e, P, (he x).2 ⟨hx₀, hex ▸ h0t⟩, fun y hy ↦ ?_⟩
  obtain ⟨hy, hyt⟩ := (he y).1 hy
  have hrsy : (r (s (e₀ y)) : _) = s (e₀ y) :=
    hval.localInverse_right_inv (interior_subset hyt : e₀ y ∈ s ⁻¹' r.source)
  have hy' : Ψ (r (s (e₀ y))) = y := hΦ.localInverse_right_inv hy
  rw [he_apply]
  conv_lhs => rw [← hy']
  rw [momentNormSq_toDual_symm_eq_dualForm, hΨμ, hrsy, hs_def,
    D.dualForm_descendedMomentMap_mk hB hBG]
  have hb : ((EuclideanSpace.basisFun _ ℝ).repr (L (e₀ y))).ofLp = (L (e₀ y)).ofLp :=
    funext (EuclideanSpace.basisFun_repr _ ℝ _)
  simpa [hb] using (hP (L (e₀ y))).symm

end SymplecticGeometry

end
