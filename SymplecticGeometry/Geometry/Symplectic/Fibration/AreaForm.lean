/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.StructureGroup
public import SymplecticGeometry.Geometry.Manifold.Orientation.PositiveForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.Positivity
import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.PartitionOfUnity.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.FiberBundle
import SymplecticGeometry.Geometry.Manifold.FiberBundle.ChangeModelFiber
import SymplecticGeometry.Geometry.Symplectic.Moser.Surface
import SymplecticGeometry.Topology.FiberBundle.Basic

/-!
# Area forms on the fibres of an oriented surface fibration

Let `A` be a smooth atlas of a map `proj : M → B` whose model fibre is a closed surface `F` with
an orientation `o`, and whose coordinate changes preserve `o`. This file builds a two-form `τ` on
`M` whose pull-back along every fibre inclusion of `A` is an area form positive for `o` with
integral one (`TauCeti.MapFiber.Atlas.exists_restricts_isPositive_area`).

The construction: a top form on `F` inducing `o`, divided by its integral, is a form `σ₀`
positive for `o` of integral one
(`TauCeti.exists_smoothForm_isPositive_integralTopForm_eq_one`). Glue the pull-backs of `σ₀`
along the fibre coordinates of the charts with a partition of unity of the base
(`TauCeti.MapFiber.Atlas.glueForm`). On the fibre over `b'`, the glued form is the combination,
with the weights at `b'`, of the pull-backs of `σ₀` along coordinate changes
(`TauCeti.MapFiber.Atlas.mpullback_fiberInclusionMap_glueForm`). These preserve `o`, so each
pull-back is positive for `o` (`TauCeti.Manifold.Orientation.IsPositive.mpullback`) and has
integral one (change of variables,
`Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt`); and the
weights are nonnegative with sum one, so the combination is positive for `o`
(`TauCeti.Manifold.Orientation.IsPositive.sum_smul`) with integral one.

Over the base set `U` of one chart `e` of `A`, such a form `τ` can be read as `σ₀` on every fibre
after a change of the fibre coordinate of `e`
(`TauCeti.MapFiber.Atlas.exists_trivialization_mpullback_fiberInclusionMap_eq`). The fibre forms
`σ_p` of `τ` over `U` are the slices of one form on `U × F`
(`Bundle.Trivialization.mpullback_prodMk_mpullback_symm`), so Moser's theorem for families of
area forms (`TauCeti.SmoothTwoForm.exists_diffeomorph_prod_mpullback_eq_of_integralTopForm_eq`)
gives a diffeomorphism `(p, x) ↦ (p, χ_p x)` of `U × F` with `χ_p^* σ_p = σ₀` and each `χ_p`
preserving `o`. The new chart is `e` followed by its inverse
(`Bundle.Trivialization.transFiberwiseHomeomorph`), and its coordinate changes with the charts
of `A` preserve `o`, since those of `A` and the `χ_p` do.

Taking one such chart at each point of the base gives a smooth atlas with the base sets of `A`
along which `τ` restricts to `σ₀` (`TauCeti.MapFiber.Atlas.exists_symplecticAtlas_of_oriented`).
Its coordinate changes then preserve `σ₀` (`TauCeti.MapFiber.Atlas.RestrictsTo.hasStructureGroup`):
for an area form `σ₀`, it is a symplectic atlas.

## Main results

* `TauCeti.MapFiber.Atlas.exists_restricts_isPositive_area`: some two-form on `M` pulls back
  along every fibre inclusion of the atlas to a form positive for `o` with integral one.
* `TauCeti.MapFiber.Atlas.exists_trivialization_mpullback_fiberInclusionMap_eq`: near each point
  of the base, a smooth chart along whose fibre inclusions such a form pulls back to `σ₀`, with
  coordinate changes with the charts of `A` that preserve `o`.
* `TauCeti.MapFiber.Atlas.exists_symplecticAtlas_of_oriented`: a smooth atlas with the base sets
  of `A` and structure group the stabilizer of `σ₀`, along which such a form restricts to `σ₀`,
  and whose coordinate changes with `A` preserve `o`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.2
  (the proof of Theorem 6.2.2).
* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
-/

public section

noncomputable section

open Bundle Set SymplecticGeometry
open scoped Manifold ContDiff

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F]
  [ChartedSpace HF F] [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M]
  {proj : M → B} {A : Atlas F proj} {o : Manifold.Orientation IF F (Fin 2)}

variable [FiniteDimensional ℝ EB] [IsManifold IB ∞ B]

/-- **Area forms on the fibres.** Let `A` be a smooth atlas of `proj : M → B`, over a Hausdorff
σ-compact base modelled on a finite-dimensional space, whose model fibre is a nonempty compact
Hausdorff surface `F` with an orientation `o`, and whose coordinate changes preserve `o`. Then
some two-form `τ` on `M` pulls back along each fibre inclusion `v ↦ (A.trivAt b)⁻¹ (b', v)`, for
`b'` in the base set of `A.trivAt b`, to a form that is positive for `o` and has integral
one. -/
theorem exists_restricts_isPositive_area [T2Space B] [SigmaCompactSpace B] [T2Space F]
    [CompactSpace F] [Nonempty F] (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup (n := ∞) (by simp) o)) :
    ∃ τ : SmoothTwoForm IM M, ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      o.IsPositive (SmoothForm.mpullback _ ((A.trivAt b).contMDiff_fiberInclusionMap
          (hA.contMDiffOn_trivAt_symm b) hb') τ).val ∧
      integralTopForm o (SmoothForm.mpullback _ ((A.trivAt b).contMDiff_fiberInclusionMap
          (hA.contMDiffOn_trivAt_symm b) hb') τ).val = 1 := by
  obtain ⟨σ₀, hσ₀, hint⟩ := exists_smoothForm_isPositive_integralTopForm_eq_one o
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate IB isClosed_univ
    (fun i ↦ (A.trivAt i).baseSet) (fun i ↦ (A.trivAt i).open_baseSet)
    A.iUnion_baseSet_trivAt.ge
  refine ⟨⟨_, (isSmoothForm_glueForm hA hρ σ₀).mem_smoothBundleForms⟩, fun b b' hb' ↦ ?_⟩
  -- On the fibre over `b'`, the glued form combines the pull-backs of `σ₀` along the coordinate
  -- changes over `b'`, which are orientation-preserving diffeomorphisms `φ i`.
  have hφ : ∀ i, ∃ φ : F ≃ₘ⟮IF, IF⟯ F, i ∈ ρ.finsupport b' →
      φ ∈ Diffeomorph.orientationPreservingSubgroup (n := ∞) (by simp) o ∧
        ⇑φ = (A.trivAt b).coordChange (A.trivAt i) b' := fun i ↦ by
    by_cases hi : i ∈ ρ.finsupport b'
    · obtain ⟨φ, hφ, hφe⟩ :=
        hasStructureGroup_iff.1 hH b i b' hb' (hρ.mem_of_mem_finsupport hi)
      exact ⟨φ, fun _ ↦ ⟨hφ, hφe⟩⟩
    · exact ⟨Diffeomorph.refl IF F ∞, fun h ↦ absurd h hi⟩
  choose φ hφ using hφ
  rw [SmoothForm.coe_mpullback, mpullback_fiberInclusionMap_glueForm hA hρ,
    Finset.sum_congr rfl fun i hi ↦ by rw [← (hφ i hi).2]]
  have hsum : ∑ i ∈ ρ.finsupport b', ρ i b' = 1 := ρ.sum_finsupport (x₀ := b') (mem_univ _)
  have hpos : ∀ i ∈ ρ.finsupport b', 0 < ρ i b' := fun i hi ↦
    lt_of_le_of_ne (ρ.nonneg i b') (Ne.symm ((ρ.mem_finsupport b').1 hi))
  have hop : ∀ i ∈ ρ.finsupport b', ∀ x,
      Manifold.Orientation.IsOrientationPreservingAt o o (φ i) x := fun i hi ↦
    Diffeomorph.mem_orientationPreservingSubgroup_iff.1 (hφ i hi).1
  refine ⟨?_, ?_⟩
  · obtain ⟨j, hj⟩ := Finset.nonempty_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
    exact Manifold.Orientation.IsPositive.sum_smul (fun i hi ↦ hσ₀.mpullback (hop i hi))
      (fun i hi ↦ (hpos i hi).le) ⟨j, hj, hpos j hj⟩
  · have hE : Module.finrank ℝ EF = 2 := by simpa using o.card_eq.symm
    have hone : ∀ i ∈ ρ.finsupport b',
        integralTopForm o (TauCeti.mpullback IF IF (φ i) σ₀.val) = 1 := fun i hi ↦
      (Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt
        (f := φ i) (φ i).toHomeomorph.isOpenEmbedding (hop i hi) (by simp)).trans hint
    rw [integralTopForm_sum o _ _ fun i _ ↦ ?_]
    · simp_rw [integralTopForm_smul]
      rw [Finset.sum_congr rfl fun i hi ↦ by rw [hone i hi, mul_one], hsum]
    · simpa using ((SmoothForm.mpullback (φ i) (φ i).contMDiff σ₀).isSmoothForm.smul
        (ρ i b')).integrableTopForm (isClosed_tsupport _).isCompact
        (Module.finBasisOfFinrankEq ℝ EF hE)

/-- **A chart reading the fibre forms as `σ₀`.** Let `A` be a smooth atlas of `proj : M → B`,
over a Hausdorff boundaryless base modelled on a finite-dimensional space, whose model fibre is a
closed surface `F`, connected or empty, with an orientation `o`, and whose coordinate changes
preserve `o`. Let `σ₀` be a two-form on `F` positive for `o`, and `τ` a two-form on `M` whose
pull-backs along the fibre inclusions of the chart `A.trivAt b` are positive for `o` with the
integral of `σ₀`.
Then there is a trivialization `e` of `proj` with the base set of `A.trivAt b`, smooth on its
source with an inverse smooth on its target, along whose fibre inclusions `τ` pulls back to
`σ₀`, and whose coordinate changes with every chart of `A`, in both directions, are
diffeomorphisms of `F` preserving `o`. -/
theorem exists_trivialization_mpullback_fiberInclusionMap_eq [T2Space B]
    [BoundarylessManifold IB B] [IF.Boundaryless] [T2Space F] [CompactSpace F]
    [PreconnectedSpace F] (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup (n := ∞) (by simp) o))
    {σ₀ : SmoothTwoForm IF F} (hσ₀ : o.IsPositive σ₀.val) {τ : SmoothTwoForm IM M} (b : B)
    (hτ : ∀ b' (hb' : b' ∈ (A.trivAt b).baseSet),
      o.IsPositive (SmoothForm.mpullback _ ((A.trivAt b).contMDiff_fiberInclusionMap
          (hA.contMDiffOn_trivAt_symm b) hb') τ).val ∧
      integralTopForm o (SmoothForm.mpullback _ ((A.trivAt b).contMDiff_fiberInclusionMap
          (hA.contMDiffOn_trivAt_symm b) hb') τ).val = integralTopForm o σ₀.val) :
    ∃ e : Trivialization F proj, ContMDiffOn IM (IB.prod IF) ∞ e e.source ∧
      ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target ∧
      e.baseSet = (A.trivAt b).baseSet ∧
      (∀ b' (hb' : b' ∈ e.baseSet),
        TauCeti.mpullback IF IM (e.fiberInclusionMap hb') τ.val = σ₀.val) ∧
      ∀ c x, x ∈ e.baseSet → x ∈ (A.trivAt c).baseSet →
        (∃ φ ∈ Diffeomorph.orientationPreservingSubgroup (n := ∞) (by simp) o,
          ⇑φ = e.coordChange (A.trivAt c) x) ∧
        ∃ φ ∈ Diffeomorph.orientationPreservingSubgroup (n := ∞) (by simp) o,
          ⇑φ = (A.trivAt c).coordChange e x := by
  set e := A.trivAt b
  have he := hA.contMDiffOn_trivAt b
  have he_symm := hA.contMDiffOn_trivAt_symm b
  set U : TopologicalSpace.Opens B := e.baseSetOpens
  have hU : (U : Set B) ⊆ e.baseSet := e.coe_baseSetOpens.subset
  -- The fibre forms `σ_p` over `U` are the slices of one form on `U × F`, and Moser's theorem
  -- for families of area forms gives `χ p` with `(χ p)^* σ_p = σ₀`.
  have hσ := e.mpullback_prodMk_mpullback_symm he_symm hU τ
  obtain ⟨Φ, χ, hΦ, hχ, hχo⟩ :=
    SmoothTwoForm.exists_diffeomorph_prod_mpullback_eq_of_integralTopForm_eq o hσ₀ _
      (fun p ↦ by rw [hσ]; exact (hτ p (hU p.property)).1) fun p ↦ by
        rw [hσ]; exact (hτ p (hU p.property)).2
  simp only [hσ] at hχ
  have hΦ' (q : U × F) : Φ.toHomeomorph q = (q.1, (χ q.1).toHomeomorph q.2) := hΦ q
  refine ⟨e.transFiberwiseHomeomorph hU Φ.toHomeomorph.symm
      (Homeomorph.fst_symm_apply_of_apply_eq_prodMk hΦ'),
    e.contMDiffOn_transFiberwiseHomeomorph hU _ _ he Φ.symm.contMDiff,
    e.contMDiffOn_transFiberwiseHomeomorph_symm hU _ _ he_symm Φ.contMDiff,
    (Trivialization.transFiberwiseHomeomorph_baseSet ..).trans e.coe_baseSetOpens,
    fun b' hb' ↦ ?_, fun c x hx hc ↦ ?_⟩
  · have hb : b' ∈ U := by rwa [Trivialization.transFiberwiseHomeomorph_baseSet] at hb'
    refine (SmoothForm.mpullback_eq_iff (Trivialization.contMDiff_fiberInclusionMap _
      (e.contMDiffOn_transFiberwiseHomeomorph_symm hU Φ.toHomeomorph.symm
        (Homeomorph.fst_symm_apply_of_apply_eq_prodMk hΦ') he_symm Φ.contMDiff) hb')).1 ?_
    rw [SmoothForm.mpullback_congr _
      ((e.contMDiff_fiberInclusionMap he_symm (hU hb)).comp (χ ⟨b', hb⟩).contMDiff)
      (by rw [e.coe_fiberInclusionMap_transFiberwiseHomeomorph_symm hU
          (χ := fun p ↦ (χ p).toHomeomorph) hΦ' hb,
        Diffeomorph.coe_toHomeomorph]),
      ← SmoothForm.mpullback_mpullback _ _ (χ ⟨b', hb⟩).contMDiff]
    exact hχ ⟨b', hb⟩
  · rw [Trivialization.transFiberwiseHomeomorph_baseSet] at hx
    obtain ⟨ψ, hψ, hψe⟩ := hasStructureGroup_iff.1 hH b c x (hU hx) hc
    obtain ⟨ψ', hψ', hψ'e⟩ := hasStructureGroup_iff.1 hH c b x hc (hU hx)
    refine ⟨⟨ψ * χ ⟨x, hx⟩, mul_mem hψ (hχo _), ?_⟩,
      ⟨(χ ⟨x, hx⟩)⁻¹ * ψ', mul_mem (inv_mem (hχo _)) hψ', ?_⟩⟩
    · rw [Trivialization.coordChange_transFiberwiseHomeomorph_symm_left e hU
        (χ := fun p ↦ (χ p).toHomeomorph) hΦ' _ hx,
        Diffeomorph.coe_mul, hψe, Diffeomorph.coe_toHomeomorph]
    · rw [Trivialization.coordChange_transFiberwiseHomeomorph_symm_right e hU
        (χ := fun p ↦ (χ p).toHomeomorph) hΦ' _ hx hc,
        Diffeomorph.coe_mul, Diffeomorph.coe_inv, hψ'e, Diffeomorph.coe_toHomeomorph_symm]

/-- **A symplectic atlas for an oriented surface fibration.** Let `A` be a smooth atlas of
`proj : M → B`, over a Hausdorff boundaryless base modelled on a finite-dimensional space, whose
model fibre is a closed surface `F`, connected or empty, with an orientation `o`, and whose
coordinate changes preserve `o`. Let `σ₀` be a two-form on `F` positive for `o`, and `τ` a
two-form on `M` whose pull-backs along the fibre inclusions of every chart of `A` are positive for
`o` with the integral of `σ₀`, such as the form of `exists_restricts_isPositive_area` when `σ₀`
has integral one. Then there is a smooth atlas `A'` of `proj`, with the same base set as `A` at
each point, whose coordinate changes preserve `σ₀`, along which `τ` restricts to `σ₀`, and whose
coordinate changes with the charts of `A` are diffeomorphisms of `F` preserving `o`. -/
theorem exists_symplecticAtlas_of_oriented [T2Space B] [BoundarylessManifold IB B]
    [IF.Boundaryless] [T2Space F] [CompactSpace F] [PreconnectedSpace F]
    (hA : A.IsContMDiff ∞ IB IF IM)
    (hH : A.HasStructureGroup (Diffeomorph.orientationPreservingSubgroup (n := ∞) (by simp) o))
    {σ₀ : SmoothTwoForm IF F} (hσ₀ : o.IsPositive σ₀.val) {τ : SmoothTwoForm IM M}
    (hτ : ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
      o.IsPositive (SmoothForm.mpullback _ ((A.trivAt b).contMDiff_fiberInclusionMap
          (hA.contMDiffOn_trivAt_symm b) hb') τ).val ∧
      integralTopForm o (SmoothForm.mpullback _ ((A.trivAt b).contMDiff_fiberInclusionMap
          (hA.contMDiffOn_trivAt_symm b) hb') τ).val = integralTopForm o σ₀.val) :
    ∃ A' : Atlas F proj, A'.IsContMDiff ∞ IB IF IM ∧
      A'.HasStructureGroup (SmoothForm.diffeomorphStabilizer σ₀) ∧ A'.RestrictsTo σ₀ τ ∧
      A.CoordChangeMem A' (Diffeomorph.orientationPreservingSubgroup (n := ∞) (by simp) o) ∧
      ∀ b, (A'.trivAt b).baseSet = (A.trivAt b).baseSet := by
  choose e he he_symm hbase hτe hce using fun b ↦
    exists_trivialization_mpullback_fiberInclusionMap_eq hA hH hσ₀ b (hτ b)
  let A' : Atlas F proj := ⟨e, fun b ↦ hbase b ▸ A.mem_baseSet_trivAt b⟩
  have hA' : A'.IsContMDiff ∞ IB IF IM := ⟨he, he_symm⟩
  have hτ' : A'.RestrictsTo σ₀ τ := restrictsTo_iff.2 hτe
  exact ⟨A', hA', hτ'.hasStructureGroup hA', hτ',
    coordChangeMem_iff.2 fun c b x hc hb ↦ (hce b c x hb hc).2, hbase⟩

end TauCeti.MapFiber.Atlas

end

end
