/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.GradientFlow
import TauCeti.Geometry.Symplectic.Manifold.Rescale

/-!
# Moment weights and limit points

For a complexified action of `Gc` on a compact manifold `M`, with `-μ` a moment map for `σ` and
the metric `g(u, w) = σ(u, J w)`, the function `t ↦ ⟨μ (exp (i t ξ) p), ξ⟩` is antitone
(`antitone_moment_expI`) and bounded below, since `M` is compact. Its limit as `t → ∞` is the
*moment weight* `w_μ(p, ξ)`, defined for every `ξ ∈ 𝔤`, following [GeorgoulasRobbinSalamon2021]
and [McDuffSalamon2017], §5.7.

For `ξ ∈ 𝔤` the curve `t ↦ exp (i t ξ) p` is the negative gradient trajectory through `p` of
`x ↦ ⟨μ x, ξ⟩`, which is a Morse–Bott function when `G` is compact. Its limit as `t → ∞` is the
*limit point* `p⁺_ξ` (`limitPoint`). It exists for every `ξ`, not only for `ξ` in
`nonzeroPeriods I G` (`tendsto_limitPoint`), and it is a critical point of `x ↦ ⟨μ x, ξ⟩`
(`limitPoint_mem_criticalPoints`). The curve is the maximal integral curve of `-grad ⟨μ, ξ⟩`
(`maximalIntegralCurve_neg_mgradient_moment`), and such trajectories converge to critical points
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_tendsto_maximalIntegralCurve_neg_mgradient`, which
rests on Tau Ceti's Morse–Bott theorem for the components of a moment map). That theorem is
stated for manifolds modelled on `𝓘(ℝ, E')`, and so are the results on limit points.

## Main definitions

* `SymplecticGeometry.momentWeight C μ p ξ`: the limit of `μ (C.expI (t • ξ) • p) ξ` as
  `t → ∞`.
* `SymplecticGeometry.limitPoint C p ξ`: the limit of `C.expI (t • ξ) • p` as `t → ∞`.

## Main results

* `SymplecticGeometry.tendsto_momentWeight`: on a compact manifold the limit defining the moment
  weight exists, for every `ξ`.
* `SymplecticGeometry.momentWeight_eq_iInf`: the moment weight is the infimum of
  `μ (C.expI (t • ξ) • p) ξ` over `t`.
* `SymplecticGeometry.momentWeight_le`: `w_μ(p, ξ) ≤ ⟨μ p, ξ⟩`.
* `SymplecticGeometry.tendsto_limitPoint`: on a compact manifold, for a compact `G`, the limit
  defining the limit point exists, for every `ξ`.
* `SymplecticGeometry.limitPoint_mem_criticalPoints`: the limit point is a critical point of
  `x ↦ ⟨μ x, ξ⟩`.
* `SymplecticGeometry.momentWeight_eq_moment_limitPoint`: `w_μ(p, ξ) = ⟨μ (p⁺_ξ), ξ⟩`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021].
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.7.
-/

public section

noncomputable section

open Filter Topology TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-! ### Moment weights -/

section Weight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {M : Type*} [MulAction Gc M]

/-- The *moment weight* `w_μ(p, ξ)`: the limit of `⟨μ (exp (i t ξ) p), ξ⟩`, that is, of
`μ (C.expI (t • ξ) • p) ξ`, as `t → ∞`. It is a junk value where the limit does not exist; for a
complexified action on a compact manifold the limit exists for every `ξ`
(`tendsto_momentWeight`). -/
def momentWeight (C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) (p : M) (ξ : GroupLieAlgebra I G) : ℝ :=
  limUnder atTop fun t : ℝ ↦ μ (C.expI (t • ξ) • p) ξ

theorem momentWeight_def (C : LieComplexification I G IC Gc)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra I G)) (p : M) (ξ : GroupLieAlgebra I G) :
    momentWeight C μ p ξ = limUnder atTop fun t : ℝ ↦ μ (C.expI (t • ξ) • p) ξ :=
  (rfl)

open _root_.Bundle
open scoped RealInnerProductSpace

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [CompactSpace M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {C : LieComplexification I G IC Gc} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- On a compact manifold, `t ↦ μ (C.expI (t • ξ) • p) ξ` converges, as `t → ∞`, to its infimum
over `t`. -/
private theorem tendsto_moment_expI_iInf (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    Tendsto (fun t : ℝ ↦ μ (C.expI (t • ξ) • p) ξ) atTop
      (𝓝 (⨅ t : ℝ, μ (C.expI (t • ξ) • p) ξ)) := by
  -- `x ↦ μ x ξ` is continuous on the compact space `M`, so the function is bounded below.
  have hc : Continuous fun x : M ↦ μ x ξ := by
    simpa using (hμ.contMDiff ξ).continuous.neg
  have hbdd : BddBelow (Set.range fun t : ℝ ↦ μ (C.expI (t • ξ) • p) ξ) := by
    obtain ⟨m, hm⟩ := isCompact_univ.bddBelow_image hc.continuousOn
    exact ⟨m, Set.forall_mem_range.2 fun t ↦ hm ⟨_, Set.mem_univ _, rfl⟩⟩
  exact tendsto_atTop_ciInf (antitone_moment_expI h hμ hg ξ p) hbdd

/-- The moment weight is the infimum of `μ (C.expI (t • ξ) • p) ξ` over `t`. -/
theorem momentWeight_eq_iInf (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    momentWeight C μ p ξ = ⨅ t : ℝ, μ (C.expI (t • ξ) • p) ξ := by
  rw [momentWeight_def]
  exact (tendsto_moment_expI_iInf h hμ hg p ξ).limUnder_eq

/-- **The moment weights exist.** For a complexified action on a compact manifold, with `-μ` a
moment map for `σ` and the metric `g(u, w) = σ(u, J w)`, the function
`t ↦ μ (C.expI (t • ξ) • p) ξ` converges to `momentWeight C μ p ξ` as `t → ∞`, for every `ξ`. -/
theorem tendsto_momentWeight (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    Tendsto (fun t : ℝ ↦ μ (C.expI (t • ξ) • p) ξ) atTop (𝓝 (momentWeight C μ p ξ)) := by
  rw [momentWeight_eq_iInf h hμ hg]
  exact tendsto_moment_expI_iInf h hμ hg p ξ

/-- The moment weight is at most `μ (C.expI (t • ξ) • p) ξ`, for every `t`. -/
theorem momentWeight_le_moment_expI_smul (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) (t : ℝ) :
    momentWeight C μ p ξ ≤ μ (C.expI (t • ξ) • p) ξ :=
  (antitone_moment_expI h hμ hg ξ p).le_of_tendsto (tendsto_momentWeight h hμ hg p ξ) t

/-- **The moment weight is at most the moment.** For a complexified action on a compact manifold,
with `-μ` a moment map for `σ` and the metric `g(u, w) = σ(u, J w)`,
`w_μ(p, ξ) ≤ ⟨μ p, ξ⟩`. -/
theorem momentWeight_le (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    momentWeight C μ p ξ ≤ μ p ξ := by
  simpa using momentWeight_le_moment_expI_smul h hμ hg p ξ 0

end Weight

/-! ### Limit points -/

section LimitPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {M : Type*} [MulAction Gc M] [TopologicalSpace M]

/-- The *limit point* `p⁺_ξ`: the limit of `exp (i t ξ) p`, that is, of `C.expI (t • ξ) • p`, as
`t → ∞`. It is a junk value where the limit does not exist. The limit exists for every `ξ` when
`G` is compact and acts, with complexified action of `Gc`, on a compact manifold modelled on
`𝓘(ℝ, E')`, with `-μ` a moment map for `σ` and the `C¹` metric `g(u, w) = σ(u, J w)`
(`tendsto_limitPoint`). -/
def limitPoint (C : LieComplexification I G IC Gc) (p : M) (ξ : GroupLieAlgebra I G) : M :=
  haveI : Nonempty M := ⟨p⟩
  limUnder atTop fun t : ℝ ↦ C.expI (t • ξ) • p

theorem limitPoint_def (C : LieComplexification I G IC Gc) (p : M) (ξ : GroupLieAlgebra I G) :
    limitPoint C p ξ =
      haveI : Nonempty M := ⟨p⟩
      limUnder atTop fun t : ℝ ↦ C.expI (t • ξ) • p :=
  (rfl)

/-- If `C.expI (t • ξ) • p` converges to `x` as `t → ∞`, then `x` is the limit point. -/
theorem limitPoint_eq_of_tendsto [T2Space M] {C : LieComplexification I G IC Gc} {p x : M}
    {ξ : GroupLieAlgebra I G} (h : Tendsto (fun t : ℝ ↦ C.expI (t • ξ) • p) atTop (𝓝 x)) :
    limitPoint C p ξ = x := by
  rw [limitPoint_def]
  exact h.limUnder_eq

open _root_.Bundle Manifold
open scoped RealInnerProductSpace

variable [FiniteDimensional ℝ E] [T2Space G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [ChartedSpace E' M] [IsManifold 𝓘(ℝ, E') ∞ M] [T2Space M] [CompactSpace M]
  [MulAction G M] [ContMDiffSMul I 𝓘(ℝ, E') ∞ G M] [ContMDiffSMul IC 𝓘(ℝ, E') ∞ Gc M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E') x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E') 1 E' (fun x : M ↦ TangentSpace 𝓘(ℝ, E') x)]
  {σ : SmoothTwoForm 𝓘(ℝ, E') M} {J : SmoothAlmostComplexStructure 𝓘(ℝ, E') M}
  {C : LieComplexification I G IC Gc} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- The curve `t ↦ C.expI (t • ξ) • p` converges to a critical point of `x ↦ μ x ξ`. -/
private theorem exists_mem_criticalPoints_tendsto_expI_smul (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace 𝓘(ℝ, E') x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    ∃ q ∈ criticalPoints 𝓘(ℝ, E') (fun x ↦ μ x ξ),
      Tendsto (fun t : ℝ ↦ C.expI (t • ξ) • p) atTop (𝓝 q) := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  -- `μ` is a moment map for `-σ`, which is nondegenerate since `σ` is compatible with `J`.
  have hμ' : (-σ).IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ := by
    simpa using hμ.neg
  have hσ' : (-σ).IsNondegenerate :=
    SmoothTwoForm.isNondegenerate_neg_iff.2
      (SmoothTwoForm.compatible_of_inner_eq hg).isNondegenerate
  rw [← maximalIntegralCurve_neg_mgradient_moment h hμ hg]
  exact hμ'.exists_tendsto_maximalIntegralCurve_neg_mgradient hσ' ξ p

/-- **The limit points exist.** For a complexified action of `Gc` on a compact manifold modelled
on `𝓘(ℝ, E')`, with `G` compact, `-μ` a moment map for `σ` and the `C¹` metric
`g(u, w) = σ(u, J w)`, the curve `t ↦ C.expI (t • ξ) • p` converges to `limitPoint C p ξ` as
`t → ∞`, for every `ξ`. -/
theorem tendsto_limitPoint (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace 𝓘(ℝ, E') x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    Tendsto (fun t : ℝ ↦ C.expI (t • ξ) • p) atTop (𝓝 (limitPoint C p ξ)) := by
  obtain ⟨q, -, hq⟩ := exists_mem_criticalPoints_tendsto_expI_smul h hμ hg p ξ
  rwa [limitPoint_eq_of_tendsto hq]

/-- The limit point is a critical point of `x ↦ μ x ξ`, under the hypotheses of
`tendsto_limitPoint`. -/
theorem limitPoint_mem_criticalPoints (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace 𝓘(ℝ, E') x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    limitPoint C p ξ ∈ criticalPoints 𝓘(ℝ, E') fun x ↦ μ x ξ := by
  obtain ⟨q, hq, hlim⟩ := exists_mem_criticalPoints_tendsto_expI_smul h hμ hg p ξ
  rwa [limitPoint_eq_of_tendsto hlim]

/-- The moment weight is the value of `x ↦ μ x ξ` at the limit point. -/
theorem momentWeight_eq_moment_limitPoint (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace 𝓘(ℝ, E') x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    momentWeight C μ p ξ = μ (limitPoint C p ξ) ξ := by
  have hc : Continuous fun x : M ↦ μ x ξ := by
    simpa using (hμ.contMDiff ξ).continuous.neg
  exact tendsto_nhds_unique (tendsto_momentWeight h hμ hg p ξ)
    ((hc.tendsto _).comp (tendsto_limitPoint h hμ hg p ξ))

end LimitPoint

end SymplecticGeometry

end
