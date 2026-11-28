/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Function
public import SymplecticGeometry.Geometry.Lie.Subgroup.Parabolic
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Analysis.Calculus.Deriv.MeanValue
import SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.GradientFlow
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Stability
import SymplecticGeometry.Topology.Algebra.Module.InnerProducts
import TauCeti.Analysis.Calculus.Deriv.Growth
import TauCeti.LinearAlgebra.BilinearForm.Basic
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

The Kempf–Ness function `Φ_p` has derivative `-⟨μ (exp (i t ξ) p), ξ⟩` along
`t ↦ exp (-i t ξ)` (`hasDerivAt_kempfNessFunction_expI_neg_smul`), so this derivative tends
to `-w_μ(p, ξ)` (`tendsto_deriv_kempfNessFunction`). Since the moment weight is also a lower
bound for `⟨μ (exp (i t ξ) p), ξ⟩`, that derivative is at most `-w_μ(p, ξ)`, so
`Φ_p (exp (-i t ξ)) ≤ -w_μ(p, ξ) t` for `t ≥ 0` (`kempfNessFunction_expI_neg_smul_le`), and a
positive weight makes `Φ_p` unbounded below. By
`isSemistable_iff_bddBelow_kempfNessFunction`, the weights of a semistable point are therefore
nonpositive (`IsSemistable.momentWeight_nonpos`), which is one half of the
numerical criterion for semistability in [GeorgoulasRobbinSalamon2021].

The moment-weight inequality `w_μ(p, ξ) ≤ ‖ξ‖ ‖μ (g p)‖`, with both norms those of an
`Ad`-invariant form `B` (`momentWeight_le_mul_norm`), is the one of [GeorgoulasRobbinSalamon2021],
and holds for every `ξ`, periodic or not. Write `exp (-i t ξ) = g⁻¹ a(t)` with
`a(t) = g exp (-i t ξ)`. The tangent line of `Φ_p` at `g⁻¹` (convexity along geodesics, through
`kempfNessFunction_sub_sqrt_momentNormSq_mul_sqrt_le`) bounds `Φ_p (exp (-i t ξ))` below by
`Φ_p (g⁻¹) - ‖μ (g p)‖ r(t)`, where `r(t)` is the polar radius of `a(t)`, which grows at most
like `‖ξ‖ t` (`LieComplexification.sqrt_polar_symm_fst_le_add_mul`). Against the upper bound
`Φ_p (exp (-i t ξ)) ≤ -w_μ(p, ξ) t` above, dividing by `t` and letting `t → ∞` gives the
inequality.

Weights and limit points move as expected under `G` and under the parabolic subgroup
`C.parabolic ξ` of [GeorgoulasRobbinSalamon2021] (arXiv v2, Lemma 7.5). For `u : G` the curve
`exp (i t Ad_u ξ) u x` is `u exp (i t ξ) x` (`LieComplexification.toHom_mul_expI_mul_inv`), and
`μ` is equivariant, which gives `momentWeight_toHom_smul` and `limitPoint_toHom_smul`. For `q`
in `C.parabolic ξ`, `exp (i t ξ) q x` is the conjugate `exp (i t ξ) q exp (-i t ξ)`, which
converges, acting on `exp (i t ξ) x` (`limitPoint_smul_of_mem_parabolic`). For the weight, the
quotient `Φ_p (exp (-i s ξ)) / s` tends to `-w_μ(p, ξ)`
(`tendsto_kempfNessFunction_expI_neg_smul_div`, by Tau Ceti's
`tendsto_inv_smul_atTop_of_tendsto_deriv` and the limit of the derivative), and by the cocycle
identity `kempfNessFunction_mul` the functions for `q x` and `x` differ along `exp (-i s ξ)` by
a bounded amount, since the conjugates of `q⁻¹` converge and so have bounded polar radius
(`abs_kempfNessFunction_expI_mul_toHom_le`, `exists_eventually_abs_kempfNessFunction_le`); so
`w_μ(q x, ξ) = w_μ(x, ξ)` (`momentWeight_smul_of_mem_parabolic`).

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
* `SymplecticGeometry.tendsto_deriv_kempfNessFunction`: the slope identity, the derivative of
  `t ↦ Φ_p (C.expI (-(t • ξ)))` tends to `-w_μ(p, ξ)` as `t → ∞`.
* `SymplecticGeometry.kempfNessFunction_expI_neg_smul_le`: `Φ_p (C.expI (-(t • ξ))) ≤ -w_μ(p, ξ) t`
  for `t ≥ 0`.
* `SymplecticGeometry.not_bddBelow_kempfNessFunction_of_momentWeight_pos`: a positive weight
  makes `Φ_p` unbounded below.
* `SymplecticGeometry.momentWeight_le_mul_norm`: the moment-weight inequality
  `w_μ(p, ξ) ≤ √(B ξ ξ) * √(‖μ (g • p)‖²)`.
* `SymplecticGeometry.momentWeight_toHom_smul`, `SymplecticGeometry.limitPoint_toHom_smul`:
  `w_μ(u x, Ad u ξ) = w_μ(x, ξ)` and `(u x)⁺_{Ad u ξ} = u x⁺_ξ` for `u : G`.
* `SymplecticGeometry.limitPoint_smul_of_mem_parabolic`,
  `SymplecticGeometry.momentWeight_smul_of_mem_parabolic`: for `q` in the parabolic subgroup
  `C.parabolic ξ`, `(q x)⁺_ξ = C.parabolicLimit ξ q • x⁺_ξ` and `w_μ(q x, ξ) = w_μ(x, ξ)`.
* `SymplecticGeometry.tendsto_kempfNessFunction_expI_neg_smul_div`:
  `Φ_p (C.expI (-(s • ξ))) / s → -w_μ(p, ξ)` as `s → ∞`.
* `SymplecticGeometry.exists_eventually_abs_kempfNessFunction_le`: along a convergent curve in
  `Gc`, `Φ_p` is eventually bounded, uniformly in `p`.
* `SymplecticGeometry.IsSemistable.momentWeight_nonpos`: at a semistable point every moment weight
  is nonpositive.

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

omit [CompactSpace M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle fun x : M ↦ TangentSpace I' x] in
/-- **Moment weights under `G`.** For a complexified action, with `-μ` an equivariant moment map
for `σ` and `G` connected, `w_μ(u x, Ad u ξ) = w_μ(x, ξ)` for every `u : G`. -/
theorem momentWeight_toHom_smul [FiniteDimensional ℝ E] [ConnectedSpace G]
    (h : IsComplexifiedAction C J) (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x) (u : G) (x : M)
    (ξ : GroupLieAlgebra I G) :
    momentWeight C μ (C.toHom u • x) (Lie.tangentAd (I := I) u ξ) = momentWeight C μ x ξ := by
  have := C.finiteDimensional
  have := FiniteDimensional.completeSpace ℝ E'
  simp only [momentWeight_def]
  congr 1
  funext t
  rw [← map_smul, ← C.toHom_mul_expI_mul_inv, smul_smul, inv_mul_cancel_right, mul_smul,
    h.moment_toHom_smul hμ, Lie.coadjointRepresentation_apply, ← Lie.tangentAd_apply,
    Lie.tangentAd_inv, LieEquiv.symm_apply_apply]

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

/-- **Limit points under `G`.** Under the hypotheses of `tendsto_limitPoint`, with `G` connected,
`(u x)⁺_{Ad u ξ} = u x⁺_ξ` for every `u : G`. -/
theorem limitPoint_toHom_smul [ConnectedSpace G] (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace 𝓘(ℝ, E') x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (u : G) (x : M) (ξ : GroupLieAlgebra I G) :
    limitPoint C (C.toHom u • x) (Lie.tangentAd (I := I) u ξ) = C.toHom u • limitPoint C x ξ := by
  have := C.finiteDimensional
  have : ContinuousSMul Gc M := ContMDiffSMul.continuousSMul (I := IC) (I' := 𝓘(ℝ, E')) ∞
  refine limitPoint_eq_of_tendsto (((tendsto_limitPoint h hμ hg x ξ).const_smul
    (C.toHom u)).congr fun t ↦ ?_)
  rw [← map_smul, ← C.toHom_mul_expI_mul_inv, smul_smul, smul_smul, inv_mul_cancel_right]

/-- **Limit points under the parabolic subgroup.** Under the hypotheses of `tendsto_limitPoint`,
for `q` in the parabolic subgroup `C.parabolic ξ`, the limit point `(q x)⁺_ξ` is the image of
`x⁺_ξ` under `C.parabolicLimit ξ q`, the limit of the conjugates `exp (i t ξ) q exp (-i t ξ)`. -/
theorem limitPoint_smul_of_mem_parabolic (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace 𝓘(ℝ, E') x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {ξ : GroupLieAlgebra I G} (q : C.parabolic ξ) (x : M) :
    limitPoint C ((q : Gc) • x) ξ = C.parabolicLimit ξ q • limitPoint C x ξ := by
  have : ContinuousSMul Gc M := ContMDiffSMul.continuousSMul (I := IC) (I' := 𝓘(ℝ, E')) ∞
  -- `exp (i t ξ) q x` is the conjugate of `q` at time `t` acting on `exp (i t ξ) x`.
  refine limitPoint_eq_of_tendsto (((C.tendsto_parabolicLimit ξ q).smul
    (tendsto_limitPoint h hμ hg x ξ)).congr fun t ↦ ?_)
  rw [smul_smul, C.expI_neg, inv_mul_cancel_right, mul_smul]

end LimitPoint

/-! ### The slope identity and the obstruction to semistability -/

section Slope

open _root_.Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [ConnectedSpace G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [CompactSpace M]
  [MulAction G M] [MulAction Gc M] [ContMDiffSMul I I' ∞ G M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {C : LieComplexification I G IC Gc} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

open scoped RealInnerProductSpace

/-- **The slope identity.** For a complexified action on a compact manifold, with `-μ` an
equivariant moment map for `σ` and the metric `g(u, w) = σ(u, J w)`, the derivative of
`t ↦ Φ_p (C.expI (-(t • ξ)))`, the Kempf–Ness function along `exp (-i t ξ)`, tends to
`-w_μ(p, ξ)` as `t → ∞`, for every `ξ`. -/
theorem tendsto_deriv_kempfNessFunction (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    Tendsto (deriv fun t : ℝ ↦ kempfNessFunction C μ p (C.expI (-(t • ξ)))) atTop
      (𝓝 (-momentWeight C μ p ξ)) := by
  have hd : (deriv fun t : ℝ ↦ kempfNessFunction C μ p (C.expI (-(t • ξ)))) =
      fun t ↦ -μ (C.expI (t • ξ) • p) ξ :=
    funext fun t ↦ (hasDerivAt_kempfNessFunction_expI_neg_smul C μ p h hμ hg ξ t).deriv
  rw [hd]
  exact (tendsto_momentWeight h hμ.toIsMomentMap hg p ξ).neg

/-- Along `t ↦ C.expI (-(t • ξ))`, the Kempf–Ness function decreases with slope at least
`w_μ(p, ξ)`: `Φ_p (C.expI (-(t • ξ))) ≤ -(w_μ(p, ξ) * t)` for `t ≥ 0`, under the hypotheses of
`tendsto_deriv_kempfNessFunction`. -/
theorem kempfNessFunction_expI_neg_smul_le (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) {t : ℝ} (ht : 0 ≤ t) :
    kempfNessFunction C μ p (C.expI (-(t • ξ))) ≤ -(momentWeight C μ p ξ * t) := by
  have hd := hasDerivAt_kempfNessFunction_expI_neg_smul C μ p h hμ hg ξ
  have := image_sub_le_mul_sub_of_deriv_le (fun s ↦ (hd s).differentiableAt)
    (fun s ↦ (hd s).deriv.trans_le <|
      neg_le_neg (momentWeight_le_moment_expI_smul h hμ.toIsMomentMap hg p ξ s)) ht
  simp only [zero_smul, neg_zero, C.expI_zero, kempfNessFunction_one, sub_zero] at this
  linarith

/-- If the moment weight `w_μ(p, ξ)` is positive, then the Kempf–Ness function `Φ_p` is not
bounded below, under the hypotheses of `tendsto_deriv_kempfNessFunction`: along
`t ↦ C.expI (-(t • ξ))` it is at most `-(w_μ(p, ξ) * t)` for `t ≥ 0`. -/
theorem not_bddBelow_kempfNessFunction_of_momentWeight_pos (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {p : M} {ξ : GroupLieAlgebra I G} (hw : 0 < momentWeight C μ p ξ) :
    ¬BddBelow (Set.range (kempfNessFunction C μ p)) := by
  rintro ⟨m, hm⟩
  -- At `t = (|m| + 1) / w_μ(p, ξ)` the upper bound `-(w_μ(p, ξ) * t)` is below `m`.
  have ht : 0 ≤ (|m| + 1) / momentWeight C μ p ξ := by positivity
  have hup := kempfNessFunction_expI_neg_smul_le h hμ hg p ξ ht
  rw [mul_div_cancel₀ _ hw.ne'] at hup
  linarith [(hm ⟨_, rfl⟩).trans hup, neg_abs_le m]

/-- **The asymptotic slope of the Kempf–Ness function.** Under the hypotheses of
`tendsto_deriv_kempfNessFunction`, `Φ_p (C.expI (-(s • ξ))) / s` tends to `-w_μ(p, ξ)` as
`s → ∞`. -/
theorem tendsto_kempfNessFunction_expI_neg_smul_div (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) :
    Tendsto (fun s : ℝ ↦ kempfNessFunction C μ p (C.expI (-(s • ξ))) / s) atTop
      (𝓝 (-momentWeight C μ p ξ)) := by
  simpa [div_eq_inv_mul] using tendsto_inv_smul_atTop_of_tendsto_deriv
    (.of_forall (hasDerivAt_kempfNessFunction_expI_neg_smul C μ p h hμ hg ξ))
    (tendsto_momentWeight h hμ.toIsMomentMap hg p ξ).neg

omit [ConnectedSpace G] [FiniteDimensional ℝ E'] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  [ContMDiffSMul IC I' ∞ Gc M] [RiemannianBundle (fun x : M ↦ TangentSpace I' x)] in
/-- **Kempf–Ness functions along a convergent curve.** On a compact manifold, with `-μ` a moment
map for `σ`, if `k` converges along `l`, then `Φ_p (k s)` is eventually bounded along `l`,
uniformly in `p`. -/
theorem exists_eventually_abs_kempfNessFunction_le
    {a : InfinitesimalAction (GroupLieAlgebra I G) I' M} (hμ : σ.IsMomentMap a fun x ↦ -μ x)
    {α : Type*} {l : Filter α} {k : α → Gc} {g₀ : Gc} (hk : Tendsto k l (𝓝 g₀)) :
    ∃ R, ∀ᶠ s in l, ∀ p, |kempfNessFunction C μ p (k s)| ≤ R := by
  -- A positive definite form `B` on the Lie algebra, from an inner product on it. The norm
  -- of `E` on the Lie algebra is opened only to state `innerProducts`.
  open scoped GroupLieAlgebra in
  obtain ⟨g, hg⟩ := innerProducts_nonempty (GroupLieAlgebra I G)
  obtain ⟨hgs, hgp⟩ := mem_innerProducts.1 hg
  let B := g.toBilinForm
  have hBp : B.toQuadraticMap.PosDef := fun v hv ↦ by simpa [B] using hgp v hv
  have hBs : B.IsSymm := ContinuousLinearMap.isSymm_toBilinForm_iff.2 hgs
  have hB : B.Nondegenerate := B.nondegenerate_of_anisotropic hBp.anisotropic
  -- A bound `L` for `√(‖μ‖²)` on `M`, so `|Φ_p (k s)|` is at most `L` times the polar radius.
  obtain ⟨L, hL⟩ := isCompact_univ.bddAbove_image
    (hμ.contMDiff_momentNormSq.continuous.sqrt.continuousOn :
      ContinuousOn (fun y ↦ √(momentNormSq (fun x ↦ -μ x) (B.toDual hB).symm y)) Set.univ)
  have hL' (y : M) : √(momentNormSq μ (B.toDual hB).symm y) ≤ L := by
    simpa [momentNormSq_neg] using hL ⟨y, Set.mem_univ y, rfl⟩
  have hc : Continuous fun g' : Gc ↦
      L * √(B ((C.polar.symm g').1 : GroupLieAlgebra I G) (C.polar.symm g').1) :=
    continuous_const.mul (((LinearMap.continuous_apply_self B).comp
      (continuous_fst.comp C.polar.symm.continuous)).sqrt)
  obtain ⟨R, hR⟩ := ((hc.tendsto g₀).comp hk).isBoundedUnder_le
  refine ⟨R, (eventually_map.1 hR).mono fun s hs p ↦ ?_⟩
  rw [← C.expI_mul_toHom_polar_symm (k s)]
  exact (abs_kempfNessFunction_expI_mul_toHom_le C μ p hBs
    (LinearMap.BilinForm.isNonneg_def.2 hBp.nonneg) hL' _ _).trans hs

/-- **Moment weights under the parabolic subgroup.** Under the hypotheses of
`tendsto_deriv_kempfNessFunction`, `w_μ(q x, ξ) = w_μ(x, ξ)` for every `q` in the
parabolic subgroup `C.parabolic ξ`. -/
theorem momentWeight_smul_of_mem_parabolic (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {ξ : GroupLieAlgebra I G} (q : C.parabolic ξ) (x : M) :
    momentWeight C μ ((q : Gc) • x) ξ = momentWeight C μ x ξ := by
  have := topologicalGroup_of_lieGroup IC ∞ (G := Gc)
  -- The conjugates `k s = exp (i s ξ) q⁻¹ exp (-i s ξ)` converge, so `Φ` is bounded along them.
  set k : ℝ → Gc := fun s ↦ C.expI (s • ξ) * (q : Gc)⁻¹ * C.expI (-(s • ξ))
  have hk : Tendsto k atTop (𝓝 (C.parabolicLimit ξ q⁻¹)) := by
    simpa only [Subgroup.coe_inv] using C.tendsto_parabolicLimit ξ q⁻¹
  obtain ⟨R, hR⟩ := exists_eventually_abs_kempfNessFunction_le (C := C) hμ.toIsMomentMap hk
  -- `Φ_{q x} (exp (-i s ξ)) = Φ_x (exp (-i s ξ)) + Φ_y (k s) - Φ_x q⁻¹` with `y = exp (i s ξ) x`.
  have hid (s : ℝ) : kempfNessFunction C μ ((q : Gc) • x) (C.expI (-(s • ξ))) =
      kempfNessFunction C μ x (C.expI (-(s • ξ))) +
        (kempfNessFunction C μ ((C.expI (-(s • ξ)))⁻¹ • x) (k s) -
          kempfNessFunction C μ x (q : Gc)⁻¹) := by
    have h1 := kempfNessFunction_mul C μ x h hμ hg (q : Gc)⁻¹ (C.expI (-(s • ξ)))
    have h2 := kempfNessFunction_mul C μ x h hμ hg (C.expI (-(s • ξ))) (k s)
    rw [inv_inv] at h1
    have he : C.expI (-(s • ξ)) * k s = (q : Gc)⁻¹ * C.expI (-(s • ξ)) := by
      simp only [k, C.expI_neg]
      group
    rw [he] at h2
    linarith
  have hsmall : Tendsto (fun s : ℝ ↦
      (kempfNessFunction C μ ((C.expI (-(s • ξ)))⁻¹ • x) (k s) -
        kempfNessFunction C μ x (q : Gc)⁻¹) / s) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      ((tendsto_const_nhds (x := R + |kempfNessFunction C μ x (q : Gc)⁻¹|)).div_atTop tendsto_id)
    filter_upwards [hR, eventually_gt_atTop 0] with s hRs hs
    rw [norm_div, Real.norm_of_nonneg hs.le, Real.norm_eq_abs, id_eq]
    refine div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add_left ?_ _)) hs.le
    exact hRs _
  have := tendsto_nhds_unique (tendsto_kempfNessFunction_expI_neg_smul_div h hμ hg _ ξ)
    (((tendsto_kempfNessFunction_expI_neg_smul_div h hμ hg x ξ).add hsmall).congr fun s ↦ by
      rw [hid, add_div])
  linarith

/-- **The moment-weight inequality.** For a complexified action on a compact manifold, with `-μ`
an equivariant moment map for `σ`, the metric `g(u, w) = σ(u, J w)` and a symmetric, nonnegative,
nondegenerate, `Ad`-invariant form `B` on the Lie algebra of the connected group `G`,
`w_μ(p, ξ) ≤ √(B ξ ξ) * √(‖μ (g • p)‖²)` for every `ξ` and every `g : Gc`, where `‖μ x‖²` is
`momentNormSq μ (B.toDual hB).symm x`: both norms are those of `B`. -/
theorem momentWeight_le_mul_norm (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)} {hB : B.Nondegenerate} (hBs : B.IsSymm)
    (hpos : B.IsNonneg) (hBG : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B)
    (p : M) (ξ : GroupLieAlgebra I G) (g : Gc) :
    momentWeight C μ p ξ ≤ √(B ξ ξ) * √(momentNormSq μ (B.toDual hB).symm (g • p)) := by
  set w := momentWeight C μ p ξ
  set K := √(B ξ ξ)
  set S := √(momentNormSq μ (B.toDual hB).symm (g • p))
  -- The curve `a t = g * exp (-i t ξ)`, with constant left-trivialized derivative
  -- `-cplx (lieMap ξ)`, whose imaginary part is `-ξ`.
  set a : ℝ → Gc := fun t ↦ g * C.expI (-(t • ξ))
  have ha : HasLeftTrivializedDerivOn a (fun _ ↦ -C.cplx (C.lieMap ξ)) Set.univ := by
    refine ((hasLeftTrivializedDerivOn_mulInvariantExp_smul (I := IC)
      (-C.cplx (C.lieMap ξ))).const_mul g).congr fun t _ ↦ ?_
    simp only [a, C.expI_def, map_neg, map_smul, smul_neg]
  have hK (_ : ℝ) : √(B (C.im (-C.cplx (C.lieMap ξ))) (C.im (-C.cplx (C.lieMap ξ)))) ≤ K := by
    rw [map_neg, C.im_cplx_lieMap, LinearMap.map_neg₂, map_neg, neg_neg]
  set R₀ := √(B (C.polar.symm (a 0)).1 (C.polar.symm (a 0)).1)
  set c := S * R₀ - kempfNessFunction C μ p g⁻¹
  -- The lower bound from convexity at `g⁻¹`, with the polar radius of `a t`, against the upper
  -- bound along `exp (-i t ξ)`.
  have hmain {t : ℝ} (ht : 0 ≤ t) : w * t ≤ c + K * S * t := by
    have hR := C.sqrt_polar_symm_fst_le_add_mul hBs hpos hBG ha hK ht
    have hlow := kempfNessFunction_sub_sqrt_momentNormSq_mul_sqrt_le C μ p h hμ hg (hB := hB) hBs
      hpos g⁻¹ (C.polar.symm (a t)).1 (C.polar.symm (a t)).2
    rw [inv_inv, mul_assoc, C.expI_mul_toHom_polar_symm, inv_mul_cancel_left] at hlow
    have hup := kempfNessFunction_expI_neg_smul_le h hμ hg p ξ ht
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hR hS]
  -- So `t ↦ c + (K * S - w) * t` is nonnegative for `t ≥ 0`, and its slope is nonnegative.
  have hslope := nonneg_of_bddBelow_of_hasDerivAt_le (a := 0) (c := K * S - w)
    (f := fun t ↦ c + (K * S - w) * t)
    ⟨0, by rintro _ ⟨t, ht, rfl⟩; linarith [hmain (Set.mem_Ici.1 ht)]⟩
    (fun t _ ↦ by simpa using ((hasDerivAt_id t).const_mul (K * S - w)).const_add c)
    fun _ _ ↦ le_rfl
  linarith

end Slope

section Semistable

open _root_.Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G] [T2Space G] [ConnectedSpace G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC} [IC.Boundaryless]
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [CompactSpace M]
  [T2Space M]
  [MulAction G M] [MulAction Gc M] [ContMDiffSMul I I' ∞ G M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  [IsContMDiffRiemannianBundle I' 1 E' (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {C : LieComplexification I G IC Gc}
  {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

open scoped RealInnerProductSpace

/-- **Semistable points have nonpositive weights.** In the Kähler setting of
`isSemistable_iff_bddBelow_kempfNessFunction`, if `p` is semistable then `w_μ(p, ξ) ≤ 0` for
every `ξ` in the Lie algebra of `G`, in particular for every `ξ ∈ nonzeroPeriods I G`. -/
theorem IsSemistable.momentWeight_nonpos (h : IsComplexifiedAction C J)
    (hσc : σ.IsClosed) (hσ : σ.IsNondegenerate)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hgm : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (hBs : B.IsSymm)
    (hBp : B.toQuadraticMap.PosDef)
    (hBG : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B) {p : M}
    (hp : IsSemistable C μ p) (ξ : GroupLieAlgebra I G) :
    momentWeight C μ p ξ ≤ 0 :=
  not_lt.1 fun hw ↦ not_bddBelow_kempfNessFunction_of_momentWeight_pos h hμ hgm hw
    ((isSemistable_iff_bddBelow_kempfNessFunction h hσc hσ hσG hμ hgm hBs hBp hBG p).1 hp)

end Semistable

end SymplecticGeometry

end
