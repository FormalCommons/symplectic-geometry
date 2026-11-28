/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Function
public import SymplecticGeometry.Geometry.Lie.Exponential.Periods
public import SymplecticGeometry.Geometry.Lie.Subgroup.Parabolic
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Analysis.Calculus.Deriv.MeanValue
import SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.ContMDiff
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.GradientFlow
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.NormSquare
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Stability
import SymplecticGeometry.Topology.Algebra.GroupAction.Stabilizer
import SymplecticGeometry.Topology.Algebra.Module.BilinearForm
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

These give the necessity halves of the polystable and stable criteria, following the proof of
[GeorgoulasRobbinSalamon2021], Theorem 7.4. The weight `w_μ(x, ξ)` is the infimum of the
antitone function `t ↦ ⟨μ (exp (i t ξ) x), ξ⟩`, so it equals its value `⟨μ x, ξ⟩` at `t = 0`
exactly when that function is constant, that is, when `x` is fixed by every `exp (i t ξ)`
(`momentWeight_eq_moment_iff`). Writing `g = u q` with `u : G` and `q` parabolic turns this into
`exists_momentWeight_smul_eq_moment_of_forall_expI_smul_eq`. For a polystable `p`, splitting
`g⁻¹ = q u` for a `g` with `μ (g p) = 0` gives `p = q x` with `μ x = 0`
(`IsPolystable.exists_mem_parabolic_smul_eq`), so `w_μ(p, ξ) = w_μ(x, ξ) ≤ ⟨μ x, ξ⟩ = 0`
(`IsPolystable.momentWeight_nonpos`). If moreover `w_μ(p, ξ) = 0`, then `x` is fixed by every
`exp (i t ξ)` (`IsPolystable.exists_mem_parabolic_smul_eq_of_momentWeight_eq_zero`). Then
`exp (i t ξ) q x` is the conjugate of `q` at time `t` acting on `x`, so
`p⁺_ξ = C.parabolicLimit ξ q • x` lies in the orbit of `p` (`IsPolystable.limitPoint_mem_orbit`),
and, if `p` is stable, the stabilizer of `x` is discrete, so `X_ξ x = 0` forces `ξ = 0`
(`IsStable.momentWeight_neg`).

With these transformation rules one proves steps 6 and 7 of the sufficiency half of the
polystability criterion in [GeorgoulasRobbinSalamon2021] (arXiv v2, Theorem 12.5). Suppose
`exp (i t ζ) y` tends to a zero `x` of `μ` outside the orbit of `p`, for a period `ζ` and
`p = g y`. Write `g = u q` with `u : G` and `q` in `C.parabolic ζ`. Then `ξ = Ad u ζ` has
`w_μ(p, ξ) = w_μ(y, ζ) = μ x ζ = 0`, and `p⁺_ξ = u q₊ x`, where `q₊` is `C.parabolicLimit ζ q`.
That point is in the orbit of `x`, hence not in the orbit of `p`
(`exists_momentWeight_eq_zero_limitPoint_not_mem_orbit`).

The weight is positively homogeneous in `ξ` (`momentWeight_smul_of_nonneg`), by a change of time.
It is unchanged when `p` moves by `exp (i η)` with `⁅η, ξ⁆ = 0`
(`momentWeight_expI_smul_of_lie_eq_zero`): the one-parameter subgroups of `η` and `ξ` commute
(`LieComplexification.commute_expI_of_lie_eq_zero`), so the limit point moves by `exp (i η)`
(`limitPoint_expI_smul_of_lie_eq_zero`); every `exp (i t ξ)` fixes it (`expI_smul_limitPoint`),
and so every point `exp (i s η) p⁺_ξ`, where `X_ξ` therefore vanishes; by
`hasDerivAt_moment_apply_expI`, `⟨μ, ξ⟩` is then constant along `s ↦ exp (i s η) p⁺_ξ`.
On a subspace `𝔞` of pairwise commuting elements, `w_μ(p, ξ)` is then the minimum of `⟨μ y, ξ⟩`
over the closure of the points `exp (i η) p` with `η ∈ 𝔞`, which is compact, so it is continuous
in `ξ ∈ 𝔞` (`continuousOn_momentWeight`, by `IsCompact.continuous_sInf`). This follows the proof
of Theorem 11.1 in [GeorgoulasRobbinSalamon2021].

A positive infimum `m²` of `‖μ‖²` over the orbit of `p` gives a unit direction of positive weight
(`exists_momentWeight_pos_of_iInf_momentNormSq_pos`), by the argument of Lemma 10.5 of
[GeorgoulasRobbinSalamon2021] (arXiv v2) run along the negative gradient flow of `‖μ‖²`, which
avoids their generalized Kempf existence theorem. Along the curve `g` in `Gc` that this flow
gives (`exists_mem_orbit_maximalIntegralCurve`), `Φ_p (g t) ≤ -2 m² t`, while the polar radius of
`g t` is at most `2 L t`, for `L` a bound of `√(‖μ‖²)` on `M`
(`exists_sqrt_le_kempfNessFunction_expI_le`). Convexity of `Φ_p` along `s ↦ exp (i s ζ)`
(`mul_kempfNessFunction_expI_smul_le`) turns this into `Φ_p (exp (i s ζ)) ≤ -(m² / L) s` up to
the radius, for the unit directions `ζ` of the polar decomposition. These accumulate at some
`ζ₀`, where the bound then holds for every `s ≥ 0`, and the asymptotic slope
(`tendsto_kempfNessFunction_expI_neg_smul_div`) gives `w_μ(p, -ζ₀) ≥ m² / L`
(`le_momentWeight_neg_of_kempfNessFunction_expI_smul_le`).

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
* `SymplecticGeometry.momentWeight_smul_of_nonneg`: `w_μ(p, c ξ) = c w_μ(p, ξ)` for `0 ≤ c`.
* `SymplecticGeometry.tendsto_limitPoint`: on a compact manifold, for a compact `G`, the limit
  defining the limit point exists, for every `ξ`.
* `SymplecticGeometry.limitPoint_mem_criticalPoints`: the limit point is a critical point of
  `x ↦ ⟨μ x, ξ⟩`.
* `SymplecticGeometry.momentWeight_eq_moment_limitPoint`: `w_μ(p, ξ) = ⟨μ (p⁺_ξ), ξ⟩`.
* `SymplecticGeometry.expI_smul_limitPoint`: `exp (i t ξ)` fixes `p⁺_ξ`.
* `SymplecticGeometry.limitPoint_expI_smul_of_lie_eq_zero`: `(exp (i η) p)⁺_ξ = exp (i η) p⁺_ξ`
  when `⁅η, ξ⁆ = 0`.
* `SymplecticGeometry.momentWeight_expI_smul_of_lie_eq_zero`: `w_μ(exp (i η) p, ξ) = w_μ(p, ξ)`
  when `⁅η, ξ⁆ = 0`.
* `SymplecticGeometry.continuousOn_momentWeight`: `ξ ↦ w_μ(p, ξ)` is continuous on every subspace
  of pairwise commuting elements.
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
  `C.parabolic ξ`, `(q x)⁺_ξ = C.parabolicLimit ξ q • x⁺_ξ` and `w_μ(q x, ξ) = w_μ(x, ξ)`. The
  first is a case of `SymplecticGeometry.limitPoint_smul_of_mem_parabolic_of_tendsto`, which
  assumes only that `exp (i t ξ) x` converges.
* `SymplecticGeometry.tendsto_kempfNessFunction_expI_neg_smul_div`:
  `Φ_p (C.expI (-(s • ξ))) / s → -w_μ(p, ξ)` as `s → ∞`.
* `SymplecticGeometry.exists_eventually_abs_kempfNessFunction_le`: along a convergent curve in
  `Gc`, `Φ_p` is eventually bounded, uniformly in `p`.
* `SymplecticGeometry.IsSemistable.momentWeight_nonpos`: at a semistable point every moment weight
  is nonpositive.
* `SymplecticGeometry.momentWeight_eq_moment_iff`: `w_μ(x, ξ) = ⟨μ x, ξ⟩` exactly when every
  `C.expI (t • ξ)` fixes `x`.
* `SymplecticGeometry.IsPolystable.momentWeight_nonpos`: at a polystable point every moment weight
  is nonpositive.
* `SymplecticGeometry.IsPolystable.limitPoint_mem_orbit`: at a polystable point, the limit point
  of a direction of weight `0` lies in the orbit under `Gc`.
* `SymplecticGeometry.IsStable.momentWeight_neg`: at a stable point every nonzero direction has
  negative weight.
* `SymplecticGeometry.exists_momentWeight_eq_zero_limitPoint_not_mem_orbit`: a period `ζ` along
  which a point of the orbit of `p` flows to a zero of `μ` outside that orbit gives a period
  `ξ` with `w_μ(p, ξ) = 0` and `p⁺_ξ` outside the orbit.
* `SymplecticGeometry.exists_momentWeight_pos_of_iInf_momentNormSq_pos`: if the infimum of `‖μ‖²`
  over the orbit of `p` is positive, some `ξ` with `B ξ ξ = 1` has `0 < w_μ(p, ξ)`.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], Lemmas 7.5 and 10.5 and Theorem 7.4.
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

/-- **Moment weights are positively homogeneous.** For a complexified action on a compact
manifold, with `-μ` a moment map for `σ` and the metric `g(u, w) = σ(u, J w)`,
`w_μ(p, c ξ) = c w_μ(p, ξ)` for `0 ≤ c`. -/
theorem momentWeight_smul_of_nonneg (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) {c : ℝ} (hc : 0 ≤ c) :
    momentWeight C μ p (c • ξ) = c * momentWeight C μ p ξ := by
  rcases hc.eq_or_lt with rfl | hc
  · -- The curve for the direction `0` is the constant `0`.
    rw [zero_smul, zero_mul, momentWeight_def]
    simp only [map_zero]
    exact tendsto_const_nhds.limUnder_eq
  -- Along `t ↦ c * t`, `μ (C.expI ((c * t) • ξ) • p) (c • ξ)` is `c` times the curve for `ξ`.
  refine tendsto_nhds_unique (tendsto_momentWeight h hμ hg p (c • ξ))
    ((((tendsto_momentWeight h hμ hg p ξ).comp (tendsto_id.const_mul_atTop hc)).const_mul
      c).congr fun t ↦ ?_)
  simp only [Function.comp_apply, id_eq, smul_smul, map_smul, smul_eq_mul, mul_comm t c]

/-- **Weights equal to the moment.** Under the hypotheses of `momentWeight_le`,
`w_μ(x, ξ) = ⟨μ x, ξ⟩` exactly when `C.expI (t • ξ)` fixes `x` for every `t`. -/
theorem momentWeight_eq_moment_iff (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {x : M} {ξ : GroupLieAlgebra I G} :
    momentWeight C μ x ξ = μ x ξ ↔ ∀ t : ℝ, C.expI (t • ξ) • x = x := by
  constructor
  · intro hw
    -- For `t ≥ 0`, `⟨μ x, t ξ⟩ = t w_μ(x, ξ) ≤ ⟨μ (exp (i t ξ) x), t ξ⟩`, so `exp (i t ξ)`
    -- fixes `x`.
    have hpos {t : ℝ} (ht : 0 ≤ t) : C.expI (t • ξ) • x = x := by
      refine expI_smul_eq_self_of_moment_apply_le h hμ hg ?_
      simp only [map_smul, smul_eq_mul]
      rw [← hw]
      exact mul_le_mul_of_nonneg_left (momentWeight_le_moment_expI_smul h hμ hg x ξ t) ht
    intro t
    rcases le_total 0 t with ht | ht
    · exact hpos ht
    · -- For `t ≤ 0`, apply `exp (i t ξ)` to `exp (-i t ξ) x = x`.
      conv_lhs => rw [← hpos (neg_nonneg.2 ht)]
      rw [smul_smul, ← C.expI_add_smul, add_neg_cancel, zero_smul, C.expI_zero, one_smul]
  · intro hx
    refine tendsto_nhds_unique (tendsto_momentWeight h hμ hg x ξ) ?_
    simp only [hx]
    exact tendsto_const_nhds

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

/-- **Limit points under the parabolic subgroup, given a limit.** If `C.expI (t • ξ) • x`
converges to `y` as `t → ∞`, then for `q` in the parabolic subgroup `C.parabolic ξ` the limit
point `(q x)⁺_ξ` is `C.parabolicLimit ξ q • y`, where `C.parabolicLimit ξ q` is the limit of the
conjugates `exp (i t ξ) q exp (-i t ξ)`. -/
theorem limitPoint_smul_of_mem_parabolic_of_tendsto [ContinuousSMul Gc M] [T2Space M]
    {C : LieComplexification I G IC Gc} {ξ : GroupLieAlgebra I G} (q : C.parabolic ξ) {x y : M}
    (hx : Tendsto (fun t : ℝ ↦ C.expI (t • ξ) • x) atTop (𝓝 y)) :
    limitPoint C ((q : Gc) • x) ξ = C.parabolicLimit ξ q • y := by
  -- `exp (i t ξ) q x` is the conjugate of `q` at time `t` acting on `exp (i t ξ) x`.
  refine limitPoint_eq_of_tendsto (((C.tendsto_parabolicLimit ξ q).smul hx).congr fun t ↦ ?_)
  rw [smul_smul, C.expI_neg, inv_mul_cancel_right, mul_smul]

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
  exact limitPoint_smul_of_mem_parabolic_of_tendsto q (tendsto_limitPoint h hμ hg x ξ)

/-- **Limit points are fixed by the flow.** Under the hypotheses of `tendsto_limitPoint`,
`exp (i t ξ)` fixes the limit point `p⁺_ξ` for every `t`. -/
theorem expI_smul_limitPoint (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace 𝓘(ℝ, E') x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) (ξ : GroupLieAlgebra I G) (t : ℝ) :
    C.expI (t • ξ) • limitPoint C p ξ = limitPoint C p ξ := by
  have : ContinuousSMul Gc M := ContMDiffSMul.continuousSMul (I := IC) (I' := 𝓘(ℝ, E')) ∞
  have hlim := tendsto_limitPoint h hμ hg p ξ
  refine tendsto_nhds_unique (hlim.const_smul _) (hlim.comp
    (tendsto_atTop_add_const_left _ t tendsto_id) |>.congr fun s ↦ ?_)
  rw [Function.comp_apply, id_eq, smul_smul, ← C.expI_add_smul]

/-- **Limit points along a commuting direction.** Under the hypotheses of `tendsto_limitPoint`,
if `⁅η, ξ⁆ = 0` then `(exp (i η) p)⁺_ξ = exp (i η) p⁺_ξ`. -/
theorem limitPoint_expI_smul_of_lie_eq_zero (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace 𝓘(ℝ, E') x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {η ξ : GroupLieAlgebra I G} (hηξ : ⁅η, ξ⁆ = 0) (p : M) :
    limitPoint C (C.expI η • p) ξ = C.expI η • limitPoint C p ξ := by
  have : ContinuousSMul Gc M := ContMDiffSMul.continuousSMul (I := IC) (I' := 𝓘(ℝ, E')) ∞
  refine limitPoint_eq_of_tendsto (((tendsto_limitPoint h hμ hg p ξ).const_smul
    (C.expI η)).congr fun t ↦ ?_)
  have hηtξ : ⁅η, t • ξ⁆ = 0 := by rw [lie_smul t η ξ, hηξ, smul_zero]
  rw [smul_smul, smul_smul, (C.commute_expI_of_lie_eq_zero hηtξ).eq]

/-- **Moment weights along a commuting direction.** Under the hypotheses of
`tendsto_limitPoint`, if `⁅η, ξ⁆ = 0` then `w_μ(exp (i η) p, ξ) = w_μ(p, ξ)`. -/
theorem momentWeight_expI_smul_of_lie_eq_zero (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace 𝓘(ℝ, E') x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {η ξ : GroupLieAlgebra I G} (hηξ : ⁅η, ξ⁆ = 0) (p : M) :
    momentWeight C μ (C.expI η • p) ξ = momentWeight C μ p ξ := by
  set x := limitPoint C p ξ
  -- Every `C.expI (t • ξ)` fixes `x`, and so, by commutation, every `C.expI (s • η) • x`.
  have hX (s : ℝ) : fundamentalVectorField 𝓘(ℝ, E') ξ (C.expI (s • η) • x) = 0 :=
    h.expI_smul_smul_eq_self_iff.1 fun t ↦ by
      rw [smul_smul, ← (C.commute_expI_of_lie_eq_zero
        (by rw [smul_lie, lie_smul, hηξ, smul_zero, smul_zero])).eq, mul_smul,
        expI_smul_limitPoint h hμ hg]
  -- So `s ↦ μ (C.expI (s • η) • x) ξ` has derivative zero, and is constant.
  have hconst := is_const_of_deriv_eq_zero
    (fun s ↦ (hasDerivAt_moment_apply_expI h hμ hg ξ η x s).differentiableAt)
    (fun s ↦ by rw [(hasDerivAt_moment_apply_expI h hμ hg ξ η x s).deriv, hX, inner_zero_left,
      neg_zero]) 1 0
  simp only [one_smul, zero_smul, C.expI_zero] at hconst
  rw [momentWeight_eq_moment_limitPoint h hμ hg, momentWeight_eq_moment_limitPoint h hμ hg,
    limitPoint_expI_smul_of_lie_eq_zero h hμ hg hηξ, hconst]

/-- **Moment weights are continuous along commuting directions.** Under the hypotheses of
`tendsto_limitPoint`, for a subspace `𝔞` of pairwise commuting elements of the Lie algebra, the
map `ξ ↦ w_μ(p, ξ)` is continuous on `𝔞`. -/
theorem continuousOn_momentWeight (h : IsComplexifiedAction C J)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace 𝓘(ℝ, E') x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    (p : M) {𝔞 : Submodule ℝ (GroupLieAlgebra I G)} (h𝔞 : ∀ η ∈ 𝔞, ∀ ξ ∈ 𝔞, ⁅η, ξ⁆ = 0) :
    ContinuousOn (momentWeight C μ p) 𝔞 := by
  have : FiniteDimensional ℝ (GroupLieAlgebra I G) := inferInstanceAs (FiniteDimensional ℝ E)
  have hc (ξ : GroupLieAlgebra I G) : Continuous fun x : M ↦ μ x ξ :=
    (hμ.contMDiff_of_neg ξ).continuous
  -- `(ξ, y) ↦ μ y ξ` is continuous, since `μ` is continuous as a map to `E →L[ℝ] ℝ`; the Lie
  -- algebra `GroupLieAlgebra I G` is the model space `E` by definition.
  have hμ' : (-σ).IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ := by
    simpa using hμ.neg
  have hc₂ : Continuous fun q : E × M ↦ μ q.2 q.1 :=
    ((hμ'.continuous_linearMap_comp (LinearMap.toContinuousLinearMap :
      (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ))).comp continuous_snd).clm_apply continuous_fst
  -- `K` is the closure of the points `C.expI η • p` for `η ∈ 𝔞`.
  set K := closure {y | ∃ η ∈ 𝔞, C.expI η • p = y}
  have hK : IsCompact K := isClosed_closure.isCompact
  -- On `𝔞`, the moment weight is the infimum of `μ y ξ` over `y ∈ K`.
  have heq : Set.EqOn (momentWeight C μ p) (fun ξ ↦ sInf ((fun y ↦ μ y ξ) '' K)) 𝔞 := by
    intro ξ hξ
    have hmem : limitPoint C p ξ ∈ K := mem_closure_of_tendsto (tendsto_limitPoint h hμ hg p ξ)
      (Eventually.of_forall fun t ↦ ⟨t • ξ, 𝔞.smul_mem t hξ, rfl⟩)
    have hlow : ∀ y ∈ K, momentWeight C μ p ξ ≤ μ y ξ := by
      refine fun y hy ↦ closure_minimal (t := {y | momentWeight C μ p ξ ≤ μ y ξ}) ?_
        (isClosed_le continuous_const (hc ξ)) hy
      rintro _ ⟨η, hη, rfl⟩
      rw [Set.mem_ofPred_eq, ← momentWeight_expI_smul_of_lie_eq_zero h hμ hg (h𝔞 η hη ξ hξ)]
      exact momentWeight_le h hμ hg _ ξ
    refine le_antisymm (le_csInf ⟨_, Set.mem_image_of_mem _ hmem⟩ ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hlow y hy
    · rw [momentWeight_eq_moment_limitPoint h hμ hg]
      exact csInf_le (hK.bddBelow_image (hc ξ).continuousOn) (Set.mem_image_of_mem _ hmem)
  exact (hK.continuous_sInf (f := fun ξ y ↦ μ y ξ) hc₂).continuousOn.congr heq

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

/-- **A linear bound gives a weight.** Under the hypotheses of `tendsto_deriv_kempfNessFunction`,
if `Φ_p (C.expI (s • ζ)) ≤ -(c * s)` for every `s > 0`, then `c ≤ w_μ(p, -ζ)`. -/
theorem le_momentWeight_neg_of_kempfNessFunction_expI_smul_le (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {p : M} {ζ : GroupLieAlgebra I G} {c : ℝ}
    (hc : ∀ s > 0, kempfNessFunction C μ p (C.expI (s • ζ)) ≤ -(c * s)) :
    c ≤ momentWeight C μ p (-ζ) := by
  -- `Φ_p (C.expI (s • ζ)) / s` tends to `-w_μ(p, -ζ)` and is at most `-c`.
  have hslope := tendsto_kempfNessFunction_expI_neg_smul_div h hμ hg p (-ζ)
  simp only [smul_neg, neg_neg] at hslope
  have : -momentWeight C μ p (-ζ) ≤ -c :=
    le_of_tendsto hslope ((eventually_gt_atTop 0).mono fun s hs ↦
      (div_le_iff₀ hs).2 (by linarith [hc s hs]))
  linarith

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
  obtain ⟨L, -, hL'⟩ :=
    hμ.exists_pos_forall_sqrt_momentNormSq_le_of_neg (K := (B.toDual hB).symm)
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

/-- **Weights along the orbit of a fixed point.** Under the hypotheses of
`tendsto_deriv_kempfNessFunction`, with `G` compact, if `C.expI (t • ξ)` fixes `x` for every
`t`, then for every `g : Gc` some `u : G` has `w_μ(g x, Ad u ξ) = ⟨μ x, ξ⟩`. -/
theorem exists_momentWeight_smul_eq_moment_of_forall_expI_smul_eq [CompactSpace G]
    (h : IsComplexifiedAction C J) (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {ξ : GroupLieAlgebra I G} {x : M} (hx : ∀ t : ℝ, C.expI (t • ξ) • x = x) (g : Gc) :
    ∃ u : G, momentWeight C μ (g • x) (Lie.tangentAd (I := I) u ξ) = μ x ξ := by
  obtain ⟨u, q, hq, rfl⟩ := C.exists_toHom_mul_mem_parabolic ξ g
  refine ⟨u, ?_⟩
  rw [mul_smul, momentWeight_toHom_smul h hμ,
    momentWeight_smul_of_mem_parabolic h hμ hg (⟨q, hq⟩ : C.parabolic ξ),
    momentWeight_eq_moment_iff h hμ.toIsMomentMap hg]
  exact hx

omit [ConnectedSpace G] [CompactSpace M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle fun x : M ↦ TangentSpace I' x] in
/-- **Splitting a polystable point.** For a complexified action, with `-μ` an equivariant moment
map for `σ`, if `p` is polystable then for every `ξ` there are `q` in the parabolic subgroup
`C.parabolic ξ` and a zero `x` of `μ` with `p = q • x`. -/
theorem IsPolystable.exists_mem_parabolic_smul_eq [CompactSpace G] (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x) {p : M} (hp : IsPolystable C μ p)
    (ξ : GroupLieAlgebra I G) :
    ∃ q ∈ C.parabolic ξ, ∃ x, μ x = 0 ∧ p = q • x := by
  have := FiniteDimensional.completeSpace ℝ E'
  -- Take `g` with `μ (g • p) = 0` and write `g⁻¹ = q * C.toHom u`; then `x = C.toHom u • g • p`.
  obtain ⟨g, hg0⟩ := isPolystable_iff_exists_smul.1 hp
  obtain ⟨q, hq, u, hgu⟩ := C.exists_mem_parabolic_mul_toHom ξ g⁻¹
  refine ⟨q, hq, C.toHom u • g • p, ?_, ?_⟩
  · rw [h.moment_toHom_smul hμ, hg0, map_zero]
  · rw [smul_smul, ← hgu, inv_smul_smul]

/-- **A polystable point of weight zero.** Under the hypotheses of
`tendsto_deriv_kempfNessFunction`, with `G` compact, if `p` is polystable and
`w_μ(p, ξ) = 0`, then `p = q • x` for some `q` in the parabolic subgroup `C.parabolic ξ` and
some zero `x` of `μ` that every `C.expI (t • ξ)` fixes. -/
theorem IsPolystable.exists_mem_parabolic_smul_eq_of_momentWeight_eq_zero [CompactSpace G]
    (h : IsComplexifiedAction C J) (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {p : M}
    (hp : IsPolystable C μ p) {ξ : GroupLieAlgebra I G} (hw : momentWeight C μ p ξ = 0) :
    ∃ q ∈ C.parabolic ξ, ∃ x, μ x = 0 ∧ (∀ t : ℝ, C.expI (t • ξ) • x = x) ∧ p = q • x := by
  obtain ⟨q, hq, x, hx0, rfl⟩ := hp.exists_mem_parabolic_smul_eq h hμ ξ
  refine ⟨q, hq, x, hx0, (momentWeight_eq_moment_iff h hμ.toIsMomentMap hg).1 ?_, rfl⟩
  rw [hx0, LinearMap.zero_apply, ← hw,
    momentWeight_smul_of_mem_parabolic h hμ hg (⟨q, hq⟩ : C.parabolic ξ)]

/-- **Polystable points have nonpositive weights.** Under the hypotheses of
`tendsto_deriv_kempfNessFunction`, with `G` compact, if `p` is polystable then `w_μ(p, ξ) ≤ 0`
for every `ξ` in the Lie algebra of `G`. -/
theorem IsPolystable.momentWeight_nonpos [CompactSpace G] (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {p : M}
    (hp : IsPolystable C μ p) (ξ : GroupLieAlgebra I G) :
    momentWeight C μ p ξ ≤ 0 := by
  -- With `p = q • x` and `μ x = 0`, `w_μ(p, ξ) = w_μ(x, ξ) ≤ ⟨μ x, ξ⟩ = 0`.
  obtain ⟨q, hq, x, hx0, rfl⟩ := hp.exists_mem_parabolic_smul_eq h hμ ξ
  rw [momentWeight_smul_of_mem_parabolic h hμ hg (⟨q, hq⟩ : C.parabolic ξ)]
  simpa [hx0] using momentWeight_le h hμ.toIsMomentMap hg x ξ

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

/-- **Stable points have negative weights.** For a complexified action on a compact Hausdorff
manifold without boundary, with `G` compact, `-μ` an equivariant moment map for `σ` and the
metric `g(u, w) = σ(u, J w)`, if `p` is stable then `w_μ(p, ξ) < 0` for every nonzero `ξ` in
the Lie algebra of `G`, in particular for every `ξ ∈ nonzeroPeriods I G`. -/
theorem IsStable.momentWeight_neg [CompactSpace G] [T2Space M] [BoundarylessManifold I' M]
    (h : IsComplexifiedAction C J) (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {p : M}
    (hp : IsStable C μ p) {ξ : GroupLieAlgebra I G} (hξ : ξ ≠ 0) :
    momentWeight C μ p ξ < 0 := by
  have := continuousMul_of_contMDiffMul IC ∞ (G := Gc)
  refine (hp.isPolystable.momentWeight_nonpos h hμ hg ξ).lt_of_ne fun hw ↦ hξ ?_
  -- A weight `0` gives `p = q • x` with `μ x = 0` and `X_ξ x = 0`, where the stabilizer of `x`,
  -- conjugate to that of `p`, is discrete; this forces `ξ = 0`.
  obtain ⟨q, -, x, hx0, hx, rfl⟩ :=
    hp.isPolystable.exists_mem_parabolic_smul_eq_of_momentWeight_eq_zero h hμ hg hw
  have hd := (MulAction.discreteTopology_stabilizer_smul_iff q x).1 hp.discreteTopology_stabilizer
  exact (h.discreteTopology_stabilizer_iff_of_moment_eq_zero hμ hg hx0).1 hd ξ
    ((h.expI_smul_smul_eq_self_iff).1 hx)

/-- **Limit points of polystable points.** For a complexified action on a compact Hausdorff
manifold, with `G` compact, `-μ` an equivariant moment map for `σ` and the metric
`g(u, w) = σ(u, J w)`, if `p` is polystable and `w_μ(p, ξ) = 0`, then the limit point `p⁺_ξ`
lies in the orbit of `p` under `Gc`. -/
theorem IsPolystable.limitPoint_mem_orbit [CompactSpace G] [T2Space M]
    (h : IsComplexifiedAction C J) (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {p : M}
    (hp : IsPolystable C μ p) {ξ : GroupLieAlgebra I G} (hw : momentWeight C μ p ξ = 0) :
    limitPoint C p ξ ∈ MulAction.orbit Gc p := by
  have := C.finiteDimensional
  have : ContinuousSMul Gc M := ContMDiffSMul.continuousSMul (I := IC) (I' := I') ∞
  obtain ⟨q, hq, x, -, hx, rfl⟩ :=
    hp.exists_mem_parabolic_smul_eq_of_momentWeight_eq_zero h hμ hg hw
  -- As `x` is fixed by every `C.expI (t • ξ)`, the curve `C.expI (t • ξ) • x` is constant.
  have hlim : limitPoint C (q • x) ξ = C.parabolicLimit ξ ⟨q, hq⟩ • x :=
    limitPoint_smul_of_mem_parabolic_of_tendsto ⟨q, hq⟩
      (tendsto_const_nhds.congr fun t ↦ (hx t).symm)
  refine MulAction.mem_orbit_iff.2 ⟨C.parabolicLimit ξ ⟨q, hq⟩ * q⁻¹, ?_⟩
  rw [hlim, mul_smul, inv_smul_smul]

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

/-! ### A destabilizing direction -/

section Destabilizing

open _root_.Bundle
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [ConnectedSpace G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC} [IC.Boundaryless]
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [CompactSpace M]
  [T2Space M] [BoundarylessManifold I' M]
  [MulAction G M] [MulAction Gc M] [ContMDiffSMul I I' ∞ G M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  [IsContMDiffRiemannianBundle I' 1 E' (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {C : LieComplexification I G IC Gc}
  {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)} {hB : B.Nondegenerate}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **A positive infimum of the norm square gives a direction of positive weight.** In the
setting of `exists_mem_orbit_maximalIntegralCurve`, with `B` moreover positive definite and
`Ad`-invariant, if the infimum of `‖μ‖²` over the `Gc`-orbit of `p` is positive, then some `ξ` with
`B ξ ξ = 1` has `0 < w_μ(p, ξ)`. -/
theorem exists_momentWeight_pos_of_iInf_momentNormSq_pos (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (hBs : B.IsSymm)
    (hBp : B.toQuadraticMap.PosDef)
    (hBG : Representation.IsInvariantForm (Lie.adjointRepresentation ℝ I G) B) {p : M}
    (hm : 0 < ⨅ g : Gc, momentNormSq μ (B.toDual hB).symm (g • p)) :
    ∃ ξ : GroupLieAlgebra I G, B ξ ξ = 1 ∧ 0 < momentWeight C μ p ξ := by
  set m := ⨅ g : Gc, momentNormSq μ (B.toDual hB).symm (g • p)
  have hpos : B.IsNonneg := LinearMap.BilinForm.isNonneg_def.2 hBp.nonneg
  obtain ⟨L, hL0, hL⟩ :=
    hμ.toIsMomentMap.exists_pos_forall_sqrt_momentNormSq_le_of_neg (K := (B.toDual hB).symm)
  -- For each `n`, a direction `η n` of radius `r n ≤ 2 L (n + 1)` along which `Φ_p` is at most
  -- `-2 m² (n + 1)`; then also `2 m² (n + 1) ≤ L r n`.
  choose η hηr hηΦ using fun n : ℕ ↦ exists_sqrt_le_kempfNessFunction_expI_le (C := C) h hμ hg
    hBs hpos hBG p hL (t := n + 1) (by positivity)
  set r : ℕ → ℝ := fun n ↦ √(B (η n) (η n))
  have hηΦ' (n : ℕ) : kempfNessFunction C μ p (C.expI (η n)) ≤ -(2 * m * (n + 1)) := hηΦ n
  have hrlow (n : ℕ) : 2 * m * (n + 1) ≤ L * r n := by
    have hlow := kempfNessFunction_sub_sqrt_momentNormSq_mul_sqrt_le C μ p h hμ hg (hB := hB) hBs
      hpos 1 (η n) 1
    rw [inv_one, one_smul, one_mul, map_one, mul_one, kempfNessFunction_one] at hlow
    have := mul_le_mul_of_nonneg_right (hL p) (Real.sqrt_nonneg (B (η n) (η n)))
    linarith [hηΦ' n]
  have hr0 (n : ℕ) : 0 < r n :=
    pos_of_mul_pos_right ((by positivity : 0 < 2 * m * (n + 1)).trans_le (hrlow n)) hL0.le
  -- The unit directions `ζ n` have a convergent subsequence, with limit `ζ₀`.
  set ζ : ℕ → GroupLieAlgebra I G := fun n ↦ (r n)⁻¹ • η n
  have hζ (n : ℕ) : B (ζ n) (ζ n) = 1 := by
    have hrB : B (η n) (η n) = r n ^ 2 := (Real.sq_sqrt (hpos.nonneg _)).symm
    simp only [ζ, map_smul, LinearMap.smul_apply, smul_eq_mul, hrB]
    field_simp [(hr0 n).ne']
  have hζη (n : ℕ) : r n • ζ n = η n := by simp [ζ, smul_smul, (hr0 n).ne']
  have hK : IsCompact {v : E | B v v ≤ 1} :=
    LinearMap.BilinForm.isCompact_setOfPred_apply_self_le (E := E) hBp 1
  -- The Lie algebra is the model space `E` by definition, with its topology.
  obtain ⟨ζ₀', -, φ, hφ, hlim⟩ := hK.tendsto_subseq (X := E) (x := ζ) fun n ↦ (hζ n).le
  obtain ⟨ζ₀, rfl⟩ : ∃ ζ₀ : GroupLieAlgebra I G, ζ₀ = ζ₀' := ⟨ζ₀', rfl⟩
  have hBc : Continuous fun v : E ↦ B v v := LinearMap.continuous_apply_self B
  have hζ₀ : B ζ₀ ζ₀ = 1 := by
    have hconst : (fun v : E ↦ B v v) ∘ (ζ ∘ φ) = fun _ ↦ 1 := funext fun n ↦ hζ (φ n)
    have := (hBc.tendsto ζ₀).comp hlim
    rw [hconst] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  -- Along every `ζ n`, convexity bounds `Φ_p (C.expI (s • ζ n))` by `-(m / L * s)` on
  -- `[0, r n]`.
  have hconv (n : ℕ) {s : ℝ} (hs : 0 < s) (hsr : s ≤ r n) :
      kempfNessFunction C μ p (C.expI (s • ζ n)) ≤ -(m / L * s) := by
    have hc := mul_kempfNessFunction_expI_smul_le C μ p h hμ hg (ζ n) hs hsr
    rw [hζη] at hc
    have h1 : -(m / L * s) * (r n * L) = -(m * s * r n) := by field_simp
    refine le_of_mul_le_mul_right ?_ (mul_pos (hr0 n) hL0)
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_right hc hL0.le,
      mul_le_mul_of_nonneg_right (hηΦ' n) (mul_nonneg hs.le hL0.le),
      mul_le_mul_of_nonneg_left (hηr n) (mul_nonneg hm.le hs.le)]
  -- In the limit, `Φ_p (C.expI (s • ζ₀)) ≤ -(m / L * s)` for every `s > 0`.
  have hφt : Tendsto (fun n ↦ r (φ n)) atTop atTop := by
    refine tendsto_atTop_mono (f := fun n ↦ 2 * m * ((φ n : ℝ) + 1) / L)
      (fun n ↦ (div_le_iff₀' hL0).2 (hrlow (φ n))) ?_
    refine Tendsto.atTop_div_const hL0 (Tendsto.const_mul_atTop (by positivity) ?_)
    exact tendsto_atTop_add_const_right _ 1
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hlimit (s : ℝ) (hs : 0 < s) :
      kempfNessFunction C μ p (C.expI (s • ζ₀)) ≤ -(m / L * s) := by
    have hc : Continuous fun v : E ↦ kempfNessFunction C μ p (C.expI (s • v)) :=
      (contMDiff_kempfNessFunction C μ p hμ.toIsMomentMap.contMDiff_of_neg).continuous.comp
        (C.contMDiff_expI.continuous.comp (continuous_const_smul s))
    exact le_of_tendsto ((hc.tendsto ζ₀).comp hlim)
      ((hφt.eventually_ge_atTop s).mono fun n hn ↦ hconv (φ n) hs hn)
  -- So the weight of `-ζ₀` is at least `m / L`.
  exact ⟨-ζ₀, by rw [LinearMap.map_neg₂, map_neg, neg_neg, hζ₀],
    (div_pos hm hL0).trans_le
      (le_momentWeight_neg_of_kempfNessFunction_expI_smul_le h hμ hg hlimit)⟩

end Destabilizing

/-! ### A weight-zero direction whose limit point leaves the orbit -/

section Polystable

open _root_.Bundle
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G] [T2Space G] [ConnectedSpace G] [BoundarylessManifold I G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E' M] [IsManifold 𝓘(ℝ, E') ∞ M] [T2Space M]
  [CompactSpace M]
  [MulAction G M] [MulAction Gc M] [ContMDiffSMul I 𝓘(ℝ, E') ∞ G M]
  [ContMDiffSMul IC 𝓘(ℝ, E') ∞ Gc M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E') x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E') 1 E' (fun x : M ↦ TangentSpace 𝓘(ℝ, E') x)]
  {σ : SmoothTwoForm 𝓘(ℝ, E') M} {J : SmoothAlmostComplexStructure 𝓘(ℝ, E') M}
  {C : LieComplexification I G IC Gc} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **A weight-zero direction whose limit point leaves the orbit.** Under the hypotheses of
`tendsto_limitPoint`, with `-μ` equivariant and `G` connected, suppose that some `y` in the
`Gc`-orbit of `p` and some `ζ ∈ nonzeroPeriods I G` have `C.expI (t • ζ) • y → x` as `t → ∞`,
where `μ x = 0` and `x` is not in the orbit of `p`. Then some `ξ ∈ nonzeroPeriods I G` has
`w_μ(p, ξ) = 0` and its limit point `p⁺_ξ` is not in the orbit of `p`. -/
theorem exists_momentWeight_eq_zero_limitPoint_not_mem_orbit (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace 𝓘(ℝ, E') x), ⟪u, w⟫ = σ.eval₂ x u (J x w))
    {p x y : M} (hy : y ∈ MulAction.orbit Gc p) {ζ : GroupLieAlgebra I G}
    (hζ : ζ ∈ nonzeroPeriods I G) (hlim : Tendsto (fun t : ℝ ↦ C.expI (t • ζ) • y) atTop (𝓝 x))
    (hx : μ x = 0) (hxp : x ∉ MulAction.orbit Gc p) :
    ∃ ξ ∈ nonzeroPeriods I G,
      momentWeight C μ p ξ = 0 ∧ limitPoint C p ξ ∉ MulAction.orbit Gc p := by
  obtain ⟨g, hgy⟩ := MulAction.mem_orbit_iff.1 hy
  -- Write `g⁻¹ = C.toHom u * q` with `q` in the parabolic subgroup of `ζ`, so `p = u q y`.
  obtain ⟨u, q, hq, hgq⟩ := C.exists_toHom_mul_mem_parabolic ζ g⁻¹
  have hp : p = C.toHom u • ((⟨q, hq⟩ : C.parabolic ζ) : Gc) • y := by
    rw [smul_smul, ← hgq, ← hgy, inv_smul_smul]
  have hxy : limitPoint C y ζ = x := limitPoint_eq_of_tendsto hlim
  refine ⟨Lie.tangentAd (I := I) u ζ, tangentAd_mem_nonzeroPeriods hζ u, ?_, ?_⟩
  · rw [hp, momentWeight_toHom_smul h hμ, momentWeight_smul_of_mem_parabolic h hμ hg,
      momentWeight_eq_moment_limitPoint h hμ.toIsMomentMap hg, hxy, hx, LinearMap.zero_apply]
  · -- The limit point lies in the orbit of `x`, which is disjoint from that of `p`.
    have hpx : limitPoint C p (Lie.tangentAd (I := I) u ζ) =
        (C.toHom u * C.parabolicLimit ζ ⟨q, hq⟩) • x := by
      rw [hp, limitPoint_toHom_smul h hμ.toIsMomentMap hg,
        limitPoint_smul_of_mem_parabolic h hμ.toIsMomentMap hg, hxy, mul_smul]
    rw [hpx, ← MulAction.orbit_eq_iff, MulAction.orbit_smul, MulAction.orbit_eq_iff]
    exact hxp

end Polystable

end SymplecticGeometry

end
