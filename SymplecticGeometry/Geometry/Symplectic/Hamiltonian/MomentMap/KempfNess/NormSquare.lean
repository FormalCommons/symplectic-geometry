/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import SymplecticGeometry.Geometry.Lie.LeftTrivializedDeriv
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Function
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalNormalForm
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.NormSq
public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import SymplecticGeometry.Analysis.Calculus.Lojasiewicz.Polynomial
import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
import SymplecticGeometry.Geometry.Lie.LeftTrivializedCurve.Basic
import SymplecticGeometry.Geometry.Manifold.Riemannian.Gradient.Lojasiewicz
import SymplecticGeometry.Geometry.Manifold.Riemannian.Gradient.PartialDiffeomorph
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.ContMDiff
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Geometry.Manifold.Flow.TimeDependent
import TauCeti.Geometry.Manifold.IntegralCurve.Regularity

/-!
# The norm square of a moment map

For a nondegenerate bilinear form `B` on the Lie algebra `𝔤` of `G` and a map
`μ : M → 𝔤^*`, this file studies the norm square `f = SymplecticGeometry.momentNormSq B hB μ`,
`f y = B^∨ (μ y) (μ y)`.

## The gradient

We first work in the setting of `KempfNess/Basic.lean`: `-μ` is a moment map for `σ` of the
action of `G` on `M` by fundamental vector fields, `J` is an almost complex structure on `M`, and
the metric is `g(u, w) = σ(u, J w)`. For symmetric `B`, `SymplecticGeometry.mgradient_momentNormSq`
computes the gradient of `f`.

The gradient is computed from the derivative `SymplecticGeometry.mvfderiv_momentNormSq`, twice
that of the component `y ↦ μ y (μ♯ x)`, and the gradient `-J X_ξ` of the component `y ↦ μ y ξ`
(`SymplecticGeometry.mgradient_moment_apply`), taken at `ξ = μ♯ x`. No `Ad`-invariance of `B`
and no nondegeneracy of `σ` are used. With the norm square normalized as `½ ‖μ‖²` instead, the
gradient is `-J X_{μ♯ x}(x)`.

## The Łojasiewicz inequality

Then let a compact Hausdorff Lie group `G` act smoothly on a manifold `M` without boundary, with
a closed nondegenerate `G`-invariant two-form `σ` and a coadjoint-equivariant moment map `μ`, and
let `B` be `Ad`-invariant. For any continuous Riemannian metric on `M`, `f` satisfies
Łojasiewicz's gradient inequality near every point `p`
(`SymplecticGeometry.exists_lojasiewicz_momentNormSq`): there are `θ ∈ [1/2, 1)` and `c > 0` with
`c * |f y - f p| ^ θ ≤ ‖grad f y‖` for `y` near `p`. This is the hypothesis of the convergence
theorem `SymplecticGeometry.tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz` for the
negative gradient flow of `f`. No complex structure is involved.

The proof is Lerman's. By the local normal form
(`SymplecticGeometry.exists_partialDiffeomorph_momentNormSq_eq_eval`), `f` is a real polynomial
`P` in the coordinates of a smooth partial diffeomorphism `e` from `M` to a Euclidean space, with
`p` in its source. The polynomial satisfies the inequality near `e p`
(`MvPolynomial.exists_lojasiewicz_gradient`), and it passes to `f` through `e`
(`PartialDiffeomorph.exists_mul_abs_sub_rpow_le_norm_mgradient`).

Since `momentNormSq` does not change when `μ` is replaced by `-μ`
(`SymplecticGeometry.momentNormSq_neg`), the inequality holds for either sign convention of the
moment map.

## Convergence of the gradient flow

On a compact `M`, with a `C¹` Riemannian metric, the negative gradient flow of `f` from any point
exists for all positive time and converges to a critical point of `f`, with a bound on the
distance to the limit (`SymplecticGeometry.tendsto_maximalIntegralCurve_momentNormSq`). The
forward trajectory stays in the compact space `M`, where the inequality above holds near every
point, so the convergence theorem for trapped trajectories
(`SymplecticGeometry.exists_tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz`) applies
with `K = M`; the bound uses the exponent `θ ∈ [1/2, 1)` of the inequality at the limit. This is
Lerman's argument; no particular metric is needed, so it applies to the metric `σ(·, J ·)` of a
compatible almost complex structure.

## Main results

* `SymplecticGeometry.mgradient_momentNormSq`: the gradient of `‖μ‖²` at `x` is
  `-2 J X_{μ♯ x}(x)`, with `X_ξ` the fundamental vector field of `ξ` and `μ♯ x` the vector dual
  to `μ x` under `B`.
* `SymplecticGeometry.exists_lojasiewicz_momentNormSq`: the Łojasiewicz gradient inequality for
  the norm square of a moment map.
* `SymplecticGeometry.tendsto_maximalIntegralCurve_momentNormSq`: on a compact manifold, the
  negative gradient flow of the norm square of a moment map converges to a critical point.

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021].
* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign. Math. 51 (2005),
  117–127, proof of Theorem 1.1.
-/

public section

noncomputable section

open _root_.Bundle Manifold TauCeti
open scoped Manifold ContDiff RealInnerProductSpace

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)} {hB : B.Nondegenerate}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **The gradient of the norm square of a moment map.** Let `-μ` be a moment map for `σ` of the
action of `G` by fundamental vector fields, let the metric be `g(u, w) = σ(u, J w)`, and let `B`
be a nondegenerate symmetric form on the Lie algebra. Then the gradient of the norm square
`x ↦ ‖μ x‖²` is `-2 J X_{μ♯ x}`, where `μ♯ x` is the vector dual to `μ x` under `B` and `X_ξ` is
the fundamental vector field of `ξ`. -/
theorem mgradient_momentNormSq
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (hBs : B.IsSymm)
    (x : M) :
    Manifold.mgradient I' (momentNormSq B hB μ) x =
      (-2 : ℝ) • J x (fundamentalVectorField I' (momentSharp B hB μ x) x) := by
  have hd (ξ : GroupLieAlgebra I G) : MDifferentiableAt I' 𝓘(ℝ) (fun y ↦ μ y ξ) x :=
    (hμ.contMDiff_of_neg ξ).mdifferentiableAt (by simp)
  rw [neg_smul, ← smul_neg, ← mgradient_moment_apply hμ hg]
  refine ext_inner_right ℝ fun v ↦ ?_
  rw [Manifold.inner_mgradient, mvfderiv_momentNormSq hBs hd, real_inner_smul_left,
    Manifold.inner_mgradient, smul_apply, smul_eq_mul]

end Gradient

section Lojasiewicz

open Filter Set Topology TauCeti.Lie TauCeti.Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G] [T2Space G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

open scoped GroupLieAlgebra in
/-- **The Łojasiewicz gradient inequality for the norm square of a moment map.** Let a compact
Hausdorff Lie group `G` act smoothly on a manifold `M` without boundary, let `σ` be a closed
nondegenerate `G`-invariant two-form on `M` with coadjoint-equivariant moment map `μ`, let `B` be
a nondegenerate `Ad`-invariant bilinear form on `𝔤`, and give `M` a continuous Riemannian metric.
Then near every point `p : M` the norm square `f = momentNormSq B hB μ` satisfies
`c * |f y - f p| ^ θ ≤ ‖grad f y‖` for some `θ ∈ [1/2, 1)` and `c > 0`. -/
theorem exists_lojasiewicz_momentNormSq [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
    [IsContinuousRiemannianBundle E' (fun x : M ↦ TangentSpace I' x)] (hσc : σ.IsClosed)
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ)
    (hμ : σ.IsEquivariantMomentMap μ) {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
    (hB : B.Nondegenerate)
    (hBG : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B) (p : M) :
    ∃ θ ∈ Ico (1 / 2 : ℝ) 1, ∃ c > 0, ∀ᶠ y in 𝓝 p,
      c * |momentNormSq B hB μ y - momentNormSq B hB μ p| ^ θ ≤
        ‖mgradient I' (momentNormSq B hB μ) y‖ := by
  obtain ⟨d, e, P, hp, hP⟩ :=
    exists_partialDiffeomorph_momentNormSq_eq_eval hσc hσ hσG hμ hB hBG p
  obtain ⟨θ, hθ, c, hc, hL⟩ := P.exists_lojasiewicz_gradient (e p)
  refine ⟨θ, hθ, e.exists_mul_abs_sub_rpow_le_norm_mgradient (by simp) hp
    (g := fun z ↦ MvPolynomial.eval z P) hP hc ?_⟩
  simpa only [TauCeti.norm_gradient_eq_norm_fderiv] using hL

/-- **Convergence of the negative gradient flow of the norm square of a moment map.** Let a
compact Hausdorff Lie group `G` act smoothly on a compact manifold `M` without boundary, let `σ`
be a closed nondegenerate `G`-invariant two-form on `M` with coadjoint-equivariant moment map `μ`,
let `B` be a nondegenerate `Ad`-invariant bilinear form on `𝔤`, and give `M` a `C¹` Riemannian
metric. Then the maximal integral curve `γ` of `-grad f` through any `x`, for
`f = momentNormSq B hB μ`, is defined for all `t ≥ 0` and converges as `t → ∞` to a point `p` at
which `grad f` vanishes. Moreover, for some `θ ∈ [1/2, 1)` and `c > 0` and all large `t`, the
Riemannian distance from `γ t` to `p` is at most `(f (γ t) - f p) ^ (1 - θ) / (c * (1 - θ))`. -/
theorem tendsto_maximalIntegralCurve_momentNormSq [CompactSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
    [IsContMDiffRiemannianBundle I' 1 E' (fun x : M ↦ TangentSpace I' x)] (hσc : σ.IsClosed)
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ)
    (hμ : σ.IsEquivariantMomentMap μ) {B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G)}
    (hB : B.Nondegenerate)
    (hBG : Representation.IsInvariantForm (adjointRepresentation ℝ I G) B) (x : M) :
    Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I' (momentNormSq B hB μ)) x ∧
      ∃ p, mgradient I' (momentNormSq B hB μ) p = 0 ∧
        Tendsto (maximalIntegralCurve (-mgradient I' (momentNormSq B hB μ)) x) atTop (𝓝 p) ∧
        ∃ θ ∈ Ico (1 / 2 : ℝ) 1, ∃ c > 0, ∀ᶠ t in atTop,
          riemannianEDist I' (maximalIntegralCurve (-mgradient I' (momentNormSq B hB μ)) x t) p ≤
            ENNReal.ofReal ((momentNormSq B hB μ
              (maximalIntegralCurve (-mgradient I' (momentNormSq B hB μ)) x t) -
                momentNormSq B hB μ p) ^ (1 - θ) / (c * (1 - θ))) := by
  have : IsContinuousRiemannianBundle E' (fun x : M ↦ TangentSpace I' x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I') (n := 1)
  have hf : ContMDiff I' 𝓘(ℝ) 2 (momentNormSq B hB μ) :=
    (contMDiff_momentNormSq fun ξ ↦ hμ.toIsMomentMap.contMDiff ξ).of_le (by norm_cast)
  have hL (q : M) := exists_lojasiewicz_momentNormSq hσc hσ hσG hμ hB hBG q
  -- The forward trajectory stays in the compact space `M`.
  obtain ⟨hx, p, hpc, hconv, hdist⟩ :=
    exists_tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz hf isCompact_univ
      (mapsTo_univ _ _) fun q _ ↦ by
        obtain ⟨θ, hθ, c, hc, h⟩ := hL q
        exact ⟨θ, hθ.2, c, hc, h⟩
  obtain ⟨θ, hθ, c, hc, hLp⟩ := hL p
  exact ⟨hx, p, mgradient_eq_zero_iff.mpr (mem_criticalPoints.mp hpc.1), hconv, θ, hθ, c, hc,
    hdist hc hθ.2 hLp⟩

end Lojasiewicz

section Flow

open Set TauCeti.Manifold
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [ConnectedSpace G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  [FiniteDimensional ℝ EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC} [IC.Boundaryless]
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [FiniteDimensional ℝ E']
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

/-- **The negative gradient flow of `‖μ‖²` stays in the complex orbit.** Let the action of `Gc`
on the compact manifold `M` without boundary be a complexified action, let `-μ` be an equivariant
moment map for `σ`, let the `C¹` metric be `g(u, w) = σ(u, J w)`, and let `B` be a nondegenerate
symmetric form on the Lie algebra. Let `x` be the maximal integral curve of `-grad ‖μ‖²` through
`p`. Then there is a curve `g : ℝ → Gc` with `g 0 = 1` and left-trivialized derivative
`g⁻¹ ġ = -2 i μ♯(g⁻¹ p)` at every time, where `i = C.cplx` and `μ♯` is the vector dual to `μ`
under `B`, such that `x t = (g t)⁻¹ • p` for every `t`, and the Kempf–Ness function `Φ_p` has
derivative `-2 ‖μ (g⁻¹ p)‖²` along `g`. -/
theorem exists_mem_orbit_maximalIntegralCurve (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) (hBs : B.IsSymm)
    (p : M) :
    ∃ g : ℝ → Gc, g 0 = 1 ∧
      HasLeftTrivializedDerivOn g
        (fun t ↦ (-2 : ℝ) • C.cplx (C.lieMap (momentSharp B hB μ ((g t)⁻¹ • p)))) univ ∧
      (∀ t, maximalIntegralCurve (-mgradient I' (momentNormSq B hB μ)) p t = (g t)⁻¹ • p) ∧
      ∀ t, HasDerivAt (fun s ↦ kempfNessFunction C μ p (g s))
        (-2 * momentNormSq B hB μ ((g t)⁻¹ • p)) t := by
  have : LieGroup IC 1 Gc := LieGroup.of_le (n := ∞) (by norm_num)
  have hμm := hμ.toIsMomentMap
  set γ := maximalIntegralCurve (-mgradient I' (momentNormSq B hB μ)) p
  have hf : ContMDiff I' 𝓘(ℝ) 2 (momentNormSq B hB μ) :=
    (contMDiff_momentNormSq fun ξ ↦ hμm.contMDiff_of_neg ξ).of_le (by norm_cast)
  have hv := contMDiff_neg_mgradient_one hf
  -- On the compact manifold `M` the flow is defined for all time, and it is `C¹`.
  have hγ : IsMIntegralCurve γ (-mgradient I' (momentNormSq B hB μ)) :=
    isMIntegralCurve_maximalIntegralCurve hv
  have hγc : ContMDiff 𝓘(ℝ) I' 1 γ := by
    rw [← contMDiffOn_univ]
    exact (contMDiffOn_two_of_isMIntegralCurveOn uniqueDiffOn_univ
      (hγ.isMIntegralCurveOn univ) fun _ _ ↦ hv.contMDiffAt).of_le one_le_two
  -- The curve `ξ` in the Lie algebra of `Gc` along which `g` is solved for.
  set ξ : ℝ → GroupLieAlgebra IC Gc :=
    fun t ↦ (-2 : ℝ) • C.cplx (C.lieMap (momentSharp B hB μ (γ t)))
  -- `ξ` is `γ` followed by `-μ` and a linear map, read as a curve in the model space `EC`.
  have hξ : ContMDiff 𝓘(ℝ) 𝓘(ℝ, EC) 1 (@id (ℝ → EC) ξ) := by
    let L : Module.Dual ℝ (GroupLieAlgebra I G) →ₗ[ℝ] EC :=
      (2 : ℝ) • (C.cplx.toLinearMap ∘ₗ C.lieMap.toLinearMap ∘ₗ (B.toDual hB).symm.toLinearMap)
    have hL (t : ℝ) : ξ t = L (-μ (γ t)) := by
      -- `L` takes values in the model space `EC`; read its value in the Lie algebra of `Gc`,
      -- which is `EC` by definition, to compute it.
      change _ = (2 : ℝ) • C.cplx (C.lieMap ((B.toDual hB).symm (-μ (γ t))))
      simp [ξ, momentSharp_def]
    exact (((hμm.contMDiff_linearMap_comp L).of_le (by norm_cast)).comp hγc).congr hL
  set g := leftTrivializedCurve ξ 1
  have hgξ : HasLeftTrivializedDerivOn g ξ univ :=
    hasLeftTrivializedDerivOn_leftTrivializedCurve (n := ∞) (by norm_cast) hξ.continuous 1
  have hg0 : g 0 = 1 := leftTrivializedCurve_zero (n := ∞) (by norm_cast) hξ.continuous 1
  -- Both curves solve `ż = X_{-ξ t}(z)`, for the fundamental vector fields of `Gc`.
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I') I'.tangent 1 (fun q : ℝ × M ↦
      (⟨q.2, fundamentalVectorField I' (-ξ q.1) q.2⟩ : TangentBundle I' M)) :=
    ContMDiff.contMDiff_prod_fundamentalVectorField Gc hξ.neg (by norm_cast)
  have hy (t : ℝ) : HasMFDerivAt 𝓘(ℝ, ℝ) I' (fun u ↦ (g u)⁻¹ • p) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (fundamentalVectorField I' (-ξ t) ((g t)⁻¹ • p))) := by
    have := hasMFDerivWithinAt_univ.mp (hgξ.hasMFDerivWithinAt_inv_smul (I' := I') (p := p)
      (mem_univ t) (((ContMDiffSMul.contMDiff_smul_const (I := IC) (I' := I') p).comp
        (contMDiff_inv IC ∞)).mdifferentiableAt (by simp)))
    rwa [fundamentalVectorField_neg, Pi.neg_apply]
  have hx (t : ℝ) : HasMFDerivAt 𝓘(ℝ, ℝ) I' γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (fundamentalVectorField I' (-ξ t) (γ t))) := by
    have hγt := hγ t
    rw [Pi.neg_apply, mgradient_momentNormSq hμm hg hBs, ← neg_smul, neg_neg,
      ← h.fundamentalVectorField_lieMap, ← h.fundamentalVectorField_cplx, ← Pi.smul_apply,
      ← fundamentalVectorField_smul] at hγt
    convert hγt using 4
    simp [ξ]
  have heq (t : ℝ) : γ t = (g t)⁻¹ • p := by
    have h₁ := timeDependentFlowOf_eq_of_forall_hasMFDerivAt
      (X := fun u z ↦ fundamentalVectorField I' (-ξ u) z) hX hx 0 t
    have h₂ := timeDependentFlowOf_eq_of_forall_hasMFDerivAt
      (X := fun u z ↦ fundamentalVectorField I' (-ξ u) z) hX hy 0 t
    have hγ0 : γ 0 = p := maximalIntegralCurve_zero
    rw [← h₁, ← h₂, hg0, inv_one, one_smul, hγ0]
  have hξg : (fun t ↦ (-2 : ℝ) • C.cplx (C.lieMap (momentSharp B hB μ ((g t)⁻¹ • p)))) = ξ :=
    funext fun t ↦ by rw [← heq]
  refine ⟨g, hg0, hξg ▸ hgξ, heq, fun t ↦ ?_⟩
  -- The derivative of `Φ_p` along `g` is `μ (g⁻¹ p) (C.im (g⁻¹ ġ))`.
  obtain ⟨w, hw', hwξ⟩ := hasLeftTrivializedDerivOn_univ_iff.mp hgξ t
  have hΦ := hasDerivAt_kempfNessFunction_comp C μ p h hμ hg hw'.mdifferentiableAt
  have hw1 : mfderiv 𝓘(ℝ) IC g t (1 : ℝ) = w := by
    rw [hw'.mfderiv]
    exact one_smul ℝ w
  refine hΦ.congr_deriv ?_
  rw [hw1, hwξ]
  rw [map_smul, C.im_cplx_lieMap, map_smul, smul_eq_mul, heq, momentNormSq_eq_apply_momentSharp]

end Flow

end SymplecticGeometry

end
