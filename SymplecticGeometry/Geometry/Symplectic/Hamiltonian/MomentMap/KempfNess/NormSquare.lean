/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalNormalForm
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import SymplecticGeometry.Analysis.Calculus.Gradient.Basic
import SymplecticGeometry.Analysis.Calculus.Lojasiewicz.Polynomial
import SymplecticGeometry.Geometry.Manifold.Riemannian.Gradient.PartialDiffeomorph

/-!
# The norm square of a moment map

Let a compact Hausdorff Lie group `G` act smoothly on a manifold `M` without boundary, with a
closed nondegenerate `G`-invariant two-form `σ` and a coadjoint-equivariant moment map `μ`, and
let `B` be a nondegenerate `Ad`-invariant bilinear form on the Lie algebra `𝔤`. This file
studies the norm square `f = SymplecticGeometry.momentNormSq B hB μ`, `f y = B^∨ (μ y) (μ y)`.

It proves Łojasiewicz's gradient inequality for `f` near every point `p`, for any continuous
Riemannian metric on `M` (`SymplecticGeometry.exists_lojasiewicz_momentNormSq`): there are
`θ ∈ [1/2, 1)` and `c > 0` with `c * |f y - f p| ^ θ ≤ ‖grad f y‖` for `y` near `p`. This is the
hypothesis of the convergence theorem
`SymplecticGeometry.tendsto_maximalIntegralCurve_neg_mgradient_of_lojasiewicz` for the negative
gradient flow of `f`. No complex structure is involved.

The proof is Lerman's. By the local normal form
(`SymplecticGeometry.exists_partialDiffeomorph_momentNormSq_eq_eval`), `f` is a real polynomial
`P` in the coordinates of a smooth partial diffeomorphism `e` from `M` to a Euclidean space, with
`p` in its source. The polynomial satisfies the inequality near `e p`
(`MvPolynomial.exists_lojasiewicz_gradient`), and it passes to `f` through `e`
(`PartialDiffeomorph.exists_mul_abs_sub_rpow_le_norm_mgradient`).

Since `momentNormSq` does not change when `μ` is replaced by `-μ`
(`SymplecticGeometry.momentNormSq_neg`), the inequality holds for either sign convention of the
moment map.

## Main results

* `SymplecticGeometry.exists_lojasiewicz_momentNormSq`: the Łojasiewicz gradient inequality for
  the norm square of a moment map.

## References

* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign. Math. 51 (2005),
  117–127, proof of Theorem 1.1.
-/

public section

open Bundle Filter Set Topology TauCeti TauCeti.Lie TauCeti.Manifold
open scoped Manifold ContDiff

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
  simpa only [norm_gradient] using hL

end SymplecticGeometry

end
