/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Orientation.Diffeomorph
public import TauCeti.AlgebraicTopology.Cohomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Homeomorph
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth

/-!
# Fundamental classes carried along a diffeomorphism

Let `e : M ≃ₘ^k⟮I, J⟯ N` be a `C^k` diffeomorphism, `k ≠ 0`, between compact Hausdorff manifolds
with boundaryless models of real dimension `n + 1`, possibly on different model spaces, and let
`o` be an orientation of `M`. Then `e` carries the fundamental class of `o` to the fundamental
class of the carried orientation `o.map e` of `N`, and so evaluating a cohomology class of `N` on
the fundamental class of `o.map e` is evaluating its pullback along `e` on that of `o`.

No connectedness is assumed. Since `e` preserves orientation from `o` to `o.map e` at every
point, the map it induces on local homology at `x` carries the local orientation of `o` to that
of `o.map e` (`TauCeti.Manifold.Orientation.localHomologyMap_toHomologicalOrientation`), and a
homeomorphism that does so carries the fundamental class of the one to that of the other
(`TauCeti.HomologicalOrientation.mapFundamentalClass_homeomorph_of_localHomologyMap`).

## Main results

* `TauCeti.Manifold.Orientation.mapFundamentalClass_toHomologicalOrientation_map`:
  `e_*[M, o] = [N, o.map e]`.
* `TauCeti.Manifold.Orientation.evalFundamentalClass_toHomologicalOrientation_map`:
  `⟨w, [N, o.map e]⟩ = ⟨e^* w, [M, o]⟩` for every cohomology class `w` of `N`.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

open Module

open scoped Manifold ContDiff

namespace TauCeti.Manifold.Orientation

variable {M N E F : Type} {H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace H M] [ChartedSpace E M]
  [IsManifold I 1 M]
  [TopologicalSpace N] [T2Space N] [CompactSpace N] [ChartedSpace H' N] [ChartedSpace F N]
  [IsManifold J 1 N]
  {n : ℕ} (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n + 1) {k : ℕ∞ω}

/-- **A diffeomorphism carries the fundamental class to the fundamental class.** A `C^k`
diffeomorphism `e : M → N`, `k ≠ 0`, of compact manifolds of dimension `n + 1` carries the
fundamental class of an orientation `o` of `M` to the fundamental class of the orientation
`o.map e` of `N`. -/
theorem mapFundamentalClass_toHomologicalOrientation_map (o : Orientation I M (Fin (n + 1)))
    (e : M ≃ₘ^k⟮I, J⟯ N) (hk : k ≠ 0) :
    (o.toHomologicalOrientation hE).mapFundamentalClass hE (e.toHomeomorph : C(M, N)) =
      ((o.map e hk ((Fintype.card_fin _).trans hF.symm)).toHomologicalOrientation hF
        ).fundamentalClass hF :=
  HomologicalOrientation.mapFundamentalClass_homeomorph_of_localHomologyMap hE hF _ _
    e.toHomeomorph fun x hx ↦ localHomologyMap_toHomologicalOrientation hE hF _ hx
      (isOrientationPreservingAt_map o e hk _ x)

/-- **Evaluation on the carried fundamental class.** For a `C^k` diffeomorphism `e : M → N`,
`k ≠ 0`, of compact manifolds of dimension `n + 1` and an orientation `o` of `M`, evaluating a
cohomology class `w` of `N` on the fundamental class of `o.map e` is evaluating its pullback
`e^* w` on the fundamental class of `o`. -/
theorem evalFundamentalClass_toHomologicalOrientation_map (o : Orientation I M (Fin (n + 1)))
    (e : M ≃ₘ^k⟮I, J⟯ N) (hk : k ≠ 0) (R : ModuleCat.{0} ℤ)
    (w : (TopCat.of N).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ R (n + 1)) :
    ((o.map e hk ((Fintype.card_fin _).trans hF.symm)).toHomologicalOrientation hF
        ).evalFundamentalClass hF R (ContinuousMap.id N) w =
      (o.toHomologicalOrientation hE).evalFundamentalClass hE R (ContinuousMap.id M)
        (TopCat.singularCohomologyMap (TopCat.ofHom (e.toHomeomorph : C(M, N))) _ w) := by
  rw [HomologicalOrientation.evalFundamentalClass_id_singularCohomologyMap,
    HomologicalOrientation.evalFundamentalClass_apply,
    HomologicalOrientation.evalFundamentalClass_apply,
    HomologicalOrientation.mapFundamentalClass_id,
    mapFundamentalClass_toHomologicalOrientation_map hE hF o e hk]

end TauCeti.Manifold.Orientation
