/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.ProjectiveSpaceClassifying
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.Geometry.Manifold.Morse.CWModel
public import TauCeti.Geometry.Manifold.Morse.Generic.Basic
public import TauCeti.Geometry.Manifold.Morse.Index

/-!
# Classes of degree two on a compact manifold come from complex projective space

Let `M` be a compact boundaryless smooth manifold and `N` a natural number with
`dim M ≤ 2 * N`. This file shows that every class `b ∈ H²(M; ℤ)` is the pull-back `F^* h` of the
hyperplane class `h` of `ℙ ℂ (Fin (N + 1) → ℂ)` along a continuous map
`F : M → ℙ ℂ (Fin (N + 1) → ℂ)`
(`Projectivization.exists_continuousMap_projectivization_pullback_eq_of_isManifold`).

## Proof

A Morse function on `M` gives a finite CW complex `W` homotopy equivalent to `M` whose cells have
dimension at most `dim M` (`TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`,
`TauCeti.manifoldMorseIndex_le_finrank`). This is the argument of Tau Ceti's
`TauCeti.FiniteCWType.of_isManifold`, with control of the dimensions of the cells. The class
`b`, carried to `W`, is the pull-back of `h` along a map `W → ℙ ℂ (Fin (N + 1) → ℂ)`
(`Projectivization.exists_continuousMap_projectivization_pullback_eq`). Composed with the
homotopy equivalence `M → W`, this gives a map pulling `h` back to `b`, by homotopy invariance
(`TopCat.Homotopy.congr_singularCohomologyMap`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.3 (maps into
  `ℂPᴺ`).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 (the CW model of a manifold from a Morse function).
-/

public section

open CategoryTheory Module Set TauCeti Topology.RelCWComplex
open scoped LinearAlgebra.Projectivization Manifold ContDiff

namespace Projectivization

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

include I in
/-- **Classes of degree two on a compact manifold come from complex projective space.** Let `M` be
a compact boundaryless smooth manifold, and `N` a natural number with `dim M ≤ 2 * N`. Every class
`b ∈ H²(M; ℤ)` is the pull-back `F^* h` of the hyperplane class `h` of `ℙ ℂ (Fin (N + 1) → ℂ)`
along some continuous map `F : M → ℙ ℂ (Fin (N + 1) → ℂ)`. -/
theorem exists_continuousMap_projectivization_pullback_eq_of_isManifold {N : ℕ}
    (hN : finrank ℝ E ≤ 2 * N) (b : (TopCat.of M).integralCohomology 2) :
    ∃ F : C(M, ℙ ℂ (Fin (N + 1) → ℂ)),
      TopCat.singularCohomologyMap (TopCat.ofHom F) 2
        (hyperplaneClass (Fin (N + 1) → ℂ)) = b := by
  obtain ⟨φ, hφ⟩ := exists_isMorse (I := I) (M := M)
  obtain ⟨W, _, _, _, -, ⟨e⟩, hcell⟩ := hφ.exists_finite_cwComplex_homotopyEquiv
  -- The `m`-cells of `W` are critical points of index `m ≤ dim M`.
  have hW : ∀ m, 2 * N < m → IsEmpty (cell (univ : Set W) m) := fun m hm ↦ by
    obtain ⟨σ⟩ := hcell m
    refine ⟨fun c ↦ ?_⟩
    have h := (σ c).property.2
    have := manifoldMorseIndex_le_finrank (I := I) (f := φ) (x := (σ c : M))
    omega
  -- Carry `b` to the CW complex `univ ⊆ W`, homotopy equivalent to `M`.
  let e' : ContinuousMap.HomotopyEquiv (univ : Set W) M :=
    (Homeomorph.Set.univ W).toHomotopyEquiv.trans e
  obtain ⟨F, hF⟩ := exists_continuousMap_projectivization_pullback_eq
    (C := (univ : Set W)) (N := N) hW
    (TopCat.singularCohomologyMap (TopCat.ofHom e'.toFun) 2 b)
  refine ⟨F.comp e'.invFun, ?_⟩
  rw [TopCat.ofHom_comp, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply, hF,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    TopCat.Homotopy.congr_singularCohomologyMap
      (f := TopCat.ofHom e'.invFun ≫ TopCat.ofHom e'.toFun) (g := 𝟙 _) e'.right_inv.some _ ℤ _ 2,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

end Projectivization

end
