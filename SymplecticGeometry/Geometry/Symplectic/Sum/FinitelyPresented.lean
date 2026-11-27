/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Sum.GraphTorus
import SymplecticGeometry.AlgebraicTopology.FundamentalGroup.AddCircle
import SymplecticGeometry.Geometry.Manifold.GeneralPosition
import SymplecticGeometry.Geometry.Manifold.NullSet
import SymplecticGeometry.Topology.Homotopy.AddCircle

/-!
# Disjoint symplectic tori in `Σ × T` for finitely many loops

This file prepares the realization of finitely presented groups as fundamental groups of closed
symplectic four-manifolds. Let `Σ` be a Hausdorff manifold of dimension at least two, smooth and
without boundary, such as the closed surface of genus `g`
(`SymplecticGeometry.ClosedSurface g`), and let `T = ∀ j : ι ⊕ ι, AddCircle (p j)` be the
standard torus with one of its coordinates `i`. For finitely many based loops `γ k` at `x` in `Σ`,
`exists_graphTorus_family` gives smooth circle maps `h k : AddCircle (p i) → Σ` and a point `z`
of `Σ` such that

* the loops of the `h k`, brought to `x` along any paths, normally generate the same subgroup of
  `π₁(Σ, x)` as the `γ k`;
* the graph tori `y ↦ (h k (y i), y)` (`SymplecticGeometry.graphTorus`) are pairwise disjoint;
* each of them is disjoint from the fibre torus `{z} × T`, which is the graph torus of the
  constant map at `z`.

The maps come from the general position of finitely many circle maps
(`SymplecticGeometry.exists_contMDiff_homotopic_forall_ne_addCircle`), applied to the circle maps
`(γ k).toAddCircle` of the loops, and `z` from the density of the complement of finitely many
smooth loops (`SymplecticGeometry.dense_compl_iUnion_range_addCircle`). Free homotopies do not
change the normal closure (`ContinuousMap.normalClosure_range_toLoop_eq_of_homotopic`).

When `Σ` is a surface with a nondegenerate two-form `σ`, such as an area form of the closed
surface (`SymplecticGeometry.ClosedSurface.exists_isSymplectic`), the rest is in
`Sum/GraphTorus.lean`, for every graph torus and so for the fibre torus too: it pulls the product
form `pr₁^* σ + pr₂^* ω_T` back to `ω_T = TauCeti.torusSymplecticForm p`
(`SymplecticGeometry.mpullback_graphTorus_prod_torusSymplecticForm`), so it is symplectic
(`SymplecticGeometry.hasSymplecticTangentImages_graphTorus`); it has a symplectic framing
(`SymplecticGeometry.nonempty_symplecticFraming_graphTorus`); and in
`π₁(Σ × T) ≃* π₁(Σ) × π₁(T)` it sends the generator of the `i`-th circle of `T` to the pair of
the loop of `h k` and that generator, and every other generator `α` to `(1, α)`
(`SymplecticGeometry.prodMulEquiv_mapOfEq_graphTorus_torusLoop_single_self`,
`SymplecticGeometry.prodMulEquiv_mapOfEq_graphTorus_torusLoop_single_of_ne`).

## Main result

* `SymplecticGeometry.exists_graphTorus_family`: smooth loops in general position, homotopic to
  given loops, whose graph tori are pairwise disjoint and miss a fibre torus.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 7.2.8.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
-/

public section

noncomputable section

open Set Function TauCeti Module
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [FiniteDimensional ℝ E] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {ι : Type*} [Fintype ι] {p : ι ⊕ ι → ℝ} [∀ i, Fact (0 < p i)] {i : ι ⊕ ι}

/-- **Disjoint graph tori for finitely many loops.** Let `M` be a Hausdorff manifold of dimension
at least two, smooth and without boundary, and `γ k`, for `k` in a finite type, loops at `x`.
Then there are smooth circle maps `h k : AddCircle (p i) → M` and a point `z` of `M` such that

* the loops `ψ k · h k · (ψ k)⁻¹` at `x`, for any paths `ψ k` from `x` to `h k 0`, normally
  generate the same subgroup of `π₁(M, x)` as the `γ k`;
* the graph tori of the `h k` in `M × T` are pairwise disjoint;
* each of them is disjoint from the fibre torus `{z} × T`, the graph torus of the constant map
  at `z`. -/
theorem exists_graphTorus_family (hE : 2 ≤ finrank ℝ E) {x : M} {κ : Type*} [Finite κ]
    (γ : κ → Path x x) :
    ∃ (h : κ → C(AddCircle (p i), M)) (hh : ∀ k, ContMDiff 𝓘(ℝ) I ∞ (h k)) (z : M),
      (∀ ψ : ∀ k, Path x (h k 0),
        Subgroup.normalClosure (range fun k ↦ FundamentalGroup.fromPath (.mk ((ψ k).trans
          ((h k).toLoop.trans (ψ k).symm)))) =
          Subgroup.normalClosure (range fun k ↦ FundamentalGroup.fromPath (.mk (γ k)))) ∧
      Pairwise (fun k l ↦ Disjoint (range (graphTorus (hh k))) (range (graphTorus (hh l)))) ∧
      ∀ k, Disjoint (range (graphTorus (hh k))) (range (graphTorus
        (contMDiff_const : ContMDiff 𝓘(ℝ) I ∞ fun _ : AddCircle (p i) ↦ z))) := by
  -- The circle maps of the loops, moved into general position.
  let f : κ → C(AddCircle (p i), M) := fun k ↦ (γ k).toAddCircle (p i)
  have : Nonempty M := ⟨x⟩
  obtain ⟨g, hg, hne⟩ := exists_contMDiff_homotopic_forall_ne_addCircle (I := I) hE f
  -- A point off the images of the `g k`.
  obtain ⟨z, hz⟩ := (dense_compl_iUnion_range_addCircle (I := I) (by omega)
    fun k ↦ (hg k).1.mdifferentiable (by simp)).nonempty
  simp only [mem_compl_iff, mem_iUnion, mem_range, not_exists] at hz
  refine ⟨g, fun k ↦ (hg k).1, z, fun ψ ↦ ?_, fun k l hkl ↦ ?_, fun k ↦ ?_⟩
  · -- The loops of the `f k`, read at `x` along constant paths, are the `γ k`.
    let χ : ∀ k, Path x (f k 0) := fun k ↦ (Path.refl x).cast rfl ((γ k).toAddCircle_zero)
    have hχ (k : κ) : FundamentalGroup.fromPath (.mk ((χ k).trans ((f k).toLoop.trans
        (χ k).symm))) = FundamentalGroup.fromPath (.mk (γ k)) := by
      have hpath : (χ k).trans ((f k).toLoop.trans (χ k).symm) =
          (Path.refl x).trans ((γ k).trans (Path.refl x).symm) := by
        rw [ContinuousMap.toLoop_toAddCircle]
        ext t
        simp [χ, Path.trans_apply]
      rw [hpath, Path.refl_symm]
      exact congrArg _ (Path.Homotopic.Quotient.eq.2 ((Path.Homotopic.refl_trans _).trans
        (Path.Homotopic.trans_refl _)))
    rw [← ContinuousMap.normalClosure_range_toLoop_eq_of_homotopic (fun k ↦ (hg k).2) χ ψ]
    simp_rw [hχ]
  · exact (disjoint_range_graphTorus_iff _ _).2 (hne k l hkl)
  · exact (disjoint_range_graphTorus_iff _ _).2 fun t ht ↦ hz k t ht

end SymplecticGeometry

end
