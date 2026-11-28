/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber
public import TauCeti.AlgebraicTopology.Cohomology.LerayHirsch.FiniteCover
public import TauCeti.Geometry.Manifold.SmoothSingular.SingularCohomology
import SymplecticGeometry.Topology.Category.TopCat.Trivialization
import SymplecticGeometry.LinearAlgebra.LinearIndependent
import TauCeti.Geometry.Manifold.SmoothSingular.DeRham.Equiv

/-!
# The Leray–Hirsch theorem for de Rham classes

Let `proj : M → B` be a continuous map from a smooth manifold to a manifold, with finitely many
trivializations `t j` with model fibre a smooth manifold `F`, whose base sets cover `B` and whose
inverses are smooth, so that their fibre inclusions `F → M` are smooth
(`Bundle.Trivialization.contMDiff_fiberInclusionMap`). Suppose that the real singular homology of
`F` is finite-dimensional in degrees `d ≤ n`, and that de Rham classes `c d i ∈ H^d_dR(M)` pull
back, along the fibre inclusion of every `t j` over every point of its base set, to a basis of
`H^d_dR(F)` for each `d ≤ n`. Then the singular Leray–Hirsch map with real coefficients for the
classes `TauCeti.deRhamHom (c d i) ∈ Hᵈ(M; ℝ)`,

`⨁_{d + q = m} ⨁_{i : ι d} H^q(B; ℝ) ⟶ Hᵐ(M; ℝ)`,
`(a_{d,i}) ↦ ∑ proj^* a_{d,i} ⌣ deRhamHom (c d i)`,

is bijective in every degree `m ≤ n` (`TopCat.lerayHirsch_deRhamHom_bijective`). The fibre need
not be a sphere: besides the finiteness of its homology, it is only asked to be a Hausdorff
`σ`-compact manifold modelled on a finite-dimensional space, and of the base only the finite
trivializing cover is used.

## Proof

This is Tau Ceti's `TopCat.lerayHirsch_bijective_of_trivializations`, for the morphism of `TopCat`
given by `proj`. Its hypothesis on the fibre is moved from de Rham to singular classes by the
de Rham theorem on `F`, as the linear equivalence `TauCeti.deRhamEquiv`, and its naturality
along the smooth fibre inclusions (`TauCeti.deRhamHom_map`); the continuous fibre inclusions are
Tau Ceti's fibre inclusions in `TopCat` by `Bundle.Trivialization.ofHom_fiberInclusionMap`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4D.1 (Leray–Hirsch), for the singular theorem.
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §14, which proves
  the de Rham form by a different argument, through the Čech–de Rham complex.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology Bundle TauCeti
open scoped Manifold ContDiff

namespace TopCat

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF] {HF : Type}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type} [TopologicalSpace F]
  [ChartedSpace HF F] [T2Space F] [SigmaCompactSpace F] [IsManifold IF ∞ F]
  {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM] {HM : Type}
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type} [TopologicalSpace M]
  [ChartedSpace HM M] [T2Space M] [SigmaCompactSpace M] [IsManifold IM ∞ M]
  {proj : M → B} {ι : ℕ → Type*} [∀ d, DecidableEq (ι d)]

/-- **The Leray–Hirsch theorem for de Rham classes.** Let `proj : M → B` be continuous, and
`t j`, for `j` in a finite set `s`, trivializations of `proj` with model fibre `F` whose base sets
cover `B` and whose inverses are smooth on their targets. Suppose that the real singular homology
of `F` is finite-dimensional in degrees `d ≤ n`, and that for each `d ≤ n` the de Rham classes
`c d i ∈ H^d_dR(M)` pull back, along the fibre inclusion of each `t j` over each point of its
base set, to a basis of `H^d_dR(F)`. Then for every `m ≤ n` the Leray–Hirsch map
`⨁_{d + q = m} ⨁_{i : ι d} H^q(B; ℝ) ⟶ Hᵐ(M; ℝ)`,
`(a_{d,i}) ↦ ∑ proj^* a_{d,i} ⌣ deRhamHom (c d i)`,
is bijective. -/
theorem lerayHirsch_deRhamHom_bijective (hproj : Continuous proj) {κ : Type*} (s : Finset κ)
    (t : κ → Trivialization F proj) (hcover : ⋃ j ∈ s, (t j).baseSet = Set.univ)
    (ht : ∀ j ∈ s, ContMDiffOn (IB.prod IF) IM ∞ (t j).toOpenPartialHomeomorph.symm (t j).target)
    (n : ℕ) (hF : ∀ d ≤ n, Module.Finite ℝ (((singularHomologyFunctor (ModuleCat.{0} ℝ) d).obj
      (𝟙_ (ModuleCat.{0} ℝ))).obj (of F)))
    (c : ∀ d, ι d → deRhamCohomology IM M d)
    (hc : ∀ j (hj : j ∈ s) b (hb : b ∈ (t j).baseSet), ∀ d ≤ n,
      LinearIndependent ℝ (fun i ↦ deRhamCohomology.map ((t j).fiberInclusionMap hb)
        ((t j).contMDiff_fiberInclusionMap (ht j hj) hb) d (c d i)) ∧
      ⊤ ≤ Submodule.span ℝ (Set.range fun i ↦ deRhamCohomology.map ((t j).fiberInclusionMap hb)
        ((t j).contMDiff_fiberInclusionMap (ht j hj) hb) d (c d i))) :
    ∀ m ≤ n, Function.Bijective
      (lerayHirsch (ofHom ⟨proj, hproj⟩) m fun d i ↦ deRhamHom IM M d (c d i)) := by
  refine lerayHirsch_bijective_of_trivializations (F := of F) (p := ofHom ⟨proj, hproj⟩) _ s t
    hcover n hF fun j hj b hb d hd ↦ ?_
  rw [← Trivialization.ofHom_fiberInclusionMap (F := of F)]
  -- The de Rham theorem on `F` carries the de Rham basis to the singular one.
  have h := ((deRhamEquiv IF F d).linearIndependent_comp_and_top_le_span_iff _).2
    (hc j hj b hb d hd)
  simp only [Function.comp_def, deRhamEquiv_apply, deRhamHom_map] at h
  exact h

end TopCat
