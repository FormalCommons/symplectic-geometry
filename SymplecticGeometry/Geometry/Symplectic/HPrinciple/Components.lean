/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.HPrinciple.FormSpaces
public import Mathlib.Topology.Sets.OpenCover
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Components
import SymplecticGeometry.Geometry.Symplectic.Manifold.Opens

/-!
# The spaces of nondegenerate and of symplectic forms over the components

Let `U : ι → Opens M` be an open cover of a manifold `M`, such as the connected components
`ConnectedComponents.opens` of `M` (with `IsOpenCover.mk ConnectedComponents.iSup_opens`).
Nondegeneracy of a two-form is a pointwise condition and restriction to an open subset does not
change the form at a point, so a two-form is nondegenerate exactly when each of its restrictions
to the `U i` is, and so is a symplectic form (`Symplectic/Manifold/Opens.lean`). Exactness can be
tested on the `U i` when they are moreover pairwise disjoint (`DifferentialForm/Components.lean`),
so membership in the spaces of `HPrinciple/FormSpaces.lean` is tested on the members of the
cover.

## Main results

* `mem_nondegenerateForms_iff_forall_restrict`: a two-form on the tangent bundle of `M` is in
  `nondegenerateForms I M` exactly when each of its restrictions is in the space of nondegenerate
  forms on `U i`.
* `mem_symplecticFormsInClass_iff_forall_restrict`: for a pairwise disjoint open cover, a two-form
  is in `symplecticFormsInClass α` exactly when each restriction is in the space of symplectic
  forms in the class of the restriction of `α`.

The restriction of a two-form `ω` on the tangent bundle is read through
`Bundle.ContMDiffTwoForm.tangentEquiv`, as in
`Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback_subtypeVal`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.3.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapters 14 and 17.
-/

public section

open Bundle Function SymplecticGeometry.Bundle TopologicalSpace
open scoped Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  {ι : Type*} {U : ι → Opens M}

namespace SymplecticGeometry

/-- A smooth two-form `ω` on the tangent bundle of `M` is nondegenerate exactly when, for each
member `U i` of an open cover of `M`, its restriction to `U i` is nondegenerate. -/
theorem mem_nondegenerateForms_iff_forall_restrict (hcover : IsOpenCover U)
    {ω : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))} :
    ω ∈ nondegenerateForms I M ↔
      ∀ i, ContMDiffTwoForm.tangentEquiv.symm (TauCeti.SmoothForm.mpullback
        (Subtype.val : U i → M) contMDiff_subtypeVal (ContMDiffTwoForm.tangentEquiv ω)) ∈
          nondegenerateForms I (U i) := by
  simp only [mem_nondegenerateForms, ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff,
    ← TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_mpullback_subtype_val hcover,
    ContMDiffTwoForm.isNondegenerate_tangentEquiv_iff]

/-- For pairwise disjoint open subsets `U i` covering `M` and a smooth two-form `α` on `M`, a
smooth two-form `ω` on the tangent bundle of `M` is symplectic in the class of `α` exactly when,
for each `i`, its restriction to `U i` is symplectic in the class of the restriction of `α`. -/
theorem mem_symplecticFormsInClass_iff_forall_restrict (hU : Pairwise (Disjoint on U))
    (hcover : IsOpenCover U) {α : TauCeti.SmoothTwoForm I M}
    {ω : ContMDiffTwoForm I ⊤ E (TangentSpace I (M := M))} :
    ω ∈ symplecticFormsInClass α ↔
      ∀ i, ContMDiffTwoForm.tangentEquiv.symm (TauCeti.SmoothForm.mpullback
        (Subtype.val : U i → M) contMDiff_subtypeVal (ContMDiffTwoForm.tangentEquiv ω)) ∈
          symplecticFormsInClass
            (TauCeti.SmoothForm.mpullback (Subtype.val : U i → M) contMDiff_subtypeVal α) := by
  simp only [mem_symplecticFormsInClass, LinearEquiv.apply_symm_apply, ← map_sub, forall_and,
    ← TauCeti.SmoothTwoForm.isSymplectic_iff_forall_mpullback_subtype_val hcover,
    ← TauCeti.SmoothForm.mem_exactForms_iff_forall_mpullback_subtype_val hU hcover]

end SymplecticGeometry

end
