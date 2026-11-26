/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Components
public import TauCeti.Geometry.Symplectic.Manifold.Opens
import SymplecticGeometry.Geometry.Manifold.DeRham.Basic

/-!
# Nondegenerate and symplectic two-forms on an open cover

Tau Ceti's `TauCeti/Geometry/Symplectic/Manifold/Opens.lean` restricts a nondegenerate or
symplectic two-form to one open subset. This file gives the converse for an open cover
`U : ι → Opens M`: nondegeneracy is a pointwise condition, and the restriction to an open subset
does not change the form at a point, so a two-form is nondegenerate when each of its restrictions
to the `U i` is. With the test of closedness on an open cover from
`DifferentialForm/Components.lean`, the same holds for symplectic forms.

## Main results

* `TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_mpullback_subtype_val`: a two-form is
  nondegenerate exactly when its restriction to each member of an open cover is.
* `TauCeti.SmoothTwoForm.isSymplectic_iff_forall_mpullback_subtype_val`: a two-form is
  symplectic exactly when its restriction to each member of an open cover is.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapters 14 and 17.
-/

public section

open TopologicalSpace
open scoped Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  {ι : Type*} {U : ι → Opens M}

namespace TauCeti.SmoothTwoForm

/-- A two-form is nondegenerate exactly when its restriction to each member of an open cover is
nondegenerate. -/
theorem isNondegenerate_iff_forall_mpullback_subtype_val (hcover : IsOpenCover U)
    {σ : SmoothTwoForm I M} :
    σ.IsNondegenerate ↔
      ∀ i, IsNondegenerate (SmoothForm.mpullback (Subtype.val : U i → M) contMDiff_subtypeVal σ) :=
  ⟨fun h i ↦ h.mpullback_subtype_val (U i), fun h ↦ by
    simp only [isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot,
      bilinFormAt_mpullback_subtype_val, Subtype.forall] at h ⊢
    intro x
    obtain ⟨i, hx⟩ := hcover.exists_mem x
    exact h i x hx⟩

/-- A two-form is symplectic exactly when its restriction to each member of an open cover is
symplectic. -/
theorem isSymplectic_iff_forall_mpullback_subtype_val (hcover : IsOpenCover U)
    {σ : SmoothTwoForm I M} :
    σ.IsSymplectic ↔
      ∀ i, IsSymplectic
        (SmoothForm.mpullback (Subtype.val : U i → M) contMDiff_subtypeVal σ) := by
  refine ⟨fun h i ↦ h.mpullback_subtype_val (U i), fun h ↦ ⟨?_,
    (isNondegenerate_iff_forall_mpullback_subtype_val hcover).mpr fun i ↦ (h i).isNondegenerate⟩⟩
  rw [SmoothForm.isClosed_iff_mem_closedForms,
    SmoothForm.mem_closedForms_iff_forall_mpullback_subtype_val hcover]
  exact fun i ↦ (SmoothForm.isClosed_iff_mem_closedForms _).mp (h i).isClosed

end TauCeti.SmoothTwoForm

end
