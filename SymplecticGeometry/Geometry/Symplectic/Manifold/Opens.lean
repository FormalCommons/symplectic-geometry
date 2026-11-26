/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Opens
public import Mathlib.Topology.Sets.OpenCover
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Components
import SymplecticGeometry.Geometry.Manifold.DeRham.Basic

/-!
# Nondegenerate and symplectic two-forms on open subsets and open covers

Tau Ceti's `TauCeti/Geometry/Symplectic/Manifold/Opens.lean` restricts a nondegenerate or
symplectic two-form to one open subset. Nondegeneracy is a pointwise condition, and the
restriction to an open subset does not change the form at a point, so the restriction of a
two-form to an open set `U` is nondegenerate exactly when the form is nondegenerate at each point
of `U`, and is then symplectic if the form is closed. For an open cover `U : ι → Opens M`, this
gives the converse of the restriction: a two-form is nondegenerate when each of its restrictions
to the `U i` is. With the test of closedness on an open cover from
`DifferentialForm/Components.lean`, the same holds for symplectic forms.

## Main results

* `TauCeti.SmoothTwoForm.isNondegenerate_mpullback_subtype_val_iff`: the restriction of a
  two-form to an open set is nondegenerate exactly when the form is nondegenerate at each point of
  the set.
* `TauCeti.SmoothForm.IsClosed.isSymplectic_mpullback_subtype_val`: a closed two-form that is
  nondegenerate at each point of an open set restricts to a symplectic form on it.
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

/-- The restriction of a two-form `σ` to an open set `U` is nondegenerate if and only if `σ` is
nondegenerate at every point of `U`. -/
theorem isNondegenerate_mpullback_subtype_val_iff {σ : SmoothTwoForm I M} {U : Opens M} :
    IsNondegenerate (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ) ↔
      ∀ x ∈ U, (σ.bilinFormAt x).Nondegenerate :=
  ⟨fun h x hx ↦ (nondegenerate_bilinFormAt_mpullback_subtype_val_iff ⟨x, hx⟩).1
      (h.nondegenerate_bilinFormAt _),
    fun h ↦ isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot.2 fun x ↦
      ((nondegenerate_bilinFormAt_mpullback_subtype_val_iff (σ := σ) x).2
        (h x x.property)).ker_eq_bot⟩

/-- A closed two-form `σ` that is nondegenerate at every point of an open set `U` restricts to a
symplectic form on `U`. -/
theorem _root_.TauCeti.SmoothForm.IsClosed.isSymplectic_mpullback_subtype_val
    {σ : SmoothTwoForm I M} (hσ : σ.IsClosed) {U : Opens M}
    (h : ∀ x ∈ U, (σ.bilinFormAt x).Nondegenerate) :
    IsSymplectic (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal σ) :=
  ⟨hσ.mpullback _ _, isNondegenerate_mpullback_subtype_val_iff.2 h⟩

/-- A two-form is nondegenerate exactly when its restriction to each member of an open cover is
nondegenerate. -/
theorem isNondegenerate_iff_forall_mpullback_subtype_val (hcover : IsOpenCover U)
    {σ : SmoothTwoForm I M} :
    σ.IsNondegenerate ↔
      ∀ i, IsNondegenerate (SmoothForm.mpullback (Subtype.val : U i → M) contMDiff_subtypeVal σ) :=
  ⟨fun h i ↦ h.mpullback_subtype_val (U i), fun h ↦
    isNondegenerate_iff_forall_ker_bilinFormAt_eq_bot.2 fun x ↦
      let ⟨i, hx⟩ := hcover.exists_mem x
      (isNondegenerate_mpullback_subtype_val_iff.1 (h i) x hx).ker_eq_bot⟩

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
