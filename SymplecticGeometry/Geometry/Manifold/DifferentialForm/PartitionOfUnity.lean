/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.PartitionOfUnity.Basic

/-!
# Gluing differential forms with a smooth partition of unity

Let `ρ` be a smooth partition of unity on a manifold `N`, subordinate to an open cover `U`, and
let `p : M → N` be a `C^n` map. If each form `φ i` on `M` is `C^n` over `p ⁻¹' U i`, then the
locally finite sum `∑ᶠ i, (ρ i ∘ p) • φ i` is a `C^n` form on `M`. With `p` the identity this
is the usual gluing of local forms; with `p` the projection of a bundle it glues forms defined
over the preimages of open sets of the base.

## Main results

* `SmoothPartitionOfUnity.IsSubordinate.isSmoothForm_finsum_smul_comp`: the glued form is
  `C^n`. It is `SmoothPartitionOfUnity.IsSubordinate.contMDiff_finsum_smul_comp_section` for
  the bundle of alternating forms.
* `SmoothPartitionOfUnity.finsum_smul_comp_apply`: on tangent vectors at `x`, the glued form is
  the finite sum over `ρ.finsupport (p x)`, by Mathlib's
  `SmoothPartitionOfUnity.sum_finsupport_smul_eq_finsum`.
* `SmoothPartitionOfUnity.finsum_smul_comp_apply_eq_of_forall_eq`: if every form whose bump does
  not vanish at `p x` takes the value `c` on `v`, so does the glued form, by Tau Ceti's
  `SmoothPartitionOfUnity.sum_finsupport_smul_eq_of_forall_eq`. This is how affine conditions,
  such as those on a connection form, pass to the glued form.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace SmoothPartitionOfUnity

variable {E H M EN HN N F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {n : ℕ∞}

/-- **Gluing forms with a partition of unity.** Let `ρ` be a smooth partition of unity on `N`
subordinate to a family `U` of open sets, and `p : M → N` a `C^n` map. If each form `φ i` on
`M` is `C^n` on `p ⁻¹' U i`, then `x ↦ ∑ᶠ i, ρ i (p x) • φ i x` is a `C^n` form on `M`. -/
theorem IsSubordinate.isSmoothForm_finsum_smul_comp {s : Set N}
    {ρ : SmoothPartitionOfUnity ι J N s} {U : ι → Set N} (hρ : ρ.IsSubordinate U)
    (hU : ∀ i, IsOpen (U i)) {p : M → N} (hp : ContMDiff I J n p)
    {φ : ι → TauCeti.RoughForm I M F k}
    (hφ : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ i x)) (p ⁻¹' U i)) :
    TauCeti.IsSmoothForm I n (fun x ↦ ∑ᶠ i, ρ i (p x) • φ i x) :=
  (TauCeti.isSmoothForm_def _ _).2 (hρ.contMDiff_finsum_smul_comp_section hU hp hφ)

omit [IsManifold I 1 M] in
/-- **A glued form, evaluated at a point.** At `x`, the form `∑ᶠ i, ρ i (p x) • φ i x` takes on
`v` the value `∑ i ∈ ρ.finsupport (p x), ρ i (p x) • φ i x v`, a finite sum over the indices whose
bump does not vanish at `p x`. -/
theorem finsum_smul_comp_apply {s : Set N} (ρ : SmoothPartitionOfUnity ι J N s) (p : M → N)
    (φ : ι → TauCeti.RoughForm I M F k) (x : M) (v : Fin k → TangentSpace I x) :
    (∑ᶠ i, ρ i (p x) • φ i x) v = ∑ i ∈ ρ.finsupport (p x), ρ i (p x) • φ i x v := by
  rw [← ρ.sum_finsupport_smul_eq_finsum (p x) fun i _ ↦ φ i x,
    ContinuousAlternatingMap.sum_apply]
  simp only [ContinuousAlternatingMap.smul_apply]

omit [IsManifold I 1 M] in
/-- **Gluing preserves a common value.** If, at `x` with `p x ∈ s`, each form `φ i` whose bump
`ρ i` does not vanish at `p x` takes the value `c` on `v`, then so does the glued form
`∑ᶠ i, ρ i (p x) • φ i x`. -/
theorem finsum_smul_comp_apply_eq_of_forall_eq {s : Set N} {ρ : SmoothPartitionOfUnity ι J N s}
    {p : M → N} {x : M} (hx : p x ∈ s) {φ : ι → TauCeti.RoughForm I M F k}
    {v : Fin k → TangentSpace I x} {c : F} (hφ : ∀ i ∈ ρ.finsupport (p x), φ i x v = c) :
    (∑ᶠ i, ρ i (p x) • φ i x) v = c := by
  rw [finsum_smul_comp_apply]
  exact ρ.sum_finsupport_smul_eq_of_forall_eq hx hφ

end SmoothPartitionOfUnity
