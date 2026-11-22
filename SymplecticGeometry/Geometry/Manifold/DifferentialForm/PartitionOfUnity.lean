/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth

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

end SmoothPartitionOfUnity
