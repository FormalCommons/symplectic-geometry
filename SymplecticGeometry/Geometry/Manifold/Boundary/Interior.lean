/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.IsManifold.InteriorBoundary
public import SymplecticGeometry.Geometry.Manifold.Orientation.Diffeomorph
public import TauCeti.Geometry.Manifold.Boundary.Interior
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Maps into the charted interior, and its identification with the open interior

Let `M` be a manifold modelled on `I : ModelWithCorners 𝕜 E H`, a model which may have boundary
or corners, with `E` finite-dimensional. Tau Ceti makes the interior `I.interior M`, as a
subtype of `M`, a charted space over `E`, and a `C^n` manifold over `𝓘(𝕜, E)` when `M` is a
`C^n` manifold (`ModelWithCorners.instChartedSpaceInterior`,
`ModelWithCorners.instIsManifoldInterior`); its charts are the extended charts of `M` restricted
to the interior. This is the model the library uses for the interior of a manifold with boundary.

This file gives the maps into and out of that charted interior. A `C^n` map into `M` with values
in the interior is `C^n` into `I.interior M` (`ContMDiff.codRestrict_interior`), since read in
the chart of the interior it is the map followed by an extended chart of `M`. The open subset
`I.interiorOpens M` and the charted interior `I.interior M` have the same points, and the
identity between them is a `C^n` diffeomorphism at every `n` once `M` is `C¹`
(`ModelWithCorners.interiorOpensDiffeomorph`): into `I.interior M` by the previous result, and
into `I.interiorOpens M` by Tau Ceti's `TauCeti.ContMDiff.subtypeVal_comp_iff` and
`ModelWithCorners.contMDiff_subtypeVal_interior`. Orientations of `I.interiorOpens M` are carried
across it by `TauCeti.Manifold.Orientation.map`.

## Main definitions

* `ModelWithCorners.interiorOpensDiffeomorph I M n`: for `E` finite-dimensional, the identity of
  the interior of a `C¹` manifold `M`, as a `C^n` diffeomorphism, at every regularity `n`, from
  the open subset `I.interiorOpens M` to Tau Ceti's charted interior `I.interior M`.
* `TauCeti.Manifold.Orientation.toInterior`: an orientation of `I.interiorOpens M`, carried to
  `I.interior M`. For the interior of a manifold `S` with boundary oriented by `o`, the
  orientation of `I.interior S` is `(o.restrict (I.interiorOpens S)).toInterior`.

## Main results

* `ContMDiff.codRestrict_interior`: a `C^n` map with values in the interior of `M` is `C^n`
  into Tau Ceti's charted interior `I.interior M`.
* `ModelWithCorners.coe_interiorOpensDiffeomorph_apply`,
  `ModelWithCorners.coe_interiorOpensDiffeomorph_symm_apply`: the diffeomorphism
  `I.interiorOpens M ≃ I.interior M` and its inverse fix the underlying points of `M`.
* `ModelWithCorners.isLocalDiffeomorph_subtypeVal_interior`: the inclusion `I.interior M → M` is
  a `C^n` local diffeomorphism.
* `ModelWithCorners.hasMFDerivAt_subtypeVal_interior`,
  `ModelWithCorners.mfderiv_subtypeVal_interior`: its differential at each point is the identity
  of `E`. The proof of `hasMFDerivAt_subtypeVal_interior` adapts that of Tau Ceti's
  `ModelWithCorners.contMDiff_subtypeVal_interior`, with a derivative in place of smoothness.
* `ModelWithCorners.mfderiv_comp_subtypeVal_interior`: so precomposing a map on `M` with the
  inclusion does not change its differential at a point of the interior.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_interiorOpensDiffeomorph`,
  `TauCeti.Manifold.Orientation.isOrientationPreservingAt_interiorOpensDiffeomorph_symm`: the
  diffeomorphism `I.interiorOpens M ≃ I.interior M` and its inverse preserve orientation;
  `TauCeti.Manifold.Orientation.eq_toInterior_iff`: the carried orientation is the only one for
  which the inverse does. `TauCeti.Manifold.Orientation.toInterior_neg`: carrying commutes with
  reversing the orientation.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 1, Proposition 1.17, and Chapter 15 (pulling back orientations along local
  diffeomorphisms).
-/

public section

noncomputable section

open TauCeti
open scoped Manifold ContDiff

namespace ModelWithCorners

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

omit [IsManifold I 1 M] in
/-- A `C^n` map `f : N → M`, with values in the interior of `M`, is `C^n` as a map into Tau
Ceti's charted interior `I.interior M`, modelled on `E`. No smoothness of `M` is needed. -/
theorem _root_.ContMDiff.codRestrict_interior {n : ℕ∞ω} {f : N → M}
    (hf : ContMDiff J I n f) (h : ∀ x, f x ∈ I.interior M) :
    ContMDiff J 𝓘(𝕜, E) n (Set.codRestrict f (I.interior M) h) := by
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨(hf.continuous.codRestrict h).continuousAt, ?_⟩
  -- Read in the chart of the interior at `f x`, the map is the extended chart of `M` at `f x`
  -- composed with `f`.
  have he : extChartAt 𝓘(𝕜, E) (Set.codRestrict f (I.interior M) h x) ∘
      Set.codRestrict f (I.interior M) h = extChartAt I (f x) ∘ f := by
    ext y
    simp only [Function.comp_apply, extChartAt_coe, modelWithCornersSelf_coe, id_eq,
      chartAt_interior_apply, Set.val_codRestrict_apply]
  rw [he]
  exact (contMDiffAt_iff_target.1 (hf x)).2

variable (I M) in
/-- For a `C¹` manifold `M` over a finite-dimensional space `E`, the identity of the interior
of `M`, as a `C^n` diffeomorphism from the open subset `I.interiorOpens M`, modelled on `I`, to
Tau Ceti's charted interior `I.interior M`, modelled on `E`, at every regularity `n`. -/
def interiorOpensDiffeomorph (n : ℕ∞ω) :
    I.interiorOpens M ≃ₘ^n⟮I, 𝓘(𝕜, E)⟯ I.interior M where
  toEquiv := Equiv.subtypeEquivRight fun _ ↦ I.mem_interiorOpens_iff_mem_interior
  contMDiff_toFun := contMDiff_subtypeVal.codRestrict_interior _
  contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff (I.interiorOpens M) _).1
    (contMDiff_subtypeVal_interior I)

variable {n : ℕ∞ω}

theorem coe_interiorOpensDiffeomorph :
    ⇑(interiorOpensDiffeomorph I M n) =
      fun x ↦ ⟨x, I.mem_interiorOpens_iff_mem_interior.1 x.property⟩ :=
  (rfl)

theorem coe_interiorOpensDiffeomorph_symm :
    ⇑(interiorOpensDiffeomorph I M n).symm =
      fun x ↦ ⟨x, I.mem_interiorOpens_iff_mem_interior.2 x.property⟩ :=
  (rfl)

/-- The diffeomorphism sends each interior point to the same point of `M`. -/
@[simp]
theorem coe_interiorOpensDiffeomorph_apply (x : I.interiorOpens M) :
    (interiorOpensDiffeomorph I M n x : M) = x := by
  rw [coe_interiorOpensDiffeomorph]

/-- The inverse diffeomorphism sends each interior point to the same point of `M`. -/
@[simp]
theorem coe_interiorOpensDiffeomorph_symm_apply (x : I.interior M) :
    ((interiorOpensDiffeomorph I M n).symm x : M) = x := by
  rw [coe_interiorOpensDiffeomorph_symm]

/-- For a `C¹` manifold `M` over a finite-dimensional space `E`, the inclusion of Tau Ceti's
charted interior `I.interior M`, modelled on `E`, into `M` is a `C^n` local diffeomorphism, at
every regularity `n`. -/
theorem isLocalDiffeomorph_subtypeVal_interior :
    IsLocalDiffeomorph 𝓘(𝕜, E) I n (Subtype.val : I.interior M → M) := by
  intro x
  have h := (interiorOpensDiffeomorph I M n).symm.isLocalDiffeomorph_subtypeVal_comp x
  convert h using 1
  ext y
  simp only [coe_interiorOpensDiffeomorph_symm_apply]

omit [IsManifold I 1 M] in
/-- The inclusion of Tau Ceti's charted interior `I.interior M` into `M` has derivative the
identity of `E` at every point: read in the chart of the interior at `x` and the extended chart of
`M` at `x`, it is the identity near the image of `x`. -/
theorem hasMFDerivAt_subtypeVal_interior (x : I.interior M) :
    HasMFDerivAt 𝓘(𝕜, E) I (Subtype.val : I.interior M → M) x
      (ContinuousLinearMap.id 𝕜 (TangentSpace 𝓘(𝕜, E) x)) := by
  refine ⟨continuous_subtypeVal.continuousAt, ?_⟩
  rw [modelWithCornersSelf_coe, Set.range_id, hasFDerivWithinAt_univ]
  refine (hasFDerivAt_id _).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x).open_target.mem_nhds
    ((chartAt E x).map_source (mem_chart_source E x))] with v hv
  have hv' := hv
  rw [chartAt_interior_target] at hv'
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_apply,
    CompTriple.comp_eq, id_eq]
  rw [coe_chartAt_interior_symm_apply I x hv, (chartAt H (x : M)).right_inv hv'.1,
    I.right_inv (interior_subset hv'.2)]

omit [IsManifold I 1 M] in
/-- The differential of the inclusion of Tau Ceti's charted interior `I.interior M` into `M` is
the identity of `E` at every point. -/
theorem mfderiv_subtypeVal_interior (x : I.interior M) :
    mfderiv 𝓘(𝕜, E) I (Subtype.val : I.interior M → M) x =
      ContinuousLinearMap.id 𝕜 (TangentSpace 𝓘(𝕜, E) x) :=
  (hasMFDerivAt_subtypeVal_interior x).mfderiv

omit [IsManifold I 1 M] in
/-- Precomposing a map `g : M → N`, differentiable at an interior point `x`, with the inclusion of
Tau Ceti's charted interior `I.interior M` does not change its differential at `x`. -/
theorem mfderiv_comp_subtypeVal_interior {g : M → N} (x : I.interior M)
    (hg : MDifferentiableAt I J g x) :
    mfderiv 𝓘(𝕜, E) J (g ∘ Subtype.val) x = mfderiv I J g x := by
  rw [mfderiv_comp x hg (hasMFDerivAt_subtypeVal_interior x).mdifferentiableAt,
    mfderiv_subtypeVal_interior]
  -- The identity is that of `TangentSpace 𝓘(𝕜, E) x`, and the differential of `g` starts at
  -- `TangentSpace I x`: both are `E`, but `rw [comp_id]` does not see it.
  exact ContinuousLinearMap.comp_id _

end ModelWithCorners

namespace TauCeti.Manifold.Orientation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] {ι : Type*} [Fintype ι]

/-- An orientation `o` of the interior of `M`, as the open subset `I.interiorOpens M`, carried to
Tau Ceti's charted interior `I.interior M`: the orientation for which the identification
`ModelWithCorners.interiorOpensDiffeomorph I M n` preserves orientation
(`isOrientationPreservingAt_interiorOpensDiffeomorph`). -/
def toInterior (o : Orientation I (I.interiorOpens M) ι) : Orientation 𝓘(ℝ, E) (I.interior M) ι :=
  o.map (I.interiorOpensDiffeomorph M 1) one_ne_zero o.card_eq

theorem toInterior_def (o : Orientation I (I.interiorOpens M) ι) :
    o.toInterior = o.map (I.interiorOpensDiffeomorph M 1) one_ne_zero o.card_eq :=
  (rfl)

/-- The inverse `I.interior M → I.interiorOpens M` of the identification preserves orientation,
from the carried orientation to `o`, at every regularity `n`. -/
theorem isOrientationPreservingAt_interiorOpensDiffeomorph_symm
    (o : Orientation I (I.interiorOpens M) ι) (n : ℕ∞ω)
    (x : I.interior M) :
    IsOrientationPreservingAt o.toInterior o (I.interiorOpensDiffeomorph M n).symm x := by
  rw [ModelWithCorners.coe_interiorOpensDiffeomorph_symm,
    ← ModelWithCorners.coe_interiorOpensDiffeomorph_symm (n := 1), toInterior_def]
  exact isOrientationPreservingAt_map_symm _ _ _ _ x

/-- The identification `I.interiorOpens M → I.interior M` preserves orientation, from `o` to the
carried orientation, at every regularity `n`. -/
theorem isOrientationPreservingAt_interiorOpensDiffeomorph
    (o : Orientation I (I.interiorOpens M) ι) (n : ℕ∞ω)
    (p : I.interiorOpens M) :
    IsOrientationPreservingAt o o.toInterior (I.interiorOpensDiffeomorph M n) p := by
  rw [ModelWithCorners.coe_interiorOpensDiffeomorph,
    ← ModelWithCorners.coe_interiorOpensDiffeomorph (n := 1)]
  exact isOrientationPreservingAt_map _ _ _ _ p

/-- The carried orientation is the only orientation of `I.interior M` from which the inverse of
the identification, at any regularity `n`, preserves orientation at every point. -/
theorem eq_toInterior_iff {o : Orientation I (I.interiorOpens M) ι}
    {o' : Orientation 𝓘(ℝ, E) (I.interior M) ι} (n : ℕ∞ω) :
    o' = o.toInterior ↔
      ∀ x, IsOrientationPreservingAt o' o (I.interiorOpensDiffeomorph M n).symm x := by
  rw [toInterior_def, eq_map_iff, ModelWithCorners.coe_interiorOpensDiffeomorph_symm,
    ModelWithCorners.coe_interiorOpensDiffeomorph_symm]

/-- Carrying the opposite orientation gives the opposite of the carried orientation. -/
@[simp]
theorem toInterior_neg (o : Orientation I (I.interiorOpens M) ι) :
    (-o).toInterior = -o.toInterior := by
  simp only [toInterior_def, map_neg]

end TauCeti.Manifold.Orientation

end
