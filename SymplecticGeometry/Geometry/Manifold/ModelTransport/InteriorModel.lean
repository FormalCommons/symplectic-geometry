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
public import TauCeti.Geometry.Manifold.ModelTransport.Interior

/-!
# A manifold without boundary points, modelled on the model vector space

Let `M` be a manifold modelled on `I : ModelWithCorners 𝕜 E H`, a model which may have boundary
or corners, and suppose that `M` has no boundary points (`BoundarylessManifold I M`); for instance
`M` is the interior of a manifold with boundary, as an open subset. Then `M` is also a manifold
modelled on `E` itself, with the extended charts of `M` as its charts. This file names that
manifold and its diffeomorphism with `M`, so that results about boundaryless manifolds over a
vector space apply to `M`.

The construction is Tau Ceti's `TauCeti.BoundarylessModel I M` with its atlas
`TauCeti.BoundarylessModel.interiorChartedSpace`, which Tau Ceti does not make an instance. The
type synonym `SymplecticGeometry.InteriorModel I M` carries that atlas as an instance.

Tau Ceti also makes the interior `I.interior M`, as a subtype of `M`, a charted space over `E`
when `E` is finite-dimensional, and a `C^n` manifold over `𝓘(𝕜, E)` when `M` is a `C^n` manifold
(`ModelWithCorners.instChartedSpaceInterior`, `ModelWithCorners.instIsManifoldInterior`), with
charts the extended charts of `M` restricted to the interior. This is the model used for the
interior of a manifold with boundary. The open subset `I.interiorOpens M` and the charted
interior `I.interior M` have the same points, and `ModelWithCorners.interiorOpensDiffeomorph`
is a `C^n` diffeomorphism between them, at every `n`, once `M` is `C¹`. Into `I.interior M`,
the identity is smooth by `ContMDiff.codRestrict_interior`: a `C^n` map into `M` with values in
the interior is `C^n` into `I.interior M`, since read in the chart of the interior it is the map
followed by an extended chart of `M`. Into `I.interiorOpens M`, it is smooth by Tau Ceti's
`TauCeti.ContMDiff.subtypeVal_comp_iff` and `ModelWithCorners.contMDiff_subtypeVal_interior`.
Orientations of `I.interiorOpens M` are carried across it by `TauCeti.Manifold.Orientation.map`.

## Main definitions

* `SymplecticGeometry.InteriorModel I M`: the space `M`, with charts in `E`.
* `SymplecticGeometry.interiorModelHomeomorph I M`: the identity of `M`, as a homeomorphism onto
  `InteriorModel I M`.
* `SymplecticGeometry.interiorModelDiffeomorph I M n`: the identity of `M`, as a `C^n`
  diffeomorphism from the model `I` to the model `𝓘(𝕜, E)`, at every regularity `n`.
* `SymplecticGeometry.InteriorModel.val`: for an open subset `U` of `M`, the point of `M`
  underlying a point of `InteriorModel I U`.
* `ModelWithCorners.interiorOpensDiffeomorph I M n`: for `E` finite-dimensional, the identity of
  the interior of a `C¹` manifold `M`, as a `C^n` diffeomorphism, at every regularity `n`, from
  the open subset `I.interiorOpens M` to Tau Ceti's charted interior `I.interior M`.
* `TauCeti.Manifold.Orientation.toInterior`: an orientation of `I.interiorOpens M`, carried to
  `I.interior M`. For the interior of a manifold `S` with boundary oriented by `o`, the
  orientation of `I.interior S` is `(o.restrict (I.interiorOpens S)).toInterior`.

## Main results

* The instances `TopologicalSpace`, `T2Space`, `SecondCountableTopology`, `PreconnectedSpace`,
  `ConnectedSpace`, `ChartedSpace E` and `IsManifold 𝓘(𝕜, E) n` on `InteriorModel I M`.
* `SymplecticGeometry.coe_interiorModelHomeomorph`,
  `SymplecticGeometry.coe_interiorModelHomeomorph_symm`: the homeomorphism and its inverse are
  the identity of the common carrier.
* `SymplecticGeometry.coe_interiorModelDiffeomorph`,
  `SymplecticGeometry.coe_interiorModelDiffeomorph_symm`: the diffeomorphism and its inverse
  are the homeomorphism and its inverse, at every regularity.
* `SymplecticGeometry.InteriorModel.isOpenEmbedding_val`,
  `SymplecticGeometry.InteriorModel.isLocalDiffeomorph_val`: the map `InteriorModel I U → M` is an
  open embedding and a local diffeomorphism.
* `ContMDiff.codRestrict_interior`: a `C^n` map with values in the interior of `M` is `C^n`
  into Tau Ceti's charted interior `I.interior M`.
* `ModelWithCorners.coe_interiorOpensDiffeomorph_apply`,
  `ModelWithCorners.coe_interiorOpensDiffeomorph_symm_apply`: the diffeomorphism
  `I.interiorOpens M ≃ I.interior M` and its inverse fix the underlying points of `M`.
* `ModelWithCorners.isLocalDiffeomorph_subtypeVal_interior`: the inclusion `I.interior M → M` is
  a `C^n` local diffeomorphism.
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

open TauCeti TopologicalSpace Topology
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (M : Type*) [TopologicalSpace M]

/-- A space `M` charted on the model `I`, to be modelled on the model vector space `E` of `I`: a
copy of `M`, with the same points and topology. When `M` is a manifold without boundary points,
its charts are the extended charts of `M`. -/
@[expose] def InteriorModel : Type _ := BoundarylessModel I M

instance : TopologicalSpace (InteriorModel I M) :=
  inferInstanceAs (TopologicalSpace (BoundarylessModel I M))

instance [T2Space M] : T2Space (InteriorModel I M) :=
  inferInstanceAs (T2Space (BoundarylessModel I M))

instance [SecondCountableTopology M] : SecondCountableTopology (InteriorModel I M) :=
  inferInstanceAs (SecondCountableTopology M)

instance [PreconnectedSpace M] : PreconnectedSpace (InteriorModel I M) :=
  inferInstanceAs (PreconnectedSpace (BoundarylessModel I M))

instance [ConnectedSpace M] : ConnectedSpace (InteriorModel I M) :=
  inferInstanceAs (ConnectedSpace (BoundarylessModel I M))

/-- The identity of `M`, as a homeomorphism onto its copy `InteriorModel I M`. -/
def interiorModelHomeomorph : M ≃ₜ InteriorModel I M :=
  BoundarylessModel.homeomorph I M

/-- The homeomorphism sends each point of `M` to the same point of the copy. -/
theorem coe_interiorModelHomeomorph : ⇑(interiorModelHomeomorph I M) = id :=
  BoundarylessModel.coe_homeomorph I M

/-- The inverse homeomorphism sends each point of the copy to the same point of `M`. -/
theorem coe_interiorModelHomeomorph_symm : ⇑(interiorModelHomeomorph I M).symm = id :=
  BoundarylessModel.coe_homeomorph_symm I M

section Boundaryless

variable [ChartedSpace H M] [IsManifold I 1 M] [BoundarylessManifold I M]

/-- The charts of `InteriorModel I M` are the extended charts of `M`, with values in `E`. -/
instance : ChartedSpace E (InteriorModel I M) :=
  BoundarylessModel.interiorChartedSpace I (M := M)

instance {n : ℕ∞ω} [IsManifold I n M] : IsManifold 𝓘(𝕜, E) n (InteriorModel I M) :=
  BoundarylessModel.instIsManifoldInteriorChartedSpace I (M := M)

/-- The identity of `M`, as a `C^n` diffeomorphism from `M`, modelled on `I`, to
`InteriorModel I M`, modelled on `E`; this holds at every regularity `n`. -/
def interiorModelDiffeomorph (n : ℕ∞ω) : M ≃ₘ^n⟮I, 𝓘(𝕜, E)⟯ InteriorModel I M :=
  BoundarylessModel.interiorDiffeomorph I (M := M) n

@[simp]
theorem coe_interiorModelDiffeomorph (n : ℕ∞ω) :
    ⇑(interiorModelDiffeomorph I M n) = interiorModelHomeomorph I M :=
  BoundarylessModel.coe_interiorDiffeomorph I n

@[simp]
theorem coe_interiorModelDiffeomorph_symm (n : ℕ∞ω) :
    ⇑(interiorModelDiffeomorph I M n).symm = (interiorModelHomeomorph I M).symm :=
  BoundarylessModel.coe_interiorDiffeomorph_symm I n

end Boundaryless

namespace InteriorModel

section Opens

variable {I M} {U : Opens M}

/-- For an open subset `U` of `M`, the point of `M` underlying a point of the copy
`InteriorModel I U` of `U`. -/
def val (q : InteriorModel I U) : M := ((interiorModelHomeomorph I U).symm q : M)

theorem val_def (q : InteriorModel I U) : q.val = ((interiorModelHomeomorph I U).symm q : M) :=
  (rfl)

@[simp]
theorem val_interiorModelHomeomorph (p : U) : (interiorModelHomeomorph I U p).val = p := by
  rw [val_def, Homeomorph.symm_apply_apply]

theorem val_mem (q : InteriorModel I U) : q.val ∈ U :=
  ((interiorModelHomeomorph I U).symm q).property

theorem isOpenEmbedding_val : IsOpenEmbedding (val (I := I) (U := U)) :=
  U.isOpen.isOpenEmbedding_subtypeVal.comp (interiorModelHomeomorph I U).symm.isOpenEmbedding

theorem continuous_val : Continuous (val (I := I) (U := U)) :=
  isOpenEmbedding_val.continuous

theorem val_injective : Function.Injective (val (I := I) (U := U)) :=
  isOpenEmbedding_val.injective

@[simp]
theorem range_val : Set.range (val (I := I) (U := U)) = U := by
  have : (val (I := I) (U := U)) = Subtype.val ∘ (interiorModelHomeomorph I U).symm := (rfl)
  rw [this, Set.range_comp, (interiorModelHomeomorph I U).symm.range_coe, Set.image_univ,
    Subtype.range_coe]

variable [ChartedSpace H M] {n : ℕ∞ω} [IsManifold I 1 M]
  [BoundarylessManifold I U]

/-- The diffeomorphism sends each point of `U` to the copy of the same point. -/
theorem val_interiorModelDiffeomorph (p : U) : (interiorModelDiffeomorph I U n p).val = p := by
  rw [coe_interiorModelDiffeomorph, val_interiorModelHomeomorph]

/-- The map from `InteriorModel I U`, modelled on `E`, to `M`, modelled on `I`, is a `C^n` local
diffeomorphism. -/
theorem isLocalDiffeomorph_val : IsLocalDiffeomorph 𝓘(𝕜, E) I n (val (I := I) (U := U)) := by
  intro q
  have h := ((interiorModelDiffeomorph I U n).symm.isLocalDiffeomorph q).comp
    (hg := isLocalDiffeomorph_subtype_val _)
  rwa [coe_interiorModelDiffeomorph_symm] at h

end Opens

end InteriorModel

end SymplecticGeometry

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
  have h := ((interiorOpensDiffeomorph I M n).symm.isLocalDiffeomorph x).comp
    (hg := isLocalDiffeomorph_subtype_val _)
  convert h using 1
  ext y
  simp only [Function.comp_apply, coe_interiorOpensDiffeomorph_symm_apply]

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
