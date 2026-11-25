/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import SymplecticGeometry.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.Boundary.Interior
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.Orientation.Pullback
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
charts the extended charts of `M` restricted to the interior. The copy
`InteriorModel I (I.interiorOpens M)` here is instead a type synonym of the open subset
`I.interiorOpens M`, needs no finite dimension, and comes with the diffeomorphism
`interiorModelDiffeomorph` and the local diffeomorphism `InteriorModel.isLocalDiffeomorph_val`
into `M`; its range is described through Tau Ceti's `ModelWithCorners.range_subtypeVal_interior`.

## Main definitions

* `SymplecticGeometry.InteriorModel I M`: the space `M`, with charts in `E`.
* `SymplecticGeometry.interiorModelHomeomorph I M`: the identity of `M`, as a homeomorphism onto
  `InteriorModel I M`.
* `SymplecticGeometry.interiorModelDiffeomorph I M n`: the identity of `M`, as a `C^n`
  diffeomorphism from the model `I` to the model `𝓘(𝕜, E)`, at every regularity `n`.
* `SymplecticGeometry.InteriorModel.val`: for an open subset `U` of `M`, the point of `M`
  underlying a point of `InteriorModel I U`.
* `SymplecticGeometry.InteriorModel.mk I p hp`: the point of `InteriorModel I (I.interiorOpens M)`
  at an interior point `p` of `M`.
* `SymplecticGeometry.InteriorPiece n W`: for a manifold `W` with boundary modelled on the
  half-space `EuclideanHalfSpace (n + 1)`, its interior re-modelled on `ℝⁿ⁺¹`, with the
  identification `SymplecticGeometry.interiorPieceDiffeomorph` of the interior of `W` with it.
* `TauCeti.Manifold.Orientation.toInteriorModel`: an orientation of `M`, carried to
  `InteriorModel I M`, for `M` without boundary points. For the interior of a manifold `S` with
  boundary oriented by `o`, the orientation of its copy is
  `(o.restrict (I.interiorOpens S)).toInteriorModel`.

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
  open embedding and a local diffeomorphism; `InteriorModel.val_mem_interior`: for the interior
  of `M`, it takes values in the interior, and `InteriorModel.range_val_interiorOpens`: its range
  is the complement of the boundary (`InteriorModel.compl_range_val_interiorOpens`: the
  complement of its range is the boundary).
* `SymplecticGeometry.InteriorModel.continuous_mk`: a continuous map with values in the interior
  of `M` is continuous into the copy of the interior.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_interiorModelDiffeomorph`,
  `TauCeti.Manifold.Orientation.isOrientationPreservingAt_interiorModelDiffeomorph_symm`: the
  diffeomorphism `M ≃ InteriorModel I M` and its inverse preserve orientation;
  `TauCeti.Manifold.Orientation.eq_toInteriorModel_iff`: the carried orientation is the only one
  for which the inverse does. `TauCeti.Manifold.Orientation.toInteriorModel_neg`: carrying
  commutes with reversing the orientation.

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

section Interior

variable {I M} [ChartedSpace H M] [IsManifold I 1 M]

/-- A point of the copy of the interior of `M` lies in the interior of `M`. -/
theorem val_mem_interior (q : InteriorModel I (I.interiorOpens M)) : q.val ∈ I.interior M :=
  I.mem_interiorOpens.1 q.val_mem

/-- A point of the copy of the interior of `M` is not a boundary point of `M`. -/
theorem val_notMem_boundary (q : InteriorModel I (I.interiorOpens M)) : q.val ∉ I.boundary M :=
  Set.disjoint_left.1 I.disjoint_interior_boundary q.val_mem_interior

/-- The copy of the interior of `M` sits in `M` as the complement of the boundary. -/
theorem range_val_interiorOpens :
    Set.range (val (I := I) (U := I.interiorOpens M)) =
      (Set.range ((↑) : I.boundary M → M))ᶜ := by
  rw [range_val, I.coe_interiorOpens, ← I.range_subtypeVal_interior, Subtype.range_coe]

/-- The complement in `M` of the copy of the interior of `M` is the boundary. -/
theorem compl_range_val_interiorOpens :
    (Set.range (val (I := I) (U := I.interiorOpens M)))ᶜ = I.boundary M := by
  rw [range_val, I.coe_interiorOpens, I.compl_interior]

variable (I) in
/-- The point of the copy `InteriorModel I (I.interiorOpens M)` of the interior of `M` at an
interior point `p` of `M`. -/
def mk (p : M) (hp : p ∈ I.interior M) : InteriorModel I (I.interiorOpens M) :=
  interiorModelHomeomorph I (I.interiorOpens M) ⟨p, I.mem_interiorOpens.2 hp⟩

theorem mk_def (p : M) (hp : p ∈ I.interior M) :
    mk I p hp =
      interiorModelHomeomorph I (I.interiorOpens M) ⟨p, I.mem_interiorOpens.2 hp⟩ :=
  (rfl)

@[simp]
theorem val_mk (p : M) (hp : p ∈ I.interior M) : (mk I p hp).val = p := by
  rw [mk_def, val_interiorModelHomeomorph]

@[simp]
theorem mk_val (q : InteriorModel I (I.interiorOpens M)) : mk I q.val q.val_mem_interior = q :=
  val_injective (val_mk _ _)

/-- A continuous map with values in the interior of `M` is continuous as a map into the copy
`InteriorModel I (I.interiorOpens M)` of the interior; this is the analogue of
`Continuous.subtype_mk`. -/
theorem continuous_mk {X : Type*} [TopologicalSpace X] {f : X → M} (hf : Continuous f)
    (hint : ∀ x, f x ∈ I.interior M) : Continuous fun x ↦ mk I (f x) (hint x) :=
  isOpenEmbedding_val.isInducing.continuous_iff.2 (by simpa only [Function.comp_def, val_mk])

end Interior

end InteriorModel

section HalfSpace

variable (n : ℕ) (W : Type*) [TopologicalSpace W]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) W] [IsManifold (𝓡∂ (n + 1)) 1 W]

/-- The interior of a manifold `W` with boundary, modelled on `EuclideanHalfSpace (n + 1)`, as a
manifold without boundary over `ℝⁿ⁺¹`. -/
abbrev InteriorPiece : Type _ :=
  InteriorModel (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W)

variable {n W} in
/-- The identity of the interior of `W`, as a smooth diffeomorphism from the open subset
`(𝓡∂ (n + 1)).interiorOpens W` of `W` to its copy `InteriorPiece n W` over `ℝⁿ⁺¹`. -/
abbrev interiorPieceDiffeomorph :
    (𝓡∂ (n + 1)).interiorOpens W ≃ₘ^∞⟮𝓡∂ (n + 1), 𝓡 (n + 1)⟯ InteriorPiece n W :=
  interiorModelDiffeomorph (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W) ∞

end HalfSpace

end SymplecticGeometry

namespace TauCeti.Manifold.Orientation

open SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] [BoundarylessManifold I M] {ι : Type*} [Fintype ι]

/-- An orientation `o` of a manifold `M` without boundary points, carried to the copy
`InteriorModel I M` of `M` modelled on `E`: the orientation for which the identification
`interiorModelDiffeomorph I M n` of `M` with its copy preserves orientation
(`isOrientationPreservingAt_interiorModelDiffeomorph`). -/
def toInteriorModel (o : Orientation I M ι) : Orientation 𝓘(ℝ, E) (InteriorModel I M) ι :=
  o.pullback (interiorModelDiffeomorph I M 1).symm.contMDiff
    (fun x ↦ ((interiorModelDiffeomorph I M 1).symm.isLocalDiffeomorph x).isInvertible_mfderiv
      one_ne_zero)
    o.card_eq

theorem toInteriorModel_def (o : Orientation I M ι) :
    o.toInteriorModel = o.pullback (interiorModelDiffeomorph I M 1).symm.contMDiff
      (fun x ↦ ((interiorModelDiffeomorph I M 1).symm.isLocalDiffeomorph x).isInvertible_mfderiv
        one_ne_zero)
      o.card_eq :=
  (rfl)

/-- The inverse `InteriorModel I M → M` of the identification preserves orientation, from the
carried orientation to `o`, at every regularity `n`. -/
theorem isOrientationPreservingAt_interiorModelDiffeomorph_symm (o : Orientation I M ι)
    (n : ℕ∞ω) (x : InteriorModel I M) :
    IsOrientationPreservingAt o.toInteriorModel o (interiorModelDiffeomorph I M n).symm x := by
  rw [coe_interiorModelDiffeomorph_symm, ← coe_interiorModelDiffeomorph_symm I M 1,
    toInteriorModel_def]
  exact isOrientationPreservingAt_pullback _ _ _ _ x

/-- The identification `M → InteriorModel I M` preserves orientation, from `o` to the carried
orientation, at every regularity `n`. -/
theorem isOrientationPreservingAt_interiorModelDiffeomorph (o : Orientation I M ι)
    (n : ℕ∞ω) (p : M) :
    IsOrientationPreservingAt o o.toInteriorModel (interiorModelDiffeomorph I M n) p := by
  rw [coe_interiorModelDiffeomorph, ← coe_interiorModelDiffeomorph I M 1]
  exact (isOrientationPreservingAt_interiorModelDiffeomorph_symm o 1 _).diffeomorph_symm
    (e := (interiorModelDiffeomorph I M 1).symm) one_ne_zero

/-- The carried orientation is the only orientation of `InteriorModel I M` from which the inverse
of the identification, at any regularity `n`, preserves orientation at every point. -/
theorem eq_toInteriorModel_iff {o : Orientation I M ι}
    {o' : Orientation 𝓘(ℝ, E) (InteriorModel I M) ι} (n : ℕ∞ω) :
    o' = o.toInteriorModel ↔
      ∀ x, IsOrientationPreservingAt o' o (interiorModelDiffeomorph I M n).symm x := by
  rw [toInteriorModel_def, eq_pullback_iff, coe_interiorModelDiffeomorph_symm,
    coe_interiorModelDiffeomorph_symm]

/-- Carrying the opposite orientation gives the opposite of the carried orientation. -/
@[simp]
theorem toInteriorModel_neg (o : Orientation I M ι) :
    (-o).toInteriorModel = -o.toInteriorModel := by
  simp only [toInteriorModel_def, pullback_neg]

end TauCeti.Manifold.Orientation

end
