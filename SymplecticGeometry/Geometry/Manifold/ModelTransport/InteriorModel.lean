/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.IsManifold.InteriorBoundary
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
  of `M`, it takes values in the interior.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 1, Proposition 1.17.
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
  inferInstanceAs (T2Space M)

instance [SecondCountableTopology M] : SecondCountableTopology (InteriorModel I M) :=
  inferInstanceAs (SecondCountableTopology M)

instance [PreconnectedSpace M] : PreconnectedSpace (InteriorModel I M) :=
  inferInstanceAs (PreconnectedSpace M)

instance [ConnectedSpace M] : ConnectedSpace (InteriorModel I M) :=
  inferInstanceAs (ConnectedSpace M)

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

end Interior

end InteriorModel

end SymplecticGeometry

end
