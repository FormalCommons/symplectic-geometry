/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph

/-!
# A manifold re-modelled along a diffeomorphism of model spaces

Let `Φ : H ≃ₘ^n⟮I, I'⟯ H'` be a `C^n` diffeomorphism between two model spaces, and let `M` be a
space charted on `H`. Composing the charts of `M` with `Φ` charts `M` on `H'`
(Tau Ceti's `Homeomorph.chartedSpaceComp`), and a `C^n` manifold modelled on `I` becomes a
`C^n` manifold modelled on `I'` (Tau Ceti's `Diffeomorph.isManifold_chartedSpaceComp`). This
file names that manifold, as a type synonym of `M` carrying the new atlas as an instance, and the
identity of `M` as a `C^n` diffeomorphism onto it (the inverse of Tau Ceti's
`Diffeomorph.chartedSpaceCompDiffeomorph`). For instance, a product of an interval and a
manifold over `ℝⁿ`, or an open subset of `ℂ`, can so be modelled on a Euclidean space
`EuclideanSpace ℝ (Fin m)`, as a piece of a gluing over it.

## Main definitions

* `SymplecticGeometry.Remodel Φ M`: the space `M`, with charts in `H'`.
* `SymplecticGeometry.remodelHomeomorph Φ M`: the identity of `M`, as a homeomorphism onto
  `Remodel Φ M`.
* `SymplecticGeometry.remodelDiffeomorph Φ M`: the identity of `M`, as a `C^n` diffeomorphism
  from the model `I` to the model `I'`.
* `SymplecticGeometry.remodelChart Φ c`: a chart `c` of `M` followed by `Φ`, as a chart of
  `Remodel Φ M`, in its maximal atlas when `c` is in that of `M`
  (`SymplecticGeometry.remodelChart_mem_maximalAtlas`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 1 (smooth structures and the smooth manifold chart lemma).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
  (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) [TopologicalSpace M]

/-- A space `M` charted on `H`, to be charted on `H'` through a diffeomorphism of models
`Φ : H ≃ₘ^n⟮I, I'⟯ H'`: a copy of `M`, with the same points and topology, whose charts are those
of `M` followed by `Φ`. -/
@[expose, nolint unusedArguments]
def Remodel (_Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) : Type _ := M

instance : TopologicalSpace (Remodel Φ M) := inferInstanceAs (TopologicalSpace M)

instance [T2Space M] : T2Space (Remodel Φ M) := inferInstanceAs (T2Space M)

instance [CompactSpace M] : CompactSpace (Remodel Φ M) := inferInstanceAs (CompactSpace M)

instance [SecondCountableTopology M] : SecondCountableTopology (Remodel Φ M) :=
  inferInstanceAs (SecondCountableTopology M)

instance [Nonempty M] : Nonempty (Remodel Φ M) := inferInstanceAs (Nonempty M)

instance [PreconnectedSpace M] : PreconnectedSpace (Remodel Φ M) :=
  inferInstanceAs (PreconnectedSpace M)

instance [ConnectedSpace M] : ConnectedSpace (Remodel Φ M) := inferInstanceAs (ConnectedSpace M)

instance [PathConnectedSpace M] : PathConnectedSpace (Remodel Φ M) :=
  inferInstanceAs (PathConnectedSpace M)

/-- The charts of `Remodel Φ M` are the charts of `M` followed by `Φ`. -/
instance [ChartedSpace H M] : ChartedSpace H' (Remodel Φ M) :=
  Φ.toHomeomorph.chartedSpaceComp M

instance [ChartedSpace H M] [IsManifold I n M] : IsManifold I' n (Remodel Φ M) :=
  Φ.isManifold_chartedSpaceComp M

/-- The identity of `M`, as a homeomorphism onto its copy `Remodel Φ M`. -/
def remodelHomeomorph : M ≃ₜ Remodel Φ M := Homeomorph.refl M

/-- The homeomorphism sends each point of `M` to the same point of the copy. -/
theorem coe_remodelHomeomorph : ⇑(remodelHomeomorph Φ M) = id := (rfl)

/-- The inverse homeomorphism sends each point of the copy to the same point of `M`. -/
theorem coe_remodelHomeomorph_symm : ⇑(remodelHomeomorph Φ M).symm = id := (rfl)

/-- The homeomorphism sends a point `x` of `M` to `x`, as a point of the copy. -/
theorem remodelHomeomorph_apply (x : M) : remodelHomeomorph Φ M x = (x : Remodel Φ M) := (rfl)

/-- The inverse homeomorphism sends a point `x` of the copy to `x`, as a point of `M`. -/
theorem remodelHomeomorph_symm_apply (x : Remodel Φ M) :
    (remodelHomeomorph Φ M).symm x = (x : M) := (rfl)

variable {M} in
/-- A chart `c` of `M`, carried to `Remodel Φ M`: `c` followed by `Φ`. -/
def remodelChart (c : OpenPartialHomeomorph M H) : OpenPartialHomeomorph (Remodel Φ M) H' :=
  c.trans Φ.toHomeomorph.toOpenPartialHomeomorph

section RemodelChart

variable {Φ M} (c : OpenPartialHomeomorph M H)

theorem remodelChart_def :
    remodelChart Φ c =
      (c.trans Φ.toHomeomorph.toOpenPartialHomeomorph : OpenPartialHomeomorph (Remodel Φ M) H') :=
  (rfl)

@[simp]
theorem remodelChart_apply (x : Remodel Φ M) :
    remodelChart Φ c x = Φ (c ((remodelHomeomorph Φ M).symm x)) :=
  (rfl)

@[simp]
theorem remodelChart_symm_apply (y : H') :
    (remodelChart Φ c).symm y = remodelHomeomorph Φ M (c.symm (Φ.symm y)) :=
  (rfl)

@[simp]
theorem remodelChart_source :
    (remodelChart Φ c).source = (remodelHomeomorph Φ M).symm ⁻¹' c.source := by
  rw [remodelChart_def, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]
  rfl

@[simp]
theorem remodelChart_target : (remodelChart Φ c).target = Φ.symm ⁻¹' c.target := by
  rw [remodelChart_def, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter]
  rfl

end RemodelChart

variable [ChartedSpace H M]

variable {Φ M} in
/-- A chart `c` of the maximal `C^n` atlas of `M`, carried to `Remodel Φ M`, is a chart of the
maximal `C^n` atlas of `Remodel Φ M`. The proof follows that of Tau Ceti's
`Diffeomorph.isManifold_chartedSpaceComp`. -/
theorem remodelChart_mem_maximalAtlas {c : OpenPartialHomeomorph M H}
    (hc : c ∈ IsManifold.maximalAtlas I n M) :
    remodelChart Φ c ∈ IsManifold.maximalAtlas I' n (Remodel Φ M) := by
  -- The same statement on `M` itself, carrying the charts of `Remodel Φ M`, as Tau Ceti states
  -- its lemmas on `Φ.toHomeomorph.chartedSpaceComp M`.
  rw [remodelChart_def]
  let := Φ.toHomeomorph.chartedSpaceComp M
  suffices c.trans Φ.toHomeomorph.toOpenPartialHomeomorph ∈
      (contDiffGroupoid n I').maximalAtlas M from this
  rw [IsManifold.maximalAtlas, mem_maximalAtlas_iff] at hc
  rw [mem_maximalAtlas_iff, Φ.toHomeomorph.atlas_chartedSpaceComp M]
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨h₁, h₂⟩ := hc d hd
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_assoc c.symm]
    exact Φ.symm_trans_trans_mem_contDiffGroupoid h₁
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_assoc d.symm]
    exact Φ.symm_trans_trans_mem_contDiffGroupoid h₂

/-- The identity of `M`, as a `C^n` diffeomorphism from `M`, modelled on `I`, to `Remodel Φ M`,
modelled on `I'`. -/
def remodelDiffeomorph : M ≃ₘ^n⟮I, I'⟯ Remodel Φ M :=
  letI := Φ.toHomeomorph.chartedSpaceComp M
  (Φ.chartedSpaceCompDiffeomorph M).symm

theorem remodelDiffeomorph_def :
    remodelDiffeomorph Φ M =
      letI := Φ.toHomeomorph.chartedSpaceComp M
      (Φ.chartedSpaceCompDiffeomorph M).symm :=
  (rfl)

@[simp]
theorem coe_remodelDiffeomorph : ⇑(remodelDiffeomorph Φ M) = remodelHomeomorph Φ M := by
  rw [remodelDiffeomorph_def, coe_remodelHomeomorph]
  -- `exact`, not `rw`: Tau Ceti states the lemma on `M`, whose type synonym is `Remodel Φ M`.
  exact Φ.coe_chartedSpaceCompDiffeomorph_symm M

@[simp]
theorem coe_remodelDiffeomorph_symm :
    ⇑(remodelDiffeomorph Φ M).symm = (remodelHomeomorph Φ M).symm := by
  rw [remodelDiffeomorph_def, coe_remodelHomeomorph_symm]
  -- `exact`, not `rw`: Tau Ceti states the lemma on `M`, whose type synonym is `Remodel Φ M`,
  -- and the double inverse of a diffeomorphism is the diffeomorphism itself by definition.
  exact Φ.coe_chartedSpaceCompDiffeomorph M

end SymplecticGeometry

end
