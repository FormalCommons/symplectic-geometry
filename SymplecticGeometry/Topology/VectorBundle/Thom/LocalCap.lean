/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Orientation.ThomClass
public import SymplecticGeometry.Topology.VectorBundle.Thom.FiberCoordinate

/-!
# The canonical Thom class near a point of the base

Let `o` be an orientation of a real vector bundle `E → B` of rank `r` with model fibre `F`, `e` a
linear trivialization of `E`, and `U` a contractible subset of the base set of `e` containing a
point `b`. A map of pairs `φ : Q ⟶ (E, E₀)` into the Thom pair whose base points lie in `U` pulls
the canonical Thom class of `o` back as the generator of the model pair `(F, F ∖ {0})` selected by
the orientation of `E_b` read in `e`, pulled back along the map of pairs `q ↦ (e (φ q)).2`.

## Main results

* `TauCeti.VectorBundleOrientation.singularCohomologyMap_canonicalThomClass_eq_modelThomGenerator`:
  the canonical Thom class, pulled back along a map of pairs into the Thom pair whose base points
  lie in a contractible subset of the base set of a linear trivialization.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom class of an oriented vector bundle).
-/

public section

open Bundle CategoryTheory Module

universe w

namespace TauCeti.VectorBundleOrientation

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {r : ℕ} (o : VectorBundleOrientation F E (Fin r)) (hr : finrank ℝ F = r)

/-- Let `e` be a linear trivialization of an oriented real vector bundle `E → B` of rank `r`, `U` a
contractible subset of its base set and `b ∈ U`. A map of pairs `φ : Q ⟶ (E, E₀)` whose base points
lie in `U` pulls the canonical Thom class of `o` back as the generator of `Hʳ(F, F ∖ {0}; ℤ)`
selected by the orientation `o b` read in `e`, pulled back along the map of pairs
`q ↦ (e (φ q)).2`. -/
theorem singularCohomologyMap_canonicalThomClass_eq_modelThomGenerator
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {U : Set B} [ContractibleSpace U]
    (hU : U ⊆ e.baseSet) {b : B} (hbU : b ∈ U) {Q : TopPair.{w}} (φ : Q ⟶ thomPair F E)
    (hφU : ∀ q, (TopPair.Hom.fst φ q).proj ∈ U) :
    TopPair.singularCohomologyMap φ r (o.canonicalThomClass hr) =
      TopPair.singularCohomologyMap (e.coordPairMap φ fun q ↦ hU (hφU q)) r
        ((e.mapOrientation (Fin r) (hU hbU) (o b)).modelThomGenerator hr) := by
  rw [singularCohomologyMap_eq_singularCohomologyMap_complZeroPairIso_inv e hU hbU φ hφU,
    singularCohomologyMap_fiberThomPairMap_canonicalThomClass o hr e (hU hbU),
    ← TopPair.singularCohomologyMap_comp_apply (Iso.inv _), Iso.inv_hom_id,
    TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]

end TauCeti.VectorBundleOrientation

end
