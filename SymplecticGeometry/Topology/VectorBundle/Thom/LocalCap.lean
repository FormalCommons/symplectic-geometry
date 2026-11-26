/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Orientation.ThomClass
public import SymplecticGeometry.Topology.VectorBundle.Thom.LocalChart
import SymplecticGeometry.Topology.VectorBundle.Thom.FiberCoordinate

/-!
# The canonical Thom class near a point of the base

Let `o` be an orientation of a real vector bundle `E → B` of rank `r` with model fibre `F`, `e` a
linear trivialization of `E`, and `U` a contractible subset of the base set of `e` containing a
point `b`. A map of pairs `φ : Q ⟶ (E, E₀)` into the Thom pair whose base points lie in `U` pulls
the canonical Thom class of `o` back as the generator of the model pair `(F, F ∖ {0})` selected by
the orientation of `E_b` read in `e`, pulled back along the map of pairs `q ↦ (e (φ q)).2`.

For the chart `Bundle.Trivialization.localChart` of the total space, `(v, q) ↦ e.symm (c.symm q, v)`
on `F × S` for a chart `c` of the base with `c b = 0`, this fibre coordinate is the first
coordinate `v`. So, for `S` contractible, the chart, as a map of pairs from `F × S` relative to the
points with `v ≠ 0` into the Thom pair, pulls the canonical Thom class back as that generator
pulled back along the first projection.

## Main results

* `TauCeti.VectorBundleOrientation.singularCohomologyMap_canonicalThomClass_eq_modelThomGenerator`:
  the canonical Thom class, pulled back along a map of pairs into the Thom pair whose base points
  lie in a contractible subset of the base set of a linear trivialization.
* `TauCeti.VectorBundleOrientation.singularCohomologyMap_localChart_canonicalThomClass`: the
  canonical Thom class read in the chart `Bundle.Trivialization.localChart` on `F × S`, `S`
  contractible, as the generator of the model pair pulled back along the first projection.

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
      TopPair.singularCohomologyMap ((TopPair.isoOfSubsetRange Q).hom ≫
        TopPair.ofSubsetMap (X := Q.fst) (Y := TopCat.of F)
          (TopCat.ofHom ⟨fun q ↦ (e (TopPair.Hom.fst φ q)).2,
            (e.continuousOn.comp_continuous (TopPair.Hom.fst φ).hom.continuous
              fun q ↦ e.mem_source.2 (hU (hφU q))).snd⟩)
          (B' := {0}ᶜ) fun q hq ↦ (e.snd_apply_ne_zero_iff ℝ (hU (hφU q))).2 <|
            mem_zeroSectionCompl.1 (TopPair.mapsTo_range_map_of_hom φ hq)) r
        ((e.mapOrientation (Fin r) (hU hbU) (o b)).modelThomGenerator hr) := by
  rw [singularCohomologyMap_eq_singularCohomologyMap_complZeroPairIso_inv e hU hbU φ hφU,
    singularCohomologyMap_fiberThomPairMap_canonicalThomClass o hr e (hU hbU),
    ← TopPair.singularCohomologyMap_comp_apply (Iso.inv _), Iso.inv_hom_id,
    TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]

open Set in
/-- Let `e` be a linear trivialization of an oriented real vector bundle `E → B` of rank `r` with
model fibre `F`, `c` a chart of the base with `c b = 0`, and `S` a contractible open subset of the
target of `c` containing `0` that `c.symm` carries into the base set of `e`. The chart
`Bundle.Trivialization.localChart`, as a map of pairs from `F × S` relative to the points with
nonzero first coordinate to the Thom pair, pulls the canonical Thom class of `o` back as the
pull-back along the first projection `F × S → F` of the generator of `Hʳ(F, F ∖ {0}; ℤ)` selected
by the orientation `o b` read in `e`. -/
theorem singularCohomologyMap_localChart_canonicalThomClass (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {Q : Type w} [TopologicalSpace Q] [Zero Q] {c : OpenPartialHomeomorph B Q}
    {S : Set Q} [ContractibleSpace S] (hS : IsOpen S) (hSc : S ⊆ c.target)
    (hSe : MapsTo c.symm S e.baseSet) {b : B} (hb : b ∈ c.source) (hcb : c b = 0)
    (h0 : (0 : Q) ∈ S) :
    TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of (univ ×ˢ S : Set (F × Q)))
          (TopCat.ofHom ⟨e.localChart c S, (e.isOpenEmbedding_localChart hS hSc hSe).continuous⟩)
          (B := {x | x.val.1 ≠ 0}) (B' := zeroSectionCompl F E)
          fun x hx ↦ mem_zeroSectionCompl.2 fun h ↦ hx ((e.localChart_snd_eq_zero_iff hSe x).1 h))
        r (o.canonicalThomClass hr) =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (X := TopCat.of (univ ×ˢ S : Set (F × Q))) (Y := TopCat.of F)
          (TopCat.ofHom ⟨fun x ↦ x.val.1, continuous_fst.comp continuous_subtypeVal⟩)
          (B := {x | x.val.1 ≠ 0}) (B' := {0}ᶜ) fun _ hx ↦ hx) r
        ((e.mapOrientation (Fin r) (by rw [← c.left_inv hb, hcb]; exact hSe h0)
          (o b)).modelThomGenerator hr) := by
  have hcb' : c.symm 0 = b := by rw [← hcb, c.left_inv hb]
  -- `c.symm` carries `S` homeomorphically onto its image, which is therefore contractible.
  have : ContractibleSpace (c.symm '' S) :=
    (c.symm.homeomorphOfImageSubsetSource (by rwa [c.symm_source]) rfl).symm.contractibleSpace
  set φ := TopPair.ofSubsetMap (X := TopCat.of (univ ×ˢ S : Set (F × Q)))
    (TopCat.ofHom ⟨e.localChart c S, (e.isOpenEmbedding_localChart hS hSc hSe).continuous⟩)
    (B := {x | x.val.1 ≠ 0}) (B' := zeroSectionCompl F E)
    fun x hx ↦ mem_zeroSectionCompl.2 fun h ↦ hx ((e.localChart_snd_eq_zero_iff hSe x).1 h)
  have hφ (x : (univ ×ˢ S : Set (F × Q))) : TopPair.Hom.fst φ x = e.localChart c S x :=
    TopPair.ofSubsetMap_fst_apply (X := TopCat.of (univ ×ˢ S : Set (F × Q)))
      (B := {x | x.val.1 ≠ 0}) _ _ x
  -- The fibre coordinate of the chart is the first projection.
  have hfst (x : (univ ×ˢ S : Set (F × Q))) : (e (e.localChart c S x)).2 = x.val.1 := by
    rw [e.localChart_def, e.apply_symm_apply (e.mem_target.2 (hSe x.property.2))]
  rw [singularCohomologyMap_canonicalThomClass_eq_modelThomGenerator o hr e hSe.image_subset
    ⟨0, h0, hcb'⟩ φ fun x ↦
      hφ x ▸ (e.proj_localChart hSe x).symm ▸ mem_image_of_mem _ x.property.2]
  congr 3
  refine TopPair.hom_ext_of_fst _ (ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
  rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply, TopPair.isoOfSubsetRange_hom_fst_apply]
  -- The point `x` of the pair is a point of `univ ×ˢ S` only up to unfolding `ofSubset`.
  erw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply]
  exact (congrArg (fun p ↦ (e p).2) (hφ x)).trans (hfst x)

end TauCeti.VectorBundleOrientation

end
