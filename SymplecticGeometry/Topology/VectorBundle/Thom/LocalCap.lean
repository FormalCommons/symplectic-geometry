/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Orientation.ThomClass
public import SymplecticGeometry.Topology.VectorBundle.Thom.FiberCoordinate
public import SymplecticGeometry.Topology.VectorBundle.Thom.LocalChartCap
public import SymplecticGeometry.Topology.VectorBundle.ZeroSection
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Basic
import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.ProdLocal
import SymplecticGeometry.Topology.VectorBundle.Thom.LocalChart

/-!
# The canonical Thom class near a point of the base, and the local cap computation

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

Combined with the cap product of the excisive couple `(E ∖ 0, E ∖ E_b)` carried through the chart
(`Bundle.Trivialization.localChartLocalHomologyIso_hom_comp_singularRelativeCap`), this computes
the cap product of a local class of `E` at `0_b` with the canonical Thom class, pushed forward to
the base: in the chart it is the cap product on `F × Q` with the generator pulled back along the
first projection, followed by the second projection. When the chart reads the local class as the
cross product, fibre factor first, of the local orientation of `F` selected by `o b` read in `e`
with a local class `ζ` of the base chart, `Cap/ProdLocal.lean` evaluates the result: it is `ζ`.
In rank zero the point class of `F` takes the place of the local orientation, and the result is
`ζ` or `-ζ` according to the sign of `o b`. Both cases hold for every degree of `ζ`, so for a
base of any dimension.

## Main results

All in the namespace `TauCeti.VectorBundleOrientation`.

* `singularCohomologyMap_canonicalThomClass_eq_modelThomGenerator`:
  the canonical Thom class, pulled back along a map of pairs into the Thom pair whose base points
  lie in a contractible subset of the base set of a linear trivialization.
* `singularCohomologyMap_localChart_canonicalThomClass`: the
  canonical Thom class read in the chart `Bundle.Trivialization.localChart` on `F × S`, `S`
  contractible, as the generator of the model pair pulled back along the first projection.
* `localChartLocalHomologyIso_hom_comp_singularRelativeCap_canonicalThomClass`:
  the cap product with the canonical Thom class, read in the chart, as the cap product on `F × Q`
  with the generator pulled back along the first projection.
* `localHomologyMap_singularRelativeCap_canonicalThomClass_of_localOrientation`:
  the local cap computation at `0_b` in positive rank.
* `localHomologyMap_singularRelativeCap_canonicalThomClass_of_finrank_eq_zero`:
  the same in rank zero.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom class of an oriented vector bundle).
* E. H. Spanier, *Algebraic Topology*, Chapter 5, Sections 6 and 7 (the cap product and its
  naturality, and the cap product of cross products).
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
        ((e.mapOrientation (Fin r) (c.mem_of_mapsTo_symm hb hcb hSe h0)
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
  rw [Trivialization.coordPairMap_fst_apply, hφ x]
  -- The point `x` of the pair is a point of `univ ×ˢ S` only up to unfolding `ofSubset`.
  erw [TopPair.ofSubsetMap_fst_apply]
  exact hfst x

section Cap

open MonoidalCategory CartesianMonoidalCategory Set

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

variable {B : Type} [TopologicalSpace B] [T1Space B] {P : Type} [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] {E : B → Type} [TopologicalSpace (TotalSpace P E)]
  [T1Space (TotalSpace P E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle P E] [VectorBundle ℝ P E] {r : ℕ}
  (o : VectorBundleOrientation P E (Fin r)) (hr : finrank ℝ P = r) {Q : Type}
  [NormedAddCommGroup Q] {c : OpenPartialHomeomorph B Q} {S : Set Q} [ContractibleSpace S]

/-- **The cap product with the canonical Thom class, read in a local chart of the total space.**
Let `e` be a linear trivialization of an oriented real vector bundle `E → B` of rank `r` with model
fibre `P`, `c` a chart of the base with `c b = 0`, and `S` a contractible open subset of the target
of `c` containing `0` that `c.symm` carries into the base set of `e`. Let `u : T ⟶ ℤ ⊗ S'` and
`μ : ℤ ⊗ S' ⟶ N` be maps of coefficients, which both cap products below use. For `r + q = n`,
carrying a class of `Hₙ(P × Q, P × Q ∖ 0; T)` to `Hₙ(E, E ∖ 0_b; T)` by the chart
`Bundle.Trivialization.localChartLocalHomologyIso`, capping it with the canonical Thom class by
the cap product of the excisive couple `(E ∖ 0, E ∖ E_b)`, pushing forward along the projection to
`H_q(B, B ∖ b; N)` and reading the result in `c` is capping the class, by the cap product of the
couple `((P ∖ 0) × Q, P × (Q ∖ 0))`, with the pull-back along the first projection of the
generator of `Hʳ(P, P ∖ 0; ℤ)` selected by the orientation `o b` read in `e`, and pushing forward
along the second projection to `H_q(Q, Q ∖ 0; N)`. -/
theorem localChartLocalHomologyIso_hom_comp_singularRelativeCap_canonicalThomClass
    (e : Trivialization P (π P E)) [e.IsLinear ℝ] (hS : IsOpen S) (hSc : S ⊆ c.target)
    (hSe : MapsTo c.symm S e.baseSet) {b : B} (hb : b ∈ c.source) (hcb : c b = 0)
    (h0 : (0 : Q) ∈ S) {S' T N : ModuleCat.{0} ℤ}
    (u : T ⟶ ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ S') (μ : ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ S' ⟶ N)
    {q n : ℕ} (hn : r + q = n) :
    (e.localChartLocalHomologyIso T hS hSc hSe hb hcb h0 n).hom ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) fun _ hv ↦
          (zeroSectionCompl_union_compl_preimage_singleton b).superset hv) T n ≫
        TopCat.singularRelativeCap ℤ u μ _
          (TopCat.ofHom ⟨π P E, FiberBundle.continuous_proj P E⟩ ⁻¹' ({b}ᶜ : Set (TopCat.of B)))
          ((isOpen_zeroSectionCompl P E).preimage continuous_subtypeVal)
          ((isOpen_compl_singleton.preimage (FiberBundle.continuous_proj P E)).preimage
            continuous_subtypeVal) r q n hn (o.canonicalThomClass hr) ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (TopCat.ofHom ⟨π P E, FiberBundle.continuous_proj P E⟩)
            (mapsTo_preimage _ ({b}ᶜ : Set (TopCat.of B)))) N q ≫
        ((localHomologyIsoOfIsOpenEmbedding N
          c.open_source.isOpenEmbedding_subtypeVal ⟨b, hb⟩ q).inv :
            localHomology N {b} q ⟶ _) ≫
        localHomologyMap N c.sourceRestrict
          (hcb ▸ (c.sourceRestrict_preimage_singleton hb).subset) q =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap _
          (TopCat.mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl
            (0 : P) (0 : Q))) T n ≫
        TopCat.singularRelativeCap ℤ u μ
          (fst (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of P)))
          (snd (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of Q)))
          (TopCat.isOpen_subtypeVal_preimage_preimage_fst_union isOpen_compl_singleton)
          (TopCat.isOpen_subtypeVal_preimage_preimage_snd_union isOpen_compl_singleton)
          r q n hn
          (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst (TopCat.of P) (TopCat.of Q)) (mapsTo_preimage _ _)) r
            ((e.mapOrientation (Fin r) (c.mem_of_mapsTo_symm hb hcb hSe h0)
              (o b)).modelThomGenerator hr)) ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (snd (TopCat.of P) (TopCat.of Q)) (mapsTo_preimage _ _)) N q := by
  refine e.localChartLocalHomologyIso_hom_comp_singularRelativeCap ℤ _ _ hS hSc hSe hb hcb h0 _
    hn _ _ ?_
  rw [singularCohomologyMap_localChart_canonicalThomClass o hr e hS hSc hSe hb hcb h0]
  refine (TopPair.singularCohomologyMap_comp_apply _ _ r _).symm.trans ?_
  exact congrArg (fun f ↦ TopPair.singularCohomologyMap f r _)
    (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ (fun _ hx ↦ hx)
      -- The first projection of `TopCat.of P ⊗ TopCat.of Q` is `Prod.fst` by definition.
      (ConcreteCategory.hom_ext _ _ fun _ ↦ rfl))

/-- **The local cap computation at a point of the zero section**, in positive rank. Let `e` be a
linear trivialization of an oriented real vector bundle `E → B` of rank `r = k + 1` with model
fibre `P`, the orientation `o` being indexed by `Fin r`, `c` a chart of the base with `c b = 0`,
and `S` a contractible open subset of the target of `c` containing `0` that `c.symm` carries into
the base set of `e`. Let `μ ∈ Hₙ(E, E ∖ 0_b)` be a class that the chart
`Bundle.Trivialization.localChartLocalHomologyIso` reads as the local cross product, normal factor
`P` first, of the local orientation of `P` selected by the orientation `o b` read in `e` and
reindexed along `Fin r ≃ Fin (k + 1)`, with a class `ζ ∈ H_q(Q, Q ∖ 0)`, in any degree `q`. Cap
`μ`, read relative to `E ∖ 0 ∪ E ∖ E_b`, with the canonical Thom class by the cap product of the
excisive couple `(E ∖ 0, E ∖ E_b)`, and push the result forward along the projection to
`H_q(B, B ∖ b)`. The chart `c` reads the result as `ζ`.

The chart puts the fibre factor first, so no exchange of factors enters here; for a class read as
the local orientation of an orientation that puts the base factor first, the exchange is made by
`Orientation.singularRelativeCap_modelThomGenerator_localOrientation_map_prodComm`. -/
theorem localHomologyMap_singularRelativeCap_canonicalThomClass_of_localOrientation {k : ℕ}
    (hk : r = k + 1) (e : Trivialization P (π P E)) [e.IsLinear ℝ] (hS : IsOpen S)
    (hSc : S ⊆ c.target)
    (hSe : MapsTo c.symm S e.baseSet) {b : B} (hb : b ∈ c.source) (hcb : c b = 0)
    (h0 : (0 : Q) ∈ S) {q n : ℕ} (hn : r + q = n)
    (ζ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set Q) q)
    (μ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
      {zeroSection P E b} n)
    (hμ : (e.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe hb hcb h0 n).inv
        μ = (SymplecticGeometry.localHomologyCross (0 : P) (0 : Q) (k + 1) q n (hk ▸ hn)).hom
          (((Orientation.reindex ℝ P (finCongr hk)
            (e.mapOrientation (Fin r) (c.mem_of_mapsTo_symm hb hcb hSe h0)
            (o b))).localOrientation (hr.trans hk)).val ⊗ₜ ζ)) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) c.sourceRestrict
        (hcb ▸ (c.sourceRestrict_preimage_singleton hb).subset) q
        ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
          c.open_source.isOpenEmbedding_subtypeVal ⟨b, hb⟩ q).inv
          (TopPair.singularHomologyMap
            (TopPair.ofSubsetMap (TopCat.ofHom ⟨π P E, FiberBundle.continuous_proj P E⟩)
              (mapsTo_preimage _ ({b}ᶜ : Set (TopCat.of B)))) (ModuleCat.of ℤ (ULift.{0} ℤ)) q
            (TopCat.singularRelativeCap ℤ (ρ_ _).inv (ρ_ _).hom _
              (TopCat.ofHom ⟨π P E, FiberBundle.continuous_proj P E⟩ ⁻¹'
                ({b}ᶜ : Set (TopCat.of B)))
              ((isOpen_zeroSectionCompl P E).preimage continuous_subtypeVal)
              ((isOpen_compl_singleton.preimage (FiberBundle.continuous_proj P E)).preimage
                continuous_subtypeVal) r q n hn (o.canonicalThomClass hr)
              (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) fun _ hv ↦
                (zeroSectionCompl_union_compl_preimage_singleton b).superset hv)
                (ModuleCat.of ℤ (ULift.{0} ℤ)) n μ)))) = ζ := by
  subst hk
  simp only [finCongr_refl, Orientation.reindex_refl] at hμ
  have h := ConcreteCategory.congr_hom
    (localChartLocalHomologyIso_hom_comp_singularRelativeCap_canonicalThomClass o hr e hS hSc hSe
      hb hcb h0 (ρ_ _).inv (ρ_ _).hom hn)
    ((e.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe hb hcb h0 n).inv μ)
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at h
  rw [h, hμ]
  exact Orientation.singularRelativeCap_modelThomGenerator_localHomologyCross_localOrientation
    hr hn _ ζ

/-- **The local cap computation at a point of the zero section**, in rank zero. Let `e` be a
linear trivialization of an oriented real vector bundle `E → B` of rank `r = 0` with model fibre
`P`, the orientation `o` being indexed by `Fin r`, `c` a chart of the base with `c b = 0`, and
`S` a contractible open subset of the target of `c` containing `0` that `c.symm` carries into the
base set of `e`. For `r + q = n`, let `μ ∈ Hₙ(E, E ∖ 0_b)` be a class that the chart
`Bundle.Trivialization.localChartLocalHomologyIso` reads as the local cross product, normal factor
`P` first, of the local orientation of `P` at `0` selected by the orientation `o b`, read in `e`
and reindexed along `Fin r ≃ Fin 0` (`Orientation.localOrientationOfZeroDim`), with a class
`ζ ∈ H_q(Q, Q ∖ 0)`. Cap
`μ`, read relative to `E ∖ 0 ∪ E ∖ E_b`, with the canonical Thom class by the cap product of the
excisive couple `(E ∖ 0, E ∖ E_b)`, and push the result forward along the projection to
`H_q(B, B ∖ b)`. The chart `c` reads the result as `ζ`. -/
theorem localHomologyMap_singularRelativeCap_canonicalThomClass_of_finrank_eq_zero
    (hk : r = 0) (e : Trivialization P (π P E)) [e.IsLinear ℝ] (hS : IsOpen S)
    (hSc : S ⊆ c.target)
    (hSe : MapsTo c.symm S e.baseSet) {b : B} (hb : b ∈ c.source) (hcb : c b = 0)
    (h0 : (0 : Q) ∈ S) {q n : ℕ} (hn : r + q = n)
    (ζ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set Q) q)
    (μ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
      {zeroSection P E b} n)
    (hμ : (e.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe hb hcb h0 n).inv
        μ = (SymplecticGeometry.localHomologyCross (0 : P) (0 : Q) 0 q n (hk ▸ hn)).hom
          (((Orientation.reindex ℝ P (finCongr hk)
            (e.mapOrientation (Fin r) (c.mem_of_mapsTo_symm hb hcb hSe h0)
            (o b))).localOrientationOfZeroDim (hr.trans hk)).val ⊗ₜ ζ)) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) c.sourceRestrict
        (hcb ▸ (c.sourceRestrict_preimage_singleton hb).subset) q
        ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
          c.open_source.isOpenEmbedding_subtypeVal ⟨b, hb⟩ q).inv
          (TopPair.singularHomologyMap
            (TopPair.ofSubsetMap (TopCat.ofHom ⟨π P E, FiberBundle.continuous_proj P E⟩)
              (mapsTo_preimage _ ({b}ᶜ : Set (TopCat.of B)))) (ModuleCat.of ℤ (ULift.{0} ℤ)) q
            (TopCat.singularRelativeCap ℤ (ρ_ _).inv (ρ_ _).hom _
              (TopCat.ofHom ⟨π P E, FiberBundle.continuous_proj P E⟩ ⁻¹'
                ({b}ᶜ : Set (TopCat.of B)))
              ((isOpen_zeroSectionCompl P E).preimage continuous_subtypeVal)
              ((isOpen_compl_singleton.preimage (FiberBundle.continuous_proj P E)).preimage
                continuous_subtypeVal) r q n hn (o.canonicalThomClass hr)
              (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) fun _ hv ↦
                (zeroSectionCompl_union_compl_preimage_singleton b).superset hv)
                (ModuleCat.of ℤ (ULift.{0} ℤ)) n μ)))) = ζ := by
  subst hk
  obtain rfl : q = n := by omega
  simp only [finCongr_refl, Orientation.reindex_refl] at hμ
  have h := ConcreteCategory.congr_hom
    (localChartLocalHomologyIso_hom_comp_singularRelativeCap_canonicalThomClass o hr e hS hSc hSe
      hb hcb h0 (ρ_ _).inv (ρ_ _).hom (zero_add q))
    ((e.localChartLocalHomologyIso (ModuleCat.of ℤ (ULift.{0} ℤ)) hS hSc hSe hb hcb h0 q).inv μ)
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at h
  rw [h, hμ]
  exact Orientation.singularRelativeCap_modelThomGenerator_localHomologyCross_of_zero hr _ ζ

end Cap

end TauCeti.VectorBundleOrientation

end
