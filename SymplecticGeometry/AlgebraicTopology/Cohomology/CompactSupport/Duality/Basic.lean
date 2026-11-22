/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.DirectedUnion
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality
public import TauCeti.AlgebraicTopology.Singular.CompactSupport
public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Extension
public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.MayerVietoris
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import SymplecticGeometry.AlgebraicTopology.Singular.MayerVietoris.Basic

/-!
# The duality map on open subsets, and on disjoint and directed unions

Fix a boundaryless `n`-manifold `M` with a homological orientation `o`, and let `L` be an
abelian group. Tau Ceti's `TauCeti.HomologicalOrientation.dualityMap` is the map
`D_M : Hᵖ_c(M; L) ⟶ H_q(M; L)`, `p + q = n`, and
`TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_dualityMap` its naturality along an
open embedding. This file adds:

* the instances of that naturality for the inclusion of an open set `W` of `M` and for the
  inclusion of nested open sets `V ⊆ W`, each open set carrying the restricted orientation, and
  their elementwise forms;
* that bijectivity of the duality map of an open subset depends only on the subset and not on the
  open embedding that presents it;
* Poincaré duality for a union of two disjoint open sets: both theories turn the disjoint union
  into a direct sum, and the duality maps respect these splittings;
* Poincaré duality for a directed union of open sets, since compact sets, and so both theories,
  are exhausted by the members;
* and, combining the two over finite partial unions, Poincaré duality for a union of pairwise
  disjoint open sets.

## Main results

* `TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_inclusion'_dualityMap` and
  `TauCeti.HomologicalOrientation.compactSupportCohomologyExtend_toTopCat_map_dualityMap`, with
  their `_apply` forms: naturality for an open subset and for nested open subsets.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_iff_of_range_eq`.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_disjoint` and
  `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup_of_disjoint`.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_iSup_eq_top` and
  `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_iSup_of_monotone`.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_iSup_of_pairwise_disjoint`.

## Provenance

The statements and proofs are those of Tau Ceti's main branch, in
`TauCeti/AlgebraicTopology/Cohomology/CompactSupport/Duality/Basic.lean`, under the same names, as
of the commits `a2b27244398126b7be07d28c3ce0d849e4ca2458` (TauCetiProject/TauCeti#42569),
`020be269104296e16423165eccaf4c5bf7d05ede` and `b9a3084bbb4cc2ac2c5a0b3ae0323198b47a34b8`; the
pinned release has only the part of that file that is its `Duality.lean`. They are stated here
under their Tau Ceti names and namespace, so that moving Tau Ceti past them deletes this file
without renames.

## Implementation notes

The naturality along inclusions of open sets is stated with `TopologicalSpace.Opens.inclusion'`
and `TopologicalSpace.Opens.toTopCat`, as in the colimit descriptions over open covers. Their
spaces agree with the subtypes only by definition, so `@[elementwise]` does not produce the
elementwise forms, which are stated separately.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, Lemma 3.36 and
  the proof of Theorem 3.35.
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §5, the
  Mayer–Vietoris argument and the disjoint-union step in the proof of Poincaré duality.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module TopologicalSpace Topology Set

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n) (L : ModuleCat.{0} ℤ)

section OpenSubset

/-! ### Naturality along inclusions of open subsets -/

/-- **Naturality of the duality map for an open subset**: for an open `W ⊆ M`, oriented by the
restriction of `o`, extending compactly supported classes from `W` to `M` and then applying the
duality map of `M` is applying the duality map of `W` and then pushing forward along the
inclusion. -/
@[reassoc]
theorem compactSupportCohomologyExtend_inclusion'_dualityMap (W : Opens (TopCat.of M)) (p q : ℕ)
    (h : p + q = n) :
    TopCat.compactSupportCohomologyExtend W.isOpenEmbedding p ≫ o.dualityMap hn L p q h =
      (o.comap W.isOpenEmbedding).dualityMap hn L p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          (Opens.inclusion' W) :=
  o.compactSupportCohomologyExtend_dualityMap hn L (j := (Opens.inclusion' W).hom)
    W.isOpenEmbedding p q h

/-- **Naturality of the duality map for nested open subsets**: for opens `V ⊆ W` of `M`, oriented
by the restrictions of `o`, extending compactly supported classes from `V` to `W` along the
inclusion `f : V ⟶ W` intertwines the duality maps of `V` and `W` with the pushforward along
`f`. -/
@[reassoc]
theorem compactSupportCohomologyExtend_toTopCat_map_dualityMap {V W : Opens (TopCat.of M)}
    (f : V ⟶ W) (p q : ℕ) (h : p + q = n) :
    TopCat.compactSupportCohomologyExtend (Opens.isOpenEmbedding_toTopCat_map f) p ≫
        (o.comap W.isOpenEmbedding).dualityMap hn L p q h =
      (o.comap V.isOpenEmbedding).dualityMap hn L p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          ((Opens.toTopCat (TopCat.of M)).map f) := by
  have := (o.comap W.isOpenEmbedding).compactSupportCohomologyExtend_dualityMap hn L
    (j := ((Opens.toTopCat (TopCat.of M)).map f).hom)
    (Opens.isOpenEmbedding_toTopCat_map f) p q h
  rwa [comap_comap_toTopCat_map] at this

-- `@[elementwise]` cannot produce this from `compactSupportCohomologyExtend_inclusion'_dualityMap`:
-- the space `(Opens.toTopCat _).obj W` of the extension and the space of the duality map of `W`
-- agree only by definition, so the composite cannot be split by rewriting.
/-- Elementwise form of `compactSupportCohomologyExtend_inclusion'_dualityMap`:
`D_M (ι_! x) = ι_* (D_W x)` for the inclusion `ι` of an open `W ⊆ M`. -/
theorem compactSupportCohomologyExtend_inclusion'_dualityMap_apply (W : Opens (TopCat.of M))
    {p q : ℕ} (h : p + q = n)
    (x : ((Opens.toTopCat (TopCat.of M)).obj W).compactSupportCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    o.dualityMap hn L p q h (TopCat.compactSupportCohomologyExtend W.isOpenEmbedding p x) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        (Opens.inclusion' W) ((o.comap W.isOpenEmbedding).dualityMap hn L p q h x) :=
  ConcreteCategory.congr_hom (o.compactSupportCohomologyExtend_inclusion'_dualityMap hn L W p q h) x

/-- Elementwise form of `compactSupportCohomologyExtend_toTopCat_map_dualityMap`:
`D_W (ι_! x) = ι_* (D_V x)` for the inclusion `ι : V ⟶ W` of nested opens of `M`. -/
theorem compactSupportCohomologyExtend_toTopCat_map_dualityMap_apply {V W : Opens (TopCat.of M)}
    (f : V ⟶ W) {p q : ℕ} (h : p + q = n)
    (x : ((Opens.toTopCat (TopCat.of M)).obj V).compactSupportCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) :
    (o.comap W.isOpenEmbedding).dualityMap hn L p q h
        (TopCat.compactSupportCohomologyExtend (Opens.isOpenEmbedding_toTopCat_map f) p x) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        ((Opens.toTopCat (TopCat.of M)).map f)
        ((o.comap V.isOpenEmbedding).dualityMap hn L p q h x) :=
  ConcreteCategory.congr_hom
    (o.compactSupportCohomologyExtend_toTopCat_map_dualityMap hn L f p q h) x


end OpenSubset

section Union

/-! ### Disjoint and directed unions of open sets -/

variable {p q : ℕ} (h : p + q = n)

/-- **The duality map of an open subset depends only on the subset.** For open embeddings
`j : U → M` and `j' : U' → M` with the same image, the duality map of the orientation pulled back
along `j` is bijective exactly when that of the orientation pulled back along `j'` is. -/
theorem bijective_dualityMap_comap_iff_of_range_eq {U U' : Type} [TopologicalSpace U] [T2Space U]
    [ChartedSpace E U] [TopologicalSpace U'] [T2Space U'] [ChartedSpace E U'] {j : U → M}
    {j' : U' → M} (hj : IsOpenEmbedding j) (hj' : IsOpenEmbedding j') (hjj' : range j = range j') :
    Function.Bijective ((o.comap hj).dualityMap hn L p q h) ↔
      Function.Bijective ((o.comap hj').dualityMap hn L p q h) := by
  -- The homeomorphism `e : U ≃ₜ U'` over `M`, along which the two orientations correspond.
  let e : U ≃ₜ U' := hj.isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr hjj').trans hj'.isEmbedding.toHomeomorph.symm)
  have he : j' ∘ e = j := funext fun x ↦ by
    rw [Function.comp_apply, ← hj'.isEmbedding.toHomeomorph_apply_coe]
    simp [e, Homeomorph.setCongr]
  let f : C(U, U') := ⟨e, e.continuous⟩
  have key := (o.comap hj').compactSupportCohomologyExtend_dualityMap hn L (j := f)
    e.isOpenEmbedding p q h
  rw [o.comap_comap_of_comp_eq hj' e.isOpenEmbedding hj he] at key
  have : IsIso (TopCat.ofHom f) := (TopCat.isIso_iff_isHomeomorph _).2 e.isHomeomorph
  have := TopCat.isIso_compactSupportCohomologyExtend (R := ModuleCat.of ℤ (ULift.{0} ℤ))
    (k := ℤ) (M := L) (f := TopCat.ofHom f) e.isOpenEmbedding p
  have hext := ConcreteCategory.bijective_of_isIso
    (TopCat.compactSupportCohomologyExtend (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L)
      (f := TopCat.ofHom f) e.isOpenEmbedding p)
  have hmap := ConcreteCategory.bijective_of_isIso
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map (TopCat.ofHom f))
  refine (Function.Bijective.of_comp_iff' hmap _).symm.trans ?_
  rw [← Function.Bijective.of_comp_iff _ hext]
  refine iff_of_eq (congrArg _ (funext fun x ↦ ?_))
  simpa only [ConcreteCategory.comp_apply, Function.comp_apply] using
    (ConcreteCategory.congr_hom key x).symm

/-- The duality maps of open subsets `U ≤ V` of `M` commute with the extension
`Hᵖ_c(U; L) ⟶ Hᵖ_c(V; L)` and the pushforward `H_q(U; L) ⟶ H_q(V; L)`. -/
private lemma compactSupportCohomologyExtend_dualityMap_of_le {U V : Opens M} (hUV : U ≤ V) :
    TopCat.compactSupportCohomologyExtend
        (f := TopCat.ofHom (⟨Set.inclusion (SetLike.coe_subset_coe.2 hUV),
          continuous_inclusion _⟩ : C(U, V))) (Opens.isOpenEmbedding_of_le hUV) p ≫
        (o.comap V.isOpenEmbedding').dualityMap hn L p q h =
      (o.comap U.isOpenEmbedding').dualityMap hn L p q h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
          (TopCat.ofHom (⟨Set.inclusion (SetLike.coe_subset_coe.2 hUV),
            continuous_inclusion _⟩ : C(U, V))) := by
  let ι : C(U, V) := ⟨Set.inclusion (SetLike.coe_subset_coe.2 hUV), continuous_inclusion _⟩
  have hι : IsOpenEmbedding ι := Opens.isOpenEmbedding_of_le hUV
  have key := (o.comap V.isOpenEmbedding').compactSupportCohomologyExtend_dualityMap hn L
    (j := ι) hι p q h
  rwa [o.comap_comap_of_comp_eq V.isOpenEmbedding' hι U.isOpenEmbedding' rfl] at key

/-- **Poincaré duality for a disjoint union of two open sets.** If `M` is the union of two
disjoint open sets `U` and `V` whose duality maps, for the pulled-back orientations, are bijective,
then the duality map `Hᵖ_c(M; L) ⟶ H_q(M; L)` is bijective. -/
theorem bijective_dualityMap_of_disjoint {U V : Opens M} (hUV : U ⊔ V = ⊤) (hd : Disjoint U V)
    (hU : Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h))
    (hV : Function.Bijective ((o.comap V.isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Bijective (o.dualityMap hn L p q h) := by
  -- The middle maps of the two Mayer–Vietoris sequences, which are isomorphisms.
  let Fc := biprod.desc
    (TopCat.compactSupportCohomologyExtend (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L)
      (f := TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))) U.isOpenEmbedding' p)
    (TopCat.compactSupportCohomologyExtend (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := L)
      (f := TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(V, M))) V.isOpenEmbedding' p)
  let Fh := biprod.desc
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))))
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtypeVal⟩ : C(V, M))))
  have hFc : IsIso Fc := TopCat.isIso_biprodDesc_compactSupportCohomologyExtend_of_disjoint
    (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L (X := TopCat.of M) U V hUV hd p
  have hFh : IsIso Fh := TopCat.isIso_biprodDesc_singularHomologyFunctor_map_of_disjoint
    (X := TopCat.of M) L U.isOpen V.isOpen (by rw [← Opens.coe_sup, hUV, Opens.coe_top])
    (Opens.coe_disjoint.2 hd) q
  have := (ConcreteCategory.isIso_iff_bijective _).2 hU
  have := (ConcreteCategory.isIso_iff_bijective _).2 hV
  have := isIso_of_mono_of_epi (biprod.map ((o.comap U.isOpenEmbedding').dualityMap hn L p q h)
    ((o.comap V.isOpenEmbedding').dualityMap hn L p q h))
  -- The duality maps commute with them, by naturality along the inclusions.
  have hsq : Fc ≫ o.dualityMap hn L p q h =
      biprod.map ((o.comap U.isOpenEmbedding').dualityMap hn L p q h)
        ((o.comap V.isOpenEmbedding').dualityMap hn L p q h) ≫ Fh := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc]
      exact o.compactSupportCohomologyExtend_dualityMap hn L
        (j := (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))) U.isOpenEmbedding' p q h
    · rw [biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc]
      exact o.compactSupportCohomologyExtend_dualityMap hn L
        (j := (⟨Subtype.val, continuous_subtypeVal⟩ : C(V, M))) V.isOpenEmbedding' p q h
  have : IsIso (Fc ≫ o.dualityMap hn L p q h) := by
    rw [hsq]
    infer_instance
  have := IsIso.of_isIso_comp_left Fc (o.dualityMap hn L p q h)
  exact ConcreteCategory.bijective_of_isIso _

/-- **Poincaré duality for a directed union of open sets.** If `M` is the union of a directed
family of open sets `U i` whose duality maps, for the pulled-back orientations, are bijective,
then the duality map `Hᵖ_c(M; L) ⟶ H_q(M; L)` is bijective. -/
theorem bijective_dualityMap_of_iSup_eq_top {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)]
    {U : ι → Opens M} (hU : Monotone U) (hcover : ⨆ i, U i = ⊤)
    (hD : ∀ i, Function.Bijective ((o.comap (U i).isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Bijective (o.dualityMap hn L p q h) := by
  -- An empty family covers only the empty manifold.
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : IsEmpty M := ⟨fun x ↦ by simpa [← hcover] using (Opens.mem_top x)⟩
    exact o.bijective_dualityMap_of_isEmpty hn L h
  -- `H_q(M; L)` is the colimit of the `H_q(U i; L)`, since compact sets lie in some `U i`.
  have hc := TauCeti.isColimitMapCoconeSingularHomologySubset (X := TopCat.of M) L q
    (U := fun i ↦ (U i : Set M)) (fun _ _ hij ↦ hU hij) fun K hK ↦
      Compacts.exists_subset_of_iSup_eq_top hU.directed_le hcover ⟨K, hK⟩
  -- Naturality along the inclusion of `U i` into `M`; `Opens.inclusion' (U i)` is by definition
  -- `TopCat.ofHom ⟨Subtype.val, _⟩`, so `Opens.coe_inclusion'` holds by `rfl`.
  have hnat (i : ι) (z) : o.dualityMap hn L p q h
      (TopCat.compactSupportCohomologyExtend (U i).isOpenEmbedding p z) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map
        (TopCat.ofHom (ContinuousMap.subtypeVal (U i : Set M)))
        ((o.comap (U i).isOpenEmbedding').dualityMap hn L p q h z) :=
    ConcreteCategory.congr_hom (o.compactSupportCohomologyExtend_dualityMap hn L
      (j := (⟨Subtype.val, continuous_subtypeVal⟩ : C(U i, M))) (U i).isOpenEmbedding' p q h) z
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨i, z, rfl⟩ := TopCat.exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top hU hcover x
    rw [hnat] at hx
    obtain ⟨k, f, g, hf⟩ := Concrete.isColimit_exists_of_rep_eq _ hc
      ((o.comap (U i).isOpenEmbedding').dualityMap hn L p q h z) 0
      (by rw [map_zero]; exact hx)
    rw [map_zero] at hf
    let ι : C(U i, U k) := ⟨Set.inclusion (SetLike.coe_subset_coe.2 (hU f.le)),
      continuous_inclusion _⟩
    have hι : IsOpenEmbedding ι := Opens.isOpenEmbedding_of_le (hU f.le)
    -- The class `z` already vanishes in `Hᵖ_c(U k)`, by duality on `U k`.
    have hz : TopCat.compactSupportCohomologyExtend (f := TopCat.ofHom ι) hι p z = 0 :=
      (injective_iff_map_eq_zero _).1 (hD k).1 _ ((ConcreteCategory.congr_hom
        (o.compactSupportCohomologyExtend_dualityMap_of_le hn L h (hU f.le)) z).trans hf)
    have hcomp := TopCat.compactSupportCohomologyExtend_comp (R := ModuleCat.of ℤ (ULift.{0} ℤ))
      (k := ℤ) (M := L) (f := TopCat.ofHom ι) (g := Opens.inclusion' (X := TopCat.of M) (U k)) hι
      (Opens.isOpenEmbedding (X := TopCat.of M) (U k)) p
      (Opens.isOpenEmbedding (X := TopCat.of M) (U i))
    have hx : TopCat.compactSupportCohomologyExtend (Opens.isOpenEmbedding (X := TopCat.of M) (U i))
        p z = TopCat.compactSupportCohomologyExtend (Opens.isOpenEmbedding (X := TopCat.of M) (U k))
          p (TopCat.compactSupportCohomologyExtend (f := TopCat.ofHom ι) hι p z) :=
      ConcreteCategory.congr_hom hcomp z
    rw [hx, hz]
    exact map_zero _
  · obtain ⟨i, w, rfl⟩ := Concrete.isColimit_exists_rep _ hc y
    obtain ⟨z, rfl⟩ := (hD i).2 w
    exact ⟨_, hnat i z⟩

/-- The duality map of an open subset `U ≤ W` of `M`, with the orientation pulled back from `M`,
is bijective exactly when that of `U`, read as an open subset of `W`, with the orientation pulled
back from `W`, is. -/
private theorem bijective_dualityMap_comap_comap_iff {U W : Opens M} (hUW : U ≤ W) :
    Function.Bijective (((o.comap W.isOpenEmbedding').comap
        (Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ U :
          Opens W).isOpenEmbedding').dualityMap hn L p q h) ↔
      Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h) := by
  rw [comap_comap]
  refine o.bijective_dualityMap_comap_iff_of_range_eq hn L h _ _ ?_
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.val.val, y.property⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨⟨⟨y.val, hUW y.property⟩, y.property⟩, rfl⟩

/-- **Poincaré duality for the union of two disjoint open subsets.** If the duality maps of two
disjoint open subsets `U` and `V` of `M` are bijective, then so is that of `U ⊔ V`, for the
orientations pulled back from `M`. -/
theorem bijective_dualityMap_comap_sup_of_disjoint {U V : Opens M} (hd : Disjoint U V)
    (hU : Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h))
    (hV : Function.Bijective ((o.comap V.isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Bijective ((o.comap (U ⊔ V).isOpenEmbedding').dualityMap hn L p q h) := by
  let i : C(↥(U ⊔ V), M) := ⟨Subtype.val, continuous_subtypeVal⟩
  refine (o.comap (U ⊔ V).isOpenEmbedding').bijective_dualityMap_of_disjoint hn L h
    (U := Opens.comap i U) (V := Opens.comap i V) ?_ ?_
    ((o.bijective_dualityMap_comap_comap_iff hn L h le_sup_left).2 hU)
    ((o.bijective_dualityMap_comap_comap_iff hn L h le_sup_right).2 hV)
  · rw [← map_sup, eq_top_iff]
    exact fun x _ ↦ x.property
  · rw [disjoint_iff, ← map_inf, disjoint_iff.1 hd, map_bot]

/-- **Poincaré duality for a directed union of open subsets.** If the duality maps of the members
of a directed family of open subsets `U i` of `M` are bijective, then so is that of their union,
for the orientations pulled back from `M`. -/
theorem bijective_dualityMap_comap_iSup_of_monotone {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] {U : ι → Opens M} (hU : Monotone U)
    (hD : ∀ i, Function.Bijective ((o.comap (U i).isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Bijective ((o.comap (⨆ i, U i).isOpenEmbedding').dualityMap hn L p q h) := by
  let i : C(↥(⨆ i, U i), M) := ⟨Subtype.val, continuous_subtypeVal⟩
  refine (o.comap (⨆ i, U i).isOpenEmbedding').bijective_dualityMap_of_iSup_eq_top hn L h
    (U := fun j ↦ Opens.comap i (U j)) (fun _ _ hjk ↦ Opens.comap_mono i (hU hjk)) ?_
    fun j ↦ (o.bijective_dualityMap_comap_comap_iff hn L h (le_iSup U j)).2 (hD j)
  rw [eq_top_iff]
  rintro x -
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 x.property
  exact Opens.mem_iSup.2 ⟨j, hj⟩

/-- **Poincaré duality for a union of pairwise disjoint open subsets.** If the duality maps of
pairwise disjoint open subsets `s i` of `M` are bijective, then so is that of their union, for the
orientations pulled back from `M`. This is the disjoint-union step of the Mayer–Vietoris induction
for Poincaré duality (`TauCeti.mayerVietoris_induction`). -/
theorem bijective_dualityMap_comap_iSup_of_pairwise_disjoint {ι : Type} {s : ι → Opens M}
    (hs : Pairwise fun i j ↦ Disjoint (s i) (s j))
    (hD : ∀ i, Function.Bijective ((o.comap (s i).isOpenEmbedding').dualityMap hn L p q h)) :
    Function.Bijective ((o.comap (⨆ i, s i).isOpenEmbedding').dualityMap hn L p q h) := by
  classical
  -- The finite partial unions form a directed family with the same union.
  let T : Finset ι → Opens M := fun F ↦ ⨆ i ∈ F, s i
  have hT : Monotone T := fun _ _ hFG ↦ biSup_mono fun _ hi ↦ hFG hi
  have hTD (F : Finset ι) :
      Function.Bijective ((o.comap (T F).isOpenEmbedding').dualityMap hn L p q h) := by
    induction F using Finset.induction_on with
    | empty =>
      have : IsEmpty ↥(T ∅) := ⟨fun x ↦ by simpa [T] using x.property⟩
      exact (o.comap _).bijective_dualityMap_of_isEmpty hn L h
    | insert a F ha ih =>
      have hTa : T (insert a F) = s a ⊔ T F := by
        simp only [T, Finset.iSup_insert]
      have hd : Disjoint (s a) (T F) := by
        simp only [T, disjoint_iSup_iff]
        exact fun i hi ↦ hs fun hai ↦ ha (hai ▸ hi)
      rw [hTa]
      exact o.bijective_dualityMap_comap_sup_of_disjoint hn L h hd (hD a) ih
  have hsup : ⨆ F, T F = ⨆ i, s i :=
    le_antisymm (iSup_le fun _ ↦ iSup₂_le fun i _ ↦ le_iSup s i)
      (iSup_le fun i ↦ le_iSup_of_le {i} (by simp [T]))
  rw [← hsup]
  exact o.bijective_dualityMap_comap_iSup_of_monotone hn L h hT hTD

end Union

end HomologicalOrientation

end TauCeti

end
