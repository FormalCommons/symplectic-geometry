/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.FiveLemma
public import SymplecticGeometry.Algebra.Category.ModuleCat.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Cap.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.MayerVietoris
public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Manifold
public import SymplecticGeometry.Topology.Sets.Opens.Comap

/-!
# Poincaré duality for unions of open sets

Fix a boundaryless `n`-manifold `M` with a homological orientation `o`, an abelian group `L`, and
give every open set of `M` the restricted orientation. This file proves the Mayer–Vietoris step of
Poincaré duality: if the duality maps `D : Hᵖ_c(-; L) ⟶ H_q(-; L)`, `p + q = n`, of open sets `U`,
`V` and `U ∩ V` are bijective in every degree, then the duality map of `U ∪ V` is bijective in
every degree.

Run over the finite unions of the members of a family of open sets that is closed under
intersection (`InfClosed.finset_sup_induction`), this step carries duality from the members to
every such union, and on to `M` when the family covers it
(`TauCeti.HomologicalOrientation.bijective_dualityMap_of_iSup_eq_top`).

The proof is the five lemma on the ladder formed by the two Mayer–Vietoris sequences,

```
Hᵖ_c(U ∩ V) → Hᵖ_c(U) ⊞ Hᵖ_c(V) → Hᵖ_c(M) → Hᵖ⁺¹_c(U ∩ V) → Hᵖ⁺¹_c(U) ⊞ Hᵖ⁺¹_c(V)
     ↓                ↓              ↓             ↓                    ↓
H_q(U ∩ V)  →  H_q(U) ⊞ H_q(V)  →  H_q(M)  →  H_{q-1}(U ∩ V)  →  H_{q-1}(U) ⊞ H_{q-1}(V)
```

whose squares commute by `compactSupportCohomologyMayerVietorisToBiprod_dualityMap`,
`compactSupportCohomologyMayerVietorisFromBiprod_dualityMap` and, up to the sign `(-1)^(p+1)`,
which we absorb into the last two vertical maps, `dualityMap_mayerVietorisδ`.

In the top degree `p = n` the homology row stops at `H₀(M)`: surjectivity of `D_M` then follows
from the surjectivity of `H₀(U) ⊞ H₀(V) ⟶ H₀(M)`, but injectivity needs the group
`Hⁿ⁺¹_c(U ∩ V; L)` to vanish. In Hatcher's argument that vanishing is part of the inductive
hypothesis, `D` being defined in all degrees with `H_q = 0` for `q < 0`. Here it holds for every
open set `W` of `M`, by `TopCat.isZero_compactSupportCohomology_of_chartedSpace_int`, in
`CompactSupport/Manifold.lean`, applied to `W` as a manifold of its own, so the two steps need no
hypothesis on it. Mathlib's five lemmas give both cases:
`AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective` below the top degree,
and `AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact` in it.

## Main results

* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_sup_eq_top'`: for open sets `U` and `V`
  covering `M`, the step from `U`, `V` and `U ∩ V` to `M`.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup'`: for any open sets `U` and `V`
  of `M`, the step from `U`, `V` and `U ∩ V` to `U ∪ V`.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_infClosed`: the induction of Hatcher's
  Lemma 3.36, from the members of a family of open sets closed under intersection that covers
  `M`, to `M`.

Tau Ceti has the first two steps under the unprimed names, with the vanishing of
`Hⁿ⁺¹_c(U ∩ V; L)` as a hypothesis; the primed versions here do not need it.

## Implementation notes

The theorems are stated for `Opens M` and the embeddings `Opens.isOpenEmbedding'`, as Tau Ceti's
disjoint case `TauCeti.HomologicalOrientation.bijective_dualityMap_of_disjoint` is, while the steps
of the proof use open sets of `TopCat.of M`, as Tau Ceti's Mayer–Vietoris squares do.

The proof of `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup'` adapts that of Tau
Ceti's `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup_of_disjoint`: it applies the
form for a cover inside `U ∪ V`, the cover being
`TopologicalSpace.Opens.comap_val_sup_comap_val_eq_top`. Its passage between an open set of
`U ∪ V` and the same open set of `M` adapts Tau Ceti's private lemma
`bijective_dualityMap_comap_comap_iff` (in
`TauCeti/AlgebraicTopology/Cohomology/CompactSupport/Duality/Basic.lean`): it combines
`TauCeti.HomologicalOrientation.comap_comap`,
`TauCeti.HomologicalOrientation.bijective_dualityMap_comap_iff_of_range_eq` and
`TopologicalSpace.Opens.range_val_comp_val_comap`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, Lemma 3.36,
  the step from `U`, `V` and `U ∩ V` to `U ∪ V` and the induction over finite unions.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opens

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : Module.finrank ℝ E = n) (L : ModuleCat.{0} ℤ)

local notation "ℤₘ" => ModuleCat.of ℤ (ULift ℤ : Type)

section Cover

/-! ### The five lemma on the Mayer–Vietoris ladder

The steps are stated for open sets of `TopCat.of M`, as Tau Ceti's Mayer–Vietoris squares are. -/

variable {U V : Opens (TopCat.of M)} (hUV : U ⊔ V = ⊤)

include hUV in
/-- Below the top degree, `D_M` is bijective. -/
private lemma bijective_dualityMap_succ {p q : ℕ} (h : p + (q + 1) = n)
    (hU : Function.Bijective ((o.comap U.isOpenEmbedding).dualityMap hn L p (q + 1) h))
    (hV : Function.Bijective ((o.comap V.isOpenEmbedding).dualityMap hn L p (q + 1) h))
    (hW : Function.Bijective ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L p (q + 1) h))
    (hU' : Function.Bijective ((o.comap U.isOpenEmbedding).dualityMap hn L (p + 1) q (by omega)))
    (hV' : Function.Bijective ((o.comap V.isOpenEmbedding).dualityMap hn L (p + 1) q (by omega)))
    (hW' : Function.Bijective
      ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L (p + 1) q (by omega))) :
    Function.Bijective (o.dualityMap hn L p (q + 1) h) := by
  have hUV' : (U : Set (TopCat.of M)) ∪ V = Set.univ := by
    simpa only [← Opens.coe_sup, hUV] using Opens.coe_top
  have hc₄ := o.compactSupportCohomologyMayerVietorisToBiprod_dualityMap hn L
    (show p + 1 + q = n by omega) U V
  refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (TopCat.compactSupportCohomologyMayerVietorisToBiprod ℤₘ ℤ L U V p).hom.toAddMonoidHom
    (TopCat.compactSupportCohomologyMayerVietorisFromBiprod ℤₘ ℤ L U V p).hom.toAddMonoidHom
    (TopCat.compactSupportCohomologyMayerVietorisδ ℤₘ ℤ L U V hUV p (p + 1)
      rfl).hom.toAddMonoidHom
    (TopCat.compactSupportCohomologyMayerVietorisToBiprod ℤₘ ℤ L U V
      (p + 1)).hom.toAddMonoidHom
    (SSet.mayerVietorisToBiprod L
      (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_left)))
      (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_right)))
        (q + 1)).hom.toAddMonoidHom
    (SSet.mayerVietorisFromBiprod L (TopCat.toSSet.map (Opens.inclusion' U))
      (TopCat.toSSet.map (Opens.inclusion' V)) (q + 1)).hom.toAddMonoidHom
    (TopCat.mayerVietorisδ L U.isOpen V.isOpen hUV' (q + 1) q rfl).hom.toAddMonoidHom
    (SSet.mayerVietorisToBiprod L
      (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_left)))
      (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_right)))
        q).hom.toAddMonoidHom
    ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L p (q + 1) h).hom.toAddMonoidHom
    (biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p (q + 1) h)
      ((o.comap V.isOpenEmbedding).dualityMap hn L p (q + 1) h)).hom.toAddMonoidHom
    (o.dualityMap hn L p (q + 1) h).hom.toAddMonoidHom
    (((-1 : ℤ) ^ (p + 1)) • (o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L (p + 1) q
      (by omega)).hom.toAddMonoidHom
    (((-1 : ℤ) ^ (p + 1)) • biprod.map
      ((o.comap U.isOpenEmbedding).dualityMap hn L (p + 1) q (by omega))
      ((o.comap V.isOpenEmbedding).dualityMap hn L (p + 1) q (by omega))).hom.toAddMonoidHom
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom
      (o.compactSupportCohomologyMayerVietorisToBiprod_dualityMap hn L h U V) x).symm)
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom
      (o.compactSupportCohomologyMayerVietorisFromBiprod_dualityMap hn L h U V) x).symm)
    (AddMonoidHom.ext fun x ↦ ConcreteCategory.congr_hom
      (o.dualityMap_mayerVietorisδ L hn U V hUV p q h) x)
    (AddMonoidHom.ext fun x ↦ ?_)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.compactSupportCohomologyMayerVietoris_exact₂ ℤₘ ℤ L U V hUV p))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.compactSupportCohomologyMayerVietoris_exact₃ ℤₘ ℤ L U V hUV p (p + 1) rfl))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.compactSupportCohomologyMayerVietoris_exact₁ ℤₘ ℤ L U V hUV p (p + 1) rfl))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.mayerVietoris_exact₂ L U.isOpen V.isOpen hUV' (q + 1)))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.mayerVietoris_exact₃ L U.isOpen V.isOpen hUV' (q + 1) q rfl))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.mayerVietoris_exact₁ L U.isOpen V.isOpen hUV' (q + 1) q rfl))
    hW.2 (ModuleCat.bijective_biprod_map _ _ hU hV)
    ((ModuleCat.bijective_zsmul_iff _ (isUnit_neg_one.pow _)).2 hW')
    ((ModuleCat.bijective_zsmul_iff _ (isUnit_neg_one.pow _)).2
      (ModuleCat.bijective_biprod_map _ _ hU' hV')).1
  -- The fourth square is the first square one degree up, multiplied by the sign.
  have hc₄' := congrArg (((-1 : ℤ) ^ (p + 1)) • ·) hc₄
  dsimp only at hc₄'
  rw [← Preadditive.comp_zsmul] at hc₄'
  -- The duality map lands in `((singularHomologyFunctor _ q).obj L).obj _`, which is the source of
  -- `SSet.mayerVietorisToBiprod` only after unfolding `singularHomologyFunctor`, as in
  -- `compactSupportCohomologyMayerVietorisToBiprod_dualityMap`; so `rw` cannot move the sign.
  erw [← Preadditive.zsmul_comp] at hc₄'
  exact (ConcreteCategory.congr_hom hc₄' x).symm

include hUV in
/-- In the top degree, `D_M : Hⁿ_c(M) ⟶ H₀(M)` is bijective, given `Hⁿ⁺¹_c(U ∩ V) = 0`. -/
private lemma bijective_dualityMap_zero {p : ℕ} (h : p + 0 = n)
    (hU : Function.Bijective ((o.comap U.isOpenEmbedding).dualityMap hn L p 0 h))
    (hV : Function.Bijective ((o.comap V.isOpenEmbedding).dualityMap hn L p 0 h))
    (hW : Function.Bijective ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L p 0 h))
    (hW₀ : IsZero (((Opens.toTopCat (TopCat.of M)).obj (U ⊓ V)).compactSupportCohomology ℤₘ ℤ L
      (p + 1))) :
    Function.Bijective (o.dualityMap hn L p 0 h) := by
  have hUV' : (U : Set (TopCat.of M)) ∪ V = Set.univ := by
    simpa only [← Opens.coe_sup, hUV] using Opens.coe_top
  -- Since `Hⁿ⁺¹_c(U ∩ V) = 0`, the map `Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(M)` is onto.
  have hδ := hW₀.eq_of_tgt (TopCat.compactSupportCohomologyMayerVietorisδ ℤₘ ℤ L U V hUV p
    (p + 1) rfl) 0
  have hf₂ : Function.Surjective
      (TopCat.compactSupportCohomologyMayerVietorisFromBiprod ℤₘ ℤ L U V p) := fun x ↦
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.compactSupportCohomologyMayerVietoris_exact₃ ℤₘ ℤ L U V hUV p (p + 1) rfl) x).1
        (by simp [hδ])
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
    (TopCat.compactSupportCohomologyMayerVietorisToBiprod ℤₘ ℤ L U V p).hom.toAddMonoidHom
    (TopCat.compactSupportCohomologyMayerVietorisFromBiprod ℤₘ ℤ L U V p).hom.toAddMonoidHom
    (SSet.mayerVietorisToBiprod L
      (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_left)))
      (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_right)))
        0).hom.toAddMonoidHom
    (SSet.mayerVietorisFromBiprod L (TopCat.toSSet.map (Opens.inclusion' U))
      (TopCat.toSSet.map (Opens.inclusion' V)) 0).hom.toAddMonoidHom
    ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L p 0 h).hom.toAddMonoidHom
    (biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p 0 h)
      ((o.comap V.isOpenEmbedding).dualityMap hn L p 0 h)).hom.toAddMonoidHom
    (o.dualityMap hn L p 0 h).hom.toAddMonoidHom
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom
      (o.compactSupportCohomologyMayerVietorisToBiprod_dualityMap hn L h U V) x).symm)
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom
      (o.compactSupportCohomologyMayerVietorisFromBiprod_dualityMap hn L h U V) x).symm)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.compactSupportCohomologyMayerVietoris_exact₂ ℤₘ ℤ L U V hUV p))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.mayerVietoris_exact₂ L U.isOpen V.isOpen hUV' 0))
    hW.2 (ModuleCat.bijective_biprod_map _ _ hU hV) hf₂
    ((ModuleCat.epi_iff_surjective _).1 (TopCat.epi_mayerVietorisFromBiprod_zero L hUV'))

end Cover

/-! ### The Mayer–Vietoris step -/

/-- **Poincaré duality for a cover by two open sets.** Let `M` be the union of open sets `U` and
`V`, each with the orientation restricted from `M`. If the duality maps of `U`, `V` and `U ∩ V`
are bijective in every degree, then the duality map `Hᵖ_c(M; L) ⟶ H_q(M; L)` is bijective. -/
theorem bijective_dualityMap_of_sup_eq_top' {U V : Opens M} (hUV : U ⊔ V = ⊤)
    (hU : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h))
    (hV : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap V.isOpenEmbedding').dualityMap hn L p q h))
    (hW : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap (U ⊓ V).isOpenEmbedding').dualityMap hn L p q h))
    {p q : ℕ} (h : p + q = n) :
    Function.Bijective (o.dualityMap hn L p q h) := by
  -- The steps above are stated for `Opens (TopCat.of M)`, which is `Opens M`, and for
  -- `Opens.isOpenEmbedding U`, which presents the same embedding as `U.isOpenEmbedding'`; so the
  -- hypotheses apply to them as they stand.
  cases q with
  | zero =>
    obtain rfl : p = n := by omega
    exact o.bijective_dualityMap_zero hn L hUV h (hU _ _ h) (hV _ _ h) (hW _ _ h)
      (TopCat.isZero_compactSupportCohomology_of_chartedSpace_int (F := E) (M := ↥(U ⊓ V)) L
        (by omega))
  | succ q =>
    exact o.bijective_dualityMap_succ hn L hUV h (hU _ _ h) (hV _ _ h) (hW _ _ h) (hU _ _ _)
      (hV _ _ _) (hW _ _ _)

/-- **Poincaré duality for the union of two open sets.** For open sets `U` and `V` of `M`, each
with the orientation restricted from `M`: if the duality maps of `U`, `V` and `U ∩ V` are
bijective in every degree, then the duality map of `U ∪ V` is bijective. -/
theorem bijective_dualityMap_comap_sup' {U V : Opens M}
    (hU : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h))
    (hV : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap V.isOpenEmbedding').dualityMap hn L p q h))
    (hW : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap (U ⊓ V).isOpenEmbedding').dualityMap hn L p q h))
    {p q : ℕ} (h : p + q = n) :
    Function.Bijective ((o.comap (U ⊔ V).isOpenEmbedding').dualityMap hn L p q h) := by
  let i : C(↥(U ⊔ V), M) := ⟨Subtype.val, continuous_subtypeVal⟩
  have hle : U ⊓ V ≤ U ⊔ V := inf_le_left.trans le_sup_left
  refine (o.comap (U ⊔ V).isOpenEmbedding').bijective_dualityMap_of_sup_eq_top' hn L
    (U := Opens.comap i U) (V := Opens.comap i V) ?_ (fun p q h ↦ ?_) (fun p q h ↦ ?_) ?_ h
  · exact Opens.comap_val_sup_comap_val_eq_top U V
  · rw [comap_comap]
    exact (o.bijective_dualityMap_comap_iff_of_range_eq hn L h _ _
      (by rw [Opens.range_val_comp_val_comap le_sup_left, Subtype.range_coe])).2 (hU p q h)
  · rw [comap_comap]
    exact (o.bijective_dualityMap_comap_iff_of_range_eq hn L h _ _
      (by rw [Opens.range_val_comp_val_comap le_sup_right, Subtype.range_coe])).2 (hV p q h)
  · rw [← map_inf]
    intro p q h
    rw [comap_comap]
    exact (o.bijective_dualityMap_comap_iff_of_range_eq hn L h _ _
      (by rw [Opens.range_val_comp_val_comap hle, Subtype.range_coe])).2 (hW p q h)

/-- **Poincaré duality over an inf-closed family of open sets.** Let `S` be a family of open sets
of `M`, closed under intersection, that covers `M`. If the duality map of every member of `S`,
with the orientation restricted from `M`, is bijective in every degree, then the duality map of
`M` is bijective. -/
theorem bijective_dualityMap_of_infClosed {S : Set (Opens M)} (hS : InfClosed S)
    (hcover : sSup S = ⊤)
    (hbase : ∀ W ∈ S, ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap W.isOpenEmbedding').dualityMap hn L p q h))
    {p q : ℕ} (h : p + q = n) : Function.Bijective (o.dualityMap hn L p q h) := by
  -- Duality in every degree passes to the finite unions of members of `S`, by Mayer–Vietoris.
  have hT (s : Finset S) : ∀ p q (h : p + q = n), Function.Bijective
      ((o.comap (s.sup Subtype.val).isOpenEmbedding').dualityMap hn L p q h) := by
    refine hS.finset_sup_induction (fun W : Opens M ↦ ∀ p q (h : p + q = n), Function.Bijective
        ((o.comap W.isOpenEmbedding').dualityMap hn L p q h)) (fun p q h ↦ ?_) hbase
      (fun V W hV hW hVW _ _ ↦ o.bijective_dualityMap_comap_sup' hn L hV hW hVW) s
    exact (o.comap _).bijective_dualityMap_of_isEmpty hn L h
  -- They form a directed family covering `M`.
  exact o.bijective_dualityMap_of_iSup_eq_top hn L h (fun _ _ hst ↦ Finset.sup_mono hst)
    (by rw [SymplecticGeometry.iSup_finset_sup_eq_iSup, ← sSup_eq_iSup', hcover]) fun s ↦ hT s p q h

end HomologicalOrientation

end TauCeti
