/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.FiveLemma
public import SymplecticGeometry.Algebra.Category.ModuleCat.Basic
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.MayerVietoris.Basic
public import SymplecticGeometry.AlgebraicTopology.Cohomology.CompactSupport.Duality.MayerVietoris

/-!
# Poincaré duality for a union of two open sets

Fix a boundaryless `n`-manifold `M` with a homological orientation `o`, an abelian group `L`, and
give every open set of `M` the restricted orientation. This file proves the Mayer–Vietoris step of
Poincaré duality: if the duality maps `D : Hᵖ_c(-; L) ⟶ H_q(-; L)`, `p + q = n`, of open sets `U`,
`V` and `U ∩ V` are bijective in every degree, and `Hⁿ⁺¹_c(U ∩ V; L) = 0`, then the duality map of
`U ∪ V` is bijective in every degree.

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
`Hⁿ⁺¹_c(U ∩ V; L)` to vanish. That vanishing is part of the inductive hypothesis of Hatcher's
argument, where `D` is defined in all degrees with `H_q = 0` for `q < 0`. It is a hypothesis of
the theorems here, and `TopCat.isZero_compactSupportCohomology_of_sup_eq_top` and
`TopCat.isZero_compactSupportCohomology_sup` carry it from `U`, `V` and `U ∩ V` to `U ∪ V`.

## Main results

* `TauCeti.HomologicalOrientation.bijective_dualityMap_of_sup_eq_top`: for open sets `U` and `V`
  covering `M`, the step from `U`, `V` and `U ∩ V` to `M`.
* `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup`: for any open sets `U` and `V`
  of `M`, the step from `U`, `V` and `U ∩ V` to `U ∪ V`.
* `TopCat.isZero_compactSupportCohomology_of_sup_eq_top` and
  `TopCat.isZero_compactSupportCohomology_sup`: vanishing of cohomology with compact supports
  passes along the same step.

## Implementation notes

The theorems are stated for `Opens M` and the embeddings `Opens.isOpenEmbedding'`, as Tau Ceti's
disjoint case `TauCeti.HomologicalOrientation.bijective_dualityMap_of_disjoint` is, while the steps
of the proof use open sets of `TopCat.of M`, as Tau Ceti's Mayer–Vietoris squares do.

The proof of `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup` adapts that of Tau
Ceti's `TauCeti.HomologicalOrientation.bijective_dualityMap_comap_sup_of_disjoint`: it applies the
form for a cover inside `U ∪ V`. The private lemma `bijective_dualityMap_comap_comap_iff` that it
uses is Tau Ceti's private lemma of that name, with its proof, in
`TauCeti/AlgebraicTopology/Cohomology/CompactSupport/Duality/Basic.lean`, which is not visible
outside that file.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, Lemma 3.36,
  the step from `U`, `V` and `U ∩ V` to `U ∪ V`.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opens

universe v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] (R : C) (k : Type v)
  [Ring k] [Linear k C] (N : C)

section

variable {X : TopCat.{v}} [T2Space X]

/-- **Vanishing of cohomology with compact supports along a cover by two open sets.** If `X` is
the union of open sets `U` and `V` with `Hᵐ_c(U) = 0`, `Hᵐ_c(V) = 0` and `Hᵐ⁺¹_c(U ∩ V) = 0`, then
`Hᵐ_c(X) = 0`. -/
theorem isZero_compactSupportCohomology_of_sup_eq_top {U V : Opens X} (hUV : U ⊔ V = ⊤) {m : ℕ}
    (hU : IsZero (((Opens.toTopCat X).obj U).compactSupportCohomology R k N m))
    (hV : IsZero (((Opens.toTopCat X).obj V).compactSupportCohomology R k N m))
    (hW : IsZero (((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k N (m + 1))) :
    IsZero (X.compactSupportCohomology R k N m) :=
  (compactSupportCohomologyMayerVietoris_exact₃ R k N U V hUV m (m + 1)).isZero_X₂
    (((biprod_isZero_iff _ _).2 ⟨hU, hV⟩).eq_of_src _ _) (hW.eq_of_tgt _ _)

end

/-- Cohomology with compact supports vanishes on a Hausdorff space exactly when it vanishes on a
homeomorphic one. -/
theorem isZero_compactSupportCohomology_iff_of_homeomorph {A B : Type v} [TopologicalSpace A]
    [TopologicalSpace B] [T2Space A] [T2Space B] (e : A ≃ₜ B) (m : ℕ) :
    IsZero ((of A).compactSupportCohomology R k N m) ↔
      IsZero ((of B).compactSupportCohomology R k N m) := by
  have : IsIso (ofHom (e : C(A, B))) := (isIso_iff_isHomeomorph _).2 e.isHomeomorph
  let φ := compactSupportCohomologyExtend (R := R) (k := k) (M := N)
    (f := ofHom (e : C(A, B))) e.isOpenEmbedding m
  have : IsIso φ := isIso_compactSupportCohomologyExtend _ m
  exact ⟨fun h ↦ h.of_iso (asIso φ).symm, fun h ↦ h.of_iso (asIso φ)⟩

variable {X : Type v} [TopologicalSpace X] [T2Space X]

/-- Cohomology with compact supports of an open set `W ≤ Y` of a Hausdorff space `X` vanishes
exactly when that of `W`, read as an open set of `Y`, does. -/
theorem isZero_compactSupportCohomology_comap_iff {Y W : Opens X} (hWY : W ≤ Y) (m : ℕ) :
    IsZero ((of ↥(Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ W :
        Opens Y)).compactSupportCohomology R k N m) ↔
      IsZero ((of W).compactSupportCohomology R k N m) :=
  isZero_compactSupportCohomology_iff_of_homeomorph R k N
    { toFun x := ⟨x.val.val, x.property⟩
      invFun y := ⟨⟨y.val, hWY y.property⟩, y.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop } m

/-- **Vanishing of cohomology with compact supports for a union of two open sets.** For open sets
`U` and `V` of a Hausdorff space with `Hᵐ_c(U) = 0`, `Hᵐ_c(V) = 0` and `Hᵐ⁺¹_c(U ∩ V) = 0`, also
`Hᵐ_c(U ∪ V) = 0`. -/
theorem isZero_compactSupportCohomology_sup {U V : Opens X} {m : ℕ}
    (hU : IsZero ((of U).compactSupportCohomology R k N m))
    (hV : IsZero ((of V).compactSupportCohomology R k N m))
    (hW : IsZero ((of ↥(U ⊓ V)).compactSupportCohomology R k N (m + 1))) :
    IsZero ((of ↥(U ⊔ V)).compactSupportCohomology R k N m) := by
  let i : C(↥(U ⊔ V), X) := ⟨Subtype.val, continuous_subtypeVal⟩
  refine isZero_compactSupportCohomology_of_sup_eq_top R k N
    (X := of ↥(U ⊔ V)) (U := Opens.comap i U) (V := Opens.comap i V) ?_
    ((isZero_compactSupportCohomology_comap_iff R k N le_sup_left m).2 hU)
    ((isZero_compactSupportCohomology_comap_iff R k N le_sup_right m).2 hV) ?_
  · rw [← map_sup, eq_top_iff]
    exact fun x _ ↦ x.property
  · rw [← map_inf]
    exact (isZero_compactSupportCohomology_comap_iff R k N
      (inf_le_left.trans le_sup_left) (m + 1)).2 hW

end TopCat

namespace TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : Module.finrank ℝ E = n) (L : ModuleCat.{0} ℤ)

local notation "ℤₘ" => ModuleCat.of ℤ (ULift ℤ : Type)

/-- The duality map of an open set `U ≤ W` of `M` is bijective exactly when that of `U`, read as an
open set of `W` with the orientation restricted from `W`, is. -/
private lemma bijective_dualityMap_comap_comap_iff {p q : ℕ} (h : p + q = n) {U W : Opens M}
    (hUW : U ≤ W) :
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

section Cover

/-! ### The five lemma on the Mayer–Vietoris ladder

The steps are stated for open sets of `TopCat.of M`, as Tau Ceti's Mayer–Vietoris squares are. -/

variable {U V : Opens (TopCat.of M)} (hUV : U ⊔ V = ⊤)

include hUV in
/-- Below the top degree, `D_M` is surjective. -/
private lemma surjective_dualityMap_succ {p q : ℕ} (h : p + (q + 1) = n)
    (hU : Function.Bijective ((o.comap U.isOpenEmbedding).dualityMap hn L p (q + 1) h))
    (hV : Function.Bijective ((o.comap V.isOpenEmbedding).dualityMap hn L p (q + 1) h))
    (hU' : Function.Bijective ((o.comap U.isOpenEmbedding).dualityMap hn L (p + 1) q (by omega)))
    (hV' : Function.Bijective ((o.comap V.isOpenEmbedding).dualityMap hn L (p + 1) q (by omega)))
    (hW' : Function.Bijective
      ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L (p + 1) q (by omega))) :
    Function.Surjective (o.dualityMap hn L p (q + 1) h) := by
  have hUV' : (U : Set (TopCat.of M)) ∪ V = Set.univ := by
    simpa only [← Opens.coe_sup, hUV] using Opens.coe_top
  have hc₄ := o.compactSupportCohomologyMayerVietorisToBiprod_dualityMap hn L
    (show p + 1 + q = n by omega) U V
  refine AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
    (TopCat.compactSupportCohomologyMayerVietorisFromBiprod ℤₘ ℤ L U V p).hom.toAddMonoidHom
    (TopCat.compactSupportCohomologyMayerVietorisδ ℤₘ ℤ L U V hUV p (p + 1)
      rfl).hom.toAddMonoidHom
    (TopCat.compactSupportCohomologyMayerVietorisToBiprod ℤₘ ℤ L U V
      (p + 1)).hom.toAddMonoidHom
    (SSet.mayerVietorisFromBiprod L (TopCat.toSSet.map (Opens.inclusion' U))
      (TopCat.toSSet.map (Opens.inclusion' V)) (q + 1)).hom.toAddMonoidHom
    (TopCat.mayerVietorisδ L U.isOpen V.isOpen hUV' (q + 1) q rfl).hom.toAddMonoidHom
    (SSet.mayerVietorisToBiprod L
      (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_left)))
      (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_right)))
        q).hom.toAddMonoidHom
    (biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p (q + 1) h)
      ((o.comap V.isOpenEmbedding).dualityMap hn L p (q + 1) h)).hom.toAddMonoidHom
    (o.dualityMap hn L p (q + 1) h).hom.toAddMonoidHom
    (((-1 : ℤ) ^ (p + 1)) • (o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L (p + 1) q
      (by omega)).hom.toAddMonoidHom
    (((-1 : ℤ) ^ (p + 1)) • biprod.map
      ((o.comap U.isOpenEmbedding).dualityMap hn L (p + 1) q (by omega))
      ((o.comap V.isOpenEmbedding).dualityMap hn L (p + 1) q (by omega))).hom.toAddMonoidHom
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom
      (o.compactSupportCohomologyMayerVietorisFromBiprod_dualityMap hn L h U V) x).symm)
    (AddMonoidHom.ext fun x ↦ ConcreteCategory.congr_hom
      (o.dualityMap_mayerVietorisδ L hn U V hUV p q h) x)
    (AddMonoidHom.ext fun x ↦ ?_)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.compactSupportCohomologyMayerVietoris_exact₁ ℤₘ ℤ L U V hUV p (p + 1) rfl))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.mayerVietoris_exact₃ L U.isOpen V.isOpen hUV' (q + 1) q rfl))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.mayerVietoris_exact₁ L U.isOpen V.isOpen hUV' (q + 1) q rfl))
    (ModuleCat.bijective_biprod_map _ _ hU hV).2
    ((ModuleCat.bijective_zsmul_iff _ (isUnit_neg_one.pow _)).2 hW').2
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
/-- Below the top degree, `D_M` is injective. -/
private lemma injective_dualityMap_succ {p q : ℕ} (h : p + (q + 1) = n)
    (hU : Function.Bijective ((o.comap U.isOpenEmbedding).dualityMap hn L p (q + 1) h))
    (hV : Function.Bijective ((o.comap V.isOpenEmbedding).dualityMap hn L p (q + 1) h))
    (hW : Function.Bijective ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L p (q + 1) h))
    (hW' : Function.Bijective
      ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L (p + 1) q (by omega))) :
    Function.Injective (o.dualityMap hn L p (q + 1) h) := by
  have hUV' : (U : Set (TopCat.of M)) ∪ V = Set.univ := by
    simpa only [← Opens.coe_sup, hUV] using Opens.coe_top
  exact AddMonoidHom.injective_of_surjective_of_injective_of_injective
    (TopCat.compactSupportCohomologyMayerVietorisToBiprod ℤₘ ℤ L U V p).hom.toAddMonoidHom
    (TopCat.compactSupportCohomologyMayerVietorisFromBiprod ℤₘ ℤ L U V p).hom.toAddMonoidHom
    (TopCat.compactSupportCohomologyMayerVietorisδ ℤₘ ℤ L U V hUV p (p + 1)
      rfl).hom.toAddMonoidHom
    (SSet.mayerVietorisToBiprod L
      (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_left)))
      (TopCat.toSSet.map ((Opens.toTopCat (TopCat.of M)).map (homOfLE inf_le_right)))
        (q + 1)).hom.toAddMonoidHom
    (SSet.mayerVietorisFromBiprod L (TopCat.toSSet.map (Opens.inclusion' U))
      (TopCat.toSSet.map (Opens.inclusion' V)) (q + 1)).hom.toAddMonoidHom
    (TopCat.mayerVietorisδ L U.isOpen V.isOpen hUV' (q + 1) q rfl).hom.toAddMonoidHom
    ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L p (q + 1) h).hom.toAddMonoidHom
    (biprod.map ((o.comap U.isOpenEmbedding).dualityMap hn L p (q + 1) h)
      ((o.comap V.isOpenEmbedding).dualityMap hn L p (q + 1) h)).hom.toAddMonoidHom
    (o.dualityMap hn L p (q + 1) h).hom.toAddMonoidHom
    (((-1 : ℤ) ^ (p + 1)) • (o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L (p + 1) q
      (by omega)).hom.toAddMonoidHom
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom
      (o.compactSupportCohomologyMayerVietorisToBiprod_dualityMap hn L h U V) x).symm)
    (AddMonoidHom.ext fun x ↦ (ConcreteCategory.congr_hom
      (o.compactSupportCohomologyMayerVietorisFromBiprod_dualityMap hn L h U V) x).symm)
    (AddMonoidHom.ext fun x ↦ ConcreteCategory.congr_hom
      (o.dualityMap_mayerVietorisδ L hn U V hUV p q h) x)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.compactSupportCohomologyMayerVietoris_exact₂ ℤₘ ℤ L U V hUV p))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.compactSupportCohomologyMayerVietoris_exact₃ ℤₘ ℤ L U V hUV p (p + 1) rfl))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.mayerVietoris_exact₂ L U.isOpen V.isOpen hUV' (q + 1)))
    hW.2 (ModuleCat.bijective_biprod_map _ _ hU hV).1
    ((ModuleCat.bijective_zsmul_iff _ (isUnit_neg_one.pow _)).2 hW').1

include hUV in
/-- In the top degree, `D_M : Hⁿ_c(M) ⟶ H₀(M)` is surjective. -/
private lemma surjective_dualityMap_zero {p : ℕ} (h : p + 0 = n)
    (hU : Function.Bijective ((o.comap U.isOpenEmbedding).dualityMap hn L p 0 h))
    (hV : Function.Bijective ((o.comap V.isOpenEmbedding).dualityMap hn L p 0 h)) :
    Function.Surjective (o.dualityMap hn L p 0 h) := by
  have hUV' : (U : Set (TopCat.of M)) ∪ V = Set.univ := by
    simpa only [← Opens.coe_sup, hUV] using Opens.coe_top
  have := TopCat.epi_mayerVietorisFromBiprod_zero L hUV'
  intro y
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 this y
  obtain ⟨w, rfl⟩ := (ModuleCat.bijective_biprod_map _ _ hU hV).2 z
  exact ⟨_, ConcreteCategory.congr_hom
    (o.compactSupportCohomologyMayerVietorisFromBiprod_dualityMap hn L h U V) w⟩

include hUV in
/-- In the top degree, `D_M : Hⁿ_c(M) ⟶ H₀(M)` is injective, given `Hⁿ⁺¹_c(U ∩ V) = 0`. -/
private lemma injective_dualityMap_zero {p : ℕ} (h : p + 0 = n)
    (hU : Function.Bijective ((o.comap U.isOpenEmbedding).dualityMap hn L p 0 h))
    (hV : Function.Bijective ((o.comap V.isOpenEmbedding).dualityMap hn L p 0 h))
    (hW : Function.Bijective ((o.comap (U ⊓ V).isOpenEmbedding).dualityMap hn L p 0 h))
    (hW₀ : IsZero (((Opens.toTopCat (TopCat.of M)).obj (U ⊓ V)).compactSupportCohomology ℤₘ ℤ L
      (p + 1))) :
    Function.Injective (o.dualityMap hn L p 0 h) := by
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
  exact AddMonoidHom.injective_of_surjective_of_injective_of_right_exact
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
    hW.2 (ModuleCat.bijective_biprod_map _ _ hU hV).1 hf₂

end Cover

/-! ### The Mayer–Vietoris step -/

/-- **Poincaré duality for a cover by two open sets.** Let `M` be the union of open sets `U` and
`V`, each with the orientation restricted from `M`. If the duality maps of `U`, `V` and `U ∩ V`
are bijective in every degree, and `Hⁿ⁺¹_c(U ∩ V; L) = 0`, then the duality map
`Hᵖ_c(M; L) ⟶ H_q(M; L)` is bijective. -/
theorem bijective_dualityMap_of_sup_eq_top {U V : Opens M} (hUV : U ⊔ V = ⊤)
    (hU : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h))
    (hV : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap V.isOpenEmbedding').dualityMap hn L p q h))
    (hW : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap (U ⊓ V).isOpenEmbedding').dualityMap hn L p q h))
    (hW₀ : IsZero ((TopCat.of ↥(U ⊓ V)).compactSupportCohomology ℤₘ ℤ L (n + 1)))
    {p q : ℕ} (h : p + q = n) :
    Function.Bijective (o.dualityMap hn L p q h) := by
  -- The steps above are stated for `Opens (TopCat.of M)`, which is `Opens M`, and for
  -- `Opens.isOpenEmbedding U`, which presents the same embedding as `U.isOpenEmbedding'`; so the
  -- hypotheses apply to them as they stand.
  cases q with
  | zero =>
    obtain rfl : p = n := by omega
    exact ⟨o.injective_dualityMap_zero hn L hUV h (hU _ _ h) (hV _ _ h) (hW _ _ h) hW₀,
      o.surjective_dualityMap_zero hn L hUV h (hU _ _ h) (hV _ _ h)⟩
  | succ q =>
    exact ⟨o.injective_dualityMap_succ hn L hUV h (hU _ _ h) (hV _ _ h) (hW _ _ h) (hW _ _ _),
      o.surjective_dualityMap_succ hn L hUV h (hU _ _ h) (hV _ _ h) (hU _ _ _) (hV _ _ _)
        (hW _ _ _)⟩

/-- **Poincaré duality for the union of two open sets.** For open sets `U` and `V` of `M`, each
with the orientation restricted from `M`: if the duality maps of `U`, `V` and `U ∩ V` are
bijective in every degree, and `Hⁿ⁺¹_c(U ∩ V; L) = 0`, then the duality map of `U ∪ V` is
bijective. -/
theorem bijective_dualityMap_comap_sup {U V : Opens M}
    (hU : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap U.isOpenEmbedding').dualityMap hn L p q h))
    (hV : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap V.isOpenEmbedding').dualityMap hn L p q h))
    (hW : ∀ p q (h : p + q = n),
      Function.Bijective ((o.comap (U ⊓ V).isOpenEmbedding').dualityMap hn L p q h))
    (hW₀ : IsZero ((TopCat.of ↥(U ⊓ V)).compactSupportCohomology ℤₘ ℤ L (n + 1)))
    {p q : ℕ} (h : p + q = n) :
    Function.Bijective ((o.comap (U ⊔ V).isOpenEmbedding').dualityMap hn L p q h) := by
  let i : C(↥(U ⊔ V), M) := ⟨Subtype.val, continuous_subtypeVal⟩
  have hle : U ⊓ V ≤ U ⊔ V := inf_le_left.trans le_sup_left
  refine (o.comap (U ⊔ V).isOpenEmbedding').bijective_dualityMap_of_sup_eq_top hn L
    (U := Opens.comap i U) (V := Opens.comap i V) ?_
    (fun p q h ↦ (o.bijective_dualityMap_comap_comap_iff hn L h le_sup_left).2 (hU p q h))
    (fun p q h ↦ (o.bijective_dualityMap_comap_comap_iff hn L h le_sup_right).2 (hV p q h))
    ?_ ?_ h
  · rw [← map_sup, eq_top_iff]
    exact fun x _ ↦ x.property
  · rw [← map_inf]
    exact fun p q h ↦ (o.bijective_dualityMap_comap_comap_iff hn L h hle).2 (hW p q h)
  · rw [← map_inf]
    exact (TopCat.isZero_compactSupportCohomology_comap_iff _ _ _ hle _).2 hW₀

end HomologicalOrientation

end TauCeti
