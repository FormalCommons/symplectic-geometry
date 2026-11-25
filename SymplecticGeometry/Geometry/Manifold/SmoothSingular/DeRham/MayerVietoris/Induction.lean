/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothSingular.DeRham.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Module
import Mathlib.Algebra.FiveLemma
import SymplecticGeometry.Algebra.Category.ModuleCat.Basic
import SymplecticGeometry.Algebra.Category.ModuleCat.Biproducts
import SymplecticGeometry.Geometry.Manifold.SmoothSingular.DeRham.Theorem
import TauCeti.Algebra.Homology.HomologySequenceBiprod
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
import TauCeti.Geometry.Manifold.Metrizable

/-!
# Test
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]

namespace deRhamCohomology

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  (U V : Opens M)

theorem exact_mayerVietoris_prod_coprod (n : ℕ) :
    Function.Exact
      ((map (I := I) (I' := I) (Opens.inclusion (le_sup_left : U ≤ U ⊔ V))
          (contMDiff_inclusion _) n).prod
        (map (I := I) (I' := I) (Opens.inclusion (le_sup_right : V ≤ U ⊔ V))
          (contMDiff_inclusion _) n))
      ((map (I := I) (I' := I) (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
          (contMDiff_inclusion _) n).coprod
        (-map (I := I) (I' := I) (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
          (contMDiff_inclusion _) n)) := by
  have hS := mayerVietorisShortComplex_shortExact (I := I) U V
  unfold mayerVietorisShortComplex at hS
  have := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (hS.biprod_homology_exact₂ n)
  simp only [deRhamComplex.homologyMap_map, HomologicalComplex.homologyMap_neg] at this
  exact Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := LinearEquiv.refl ℝ _)
    (e₂ := (ModuleCat.biprodIsoProd _ _).toLinearEquiv) (e₃ := LinearEquiv.refl ℝ _)
    (LinearMap.ext fun c ↦
      (ConcreteCategory.congr_hom (ModuleCat.biprod_lift_comp_biprodIsoProd_hom _ _) c).symm)
    (LinearMap.ext fun x ↦
      ConcreteCategory.congr_hom (ModuleCat.biprodIsoProd_hom_comp_ofHom_coprod _ _) x) this

theorem exact_mayerVietoris_coprod_mayerVietorisδ (n : ℕ) :
    Function.Exact
      ((map (I := I) (I' := I) (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
          (contMDiff_inclusion _) n).coprod
        (-map (I := I) (I' := I) (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
          (contMDiff_inclusion _) n))
      (mayerVietorisδ I U V n) := by
  have hS := mayerVietorisShortComplex_shortExact (I := I) U V
  unfold mayerVietorisShortComplex at hS
  have := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (hS.biprod_homology_exact₃ n (n + 1) rfl)
  simp only [deRhamComplex.homologyMap_map, HomologicalComplex.homologyMap_neg] at this
  exact Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := (ModuleCat.biprodIsoProd _ _).toLinearEquiv) (e₂ := LinearEquiv.refl ℝ _)
    (e₃ := LinearEquiv.refl ℝ _)
    (LinearMap.ext fun x ↦
      ConcreteCategory.congr_hom (ModuleCat.biprodIsoProd_hom_comp_ofHom_coprod _ _) x)
    (LinearMap.ext fun x ↦ by exact ConcreteCategory.congr_hom (ofHom_mayerVietorisδ U V n) x) this

theorem exact_mayerVietorisδ_mayerVietoris_prod (n : ℕ) :
    Function.Exact (mayerVietorisδ I U V n)
      ((map (I := I) (I' := I) (Opens.inclusion (le_sup_left : U ≤ U ⊔ V))
          (contMDiff_inclusion _) (n + 1)).prod
        (map (I := I) (I' := I) (Opens.inclusion (le_sup_right : V ≤ U ⊔ V))
          (contMDiff_inclusion _) (n + 1))) := by
  have hS := mayerVietorisShortComplex_shortExact (I := I) U V
  unfold mayerVietorisShortComplex at hS
  have := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (hS.biprod_homology_exact₁ n (n + 1) rfl)
  simp only [deRhamComplex.homologyMap_map] at this
  exact Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := LinearEquiv.refl ℝ _)
    (e₂ := LinearEquiv.refl ℝ _) (e₃ := (ModuleCat.biprodIsoProd _ _).toLinearEquiv)
    (LinearMap.ext fun x ↦ by exact ConcreteCategory.congr_hom (ofHom_mayerVietorisδ U V n) x)
    (LinearMap.ext fun c ↦
      (ConcreteCategory.congr_hom (ModuleCat.biprod_lift_comp_biprodIsoProd_hom _ _) c).symm) this

end deRhamCohomology

section Step

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem _root_.Diffeomorph.bijective_deRhamHom_iff {E' H' : Type} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {N : Type} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [SigmaCompactSpace N]
    [IsManifold J ∞ N] (Φ : M ≃ₘ⟮I, J⟯ N) (k : ℕ) :
    Function.Bijective (deRhamHom I M k) ↔ Function.Bijective (deRhamHom J N k) := by
  have h : ⇑(deRhamHom I M k) ∘ deRhamCohomology.equivOfDiffeomorph Φ k =
      TopCat.singularCohomologyMap (TopCat.ofHom Φ.toHomeomorph.toHomotopyEquiv.toFun) k ∘
        deRhamHom J N k :=
    funext fun c ↦ by
      rw [Function.comp_apply, deRhamCohomology.equivOfDiffeomorph_apply, deRhamHom_map]
      rfl
  have := Φ.toHomeomorph.toHomotopyEquiv.isIso_singularCohomologyMap (ModuleCat.of ℝ ℝ) ℝ
    (ModuleCat.of ℝ ℝ) k
  rw [← Function.Bijective.of_comp_iff _ (deRhamCohomology.equivOfDiffeomorph Φ k).bijective,
    ← Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso
      (TopCat.singularCohomologyMap (TopCat.ofHom Φ.toHomeomorph.toHomotopyEquiv.toFun) k))
      (deRhamHom J N k)]
  exact Eq.to_iff (congrArg Function.Bijective h)

variable {U V : Opens M} [SigmaCompactSpace U] [SigmaCompactSpace V]
  [SigmaCompactSpace (U ⊓ V : Opens M)] [SigmaCompactSpace (U ⊔ V : Opens M)]

private theorem bijective_deRhamHom_of_sup_eq_top (hUV : U ⊔ V = ⊤)
    (hU : ∀ k, Function.Bijective (deRhamHom I U k))
    (hV : ∀ k, Function.Bijective (deRhamHom I V k))
    (hUV' : ∀ k, Function.Bijective (deRhamHom I (U ⊓ V : Opens M) k)) (k : ℕ) :
    Function.Bijective (deRhamHom I (U ⊔ V : Opens M) k) := by
  obtain _ | n := k
  · exact bijective_deRhamHom_zero I _
  have hcov : (U : Set M) ∪ V = Set.univ := by rw [← Opens.coe_sup, hUV, Opens.coe_top]
  -- The inclusion of `U ⊔ V` in `M` is a homeomorphism; `e` is its inverse.
  let e : M ≃ₜ (U ⊔ V : Opens M) :=
    (Homeomorph.Set.univ M).symm.trans (Homeomorph.setCongr (by rw [hUV, Opens.coe_top]))
  let g : TopCat.of M ⟶ TopCat.of (U ⊔ V : Opens M) := TopCat.ofHom e.toHomotopyEquiv.toFun
  have hg : g ≫ TopCat.ofHom (ContinuousMap.subtypeVal ((U ⊔ V : Opens M) : Set M)) = 𝟙 _ := by
    ext; rfl
  have := e.toHomotopyEquiv.isIso_singularCohomologyMap (ModuleCat.of ℝ ℝ) ℝ
    (ModuleCat.of ℝ ℝ) (n + 1)
  -- The squares between the restrictions to `U ⊓ V`.
  have hc (m : ℕ) : TopCat.singularCohomologyMayerVietorisFromProd (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (X := TopCat.of M) U V m ∘ₗ
        (deRhamHom I U m).prodMap (deRhamHom I V m) =
      deRhamHom I (U ⊓ V : Opens M) m ∘ₗ
        (deRhamCohomology.map (I := I) (I' := I) (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
            (contMDiff_inclusion _) m).coprod
          (-deRhamCohomology.map (I := I) (I' := I) (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
            (contMDiff_inclusion _) m) := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.coprod_apply,
      LinearMap.neg_apply, ← sub_eq_add_neg, map_sub, deRhamHom_map]
    rw [TopCat.singularCohomologyMayerVietorisFromProd_apply]
    rfl
  rw [← Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso
    (TopCat.singularCohomologyMap g (n + 1)))]
  refine LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective _ _ _ _ _ _ _ _
    ((deRhamHom I U n).prodMap (deRhamHom I V n)) (deRhamHom I (U ⊓ V : Opens M) n)
    ((TopCat.singularCohomologyMap g (n + 1)).hom ∘ₗ deRhamHom I (U ⊔ V : Opens M) (n + 1))
    ((deRhamHom I U (n + 1)).prodMap (deRhamHom I V (n + 1)))
    (deRhamHom I (U ⊓ V : Opens M) (n + 1)) ?_ ?_ ?_ ?_
    (deRhamCohomology.exact_mayerVietoris_coprod_mayerVietorisδ U V n)
    (deRhamCohomology.exact_mayerVietorisδ_mayerVietoris_prod U V n)
    (deRhamCohomology.exact_mayerVietoris_prod_coprod U V (n + 1))
    (TopCat.exact_singularCohomologyMayerVietorisFromProd_δ (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (X := TopCat.of M) U.isOpen V.isOpen hcov n (n + 1))
    (TopCat.exact_singularCohomologyMayerVietorisδ_toProd (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (X := TopCat.of M) U.isOpen V.isOpen hcov n (n + 1))
    (TopCat.exact_singularCohomologyMayerVietorisToProd_fromProd (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (X := TopCat.of M) U.isOpen V.isOpen hcov (n + 1))
    ?_ (hUV' n) ?_ (hUV' (n + 1)).1
  · exact hc n
  · refine LinearMap.ext fun c ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      deRhamHom_mayerVietorisδ I hUV, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp, hg, TopCat.singularCohomologyMap_id]
    exact (ModuleCat.id_apply _ _).symm
  · refine LinearMap.ext fun c ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.prod_apply,
      Function.prod_apply, deRhamHom_map]
    rw [TopCat.singularCohomologyMayerVietorisToProd_apply, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
      ← TopCat.singularCohomologyMap_comp]
    rfl
  · exact hc (n + 1)
  · rw [LinearMap.coe_prodMap]
    exact (hU n).surjective.prodMap (hV n).surjective
  · rw [LinearMap.coe_prodMap]
    exact (hU (n + 1)).prodMap (hV (n + 1))

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
/-- An open subset `T` of an open subset `W` of `M` is diffeomorphic to the open subset `S ≤ W` of
`M` with the same points. -/
private def diffeomorphOfMemIff {W S : Opens M} (T : Opens W) (hS : S ≤ W)
    (hT : ∀ x : W, x ∈ T ↔ (x : M) ∈ S) : T ≃ₘ⟮I, I⟯ S where
  toFun x := ⟨x.val, (hT x).1 x.property⟩
  invFun y := ⟨⟨y, hS y.property⟩, (hT _).2 y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff S _).1 ?_
    exact (contMDiff_subtypeVal.comp contMDiff_subtypeVal :
      ContMDiff I I ∞ fun x : T ↦ ((x : W) : M))
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff T _).1 ((ContMDiff.subtypeVal_comp_iff W _).1 ?_)
    exact contMDiff_subtypeVal

omit [SigmaCompactSpace M] in
theorem bijective_deRhamHom_sup (hU : ∀ k, Function.Bijective (deRhamHom I U k))
    (hV : ∀ k, Function.Bijective (deRhamHom I V k))
    (hUV : ∀ k, Function.Bijective (deRhamHom I (U ⊓ V : Opens M) k)) (k : ℕ) :
    Function.Bijective (deRhamHom I (U ⊔ V : Opens M) k) := by
  -- Read `U` and `V` as open subsets `U'` and `V'` of the manifold `U ⊔ V`, which they cover.
  let U' : Opens (U ⊔ V : Opens M) := ⟨Subtype.val ⁻¹' U, U.isOpen.preimage continuous_subtypeVal⟩
  let V' : Opens (U ⊔ V : Opens M) := ⟨Subtype.val ⁻¹' V, V.isOpen.preimage continuous_subtypeVal⟩
  have hcov : U' ⊔ V' = ⊤ := eq_top_iff.2 fun x _ ↦ x.property
  have := Manifold.sigmaCompactSpace_opens I U'
  have := Manifold.sigmaCompactSpace_opens I V'
  have := Manifold.sigmaCompactSpace_opens I (U' ⊓ V')
  have := Manifold.sigmaCompactSpace_opens I (U' ⊔ V')
  refine (Diffeomorph.bijective_deRhamHom_iff
    (diffeomorphOfMemIff (U' ⊔ V') le_rfl fun x ↦ ?_) k).1
    (bijective_deRhamHom_of_sup_eq_top hcov
      (fun k ↦ (Diffeomorph.bijective_deRhamHom_iff
        (diffeomorphOfMemIff U' le_sup_left fun _ ↦ Iff.rfl) k).2 (hU k))
      (fun k ↦ (Diffeomorph.bijective_deRhamHom_iff
        (diffeomorphOfMemIff V' le_sup_right fun _ ↦ Iff.rfl) k).2 (hV k))
      (fun k ↦ (Diffeomorph.bijective_deRhamHom_iff
        (diffeomorphOfMemIff (U' ⊓ V') inf_le_sup fun _ ↦ Iff.rfl) k).2 (hUV k)) k)
  rw [hcov]
  exact iff_of_true trivial x.property

end Step

end TauCeti
