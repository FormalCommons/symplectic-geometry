/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Relative.SingularCohomology
import all TauCeti.Geometry.Manifold.DeRham.Relative.Basic
import all TauCeti.Geometry.Manifold.DeRham.Relative.Integration
import all TauCeti.Geometry.Manifold.DeRham.Relative.SingularCohomology

/-!
# Naturality of the relative de Rham homomorphism

Let `f : M → M'` be a smooth map carrying an open subset `W` of `M` into an open subset `W'` of
`M'`, with restriction `g : W → W'`. This file shows that the relative de Rham homomorphism
`TauCeti.relativeDeRhamHom` commutes with the pullbacks along `f` of relative de Rham cohomology
(the map on cohomology of `TauCeti.relativeDeRhamComplex.map`) and of relative singular
cohomology (`TopPair.singularCohomologyMap`).

The proof passes through three commutative squares.

1. Precomposition with the maps of smooth singular simplices induced by `f` and by its restriction
   `W → W'` commutes with the restriction of smooth cochains, and so induces a map of the mapping
   cocones of restriction, `TauCeti.relativeSmoothCochainComplex.map`. Relative integration
   `TauCeti.relativeDeRhamIntegration` intertwines it with `TauCeti.relativeDeRhamComplex.map`
   (`TauCeti.relativeDeRhamComplex.map_comp_relativeDeRhamIntegration`); this follows from the
   naturality `TauCeti.deRhamIntegration_naturality` of integration, as
   `TauCeti.deRhamRestriction_comp_extendMap_deRhamIntegration` does.
2. The lift `TauCeti.relativeSmoothCochainLift` of relative smooth cochains to the cocone
   intertwines it with the pullback of relative smooth cochains along the map of smooth singular
   pairs `TauCeti.smoothSingularPairMap`
   (`TauCeti.relativeSmoothCochainLift_comp_relativeSmoothCochainComplexMap`). Together with the
   first square this makes relative integration on cohomology natural
   (`TauCeti.relativeDeRhamCohomology.integration_naturality`).
3. The relative smoothing isomorphism is natural
   (`TauCeti.smoothSingularRelativeCohomologyIso_inv_naturality`).

The final step follows the proof of the absolute statement `TauCeti.deRhamHom_map`. The proof of
the first square composes the squares of mapping cones under the shift `⟦-1⟧`, as the proof of
Tau Ceti's `TauCeti.relativeDeRhamComplex.map_comp` does.

The cochain maps `TauCeti.relativeDeRhamComplex.map`, `TauCeti.relativeDeRhamIntegration` and
`TauCeti.relativeSmoothCochainLift`, and the isomorphism `TauCeti.relativeSmoothCohomologyIso`, are
not exposed by their Tau Ceti modules, so this file imports those modules with `import all` to
unfold them. It also takes the smoothness of the restriction `g` from the private Tau Ceti lemma
`relativeDeRhamComplex.contMDiff_of_val_comp`.

## Main results

* `TauCeti.relativeDeRhamCohomology.integration_naturality`: relative integration on cohomology
  commutes with pullback along smooth maps of open pairs.
* `TauCeti.relativeDeRhamHom_map`: naturality of the relative de Rham homomorphism.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982, Chapter I, §6.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18.
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex TopologicalSpace
open scoped ContDiff

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M] {W : Opens M}
  {E' H' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {M' : Type} [TopologicalSpace M'] [ChartedSpace H' M']
  {W' : Opens M'} {f : M → M'}

/-- Pullback of smooth cochains along a smooth map `f : M → M'` commutes with their restriction
to open subsets `W` and `W'`, given a smooth `g : W → W'` with `g x = f x`. -/
@[reassoc]
theorem smoothCochainRestriction_comp_extendMap_cochainComplexMap {g : W → W'}
    (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g) (hfg : ∀ x, (g x : M') = f x) :
    smoothCochainRestriction I' W' ≫ extendMap (SSet.cochainComplexMap
        (smoothSingularSubcomplexMap g hg)) ComplexShape.embeddingUpNat =
      extendMap (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf))
          ComplexShape.embeddingUpNat ≫ smoothCochainRestriction I W := by
  rw [smoothCochainRestriction_def, smoothCochainRestriction_def, ← extendMap_comp,
    ← extendMap_comp, ← SSet.cochainComplexMap_comp, ← SSet.cochainComplexMap_comp,
    ← smoothSingularSubcomplexMap_comp, ← smoothSingularSubcomplexMap_comp]
  congr 3
  exact funext hfg

namespace relativeSmoothCochainComplex

/-- The map of mapping cocones of the restriction of smooth cochains induced by a smooth map
`f : (M, W) → (M', W')` of open pairs, given with its smooth restriction `g : W → W'`: pullback of
smooth cochains along `f` and along `g`. -/
def map {g : W → W'} (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g)
    (hfg : ∀ x, (g x : M') = f x) :
    relativeSmoothCochainComplex I' W' ⟶ relativeSmoothCochainComplex I W :=
  (CochainComplex.mappingCone.map _ _ _ _
    (smoothCochainRestriction_comp_extendMap_cochainComplexMap hf hg hfg))⟦(-1 : ℤ)⟧'

/-- The map of cocones induced by a smooth map of open pairs commutes with the first projections:
on the first component it is pullback of smooth cochains along `f`. -/
@[reassoc (attr := simp)]
theorem map_fst {g : W → W'} (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g)
    (hfg : ∀ x, (g x : M') = f x) :
    map hf hg hfg ≫ CochainComplex.mappingCocone.fst (smoothCochainRestriction I W) =
      CochainComplex.mappingCocone.fst (smoothCochainRestriction I' W') ≫
        extendMap (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf))
          ComplexShape.embeddingUpNat :=
  CochainComplex.mappingCocone.shiftFunctor_map_mappingCone_map_comp_fst _ _ _ _ _

/-- The map of cocones induced by a smooth map of open pairs commutes with the second projections:
on the second component it is pullback of smooth cochains along the restriction `g`. -/
@[reassoc (attr := simp)]
theorem map_f_snd_v {g : W → W'} (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g)
    (hfg : ∀ x, (g x : M') = f x) (p : ℤ) :
    (map hf hg hfg).f p ≫
        (CochainComplex.mappingCocone.snd (smoothCochainRestriction I W)).v p (p + -1) rfl =
      (CochainComplex.mappingCocone.snd (smoothCochainRestriction I' W')).v p (p + -1) rfl ≫
        (extendMap (SSet.cochainComplexMap (smoothSingularSubcomplexMap g hg))
          ComplexShape.embeddingUpNat).f (p + -1) :=
  CochainComplex.mappingCocone.shiftFunctor_map_mappingCone_map_f_snd_v _ _ _ _ _ p

end relativeSmoothCochainComplex

/-- The lift of relative smooth cochains to the mapping cocone of restriction is natural in smooth
maps of open pairs: it intertwines the pullback of relative smooth cochains along the map of
smooth singular pairs with the map of cocones `TauCeti.relativeSmoothCochainComplex.map`. -/
@[reassoc]
theorem relativeSmoothCochainLift_comp_relativeSmoothCochainComplexMap {g : W → W'}
    (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g) (hfg : ∀ x, (g x : M') = f x)
    (hWW' : Set.MapsTo f W W') :
    relativeSmoothCochainLift I' W' ≫ relativeSmoothCochainComplex.map hf hg hfg =
      extendMap (SSetPair.cochainComplexMap (smoothSingularPairMap hf hWW'))
          ComplexShape.embeddingUpNat ≫ relativeSmoothCochainLift I W := by
  obtain rfl : g = hWW'.restrict f W W' := funext fun x ↦ Subtype.ext (hfg x)
  ext p : 1
  apply CochainComplex.mappingCocone.ext_to _ p (p + -1) rfl
  · -- On the first component both sides are the pullback of relative cochains, followed by
    -- their inclusion into the cochains of `M`.
    have h := congrArg (fun φ ↦ (extendMap φ ComplexShape.embeddingUpNat).f p)
      (SSetPair.cochainComplexπ_naturality (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (smoothSingularPairMap hf hWW'))
    simp only [extendMap_comp, comp_f, smoothSingularPairMap_right] at h
    simp only [Category.assoc, ← comp_f, relativeSmoothCochainComplex.map_fst,
      relativeSmoothCochainLift_fst_assoc, relativeSmoothCochainLift_fst]
    exact h
  · -- On the second component both sides vanish, since the lift has second component `0`.
    simp [relativeSmoothCochainLift]

section Integration

variable [IsManifold I 2 M] [IsManifold I' 2 M'] {g : W → W'}

/-- **Relative integration is natural.** Relative integration intertwines the pullback of
relative forms along a smooth map of open pairs with the map of cocones
`TauCeti.relativeSmoothCochainComplex.map`. -/
@[reassoc]
theorem relativeDeRhamComplex.map_comp_relativeDeRhamIntegration (hf : ContMDiff I I' ∞ f)
    (hg : ContMDiff I I' ∞ g) (hfg : ∀ x, (g x : M') = f x) :
    relativeDeRhamComplex.map I W hf hfg ≫ relativeDeRhamIntegration I W =
      relativeDeRhamIntegration I' W' ≫ relativeSmoothCochainComplex.map hf hg hfg := by
  -- Both sides are `⟦-1⟧` shifts of maps of mapping cones; compose those squares.
  unfold relativeDeRhamComplex.map relativeDeRhamIntegration relativeSmoothCochainComplex.map
    relativeDeRhamComplex relativeSmoothCochainComplex CochainComplex.mappingCocone
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  have ha : extendMap (deRhamComplex.map f hf) ComplexShape.embeddingUpNat ≫
      extendMap (deRhamIntegration I M) ComplexShape.embeddingUpNat =
        extendMap (deRhamIntegration I' M') ComplexShape.embeddingUpNat ≫
          extendMap (SSet.cochainComplexMap (smoothSingularSubcomplexMap f hf))
            ComplexShape.embeddingUpNat := by
    rw [← extendMap_comp, ← extendMap_comp, deRhamIntegration_naturality]
  have hb : extendMap (deRhamComplex.map g hg) ComplexShape.embeddingUpNat ≫
      extendMap (deRhamIntegration I W) ComplexShape.embeddingUpNat =
        extendMap (deRhamIntegration I' W') ComplexShape.embeddingUpNat ≫
          extendMap (SSet.cochainComplexMap (smoothSingularSubcomplexMap g hg))
            ComplexShape.embeddingUpNat := by
    rw [← extendMap_comp, ← extendMap_comp, deRhamIntegration_naturality]
  simp only [ha, hb]

namespace relativeDeRhamCohomology

/-- **Naturality of relative integration on cohomology.** For a smooth map `f : (M, W) → (M', W')`
of open pairs with restriction `g : W → W'`, the relative integral of the pullback of a class is
the pullback along the map of smooth singular pairs of its relative integral. -/
theorem integration_naturality (hf : ContMDiff I I' ∞ f) (hfg : ∀ x, (g x : M') = f x)
    (hWW' : Set.MapsTo f W W') (n : ℕ) (x : relativeDeRhamCohomology I' W' n) :
    integration I W n (homologyMap (relativeDeRhamComplex.map I W hf hfg) n x) =
      homologyMap (SSetPair.cochainComplexMap (smoothSingularPairMap hf hWW')) n
        (integration I' W' n x) := by
  have hg := relativeDeRhamComplex.contMDiff_of_val_comp I W hf hfg
  -- The lift of relative smooth cochains intertwines the two pullbacks on cohomology.
  have hℓ : homologyMap (relativeSmoothCochainComplex.map hf hg hfg) n ≫
      inv (homologyMap (relativeSmoothCochainLift I W) n) =
        inv (homologyMap (relativeSmoothCochainLift I' W') n) ≫
          homologyMap (extendMap (SSetPair.cochainComplexMap (R := ModuleCat.of ℝ ℝ) (k := ℝ)
            (M := ModuleCat.of ℝ ℝ) (smoothSingularPairMap hf hWW'))
              ComplexShape.embeddingUpNat) n := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq, ← homologyMap_comp,
      ← homologyMap_comp, relativeSmoothCochainLift_comp_relativeSmoothCochainComplexMap hf hg hfg]
  have h : homologyMap (relativeDeRhamComplex.map I W hf hfg) n ≫
      homologyMap (relativeDeRhamIntegration I W) n ≫ (relativeSmoothCohomologyIso I W n).hom =
        (homologyMap (relativeDeRhamIntegration I' W') n ≫
          (relativeSmoothCohomologyIso I' W' n).hom) ≫
            homologyMap (SSetPair.cochainComplexMap (smoothSingularPairMap hf hWW')) n := by
    rw [← homologyMap_comp_assoc,
      relativeDeRhamComplex.map_comp_relativeDeRhamIntegration hf hg hfg, homologyMap_comp,
      Category.assoc, Category.assoc]
    congr 1
    simp only [relativeSmoothCohomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
      reassoc_of% hℓ, extendHomologyIso_hom_naturality, Category.assoc]
  -- `integration` is by definition the map on cohomology composed above.
  exact ConcreteCategory.congr_hom h x

end relativeDeRhamCohomology

end Integration

section SingularCohomology

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E'] [T2Space M'] [SigmaCompactSpace M'] [IsManifold I' ∞ M'] {g : W → W'}

/-- **Naturality of the relative de Rham homomorphism.** For a smooth map `f : (M, W) → (M', W')`
of open pairs with restriction `g : W → W'`, the relative de Rham homomorphism of the pullback of a
relative de Rham class is the pullback in relative singular cohomology of its relative de Rham
homomorphism. This is the relative form of `TauCeti.deRhamHom_map`. -/
theorem relativeDeRhamHom_map (hf : ContMDiff I I' ∞ f) (hfg : ∀ x, (g x : M') = f x)
    (hWW' : Set.MapsTo f W W') (n : ℕ) (x : relativeDeRhamCohomology I' W' n) :
    relativeDeRhamHom I W n (homologyMap (relativeDeRhamComplex.map I W hf hfg) n x) =
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap (TopCat.ofHom ⟨f, hf.continuous⟩) hWW')
        n (relativeDeRhamHom I' W' n x) := by
  rw [relativeDeRhamHom_apply, relativeDeRhamCohomology.integration_naturality hf hfg hWW',
    relativeDeRhamHom_apply]
  exact ConcreteCategory.congr_hom (smoothSingularRelativeCohomologyIso_inv_naturality
    (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) hf hWW' n) _

end SingularCohomology

end TauCeti

end
