/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Module
public import TauCeti.Geometry.Manifold.DeRham.MayerVietoris
public import TauCeti.Geometry.Manifold.SmoothSingular.DeRham.Basic
public import TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris
public import TauCeti.Geometry.Manifold.SmoothSingular.SingularCohomology
public import SymplecticGeometry.Geometry.Manifold.SmoothSingular.MayerVietorisCochain
public import SymplecticGeometry.Geometry.Manifold.SmoothSingular.SmallSubcomplex

/-!
# Integration and the Mayer–Vietoris sequences

Let `U` and `V` be open subsets of a smooth manifold `M`, and `W = U ⊔ V`. This file compares
the de Rham Mayer–Vietoris sequence `Ω^•(W) ⟶ Ω^•(U) ⊞ Ω^•(V) ⟶ Ω^•(U ⊓ V)`
(`TauCeti.mayerVietorisShortComplex`) with the cochain Mayer–Vietoris sequence
(`SSet.mayerVietorisCochainShortComplex`) of the pushout square of smooth singular subcomplexes
of `U ⊓ V`, `U`, `V` and of the smooth simplices of `M` lying in `U` or in `V`
(`TauCeti.isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex`), with real
coefficients.

The map of simplicial sets `TauCeti.smallSmoothSingularSubcomplexToSup`
(`SymplecticGeometry/Geometry/Manifold/SmoothSingular/SmallSubcomplex.lean`) sends the corner of
that pushout square to the smooth singular simplices of `W`; on `U` (resp. `V`) it restricts to
the map of smooth singular subcomplexes induced by the inclusion of `U` (resp. `V`) in `W`.

Integration of forms over smooth simplices (`TauCeti.deRhamIntegration`) on `U`, `V` and `U ⊓ V`,
and on `W` followed by restriction along that map, is a morphism of short complexes
(`TauCeti.deRhamIntegrationMayerVietoris`). Both sequences take "restriction to `U` minus
restriction to `V`" for their second map, so no sign enters. The naturality of the connecting
morphism of the homology sequence then shows that integration intertwines the de Rham
Mayer–Vietoris connecting map `TauCeti.deRhamCohomology.mayerVietorisδ` with the cochain
Mayer–Vietoris connecting map `SSet.mayerVietorisCochainδ`, with sign `+1`
(`TauCeti.deRhamCohomology.ofHom_mayerVietorisδ_comp_homologyMap_deRhamIntegration`).

When `U ⊔ V = ⊤`, combining this with the comparison of the singular Mayer–Vietoris connecting map
`TopCat.singularCohomologyMayerVietorisδ` with the cochain one
(`TauCeti.singularCohomologyMayerVietorisδ_comp_homologyMap_smallSmoothSingularSubcomplex_ι`) and
with `TauCeti.homologyMap_cochainComplexMap_deRhamHom` (on smooth simplices, the de Rham
homomorphism `TauCeti.deRhamHom` is integration) shows that `TauCeti.deRhamHom` intertwines the de
Rham and the singular Mayer–Vietoris connecting maps, with sign `+1`
(`TauCeti.deRhamHom_mayerVietorisδ`). Both sides are compared after restriction to the smooth
simplices lying in `U` or in `V`, which is injective on singular cohomology by the smoothing
theorem and the theorem on small simplices (`TauCeti.smallSmoothSingularCohomologyIso`).

The restriction maps of the two Mayer–Vietoris sequences, `H^n(M) → H^n(U) × H^n(V)` and
`H^n(U) × H^n(V) → H^n(U ⊓ V)`, are pullbacks along inclusions, so the de Rham homomorphism
commutes with them by its naturality `TauCeti.deRhamHom_map`
(`TauCeti.singularCohomologyMayerVietorisToProd_deRhamHom`,
`TauCeti.singularCohomologyMayerVietorisFromProd_deRhamHom`).

The proofs about integration follow Tau Ceti's `TauCeti.smoothMayerVietorisδ_ι` and
`SSet.mayerVietorisCochainδ_naturality`, which build a morphism of short complexes and apply
`HomologicalComplex.HomologySequence.δ_naturality` in the same way.

## Main results

* `TauCeti.deRhamIntegrationMayerVietoris`: integration as a morphism from the de Rham
  Mayer–Vietoris sequence to the cochain Mayer–Vietoris sequence of small smooth simplices.
* `TauCeti.deRhamCohomology.ofHom_mayerVietorisδ_comp_homologyMap_deRhamIntegration`: integration
  commutes with the two Mayer–Vietoris connecting maps.
* `TauCeti.deRhamHom_mayerVietorisδ`: the de Rham homomorphism commutes with the de Rham and the
  singular Mayer–Vietoris connecting maps.
* `TauCeti.singularCohomologyMayerVietorisToProd_deRhamHom`,
  `TauCeti.singularCohomologyMayerVietorisFromProd_deRhamHom`: the de Rham homomorphism commutes
  with the restriction maps of the de Rham and the singular Mayer–Vietoris sequences.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18, proof of Theorem 18.14.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type} [TopologicalSpace M] [ChartedSpace H M]

section Integration

variable [IsManifold I 2 M]

/-- **Integration maps the de Rham Mayer–Vietoris sequence to small smooth cochains.** For open
sets `U` and `V` of `M`, integration over smooth simplices on `U`, on `V` and on `U ⊓ V`, and on
`U ⊔ V` followed by restriction along `TauCeti.smallSmoothSingularSubcomplexToSup`, is a morphism
from the Mayer–Vietoris short complex of de Rham complexes to the cochain Mayer–Vietoris short
complex, with real coefficients, of the pushout square
`TauCeti.isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex`. -/
def deRhamIntegrationMayerVietoris (U V : Opens M) :
    mayerVietorisShortComplex I U V ⟶
      SSet.mayerVietorisCochainShortComplex (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V).toCommSq
    where
  τ₁ := deRhamIntegration I (U ⊔ V : Opens M) ≫
    SSet.cochainComplexMap (smallSmoothSingularSubcomplexToSup I U V)
  τ₂ := biprod.map (deRhamIntegration I U) (deRhamIntegration I V)
  τ₃ := deRhamIntegration I (U ⊓ V : Opens M)
  comm₁₂ := by
    unfold mayerVietorisShortComplex
    apply biprod.hom_ext <;>
      simp [deRhamIntegration_naturality, ← SSet.cochainComplexMap_comp]
  comm₂₃ := by
    unfold mayerVietorisShortComplex
    apply biprod.hom_ext' <;>
      simp [deRhamIntegration_naturality]

/-- The first component of `TauCeti.deRhamIntegrationMayerVietoris` is integration on `U ⊔ V`
followed by restriction to the smooth simplices lying in `U` or in `V`. -/
@[simp]
theorem deRhamIntegrationMayerVietoris_τ₁ (U V : Opens M) :
    (deRhamIntegrationMayerVietoris I U V).τ₁ = deRhamIntegration I (U ⊔ V : Opens M) ≫
      SSet.cochainComplexMap (smallSmoothSingularSubcomplexToSup I U V) := (rfl)

/-- The second component of `TauCeti.deRhamIntegrationMayerVietoris` is integration on `U`
and on `V`. -/
@[simp]
theorem deRhamIntegrationMayerVietoris_τ₂ (U V : Opens M) :
    (deRhamIntegrationMayerVietoris I U V).τ₂ =
      biprod.map (deRhamIntegration I U) (deRhamIntegration I V) := (rfl)

/-- The third component of `TauCeti.deRhamIntegrationMayerVietoris` is integration on
`U ⊓ V`. -/
@[simp]
theorem deRhamIntegrationMayerVietoris_τ₃ (U V : Opens M) :
    (deRhamIntegrationMayerVietoris I U V).τ₃ = deRhamIntegration I (U ⊓ V : Opens M) := (rfl)

end Integration

namespace deRhamCohomology

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **Integration commutes with the Mayer–Vietoris connecting maps.** For open sets `U` and `V`
of `M`, the de Rham Mayer–Vietoris connecting map `H^n_dR(U ⊓ V) → H^{n+1}_dR(U ⊔ V)` followed by
integration on `U ⊔ V` and restriction to the smooth simplices lying in `U` or in `V` equals
integration on `U ⊓ V` followed by the cochain Mayer–Vietoris connecting map of the pushout square
`TauCeti.isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex`. The sign is
`+1`. -/
theorem ofHom_mayerVietorisδ_comp_homologyMap_deRhamIntegration (U V : Opens M) (n : ℕ) :
    ModuleCat.ofHom (mayerVietorisδ I U V n) ≫
        HomologicalComplex.homologyMap (deRhamIntegration I (U ⊔ V : Opens M)) (n + 1) ≫
          HomologicalComplex.homologyMap
            (SSet.cochainComplexMap (R := ModuleCat.of ℝ ℝ) (k := ℝ) (M := ModuleCat.of ℝ ℝ)
              (smallSmoothSingularSubcomplexToSup I U V)) (n + 1) =
      HomologicalComplex.homologyMap (deRhamIntegration I (U ⊓ V : Opens M)) n ≫
        SSet.mayerVietorisCochainδ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
          (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V) n
          (n + 1) := by
  rw [← HomologicalComplex.homologyMap_comp, ← deRhamIntegrationMayerVietoris_τ₁,
    ← deRhamIntegrationMayerVietoris_τ₃, ofHom_mayerVietorisδ,
    SSet.mayerVietorisCochainδ_def (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) _ n (n + 1)]
  exact HomologicalComplex.HomologySequence.δ_naturality (deRhamIntegrationMayerVietoris I U V)
    _ _ n (n + 1) rfl

end deRhamCohomology

section Restriction

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  (U V : Opens M)

/-- **The de Rham homomorphism commutes with the restrictions to `U` and `V`.** For open sets `U`
and `V` of `M` and a de Rham class `c` of `M`, the singular Mayer–Vietoris map
`H^n(M) → H^n(U) × H^n(V)`, with real coefficients, sends the de Rham homomorphism of `c` to the
pair of the de Rham homomorphisms of the restrictions of `c` to `U` and to `V`. -/
theorem singularCohomologyMayerVietorisToProd_deRhamHom [SigmaCompactSpace M]
    [SigmaCompactSpace U] [SigmaCompactSpace V] (n : ℕ) (c : deRhamCohomology I M n) :
    TopCat.singularCohomologyMayerVietorisToProd (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (X := TopCat.of M) U V n (deRhamHom I M n c) =
      (deRhamHom I U n (deRhamCohomology.map Subtype.val contMDiff_subtypeVal n c),
        deRhamHom I V n (deRhamCohomology.map Subtype.val contMDiff_subtypeVal n c)) := by
  rw [TopCat.singularCohomologyMayerVietorisToProd_apply, deRhamHom_map, deRhamHom_map]
  -- The inclusions of `U` and of `V` in `M`, as continuous maps and as smooth maps, agree.
  rfl

/-- **The de Rham homomorphism commutes with the differences of restrictions to `U ⊓ V`.** For
open sets `U` and `V` of `M`, a de Rham class `a` of `U` and a de Rham class `b` of `V`, the
singular Mayer–Vietoris map `H^n(U) × H^n(V) → H^n(U ⊓ V)`, with real coefficients, sends the
pair of the de Rham homomorphisms of `a` and `b` to the de Rham homomorphism of the difference of
the restrictions of `a` and `b` to `U ⊓ V`, which is the image of `(a, b)` under the de Rham
Mayer–Vietoris map `TauCeti.deRhamCohomology.mayerVietorisFromProd`. -/
theorem singularCohomologyMayerVietorisFromProd_deRhamHom [SigmaCompactSpace U]
    [SigmaCompactSpace V] [SigmaCompactSpace (U ⊓ V : Opens M)] (n : ℕ)
    (a : deRhamCohomology I U n) (b : deRhamCohomology I V n) :
    TopCat.singularCohomologyMayerVietorisFromProd (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (X := TopCat.of M) U V n (deRhamHom I U n a, deRhamHom I V n b) =
      deRhamHom I (U ⊓ V : Opens M) n (deRhamCohomology.mayerVietorisFromProd I U V n (a, b)) := by
  rw [TopCat.singularCohomologyMayerVietorisFromProd_apply,
    deRhamCohomology.mayerVietorisFromProd_apply, map_sub, deRhamHom_map, deRhamHom_map]
  -- The inclusions of `U ⊓ V` in `U` and in `V`, as continuous maps and as smooth maps, agree.
  rfl

end Restriction

section Singular

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {U V : Opens M} [SigmaCompactSpace (U ⊓ V : Opens M)]
  [SigmaCompactSpace (U ⊔ V : Opens M)]

/-- **The de Rham homomorphism commutes with the Mayer–Vietoris connecting maps.** Let `U` and `V`
be open sets covering `M`. For a de Rham class `c` of `U ⊓ V` in degree `n`, the de Rham
homomorphism of `U ⊔ V` sends the de Rham connecting map of `c` to the pullback along the
inclusion `U ⊔ V → M`, a homeomorphism, of the singular Mayer–Vietoris connecting map, with real
coefficients, of the de Rham homomorphism of `c`. The sign is `+1`.

The instance hypotheses on `U ⊓ V` and `U ⊔ V` always hold, by
`TauCeti.Manifold.sigmaCompactSpace_opens`. -/
theorem deRhamHom_mayerVietorisδ (hUV : U ⊔ V = ⊤) (n : ℕ)
    (c : deRhamCohomology I (U ⊓ V : Opens M) n) :
    deRhamHom I (U ⊔ V : Opens M) (n + 1) (deRhamCohomology.mayerVietorisδ I U V n c) =
      TopCat.singularCohomologyMap
        (TopCat.ofHom (ContinuousMap.subtypeVal ((U ⊔ V : Opens M) : Set M))) (n + 1)
        (TopCat.singularCohomologyMayerVietorisδ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
          U.isOpen V.isOpen (by rw [← Opens.coe_sup, hUV, Opens.coe_top]) n (n + 1) rfl
          (deRhamHom I (U ⊓ V : Opens M) n c)) := by
  -- Restriction to the smooth simplices of `M` lying in `U` or in `V` is injective on cohomology.
  have hcov : ⋃ i, ![(U : Set M), (V : Set M)] i = Set.univ := by
    rw [Set.iUnion_vecCons_pair, ← Opens.coe_sup, hUV, Opens.coe_top]
  let e := smallSmoothSingularCohomologyIso I (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) _
    (U.isOpen.vecCons V.isOpen) hcov (n + 1)
  -- Every class of `U ⊔ V` is pulled back from `M`, along the inverse of the inclusion.
  let g : TopCat.of M ⟶ TopCat.of (U ⊔ V : Opens M) :=
    TopCat.ofHom ⟨fun x ↦ ⟨x, by simp [hUV]⟩, by fun_prop⟩
  have hg : TopCat.ofHom (ContinuousMap.subtypeVal ((U ⊔ V : Opens M) : Set M)) ≫ g = 𝟙 _ := by
    -- Both sides send a point `x` of `U ⊔ V` to `x`, as points of the subtype.
    ext; rfl
  have hsurj (x : (TopCat.of (U ⊔ V : Opens M)).singularCohomology (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (n + 1)) : TopCat.singularCohomologyMap
      (TopCat.ofHom (ContinuousMap.subtypeVal ((U ⊔ V : Opens M) : Set M))) (n + 1)
      (TopCat.singularCohomologyMap g (n + 1) x) = x := by
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hg,
      TopCat.singularCohomologyMap_id]
    exact ModuleCat.id_apply _ x
  rw [← hsurj (deRhamHom _ _ _ _)]
  congr 1
  apply e.toLinearEquiv.injective
  simp only [Iso.toLinearEquiv_apply, e, smallSmoothSingularCohomologyIso_hom]
  have h1 := ConcreteCategory.congr_hom
    (deRhamCohomology.ofHom_mayerVietorisδ_comp_homologyMap_deRhamIntegration I U V n) c
  have h2 := ConcreteCategory.congr_hom
    (singularCohomologyMayerVietorisδ_comp_homologyMap_smallSmoothSingularSubcomplex_ι I
      (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) hUV n (n + 1))
      (deRhamHom I (U ⊓ V : Opens M) n c)
  simp only [ConcreteCategory.comp_apply, deRhamCohomology.homologyMap_deRhamIntegration,
    ModuleCat.hom_ofHom, homologyMap_cochainComplexMap_deRhamHom] at h1 h2 ⊢
  rw [h2, ← h1, ← singularCohomologyMap_subtypeVal_comp_smallSmoothSingularSubcomplexToSup]
  simp only [ConcreteCategory.comp_apply]
  rw [hsurj, homologyMap_cochainComplexMap_deRhamHom]

end Singular

end TauCeti
