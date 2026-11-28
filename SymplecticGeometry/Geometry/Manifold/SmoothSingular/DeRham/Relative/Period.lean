/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.RelativeClass
public import SymplecticGeometry.Geometry.Manifold.SmoothSingular.RelativeCycle
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.Geometry.Manifold.DeRham.Relative.SingularCohomology
import TauCeti.Algebra.Homology.Embedding.Extend
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.Algebra.Homology.ModuleCat.LinearYoneda
import all TauCeti.Geometry.Manifold.DeRham.Relative.SingularCohomology

/-!
# Periods of the relative de Rham homomorphism

Let `W` be an open subset of a Hausdorff `σ`-compact smooth manifold `M` modelled on a
finite-dimensional real model with corners. Tau Ceti's relative de Rham homomorphism
`TauCeti.relativeDeRhamHom I W n : H^n(M, W) →ₗ[ℝ] Hⁿ(M, W; ℝ)` is relative integration
`TauCeti.relativeDeRhamCohomology.integration`, read in relative singular cohomology through the
relative smoothing theorem. This file computes its periods: the Kronecker pairing
`TopPair.singularKronecker` of `relativeDeRhamHom x` with the relative class of a smooth relative
cycle `(c, c')` (a smooth `(k + 1)`-chain `c` of `M` with `∂c = c'` a smooth chain of `W`) is
Tau Ceti's integral `TauCeti.relativeDeRhamCohomology.integral I W k hc x`, which is
`∫_c α - ∫_{c'} β` for `x = [(α, β)]`.

The proof has three steps, as Tau Ceti's `TauCeti.singularKronecker_deRhamHom_mk_apply` proves the
absolute statement.

* On the mapping cocone `TauCeti.relativeSmoothCochainComplex I W`, Tau Ceti's lift
  `TauCeti.relativeSmoothCochainLift I W` sends a relative smooth cochain `a` to `(a, 0)`
  (`TauCeti.relativeSmoothCochainLift_f_snd_v`), so the pairing
  `TauCeti.relativeSmoothCochainComplex.eval` with `(c, c')` reads `a` on the relative chain of `c`
  (`TauCeti.relativeSmoothCochainComplex.eval_relativeSmoothCochainLift_f`). The pairing only sees
  cohomology classes (`TauCeti.relativeSmoothCochainComplex.eval_eq_of_homologyπ_eq`, from
  `TauCeti.relativeSmoothCochainComplex.eval_d`), and relative integration and the lift have the
  same class (`TauCeti.relativeDeRhamCohomology.homologyMap_relativeSmoothCochainLift_integration`).
  This gives the statement in smooth relative cohomology
  (`TauCeti.relativeDeRhamCohomology.kronecker_integration_homologyπ`).
* Naturality of the Kronecker map (`TauCeti.ChainComplex.kronecker_naturality`) along the inclusion
  `TauCeti.smoothSingularPairι I W` of smooth into continuous relative chains, with
  `TauCeti.homologyMap_cochainComplexMap_relativeDeRhamHom`, passes to singular cohomology
  (`TauCeti.singularKronecker_relativeDeRhamHom_homologyMap`).
* For a smooth simplex `σ` whose faces are smooth simplices `t i` of `W`, the class
  `TopPair.relClass` of `σ` is the image of its class in the smooth singular pair
  (`TopPair.relClass_eq_of_eq_toSSet_map_app`, `SSetPair.relClass_homologyMap`), and
  `c' = ∑ i, (-1) ^ i • t i`.

Lifting a relative cochain to the cocone is the one step that needs the definition of
`TauCeti.relativeSmoothCochainLift`, which Tau Ceti does not expose; the file imports it with
`import all`.

## Main results

* `TauCeti.relativeDeRhamCohomology.kronecker_integration_homologyπ`: the relative integral of a
  class pairs with the smooth relative class of `(c, c')` to `integral I W k hc x`.
* `TauCeti.singularKronecker_relativeDeRhamHom_homologyMap`: the same for `relativeDeRhamHom` and
  the image of that class in the singular homology of `(M, W)`.
* `TauCeti.singularKronecker_relativeDeRhamHom_relClass`: the period of `relativeDeRhamHom x` on
  the relative class `TopPair.relClass` of a smooth simplex whose faces lie in `W`.
* `TauCeti.singularKronecker_relativeDeRhamHom_mk_relClass`: for `x = [(α, β)]` this period is
  `∫_σ α - ∫_{∂σ} β`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], Chapter I, §6.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18 (Proposition 18.13 for the absolute pairing).
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex TopologicalSpace
open scoped ContDiff Simplicial

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type} [TopologicalSpace M] [ChartedSpace H M] (W : Opens M)

/-- The complex of real smooth singular chains of `X`. -/
local notation "𝒮[" X "]" =>
  SSet.chainComplex (smoothSingularSubcomplex I X : SSet) (ModuleCat.of ℝ ℝ)

/-- The complex of real smooth relative singular chains of the pair `(M, U)`. -/
local notation "𝒮ᵣ[" U "]" => SSetPair.chainComplex (smoothSingularPair I U) (ModuleCat.of ℝ ℝ)

/-- The complex of real smooth relative singular cochains of the pair `(M, U)`. -/
local notation "𝒞ᵣ[" U "]" => ChainComplex.linearYonedaObj 𝒮ᵣ[U] ℝ (ModuleCat.of ℝ ℝ)

/-- Composed with the second projection of the cocone, the lift of relative smooth cochains
vanishes: a relative cochain `a` lifts to `(a, 0)`. -/
@[reassoc (attr := simp)]
theorem relativeSmoothCochainLift_f_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (relativeSmoothCochainLift I W).f p ≫
        (CochainComplex.mappingCocone.snd (smoothCochainRestriction I W)).v p q hpq = 0 := by
  rw [relativeSmoothCochainLift, CochainComplex.mappingCocone.lift_f_snd_v,
    CochainComplex.HomComplex.Cochain.zero_v]

namespace relativeSmoothCochainComplex

/-- **The pairing on lifted cochains.** The pairing with `(c, c')` of the lift `(a, 0)` of a
relative smooth cochain `a` of degree `k + 1` is `a` evaluated on the relative chain of `c`; the
chain `c'` plays no role. -/
theorem eval_relativeSmoothCochainLift_f (k : ℕ) (c : 𝒮[M].X (k + 1)) (c' : 𝒮[W].X k)
    (a : (𝒞ᵣ[W].extend ComplexShape.embeddingUpNat).X (k + 1 : ℕ)) :
    eval I W k c c' ((relativeSmoothCochainLift I W).f (k + 1 : ℕ) a) =
      ((extendXIso 𝒞ᵣ[W] ComplexShape.embeddingUpNat rfl).hom a).hom
        (((smoothSingularPair I W).chainComplexπ (ModuleCat.of ℝ ℝ)).f (k + 1) c) := by
  have h₁ : (CochainComplex.mappingCocone.fst (smoothCochainRestriction I W)).f (k + 1 : ℕ)
      ((relativeSmoothCochainLift I W).f (k + 1 : ℕ) a) =
        (extendMap (SSetPair.cochainComplexπ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
          (smoothSingularPair I W)) ComplexShape.embeddingUpNat).f (k + 1 : ℕ) a :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (relativeSmoothCochainLift_fst I W) (k + 1 : ℕ)) a
  have h₂ : (CochainComplex.mappingCocone.snd (smoothCochainRestriction I W)).v (k + 1 : ℕ) k
      (by push_cast; lia) ((relativeSmoothCochainLift I W).f (k + 1 : ℕ) a) = 0 := by
    rw [← ModuleCat.comp_apply, relativeSmoothCochainLift_f_snd_v]
    simp
  rw [eval_apply, CochainComplex.mappingCocone.relativeCoordinates_apply]
  dsimp only
  rw [h₁, h₂, neg_zero, map_zero, ChainComplex.linearYonedaObj_hom_zero, LinearMap.zero_apply,
    sub_zero]
  have h₃ := extendMap_f_comp_extendXIso_hom_apply ComplexShape.embeddingUpNat
    (SSetPair.cochainComplexπ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) (smoothSingularPair I W))
    (i' := ((k + 1 : ℕ) : ℤ)) (i := k + 1) rfl a
  rw [ChainComplex.linearYonedaFunctor_map_f_hom_apply] at h₃
  -- The cochains of `M` are those of the ambient simplicial set of the smooth singular pair, by
  -- `smoothSingularPair_right`, a definitional equality.
  refine (congrArg (fun g ↦ ModuleCat.Hom.hom g c) h₃).trans ?_
  exact ModuleCat.comp_apply _ _ c

/-- On a relative smooth cycle, `∂c = c'` in `M`, the pairing of cocycles of the mapping cocone of
restriction depends only on their cohomology classes. -/
theorem eval_eq_of_homologyπ_eq (k : ℕ) {c : 𝒮[M].X (k + 1)} {c' : 𝒮[W].X k}
    (hc : 𝒮[M].d (k + 1) k c =
      (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : W → M)
        contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).f k c')
    {u v : (relativeSmoothCochainComplex I W).cycles (k + 1 : ℕ)}
    (huv : (relativeSmoothCochainComplex I W).homologyπ (k + 1 : ℕ) u =
      (relativeSmoothCochainComplex I W).homologyπ (k + 1 : ℕ) v) :
    eval I W k c c' ((relativeSmoothCochainComplex I W).iCycles (k + 1 : ℕ) u) =
      eval I W k c c' ((relativeSmoothCochainComplex I W).iCycles (k + 1 : ℕ) v) := by
  obtain ⟨y, hy⟩ := ((relativeSmoothCochainComplex I W).moduleCat_homologyπ_eq_iff
    (m := (k : ℤ)) (by simp) u v).1 huv
  rw [← sub_eq_zero, ← map_sub, ← hy]
  exact eval_d I W k hc y

end relativeSmoothCochainComplex

namespace relativeDeRhamCohomology

variable [IsManifold I 2 M]

/-- **Periods of relative integration.** Let `c` be a smooth `(k + 1)`-chain of `M` whose boundary
is a smooth chain `c'` of `W`, and `z` the relative smooth cycle given by `c`. The Kronecker pairing
of the relative integral of a class `x` of `H^(k+1)(M, W)` with the class of `z` in smooth relative
homology is the integral `integral I W k hc x` of `x` over `(c, c')`. -/
theorem kronecker_integration_homologyπ (k : ℕ) {c : 𝒮[M].X (k + 1)} {c' : 𝒮[W].X k}
    (hc : 𝒮[M].d (k + 1) k c =
      (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : W → M)
        contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).f k c')
    (z : 𝒮ᵣ[W].cycles (k + 1))
    (hz : 𝒮ᵣ[W].iCycles (k + 1) z =
      ((smoothSingularPair I W).chainComplexπ (ModuleCat.of ℝ ℝ)).f (k + 1) c)
    (x : relativeDeRhamCohomology I W (k + 1 : ℕ)) :
    ChainComplex.kronecker ℝ 𝒮ᵣ[W] (ModuleCat.of ℝ ℝ) (k + 1) (integration I W (k + 1) x)
        (𝒮ᵣ[W].homologyπ (k + 1) z) = integral I W k hc x := by
  obtain ⟨y, rfl⟩ := mk_surjective I W k x
  -- A cocycle `u` of the extended relative smooth cochains representing the relative integral.
  obtain ⟨u, hu⟩ := moduleCat_homologyπ_surjective _ _
    ((𝒞ᵣ[W].extendHomologyIso ComplexShape.embeddingUpNat (j' := ((k + 1 : ℕ) : ℤ)) rfl).inv
      (integration I W (k + 1) (mk I W k y)))
  have hint : integration I W (k + 1) (mk I W k y) = 𝒞ᵣ[W].homologyπ (k + 1)
      ((𝒞ᵣ[W].extendCyclesIso ComplexShape.embeddingUpNat (j' := ((k + 1 : ℕ) : ℤ)) rfl).hom
        u) := by
    rw [← ModuleCat.comp_apply, ← homologyπ_extendHomologyIso_hom, ModuleCat.comp_apply, hu,
      Iso.inv_hom_id_apply]
  rw [hint, ChainComplex.kronecker_homologyπ_homologyπ, hz, ← ModuleCat.comp_apply,
    extendCyclesIso_hom_iCycles, ModuleCat.comp_apply,
    ← relativeSmoothCochainComplex.eval_relativeSmoothCochainLift_f I W k c c',
    ← moduleCat_iCycles_cyclesMap_apply]
  -- The lift of `u` to the cocone has the class of the relative integral of the cocycle `y`.
  have h := homologyMap_relativeSmoothCochainLift_integration I W (k + 1) (mk I W k y)
  rw [← hu, moduleCat_homologyMap_homologyπ, mk_apply, homologyMap_homologyπ_moduleCatCyclesMk] at h
  rw [relativeSmoothCochainComplex.eval_eq_of_homologyπ_eq I W k hc h, iCycles_moduleCatCyclesMk,
    integral_mk]
  exact relativeSmoothCochainComplex.eval_relativeDeRhamIntegration_f_coord_symm I W k c c' _ _

end relativeDeRhamCohomology

section SingularCohomology

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

open relativeDeRhamCohomology

/-- **Periods of the relative de Rham homomorphism on smooth relative cycles.** Let `c` be a
smooth `(k + 1)`-chain of `M` whose boundary is a smooth chain `c'` of `W`, and `z` the relative
smooth cycle given by `c`. The Kronecker pairing of `relativeDeRhamHom x` with the image of the
class of `z` in the singular homology of `(M, W)` is the integral `integral I W k hc x`. -/
theorem singularKronecker_relativeDeRhamHom_homologyMap (k : ℕ) {c : 𝒮[M].X (k + 1)}
    {c' : 𝒮[W].X k}
    (hc : 𝒮[M].d (k + 1) k c =
      (SSet.chainComplexMap (smoothSingularSubcomplexMap (Subtype.val : W → M)
        contMDiff_subtypeVal) (ModuleCat.of ℝ ℝ)).f k c')
    (z : 𝒮ᵣ[W].cycles (k + 1))
    (hz : 𝒮ᵣ[W].iCycles (k + 1) z =
      ((smoothSingularPair I W).chainComplexπ (ModuleCat.of ℝ ℝ)).f (k + 1) c)
    (x : relativeDeRhamCohomology I W (k + 1 : ℕ)) :
    (TopPair.ofSubset (W : Set (TopCat.of M))).singularKronecker ℝ (k + 1)
        (relativeDeRhamHom I W (k + 1) x)
        (SSetPair.homologyMap (smoothSingularPairι I W) (ModuleCat.of ℝ ℝ) (k + 1)
          (𝒮ᵣ[W].homologyπ (k + 1) z)) =
      integral I W k hc x := by
  have h := ConcreteCategory.congr_hom (ChainComplex.kronecker_naturality
    (SSetPair.chainComplexMap (smoothSingularPairι I W) (ModuleCat.of ℝ ℝ)) (k + 1)
    (relativeDeRhamHom I W (k + 1) x)) (𝒮ᵣ[W].homologyπ (k + 1) z)
  rw [ConcreteCategory.comp_apply] at h
  rw [TopPair.singularKronecker_def, SSetPair.homologyMap]
  refine h.symm.trans ?_
  have hc' := homologyMap_cochainComplexMap_relativeDeRhamHom I W (k + 1) x
  rw [hc']
  exact kronecker_integration_homologyπ I W k hc z hz x

/-- **Periods of the relative de Rham homomorphism on smooth simplices.** Let `σ` be a smooth
`(k + 1)`-simplex of `M` whose faces are smooth simplices `t i` of `W`. The Kronecker pairing of
`relativeDeRhamHom x` with the class `TopPair.relClass` of `σ` in the singular homology of
`(M, W)` is the integral of `x` over the relative smooth cycle `(σ, ∑ i, (-1) ^ i • t i)`. -/
theorem singularKronecker_relativeDeRhamHom_relClass (k : ℕ)
    (σ : SmoothSimplex I M (k + 1)) (t : Fin (k + 2) → SmoothSimplex I W k)
    (ht : ∀ i, (smoothSingularSubcomplex I M : SSet).δ i σ =
      (smoothSingularSubcomplexMap (Subtype.val : W → M) contMDiff_subtypeVal).app _ (t i))
    (x : relativeDeRhamCohomology I W (k + 1 : ℕ)) :
    (TopPair.ofSubset (W : Set (TopCat.of M))).singularKronecker ℝ (k + 1)
        (relativeDeRhamHom I W (k + 1) x)
        ((TopPair.ofSubset (W : Set (TopCat.of M))).relClass (ModuleCat.of ℝ ℝ) σ.val
          (range_toSSetObjEquiv_δ_subset_of_eq_smoothSingularSubcomplexMap_app σ t ht) 1) =
      integral I W k
        (SSetPair.sum_ιChainComplex_comp_chainComplexMap_f_apply (Q := smoothSingularPair I W)
          (ModuleCat.of ℝ ℝ) σ t ht 1).symm x := by
  have e : (TopPair.ofSubset (W : Set (TopCat.of M))).relClass (ModuleCat.of ℝ ℝ) σ.val
        (range_toSSetObjEquiv_δ_subset_of_eq_smoothSingularSubcomplexMap_app σ t ht) =
      SSetPair.relClass (Q := smoothSingularPair I W) (ModuleCat.of ℝ ℝ) σ t ht ≫
        SSetPair.homologyMap (smoothSingularPairι I W) (ModuleCat.of ℝ ℝ) (k + 1) := by
    have h₁ := SSetPair.relClass_homologyMap (Q := smoothSingularPair I W) (ModuleCat.of ℝ ℝ) σ t
      ht (smoothSingularPairι I W)
    rw [h₁, TopPair.relClass_eq_of_eq_toSSet_map_app (TopPair.ofSubset (W : Set (TopCat.of M)))
      (ModuleCat.of ℝ ℝ) σ.val (fun i ↦ (t i).val)
      fun i ↦ δ_val_eq_toSSet_map_app_of_eq_smoothSingularSubcomplexMap_app (ht i)]
    simp only [smoothSingularPairι_right, smoothSingularPairι_left]
    -- The inclusion of a subcomplex sends a simplex to its underlying simplex, by definition of
    -- `Subfunctor.ι`; the proofs of the face conditions agree by proof irrelevance.
    rfl
  rw [e, ModuleCat.comp_apply]
  have e₂ := ConcreteCategory.congr_hom
    (SSetPair.relClass_def (Q := smoothSingularPair I W) (ModuleCat.of ℝ ℝ) σ t ht) 1
  rw [e₂, ModuleCat.comp_apply]
  refine singularKronecker_relativeDeRhamHom_homologyMap I W k _ _ ?_ x
  rw [← ModuleCat.comp_apply, liftCycles_i, ModuleCat.comp_apply]

/-- **Periods of the relative de Rham homomorphism on a relative cocycle.** For a relative cocycle
`(α, β)` of degree `k + 1` and a smooth `(k + 1)`-simplex `σ` of `M` whose faces are smooth
simplices `t i` of `W`, the relative class `relativeDeRhamHom [(α, β)]` evaluates on the relative
class of `σ` to `∫_σ α - ∫_{∂σ} β`, where `∂σ = ∑ i, (-1) ^ i • t i` is read in `W`. -/
theorem singularKronecker_relativeDeRhamHom_mk_relClass (k : ℕ)
    (σ : SmoothSimplex I M (k + 1)) (t : Fin (k + 2) → SmoothSimplex I W k)
    (ht : ∀ i, (smoothSingularSubcomplex I M : SSet).δ i σ =
      (smoothSingularSubcomplexMap (Subtype.val : W → M) contMDiff_subtypeVal).app _ (t i))
    (y : cocycles I W k) :
    (TopPair.ofSubset (W : Set (TopCat.of M))).singularKronecker ℝ (k + 1)
        (relativeDeRhamHom I W (k + 1) (mk I W k y))
        ((TopPair.ofSubset (W : Set (TopCat.of M))).relClass (ModuleCat.of ℝ ℝ) σ.val
          (range_toSSetObjEquiv_δ_subset_of_eq_smoothSingularSubcomplexMap_app σ t ht) 1) =
      (integrationCochain y.val.1.val).hom
          (((smoothSingularSubcomplex I M : SSet).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ).hom 1) -
        (integrationCochain y.val.2.val).hom
          ((∑ i, (-1 : ℤ) ^ i.val •
            (smoothSingularSubcomplex I W : SSet).ιChainComplex (R := ModuleCat.of ℝ ℝ) (t i)).hom
              1) := by
  rw [singularKronecker_relativeDeRhamHom_relClass I W k σ t ht]
  exact integral_mk I W k _ y

end SingularCohomology

end TauCeti

end
