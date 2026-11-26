/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.GoodCover.Compact
public import SymplecticGeometry.Geometry.Manifold.SmoothSingular.DeRham.MayerVietoris.Basic
import Mathlib.Algebra.FiveLemma
import SymplecticGeometry.Topology.Sets.Opens.Comap
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
import TauCeti.Geometry.Manifold.SmoothSingular.DeRham.Theorem
import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Metrizable
import TauCeti.Order.SupClosed

/-!
# The de Rham theorem by Mayer–Vietoris induction

Let `M` be a Hausdorff smooth manifold modelled on a finite-dimensional real model with corners,
and `U`, `V` open subsets of `M`. This file shows first that if the de Rham homomorphism
`TauCeti.deRhamHom` is bijective in every degree on `U`, on `V` and on `U ⊓ V`, then it is
bijective in every degree on `U ⊔ V` (`TauCeti.bijective_deRhamHom_sup`). This is the inductive
step of the proof of the de Rham theorem by induction over open covers.

The proof is the five lemma
(`LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective`) applied to the ladder
whose rows are the Mayer–Vietoris sequences in de Rham cohomology
(`TauCeti.deRhamCohomology.exact_mayerVietorisToProd_fromProd` and its two siblings) and in singular
cohomology, and whose rungs are de Rham homomorphisms. The squares made of restrictions commute
by `TauCeti.singularCohomologyMayerVietorisToProd_deRhamHom` and
`TauCeti.singularCohomologyMayerVietorisFromProd_deRhamHom`, and the square made of the
connecting maps by `TauCeti.deRhamHom_mayerVietorisδ`. In degree zero the de Rham homomorphism is
bijective on every manifold (`TauCeti.bijective_deRhamHom_zero`).

The singular Mayer–Vietoris sequence of Tau Ceti
(`TauCeti/AlgebraicTopology/Cohomology/MayerVietoris/Module.lean`) is stated for two open sets
covering the space, and `TauCeti.deRhamHom_mayerVietorisδ` for two open sets covering `M`. The
step is first proved under the hypothesis `U ⊔ V = ⊤`, and then in general by applying that case
on the manifold `U ⊔ V`, whose open subsets with the points of `U` and of `V` are diffeomorphic to
`U` and `V` (`Diffeomorph.nestedOpen`). De Rham's theorem holds on a manifold if and only if
it holds on a diffeomorphic one (`Diffeomorph.bijective_deRhamHom_iff`).

The induction itself runs over the finite joins of the intersections of a finite good cover
(`SymplecticGeometry.IsFiniteGoodCover`), which form an inf-closed family, by Tau Ceti's
`TauCeti.finset_sup_of_inf_closed`. Each such intersection is empty, where both cohomologies
vanish (`TauCeti.bijective_deRhamHom_of_isEmpty`), or smoothly contractible
(`SymplecticGeometry.IsSmoothlyContractible.bijective_deRhamHom`, from
`TauCeti.bijective_deRhamHom_of_contraction` after reversing time). This gives the de Rham theorem
on every manifold with a finite good cover (`TauCeti.bijective_deRhamHom`), in particular on
every compact boundaryless one, by Weil's good covers
(`SymplecticGeometry.hasFiniteGoodCover_of_compactSpace`).

## Main results

* `Diffeomorph.bijective_deRhamHom_iff`: the de Rham theorem is invariant under diffeomorphisms.
* `TauCeti.bijective_deRhamHom_sup`: the Mayer–Vietoris step of the de Rham theorem.
* `SymplecticGeometry.IsSmoothlyContractible.bijective_deRhamHom`: the de Rham theorem on a
  smoothly contractible manifold.
* `TauCeti.bijective_deRhamHom`: the de Rham theorem on a manifold with a finite good cover.
* `TauCeti.bijective_deRhamHom_of_compactSpace` and `TauCeti.injective_deRhamHom`: the de Rham
  theorem on a compact boundaryless manifold, and the injectivity of the de Rham homomorphism
  there.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18, proof of Theorem 18.14.
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §5
  (Mayer–Vietoris arguments over good covers).
* [A. Weil, *Sur les théorèmes de de Rham*][Weil1952], §1 (finite good covers of compact
  manifolds).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]

section Step

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]


/-- **The de Rham theorem is invariant under diffeomorphisms**: if `M` and `N` are diffeomorphic,
the de Rham homomorphism of `M` in degree `k` is bijective if and only if that of `N` is. -/
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
      -- Both continuous maps are `Φ`.
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

omit [SigmaCompactSpace M] [SigmaCompactSpace (U ⊔ V : Opens M)] in
/-- The square of the ladder between the restrictions to `U ⊓ V`. -/
private theorem singularCohomologyMayerVietorisFromProd_comp_prodMap (m : ℕ) :
    TopCat.singularCohomologyMayerVietorisFromProd (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (X := TopCat.of M) U V m ∘ₗ
        (deRhamHom I U m).prodMap (deRhamHom I V m) =
      deRhamHom I (U ⊓ V : Opens M) m ∘ₗ deRhamCohomology.mayerVietorisFromProd I U V m :=
  LinearMap.ext fun x ↦ singularCohomologyMayerVietorisFromProd_deRhamHom I U V m x.1 x.2

/-- The Mayer–Vietoris step of the de Rham theorem for two open sets covering `M`. -/
private theorem bijective_deRhamHom_of_sup_eq_top (hUV : U ⊔ V = ⊤)
    (hU : ∀ k, Function.Bijective (deRhamHom I U k))
    (hV : ∀ k, Function.Bijective (deRhamHom I V k))
    (hUV' : ∀ k, Function.Bijective (deRhamHom I (U ⊓ V : Opens M) k)) (k : ℕ) :
    Function.Bijective (deRhamHom I M k) := by
  obtain _ | n := k
  · exact bijective_deRhamHom_zero I M
  have hcov : (U : Set M) ∪ V = Set.univ := by rw [← Opens.coe_sup, hUV, Opens.coe_top]
  -- The inclusion of `U ⊔ V` in `M` is a diffeomorphism; the middle rung of the ladder is the de
  -- Rham homomorphism of `M` after pullback along its inverse.
  let Φ : (U ⊔ V : Opens M) ≃ₘ⟮I, I⟯ M := Diffeomorph.ofTop _ hUV
  let e := deRhamCohomology.equivOfDiffeomorph Φ.symm (n + 1)
  have hg : TopCat.ofHom ⟨Φ.symm, Φ.symm.contMDiff.continuous⟩ ≫
      TopCat.ofHom (ContinuousMap.subtypeVal ((U ⊔ V : Opens M) : Set M)) = 𝟙 (TopCat.of M) := by
    ext x
    exact Diffeomorph.coe_ofTop_symm_apply x
  rw [← Function.Bijective.of_comp_iff _ e.bijective]
  refine LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective _ _ _ _ _ _ _ _
    ((deRhamHom I U n).prodMap (deRhamHom I V n)) (deRhamHom I (U ⊓ V : Opens M) n)
    (deRhamHom I M (n + 1) ∘ₗ e.toLinearMap)
    ((deRhamHom I U (n + 1)).prodMap (deRhamHom I V (n + 1)))
    (deRhamHom I (U ⊓ V : Opens M) (n + 1))
    (singularCohomologyMayerVietorisFromProd_comp_prodMap n) ?_ ?_
    (singularCohomologyMayerVietorisFromProd_comp_prodMap (n + 1))
    (deRhamCohomology.exact_mayerVietorisFromProd_δ U V n)
    (deRhamCohomology.exact_mayerVietorisδ_toProd U V n)
    (deRhamCohomology.exact_mayerVietorisToProd_fromProd U V (n + 1))
    (TopCat.exact_singularCohomologyMayerVietorisFromProd_δ (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (X := TopCat.of M) U.isOpen V.isOpen hcov n (n + 1))
    (TopCat.exact_singularCohomologyMayerVietorisδ_toProd (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (X := TopCat.of M) U.isOpen V.isOpen hcov n (n + 1))
    (TopCat.exact_singularCohomologyMayerVietorisToProd_fromProd (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (X := TopCat.of M) U.isOpen V.isOpen hcov (n + 1))
    ?_ (hUV' n) ?_ (hUV' (n + 1)).1
  · refine LinearMap.ext fun c ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, deRhamCohomology.equivOfDiffeomorph_apply, deRhamHom_map,
      deRhamHom_mayerVietorisδ I hUV, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp, hg, TopCat.singularCohomologyMap_id]
    exact ModuleCat.id_apply _ _
  · refine LinearMap.ext fun c ↦ ?_
    -- Going from `W ≤ U ⊔ V` to `M` and then back to `U ⊔ V` is the inclusion of `W` in `U ⊔ V`.
    have hres (W : Opens M) (hW : W ≤ U ⊔ V) :
        deRhamCohomology.map Subtype.val contMDiff_subtypeVal (n + 1) (e c) =
          deRhamCohomology.map (I := I) (I' := I) (Opens.inclusion hW) (contMDiff_inclusion _)
            (n + 1) c := by
      have hf : (Φ.symm ∘ Subtype.val : W → (U ⊔ V : Opens M)) = Opens.inclusion hW :=
        funext fun x ↦ Subtype.ext
          ((Diffeomorph.coe_ofTop_symm_apply (x : M)).trans (Set.coe_inclusion hW x).symm)
      rw [deRhamCohomology.equivOfDiffeomorph_apply, ← LinearMap.comp_apply,
        ← deRhamCohomology.map_comp]
      simp only [hf]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      singularCohomologyMayerVietorisToProd_deRhamHom, hres U le_sup_left, hres V le_sup_right,
      LinearMap.comp_apply, deRhamCohomology.mayerVietorisToProd_apply, LinearMap.prodMap_apply]
  · rw [LinearMap.coe_prodMap]
    exact (hU n).surjective.prodMap (hV n).surjective
  · rw [LinearMap.coe_prodMap]
    exact (hU (n + 1)).prodMap (hV (n + 1))

omit [SigmaCompactSpace M] in
/-- **The Mayer–Vietoris step of the de Rham theorem.** Let `U` and `V` be open subsets of `M`. If
the de Rham homomorphism is bijective in every degree on `U`, on `V` and on `U ⊓ V`, then it is
bijective in every degree on `U ⊔ V`.

When `M` is `σ`-compact, the instance hypotheses on `U`, `V`, `U ⊓ V` and `U ⊔ V` hold, by
`TauCeti.Manifold.sigmaCompactSpace_opens`. -/
theorem bijective_deRhamHom_sup (hU : ∀ k, Function.Bijective (deRhamHom I U k))
    (hV : ∀ k, Function.Bijective (deRhamHom I V k))
    (hUV : ∀ k, Function.Bijective (deRhamHom I (U ⊓ V : Opens M) k)) (k : ℕ) :
    Function.Bijective (deRhamHom I (U ⊔ V : Opens M) k) := by
  -- Read `U` and `V` as open subsets `U'` and `V'` of the manifold `U ⊔ V`, which they cover.
  let U' : Opens (U ⊔ V : Opens M) := Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ U
  let V' : Opens (U ⊔ V : Opens M) := Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ V
  have := Manifold.sigmaCompactSpace_opens I U'
  have := Manifold.sigmaCompactSpace_opens I V'
  have := Manifold.sigmaCompactSpace_opens I (U' ⊓ V')
  have := Manifold.sigmaCompactSpace_opens I (U' ⊔ V')
  have := Manifold.sigmaCompactSpace_opens I
    (Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ (U ⊓ V) : Opens (U ⊔ V : Opens M))
  exact bijective_deRhamHom_of_sup_eq_top (Opens.comap_val_sup_comap_val_eq_top U V)
    (fun k ↦ ((Diffeomorph.nestedOpen le_sup_left).bijective_deRhamHom_iff k).2 (hU k))
    (fun k ↦ ((Diffeomorph.nestedOpen le_sup_right).bijective_deRhamHom_iff k).2 (hV k))
    (fun k ↦ ((Diffeomorph.nestedOpen inf_le_sup).bijective_deRhamHom_iff k).2 (hUV k)) k

end Step

section GoodCover

open SymplecticGeometry

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

/-- **The de Rham theorem on a smoothly contractible manifold.** If `M` is smoothly contractible,
the de Rham homomorphism of `M` is bijective in every degree. -/
theorem _root_.SymplecticGeometry.IsSmoothlyContractible.bijective_deRhamHom [SigmaCompactSpace M]
    (h : IsSmoothlyContractible I M) (k : ℕ) : Function.Bijective (deRhamHom I M k) := by
  obtain ⟨c, F, hF, h₀, h₁⟩ := isSmoothlyContractible_def.1 h
  -- Tau Ceti's contraction runs from the identity to the constant map: reverse time.
  exact bijective_deRhamHom_of_contraction I M (c := c)
    (hF.comp (contMDiff_fst.prodMk (unitInterval.contMDiff_symm.comp contMDiff_snd)))
    (fun x ↦ by simpa using h₁ x) (fun x ↦ by simpa using h₀ x) k

/-- **The de Rham theorem for manifolds with a finite good cover.** On a Hausdorff `σ`-compact
smooth manifold `M`, modelled on a finite-dimensional real model with corners, that has a finite
good cover, the de Rham homomorphism is bijective in every degree. -/
theorem bijective_deRhamHom [SigmaCompactSpace M] (hM : HasFiniteGoodCover I M) (k : ℕ) :
    Function.Bijective (deRhamHom I M k) := by
  classical
  obtain ⟨n, U, hU⟩ := hasFiniteGoodCover_def.1 hM
  -- The intersections of the nonempty subfamilies of the cover form an inf-closed family.
  let B : Set (Opens M) := {W | ∃ s : Finset (Fin n), s.Nonempty ∧ W = ⨅ i ∈ s, U i}
  have hB : InfClosed B := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, -, rfl⟩
    exact ⟨s ∪ t, hs.mono Finset.subset_union_left, Finset.iInf_union.symm⟩
  have hP := finset_sup_of_inf_closed (fun W : Opens M ↦
      ∀ (_ : SigmaCompactSpace W) k, Function.Bijective (deRhamHom I W k)) hB ?_ ?_ ?_
    (Finset.univ.image U) ?_
  · have htop : (Finset.univ.image U).sup id = ⊤ := by
      rw [Finset.sup_image, Function.id_comp, Finset.sup_univ_eq_iSup, hU.iSup_eq_top]
    rw [htop] at hP
    have := Manifold.sigmaCompactSpace_opens I (⊤ : Opens M)
    exact ((Diffeomorph.ofTop (I := I) (n := ∞) _ rfl).bijective_deRhamHom_iff k).1 (hP this k)
  · intro _ k
    have : IsEmpty (⊥ : Opens M) := ⟨fun x ↦ Opens.mem_bot.1 x.property⟩
    exact bijective_deRhamHom_of_isEmpty I _ k
  · rintro _ ⟨s, hs, rfl⟩ _ k
    rcases ((⨅ i ∈ s, U i : Opens M) : Set M).eq_empty_or_nonempty with h | h
    · have : IsEmpty (⨅ i ∈ s, U i : Opens M) :=
        ⟨fun x ↦ Set.eq_empty_iff_forall_notMem.1 h x x.property⟩
      exact bijective_deRhamHom_of_isEmpty I _ k
    · exact (hU.isSmoothlyContractible hs h).bijective_deRhamHom k
  · intro V W hV hW hVW _ k
    have := Manifold.sigmaCompactSpace_opens I V
    have := Manifold.sigmaCompactSpace_opens I W
    have := Manifold.sigmaCompactSpace_opens I (V ⊓ W)
    exact bijective_deRhamHom_sup (hV ‹_›) (hW ‹_›) (hVW ‹_›) k
  · intro V hV
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hV
    exact ⟨{i}, Finset.singleton_nonempty i, by simp⟩

variable [CompactSpace M] [BoundarylessManifold I M]

/-- **The de Rham theorem for compact manifolds.** On a compact Hausdorff boundaryless smooth
manifold, modelled on a finite-dimensional real normed space, the de Rham homomorphism is
bijective in every degree. -/
theorem bijective_deRhamHom_of_compactSpace (k : ℕ) : Function.Bijective (deRhamHom I M k) :=
  bijective_deRhamHom hasFiniteGoodCover_of_compactSpace k

/-- On a compact Hausdorff boundaryless smooth manifold, modelled on a finite-dimensional real
normed space, the de Rham homomorphism is injective in every degree: a closed form whose image in
real singular cohomology vanishes is exact. -/
theorem injective_deRhamHom (k : ℕ) : Function.Injective (deRhamHom I M k) :=
  (bijective_deRhamHom_of_compactSpace k).1


end GoodCover

end TauCeti
