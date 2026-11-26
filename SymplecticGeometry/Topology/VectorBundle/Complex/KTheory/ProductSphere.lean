/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Clutching

/-!
# Bundles over `X × ℂP¹` are clutchings

Let `X` be compact Hausdorff and `F` a finite-rank core over `X × ℙ ℂ (Fin 2 → ℂ)`, and let `E` be
its restriction to `X × {[1 : 1]}`, that is its pullback along `x ↦ (x, [1 : 1])`. Then `F` is
isomorphic to the clutching `E.clutching f` of `E` by some automorphism `f` of the pullback of `E`
to `X × Circle` (`TauCeti.FiniteRankBundleCore.exists_iso_clutching`). This is the first step of
the product theorem of [Hatcher2017, §2.1].

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.nonempty_pullback_affineChartMap_iso`: over `X × (Fin 1 → ℂ)`,
  the pullback of `F` along the inverse `ProjectiveLine.affineChartMap X i` of an affine chart of
  the projective line is the pullback of `E` along the projection, since the affine line
  contracts to the coordinate `1` of `[1 : 1]`
  (`TauCeti.FiniteRankBundleCore.nonempty_iso_pullback_fst`). Here `E` is the pullback of `F`
  along `ProjectiveLine.prodMkOne X`.
* `TauCeti.FiniteRankBundleCore.nonempty_pullback_subtypeVal_iso_of_subset_affineOpen`: hence the
  same holds for the restriction of `F` to `X × S`, for any set `S` inside an affine open.
* `TauCeti.FiniteRankBundleCore.exists_iso_clutching`: every core over `X × ℙ ℂ (Fin 2 → ℂ)` is a
  clutching of its restriction to `X × {[1 : 1]}`.

The discs, the annulus and the maps between products with them that the proof uses, such as
`ProjectiveLine.circleToAnnulus` and the radial deformation `ProjectiveLine.annulusDeformation`,
are in `SymplecticGeometry.Topology.ComplexProjectiveSpace.ProjectiveLine`.

## Proof

Each of the two discs lies in an affine open, so the restriction of `F` to its product with `X` is
the pullback of `E` along the projection, by homotopy invariance of pullbacks applied to the
segments to `[1 : 1]` in the affine chart
(`TauCeti.FiniteRankBundleCore.nonempty_iso_pullback_fst`). By
`TauCeti.FiniteRankBundleCore.isoGlue`, `F` is then the gluing of the pullback of `E` by the
transition `g` of the two isomorphisms over the product of `X` with the annulus. Let `f` be `g`
restricted to `X × Circle`. The radial deformation of the annulus onto the circle joins `g` to
`clutchingAut E f`, which glues to `E.clutching f`, and gluings by homotopic automorphisms are
isomorphic (`TauCeti.FiniteRankBundleCore.nonempty_iso_glue_of_homotopic`).

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (every bundle over `X × S²` is a
  clutching).
-/

public section

noncomputable section

open Set CategoryTheory Projectivization

open scoped LinearAlgebra.Projectivization

namespace TauCeti.FiniteRankBundleCore

open SymplecticGeometry.ProjectiveLine

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]
  [CompactSpace X] [T2Space X] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
  (F : FiniteRankBundleCore 𝕜 (X × ℙ ℂ (Fin 2 → ℂ)))

/-! ### The restriction of a core to the product with a disc -/

/-- **A core is trivial along the affine line.** For `X` compact Hausdorff and a core `F` over
`X × ℙ ℂ (Fin 2 → ℂ)`, the pullback of `F` along the inverse of an affine chart in the second
factor is isomorphic to the pullback along the projection `X × (Fin 1 → ℂ) → X` of the restriction
of `F` to `X × {[1 : 1]}`. -/
theorem nonempty_pullback_affineChartMap_iso (i : Fin 2) :
    Nonempty (F.pullback (affineChartMap X i) ≅
      (F.pullback (prodMkOne X)).pullback ContinuousMap.fst) := by
  -- The affine line contracts to the coordinate `1` of `[1 : 1]`.
  obtain ⟨e⟩ := (F.pullback (affineChartMap X i)).nonempty_iso_pullback_fst (1 : Fin 1 → ℂ)
  have hk : (affineChartMap X i).comp ((ContinuousMap.id X).prodMk (.const X 1)) =
      prodMkOne X :=
    ContinuousMap.ext fun x ↦ by simp
  rw [pullback_comp F, hk] at e
  exact ⟨e⟩

/-- **A core is trivial over the product with a part of an affine open.** For `X` compact
Hausdorff, a core `F` over `X × ℙ ℂ (Fin 2 → ℂ)` and a set `S` inside the affine open `i` of the
projective line, the restriction of `F` to `X × S` is isomorphic to that of the pullback along the
projection of the restriction of `F` to `X × {[1 : 1]}`. -/
theorem nonempty_pullback_subtypeVal_iso_of_subset_affineOpen {i : Fin 2}
    {S : Set (ℙ ℂ (Fin 2 → ℂ))} (hS : S ⊆ affineOpen i) :
    Nonempty (F.pullback (ContinuousMap.subtypeVal (Prod.snd ⁻¹' S)) ≅
      ((F.pullback (prodMkOne X)).pullback ContinuousMap.fst).pullback
        (ContinuousMap.subtypeVal (Prod.snd ⁻¹' S))) := by
  -- The coordinates of `X × S` in `X × (Fin 1 → ℂ)`.
  let k : C(↥(Prod.snd ⁻¹' S : Set (X × ℙ ℂ (Fin 2 → ℂ))), X × (Fin 1 → ℂ)) :=
    ⟨fun w ↦ (w.val.1, affineChart i w.val.2),
      (continuous_fst.comp continuous_subtypeVal).prodMk
        (continuousOn_iff_continuous_domRestrict.1 ((continuousOn_affineChart i).mono hS) |>.comp
          ((continuous_snd.comp continuous_subtypeVal).subtype_mk fun w ↦ w.property))⟩
  have hk : (affineChartMap X i).comp k = ContinuousMap.subtypeVal (Prod.snd ⁻¹' S) :=
    ContinuousMap.ext fun w ↦ Prod.ext rfl
      ((affineChart i).left_inv (by rw [affineChart_source]; exact hS w.property))
  obtain ⟨e⟩ := F.nonempty_pullback_affineChartMap_iso i
  refine ⟨eqToIso ?_ ≪≫ (pullbackFunctor k).mapIso e ≪≫ eqToIso ?_⟩
  · rw [pullbackFunctor_obj, pullback_comp, hk]
  · rw [pullbackFunctor_obj, pullback_comp, pullback_comp, pullback_comp]
    exact congrArg F.pullback (ContinuousMap.ext fun _ ↦ rfl)

/-! ### Every core over `X × ℂP¹` is a clutching -/

/-- **Every bundle over `X × ℂP¹` is a clutching.** Let `X` be compact Hausdorff and `F` a
finite-rank core over `X × ℙ ℂ (Fin 2 → ℂ)`, and let `E` be its restriction to `X × {[1 : 1]}`,
the pullback of `F` along `x ↦ (x, [1 : 1])`. Then `F` is isomorphic to the clutching of `E` by
some automorphism `f` of the pullback of `E` to `X × Circle`. -/
theorem exists_iso_clutching :
    ∃ f : (F.pullback (prodMkOne X)).pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
        (F.pullback (prodMkOne X)).pullback (ContinuousMap.fst : C(X × Circle, X)),
      Nonempty (F ≅ (F.pullback (prodMkOne X)).clutching f) := by
  obtain ⟨φ⟩ := F.nonempty_pullback_subtypeVal_iso_of_subset_affineOpen
    (S := innerDisc) innerDisc_subset_affineOpen
  obtain ⟨ψ⟩ := F.nonempty_pullback_subtypeVal_iso_of_subset_affineOpen
    (S := outerDisc) outerDisc_subset_affineOpen
  have hU : IsOpen (Prod.snd ⁻¹' innerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ))) :=
    isOpen_innerDisc.preimage continuous_snd
  have hV : IsOpen (Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ))) :=
    isOpen_outerDisc.preimage continuous_snd
  have hUV : (Prod.snd ⁻¹' innerDisc ∪ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ))) =
      univ := by
    rw [← preimage_union, innerDisc_union_outerDisc, preimage_univ]
  -- The clutching function: the transition of `φ` and `ψ` on `X × Circle`.
  refine ⟨(pullbackFunctor (circleToAnnulus X)).mapIso (glueTransition φ ψ), ?_⟩
  obtain ⟨e⟩ := nonempty_iso_glue_of_homotopic _ hU hV hUV
    (g₀ := glueTransition φ ψ)
    (g₁ := clutchingAut (F.pullback (prodMkOne X))
      ((pullbackFunctor (circleToAnnulus X)).mapIso (glueTransition φ ψ)))
    ((pullbackFunctor (annulusDeformation X)).mapIso (glueTransition φ ψ))
    -- The cores of `fiberMap_pullbackMap` are those of the statement by `pullback_comp`: all are
    -- the pullback of `E` along `w ↦ w.val.1.1`.
    (fun w ↦ (fiberMap_pullbackMap (glueTransition φ ψ).hom (annulusDeformation X) _).trans
      (congrArg _ (annulusDeformation_zero X w)))
    (fun w ↦ (fiberMap_pullbackMap (glueTransition φ ψ).hom (annulusDeformation X) _).trans <|
      (congrArg _ (annulusDeformation_one X w)).trans <|
        (fiberMap_pullbackMap (glueTransition φ ψ).hom (circleToAnnulus X) _).symm.trans
          (fiberMap_clutchingAut_hom (F.pullback (prodMkOne X))
            ((pullbackFunctor (circleToAnnulus X)).mapIso (glueTransition φ ψ)) w).symm)
  exact ⟨isoGlue φ ψ hU hV hUV ≪≫ e⟩

end TauCeti.FiniteRankBundleCore

end
