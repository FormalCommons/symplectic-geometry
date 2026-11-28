/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic
public import SymplecticGeometry.AlgebraicTopology.Singular.RelativeClass
public import TauCeti.Geometry.Manifold.Orientation.Euclidean
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.AlgebraicTopology.Cohomology.Local.Orientation
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.StdSimplex
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
import SymplecticGeometry.Topology.Algebra.Module.Equiv.Basic

/-!
# The class of a positively oriented simplex in local homology

Let `C` be a surface, a manifold modelled on a real normed space `E'` of dimension two, oriented
by `o`, and let `σ` be a smooth `2`-simplex of `C` that is the restriction to `Δ² = fullSimplex 2`
of a map `g : ℝ² → C` which, on an open neighbourhood `U` of `Δ²`, is an open embedding
preserving orientation from the standard orientation of `ℝ²` to `o` (the hypotheses of
`TauCeti.SmoothSimplex.integral_eq_integralTopForm`). For a compact `K ⊆ g '' interior Δ²`, the
faces of `σ` avoid `K` (`TauCeti.SmoothSimplex.range_toSSetObjEquiv_δ_subset_compl`), so `σ` has
a class `[σ] ∈ H₂(C, C ∖ K; ℤ)` (`TopPair.relClass`). This class is the fundamental class along
`K` of the homological orientation of `-o`
(`TauCeti.SmoothSimplex.relativeClass_eq_fundamentalClassOn`). For `C = ℝ²` with its standard
orientation and `K = {0}`, the generator of `H²(ℝ², ℝ² ∖ {0}; ℤ)` that the standard orientation
selects (`Orientation.localCohomologyClass`) therefore pairs to `-1` with `[σ]`
(`TauCeti.SmoothSimplex.singularKronecker_localCohomologyClass_relClass`).

The sign comes from `TopPair.relClass_fullSimplex_eq_neg_toHomologicalOrientation`: Tau Ceti's
homological orientation of a smooth orientation selects at each point minus the class of a
positively oriented simplex around it.

## Proof

By `TauCeti.HomologicalOrientation.eq_fundamentalClassOn`, it suffices to compare the images in
`H₂(C, C ∖ {x})` at each `x = g p ∈ K`. The simplex comes from a singular simplex `σ_U` of `U`,
whose images under `g` and under the inclusion `ι : U → ℝ²` are `σ` and the standard simplex.
Both maps preserve orientation, from the restriction to `U` of the standard orientation, so they
carry its local orientation at `p` to that of `o` at `x` and of `ℝ²` at `p`
(`TauCeti.Manifold.Orientation.localHomologyMap_toHomologicalOrientation`, in
`LocalHomology/Orientation/Smooth.lean`). The map `ι` is an isomorphism
of local homology, and carries `[σ_U]` to the class of the standard simplex, which is minus the
local orientation of `ℝ²` at `p`. So `[σ_U]` is minus the local orientation of `U` at `p`, and its
image `[σ]` under `g` is minus that of `o` at `x`.

## Main results

* `TauCeti.SmoothSimplex.range_toSSetObjEquiv_δ_subset_compl`: the faces of the simplex avoid `K`.
* `TauCeti.SmoothSimplex.relativeClass_eq_fundamentalClassOn`: the class of the simplex in
  `H₂(C, C ∖ K; ℤ)` is the fundamental class along `K` of the homological orientation of `-o`.
* `TauCeti.SmoothSimplex.singularKronecker_localCohomologyClass_relClass`: in `ℝ²`, the standard
  generator of `H²(ℝ², ℝ² ∖ {0}; ℤ)` pairs to `-1` with the class of a positively oriented
  simplex around `0`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1 (the class of a
  simplex in relative homology) and Section 3.3 (local orientations and the fundamental class
  along a compact set, Lemma 3.27).
-/

public section

noncomputable section

open CategoryTheory TauCeti Module Set Topology TopologicalSpace Simplicial
open scoped Manifold

namespace TauCeti.SmoothSimplex

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {C : Type} [TopologicalSpace C] [ChartedSpace E' C]
  (σ : SmoothSimplex 𝓘(ℝ, E') C 2) {U : Opens (EuclideanSpace ℝ (Fin 2))}
  (hU : fullSimplex 2 ⊆ U) {g : EuclideanSpace ℝ (Fin 2) → C}
  (hgσ : ∀ x : fullSimplex 2, g x = σ.toContinuousMap x)
  (hg : IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2))))

/-- The simplex `σ`, read on `U`: the inclusion of `Δ²` into `U`. -/
private def simplexOn : (TopCat.toSSet.obj (TopCat.of U)) _⦋2⦌ :=
  ((TopCat.of U).toSSetObjEquiv _).symm
    ⟨fun y ↦ ⟨((fullSimplexEquivStdSimplex 2).symm y : EuclideanSpace ℝ (Fin 2)),
      hU (Subtype.prop _)⟩, by fun_prop⟩

include hgσ in
/-- The map `g` carries the simplex read on `U` to `σ`. -/
private lemma toSSet_map_app_simplexOn :
    (TopCat.toSSet.map (TopCat.ofHom ⟨g ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2)), hg.continuous⟩)).app
      _ (simplexOn hU) = σ.val := by
  refine ((TopCat.of C).toSSetObjEquiv _).injective (ContinuousMap.ext fun y ↦ ?_)
  rw [TopCat.toSSetObjEquiv_toSSet_map_app]
  have h := hgσ ((fullSimplexEquivStdSimplex 2).symm y)
  rw [toContinuousMap_apply, Homeomorph.apply_symm_apply] at h
  exact h

/-- The inclusion of `U` carries the simplex read on `U` to the standard simplex. -/
private lemma toSSet_map_app_simplexOn_subtypeVal :
    (TopCat.toSSet.map (TopCat.ofHom ⟨((↑) : U → EuclideanSpace ℝ (Fin 2)),
      continuous_subtypeVal⟩)).app _ (simplexOn hU) =
      ((TopCat.of (EuclideanSpace ℝ (Fin 2))).toSSetObjEquiv (Opposite.op ⦋2⦌)).symm
        ((ContinuousMap.subtypeVal (fullSimplex 2)).comp (fullSimplexEquivStdSimplex 2).symm) :=
  (rfl)

include hU hgσ hg in
/-- **The faces of a simplex given by an open embedding avoid the image of the interior.** If `σ`
is the restriction to `Δ²` of a map `g` that is an open embedding on a neighbourhood `U` of `Δ²`,
the faces of `σ` lie in `C ∖ K` for every `K ⊆ g '' interior Δ²`. -/
theorem range_toSSetObjEquiv_δ_subset_compl {K : Set C}
    (hKg : K ⊆ g '' interior (fullSimplex 2)) (i : Fin 3) :
    Set.range ((TopCat.of C).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of C)).δ i σ.val)) ⊆
      Set.range (TopPair.ofSubset (Kᶜ : Set (TopCat.of C))).map := by
  rintro _ ⟨z, rfl⟩
  refine ⟨⟨_, fun hK ↦ ?_⟩, rfl⟩
  obtain ⟨p, hp, hpz⟩ := hKg hK
  -- The face of `σ` is the image under `g` of the face of the standard simplex.
  rw [← toSSet_map_app_simplexOn σ hU hgσ hg] at hpz
  obtain ⟨⟨w, hw⟩, hwz⟩ := TopPair.range_toSSetObjEquiv_δ_fullSimplex_subset hp i ⟨z, rfl⟩
  refine hw (Set.mem_singleton_iff.2 ?_)
  have hinj := hg.injective (a₁ := ⟨p, hU (interior_subset hp)⟩)
    (a₂ := (TopCat.of U).toSSetObjEquiv _ ((TopCat.toSSet.obj _).δ i (simplexOn hU)) z) hpz
  -- The inclusion of `ℝ² ∖ {p}` is `ContinuousMap.subtypeVal`, so `hwz` says that `w` is the point.
  rw [TopPair.ofSubset_map] at hwz
  exact hwz.trans (congrArg Subtype.val hinj).symm

include hU hgσ hg in
/-- **The class of a positively oriented simplex in local homology.** Let `σ` be a smooth
`2`-simplex of a surface `C` oriented by `o`, the restriction to `Δ²` of a map `g : ℝ² → C` that
is an open embedding on an open neighbourhood `U` of `Δ²` and preserves orientation there from the
standard orientation of `ℝ²` to `o`. For a compact `K ⊆ g '' interior Δ²`, the class of `σ` in
`H₂(C, C ∖ K; ℤ)` is the fundamental class along `K` of the homological orientation of `-o`. -/
theorem relativeClass_eq_fundamentalClassOn [FiniteDimensional ℝ E'] [T2Space C]
    [IsManifold 𝓘(ℝ, E') 1 C] (hE' : finrank ℝ E' = 2)
    (o : Manifold.Orientation 𝓘(ℝ, E') C (Fin 2))
    (ho : ∀ x ∈ U, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace 2) o g x)
    {K : Set C} (hK : IsCompact K) (hKg : K ⊆ g '' interior (fullSimplex 2)) :
    (TopPair.ofSubset (Kᶜ : Set (TopCat.of C))).relClass (ModuleCat.of ℤ (ULift.{0} ℤ)) (n := 1)
        σ.val (range_toSSetObjEquiv_δ_subset_compl σ hU hgσ hg hKg) 1 =
      ((-o).toHomologicalOrientation hE').fundamentalClassOn hE' hK := by
  refine HomologicalOrientation.eq_fundamentalClassOn _ hE' hK fun x hx ↦ ?_
  obtain ⟨p, hp, rfl⟩ := hKg hx
  set R := ModuleCat.of ℤ (ULift.{0} ℤ)
  have hE2 : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1 := finrank_euclideanSpace_fin
  let p' : U := ⟨p, hU (interior_subset hp)⟩
  let f : C(U, C) := ⟨g ∘ (↑), hg.continuous⟩
  let ι : C(U, EuclideanSpace ℝ (Fin 2)) := ⟨(↑), continuous_subtypeVal⟩
  have hf : f ⁻¹' {f p'} ⊆ {p'} := fun _ hz ↦ hg.injective hz
  have hι : ι ⁻¹' {ι p'} ⊆ {p'} := fun _ hz ↦ Subtype.ext hz
  have hstd := TopPair.range_toSSetObjEquiv_δ_fullSimplex_subset hp
  -- The faces of the simplex read on `U` avoid `p`.
  have hσU := TopPair.range_toSSetObjEquiv_δ_subset_of_toSSet_map_app ι (S := {p'}) (T := {p})
    (fun _ hz ↦ congrArg Subtype.val hz) (simplexOn hU) hstd
  let oU := (Manifold.Orientation.euclideanSpace 2).restrict U
  -- The class of the simplex read on `U` is minus the local orientation of `U` at `p`.
  have hclass : (TopPair.ofSubset ({p'}ᶜ : Set (TopCat.of U))).relClass R (n := 1)
      (simplexOn hU) hσU 1 = -(oU.toHomologicalOrientation hE2 p').val := by
    have hpU : p ∈ Set.range ι := by simpa [ι] using hU (interior_subset hp)
    have hinj := U.isOpenEmbedding'.injective_localHomologyMap R (j := ι) (A := {p'}) (T := {p})
      (by ext z; simp [p', ι, Subtype.ext_iff]) isClosed_singleton (singleton_subset_iff.2 hpU) 2
    have hU' := (Manifold.Orientation.euclideanSpace 2).isOrientationPreservingAt_restrict U p'
    apply hinj
    rw [map_neg, Manifold.Orientation.localHomologyMap_toHomologicalOrientation hE2 hE2 ι hι hU',
      TopPair.relClass_localHomologyMap_apply R ι hι _ hσU hstd
        (toSSet_map_app_simplexOn_subtypeVal hU),
      TopPair.relClass_fullSimplex_eq_neg_toHomologicalOrientation hp hstd]
    -- `ι p'` is `p`, and the two proofs of `finrank ℝ ℝ² = 2` agree.
    rfl
  have hmap := TopPair.relClass_localHomologyMap_apply R f (T := {g p}) hf (simplexOn hU) hσU
    (τ := σ.val) (fun i ↦ (range_toSSetObjEquiv_δ_subset_compl σ hU hgσ hg hKg i).trans
      (TopPair.range_map_ofSubset_compl_subset (singleton_subset_iff.2 hx)))
    (toSSet_map_app_simplexOn σ hU hgσ hg)
  -- `g` read on `U` preserves orientation from the restricted standard orientation to `o`.
  have hfo : Manifold.Orientation.IsOrientationPreservingAt oU o f p' :=
    (ho p p'.prop).comp (f := Subtype.val)
      ((Manifold.Orientation.euclideanSpace 2).isOrientationPreservingAt_restrict U p')
  rw [← ConcreteCategory.comp_apply, TopPair.relClass_localHomologyRestriction, ← hmap, hclass,
    map_neg,
    Manifold.Orientation.localHomologyMap_toHomologicalOrientation hE2 hE' f hf hfo,
    Manifold.Orientation.toHomologicalOrientation_neg, HomologicalOrientation.neg_apply,
    LocalOrientation.coe_neg]
  -- `f p'` is `g p`.
  rfl

end TauCeti.SmoothSimplex

namespace TauCeti.SmoothSimplex

/-- **The standard generator on a positively oriented simplex of `ℝ²`.** Let `σ` be a smooth
`2`-simplex of `ℝ²`, the restriction to `Δ²` of a map `g` that, on an open neighbourhood `U` of
`Δ²`, is an open embedding preserving the standard orientation, with `0 ∈ g (interior Δ²)`. The
generator of `H²(ℝ², ℝ² ∖ {0}; ℤ)` selected by the standard orientation
(`Orientation.localCohomologyClass`) pairs to `-1` with the class of `σ` in
`H₂(ℝ², ℝ² ∖ {0}; ℤ)`.

The generator pairs to `1` with the local orientation of `ℝ²` at `0` that the standard orientation
selects, and the class of `σ` is minus that local orientation
(`TauCeti.SmoothSimplex.relativeClass_eq_fundamentalClassOn`): Tau Ceti's local orientations are
minus the classes of positively oriented simplices
(`TopPair.relClass_fullSimplex_eq_neg_toHomologicalOrientation`). -/
theorem singularKronecker_localCohomologyClass_relClass
    (σ : SmoothSimplex 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) 2)
    {U : Opens (EuclideanSpace ℝ (Fin 2))} (hU : fullSimplex 2 ⊆ U)
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hgσ : ∀ y : fullSimplex 2, g y = σ.toContinuousMap y)
    (hg : IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2))))
    (ho : ∀ y ∈ U, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace 2) (Manifold.Orientation.euclideanSpace 2) g y)
    (h0 : 0 ∈ g '' interior (fullSimplex 2)) :
    ((TopPair.ofSubset (X := TopCat.of (EuclideanSpace ℝ (Fin 2))) {0}ᶜ).singularKronecker ℤ 2
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.localCohomologyClass
          finrank_euclideanSpace_fin)).hom
      ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).relClass
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (n := 1) σ.val
        (range_toSSetObjEquiv_δ_subset_compl σ hU hgσ hg (singleton_subset_iff.2 h0)) 1) =
      -1 := by
  have hE : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
  rw [relativeClass_eq_fundamentalClassOn σ hU hgσ hg hE _ ho isCompact_singleton
      (singleton_subset_iff.2 h0),
    HomologicalOrientation.fundamentalClassOn_singleton,
    Manifold.Orientation.toHomologicalOrientation_neg, HomologicalOrientation.neg_apply,
    LocalOrientation.coe_neg,
    Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart hE _ hE
      (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 2))) (by simp)
      (ContinuousLinearEquiv.refl ℝ _) ?_ ?_,
    ← Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl, map_neg,
    Orientation.kronecker_localCohomologyClass]
  · simpa using hasFDerivAt_id (𝕜 := ℝ) (0 : EuclideanSpace ℝ (Fin 2))
  · rw [ContinuousLinearEquiv.toLinearEquiv_refl, Orientation.map_refl]
    exact Manifold.Orientation.orientationAt_euclideanSpace 2 0

end TauCeti.SmoothSimplex
