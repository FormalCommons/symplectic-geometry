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

* `TauCeti.FiniteRankBundleCore.inclOne X`: the inclusion `x ↦ (x, [1 : 1])` of `X` in
  `X × ℙ ℂ (Fin 2 → ℂ)`, along which `E` is the pullback of `F`.
* `TauCeti.FiniteRankBundleCore.nonempty_pullback_affineChartMap_iso`: over `X × (Fin 1 → ℂ)`,
  the pullback of `F` along the inverse `affineChartMap X i` of an affine chart of the projective
  line is the pullback of `E` along the projection, since the affine line contracts to the
  coordinate `1` of `[1 : 1]`.
* `TauCeti.FiniteRankBundleCore.nonempty_pullback_subtypeVal_iso_of_subset_affineOpen`: hence the
  same holds for the restriction of `F` to `X × S`, for any set `S` inside an affine open.
* `SymplecticGeometry.ProjectiveLine.affineChart_symm_mem_annulus_iff`: the point `[z : 1]` lies
  in the annulus `innerDisc ∩ outerDisc` exactly when `1/2 < |z| < 2`.
* `TauCeti.FiniteRankBundleCore.circleToAnnulus X`: the map `(x, u) ↦ (x, [u : 1])` from
  `X × Circle` to the product of `X` with the annulus, and
  `TauCeti.FiniteRankBundleCore.annulusDeformation X`: the deformation
  `((x, [z : 1]), t) ↦ (x, [((1 - t) + t / |z|) z : 1])` of that product onto the image of the
  first map, which at time `1` is the first map after `clutchingMap`.
* `TauCeti.FiniteRankBundleCore.exists_iso_clutching`: every core over `X × ℙ ℂ (Fin 2 → ℂ)` is a
  clutching of its restriction to `X × {[1 : 1]}`.

## Proof

Each of the two discs lies in an affine open, so the restriction of `F` to its product with `X` is
the pullback of `E` along the projection, by homotopy invariance of pullbacks
(`TauCeti.FiniteRankBundleCore.nonempty_pullback_iso_of_homotopic`) applied to the segments from
`[1 : 1]` in the affine chart. By `TauCeti.FiniteRankBundleCore.isoGlue`, `F` is then the gluing of
the pullback of `E` by the transition `g` of the two isomorphisms over the product of `X` with the
annulus. Let `f` be `g` restricted to `X × Circle`. The radial deformation of the annulus onto the
circle joins `g` to `clutchingAut E f`, which glues to `E.clutching f`, and gluings by homotopic
automorphisms are isomorphic (`TauCeti.FiniteRankBundleCore.nonempty_iso_glue_of_homotopic`).

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (every bundle over `X × S²` is a
  clutching).
-/

public section

noncomputable section

open Set CategoryTheory Projectivization

open scoped unitInterval LinearAlgebra.Projectivization

/-! ### Points of the annulus in the affine chart -/

namespace SymplecticGeometry.ProjectiveLine

/-- The point `[z : 1]` of the projective line lies in the annulus `innerDisc ∩ outerDisc` exactly
when `1/2 < |z| < 2`. -/
theorem affineChart_symm_mem_annulus_iff (z : Fin 1 → ℂ) :
    (affineChart 1).symm z ∈ innerDisc ∩ outerDisc ↔ 2⁻¹ < ‖z 0‖ ∧ ‖z 0‖ < 2 := by
  rw [affineChart_symm_apply, mem_inter_iff, mk_mem_innerDisc_iff, mk_mem_outerDisc_iff]
  have h0 : Fin.insertNth (α := fun _ ↦ ℂ) 1 1 z 0 = z 0 := by
    simp
  rw [Fin.insertNth_apply_same, h0, div_one, one_div, norm_inv]
  constructor
  · rintro ⟨⟨-, h2⟩, hz, h'⟩
    refine ⟨?_, h2⟩
    have hpos : 0 < ‖z 0‖ := norm_pos_iff.2 hz
    rwa [inv_lt_comm₀ hpos (by norm_num)] at h'
  · rintro ⟨h', h2⟩
    have hpos : 0 < ‖z 0‖ := lt_trans (by norm_num) h'
    refine ⟨⟨one_ne_zero, h2⟩, norm_pos_iff.1 hpos, ?_⟩
    rwa [inv_lt_comm₀ hpos (by norm_num)]

end SymplecticGeometry.ProjectiveLine

namespace TauCeti.FiniteRankBundleCore

open SymplecticGeometry.ProjectiveLine

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] (X : Type*) [TopologicalSpace X]

/-! ### The restriction of a core to the product with a disc -/

/-- The inverse of the affine chart `i` of the projective line, in the second factor of
`X × (Fin 1 → ℂ)`. -/
def affineChartMap (i : Fin 2) : C(X × (Fin 1 → ℂ), X × ℙ ℂ (Fin 2 → ℂ)) :=
  ContinuousMap.prodMap (.id X) ⟨(affineChart i).symm, continuous_affineChart_symm i⟩

@[simp]
theorem affineChartMap_apply (i : Fin 2) (p : X × (Fin 1 → ℂ)) :
    affineChartMap X i p = (p.1, (affineChart i).symm p.2) :=
  (rfl)

/-- The inclusion `x ↦ (x, [1 : 1])` of `X` in `X × ℙ ℂ (Fin 2 → ℂ)`. -/
def inclOne : C(X, X × ℙ ℂ (Fin 2 → ℂ)) :=
  (ContinuousMap.id X).prodMk (.const X (Projectivization.mk ℂ 1 one_ne_zero))

@[simp]
theorem inclOne_apply (x : X) : inclOne X x = (x, Projectivization.mk ℂ 1 one_ne_zero) :=
  (rfl)

/-! ### The circle in the annulus, and the radial deformation onto it -/

/-- The radial deformation of the annulus onto the unit circle, at time `t`, in the affine
coordinate: `z ↦ ((1 - t) + t / |z|) z`. -/
private def radialDeform (z : Fin 1 → ℂ) (t : ℝ) : Fin 1 → ℂ :=
  ((1 - t) + t * ‖z 0‖⁻¹ : ℝ) • z

private theorem radialDeform_mem {z : Fin 1 → ℂ} (hz : 2⁻¹ < ‖z 0‖ ∧ ‖z 0‖ < 2) {t : ℝ}
    (ht : t ∈ I) : 2⁻¹ < ‖radialDeform z t 0‖ ∧ ‖radialDeform z t 0‖ < 2 := by
  have hpos : 0 < ‖z 0‖ := lt_trans (by norm_num) hz.1
  have hc : 0 ≤ (1 - t) + t * ‖z 0‖⁻¹ :=
    add_nonneg (sub_nonneg.2 ht.2) (mul_nonneg ht.1 (inv_nonneg.2 (norm_nonneg _)))
  -- The new modulus `(1 - t) |z| + t` lies between `|z|` and `1`.
  have hn : ‖radialDeform z t 0‖ = (1 - t) * ‖z 0‖ + t := by
    rw [radialDeform, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc, add_mul, mul_assoc,
      inv_mul_cancel₀ hpos.ne', mul_one]
  rw [hn]
  obtain ⟨h0, h1⟩ := ht
  constructor <;> nlinarith [hz.1, hz.2]

/-- The map `(x, u) ↦ (x, [u : 1])` from `X × Circle` to the product of `X` with the annulus
`innerDisc ∩ outerDisc`. -/
def circleToAnnulus :
    C(X × Circle, ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc :
      Set (X × ℙ ℂ (Fin 2 → ℂ)))) :=
  ⟨fun q ↦ ⟨(q.1, (affineChart 1).symm fun _ ↦ (q.2 : ℂ)),
      (affineChart_symm_mem_annulus_iff _).2 (by simp; norm_num)⟩,
    ((continuous_fst.prodMk ((continuous_affineChart_symm 1).comp
      (continuous_pi fun _ ↦ continuous_subtypeVal.comp continuous_snd)))).subtype_mk _⟩

@[simp]
theorem coe_circleToAnnulus_apply (q : X × Circle) :
    (circleToAnnulus X q : X × ℙ ℂ (Fin 2 → ℂ)) =
      (q.1, (affineChart 1).symm fun _ ↦ (q.2 : ℂ)) :=
  (rfl)

/-- The radial deformation of the product of `X` with the annulus onto the product with the unit
circle, `((x, [z : 1]), t) ↦ (x, [((1 - t) + t / |z|) z : 1])`, on the part over the annulus of
`(X × ℙ ℂ (Fin 2 → ℂ)) × I`. -/
def annulusDeformation :
    C(↥(Prod.fst ⁻¹' (Prod.snd ⁻¹' innerDisc) ∩ Prod.fst ⁻¹' (Prod.snd ⁻¹' outerDisc) :
        Set ((X × ℙ ℂ (Fin 2 → ℂ)) × I)),
      ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :=
  ⟨fun w ↦ ⟨(w.val.1.1, (affineChart 1).symm
      (radialDeform (affineChart 1 w.val.1.2) (w.val.2 : ℝ))),
      (affineChart_symm_mem_annulus_iff _).2 <| radialDeform_mem
        (by
          rw [← affineChart_symm_mem_annulus_iff, (affineChart 1).left_inv
            (by rw [affineChart_source]; exact (mem_innerDisc_iff.1 w.property.1).1)]
          exact w.property)
        w.val.2.property⟩, by
    refine Continuous.subtype_mk (continuous_fst.comp (continuous_fst.comp continuous_subtypeVal)
      |>.prodMk ((continuous_affineChart_symm 1).comp ?_)) _
    -- The affine coordinate is continuous on the annulus, and nonzero there.
    have hz : Continuous fun w : ↥(Prod.fst ⁻¹' (Prod.snd ⁻¹' innerDisc) ∩
        Prod.fst ⁻¹' (Prod.snd ⁻¹' outerDisc) : Set ((X × ℙ ℂ (Fin 2 → ℂ)) × I)) ↦
        affineChart 1 w.val.1.2 :=
      continuousOn_iff_continuous_domRestrict.1
        ((continuousOn_affineChart (K := ℂ) (n := 1) 1).mono (t := innerDisc)
          fun _ hp ↦ (mem_innerDisc_iff.1 hp).1) |>.comp
        ((continuous_snd.comp (continuous_fst.comp continuous_subtypeVal)).subtype_mk
          fun w ↦ w.property.1)
    have ht : Continuous fun w : ↥(Prod.fst ⁻¹' (Prod.snd ⁻¹' innerDisc) ∩
        Prod.fst ⁻¹' (Prod.snd ⁻¹' outerDisc) : Set ((X × ℙ ℂ (Fin 2 → ℂ)) × I)) ↦
        (w.val.2 : ℝ) :=
      continuous_subtypeVal.comp (continuous_snd.comp continuous_subtypeVal)
    have hne : ∀ w : ↥(Prod.fst ⁻¹' (Prod.snd ⁻¹' innerDisc) ∩
        Prod.fst ⁻¹' (Prod.snd ⁻¹' outerDisc) : Set ((X × ℙ ℂ (Fin 2 → ℂ)) × I)),
        ‖affineChart 1 w.val.1.2 0‖ ≠ 0 := fun w ↦
      norm_ne_zero_iff.2 (affineChart_one_ne_zero_of_mem w.property)
    exact (((continuous_const.sub ht).add (ht.mul
      (((continuous_apply 0).comp hz).norm.inv₀ hne))).smul hz)⟩

theorem coe_annulusDeformation_apply
    (w : ↥(Prod.fst ⁻¹' (Prod.snd ⁻¹' innerDisc) ∩ Prod.fst ⁻¹' (Prod.snd ⁻¹' outerDisc) :
      Set ((X × ℙ ℂ (Fin 2 → ℂ)) × I))) :
    (annulusDeformation X w : X × ℙ ℂ (Fin 2 → ℂ)) =
      (w.val.1.1, (affineChart 1).symm
        (((1 - w.val.2) + w.val.2 * ‖affineChart 1 w.val.1.2 0‖⁻¹ : ℝ) •
          affineChart 1 w.val.1.2)) :=
  (rfl)

/-- At time `0`, the radial deformation of the annulus is the identity. -/
theorem annulusDeformation_zero
    (w : ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :
    annulusDeformation X ⟨(w.val, 0), w.property⟩ = w :=
  Subtype.ext <| Prod.ext (by simp [coe_annulusDeformation_apply]) <| by
    simpa [coe_annulusDeformation_apply] using (affineChart 1).left_inv
      (by rw [affineChart_source]; exact (mem_innerDisc_iff.1 w.property.1).1)

/-- At time `1`, the radial deformation of the annulus is the radial retraction `clutchingMap`
onto `X × Circle`, followed by the inclusion of `X × Circle` in the product with the annulus. -/
theorem annulusDeformation_one
    (w : ↥(Prod.snd ⁻¹' innerDisc ∩ Prod.snd ⁻¹' outerDisc : Set (X × ℙ ℂ (Fin 2 → ℂ)))) :
    annulusDeformation X ⟨(w.val, 1), w.property⟩ = circleToAnnulus X (clutchingMap X w) := by
  refine Subtype.ext <| Prod.ext (by simp [coe_annulusDeformation_apply]) ?_
  simp only [coe_annulusDeformation_apply, coe_circleToAnnulus_apply, clutchingMap_apply,
    coe_annulusToCircle_apply, Set.Icc.coe_one, sub_self, one_mul, zero_add]
  congr 1
  funext j
  rw [Subsingleton.elim j 0, Pi.smul_apply]

variable [CompactSpace X] [T2Space X] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
  (F : FiniteRankBundleCore 𝕜 (X × ℙ ℂ (Fin 2 → ℂ)))

/-- **A core is trivial along the affine line.** For `X` compact Hausdorff and a core `F` over
`X × ℙ ℂ (Fin 2 → ℂ)`, the pullback of `F` along the inverse of an affine chart in the second
factor is isomorphic to the pullback along the projection `X × (Fin 1 → ℂ) → X` of the restriction
of `F` to `X × {[1 : 1]}`. -/
theorem nonempty_pullback_affineChartMap_iso (i : Fin 2) :
    Nonempty (F.pullback (affineChartMap X i) ≅
      (F.pullback (inclOne X)).pullback ContinuousMap.fst) := by
  -- The segments from the coordinate `1` of `[1 : 1]` contract the affine line.
  have h : (affineChartMap X i).Homotopic ((inclOne X).comp ContinuousMap.fst) :=
    ⟨⟨⟨fun q ↦ affineChartMap X i (q.2.1, 1 + (1 - q.1 : ℝ) • (q.2.2 - 1)), by fun_prop⟩,
      fun q ↦ by simp, fun q ↦ by simp⟩⟩
  exact F.nonempty_pullback_iso_of_homotopic h

/-- **A core is trivial over the product with a part of an affine open.** For `X` compact
Hausdorff, a core `F` over `X × ℙ ℂ (Fin 2 → ℂ)` and a set `S` inside the affine open `i` of the
projective line, the restriction of `F` to `X × S` is isomorphic to that of the pullback along the
projection of the restriction of `F` to `X × {[1 : 1]}`. -/
theorem nonempty_pullback_subtypeVal_iso_of_subset_affineOpen {i : Fin 2}
    {S : Set (ℙ ℂ (Fin 2 → ℂ))} (hS : S ⊆ affineOpen i) :
    Nonempty (F.pullback (ContinuousMap.subtypeVal (Prod.snd ⁻¹' S)) ≅
      ((F.pullback (inclOne X)).pullback ContinuousMap.fst).pullback
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
  obtain ⟨e⟩ := F.nonempty_pullback_affineChartMap_iso X i
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
    ∃ f : (F.pullback (inclOne X)).pullback (ContinuousMap.fst : C(X × Circle, X)) ≅
        (F.pullback (inclOne X)).pullback (ContinuousMap.fst : C(X × Circle, X)),
      Nonempty (F ≅ (F.pullback (inclOne X)).clutching f) := by
  obtain ⟨φ⟩ := F.nonempty_pullback_subtypeVal_iso_of_subset_affineOpen X
    (S := innerDisc) fun _ hp ↦ (mem_innerDisc_iff.1 hp).1
  obtain ⟨ψ⟩ := F.nonempty_pullback_subtypeVal_iso_of_subset_affineOpen X
    (S := outerDisc) fun _ hp ↦ (mem_outerDisc_iff.1 hp).1
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
    (g₁ := clutchingAut (F.pullback (inclOne X))
      ((pullbackFunctor (circleToAnnulus X)).mapIso (glueTransition φ ψ)))
    ((pullbackFunctor (annulusDeformation X)).mapIso (glueTransition φ ψ))
    -- The cores of `fiberMap_pullbackMap` are those of the statement by `pullback_comp`: all are
    -- the pullback of `E` along `w ↦ w.val.1.1`.
    (fun w ↦ (fiberMap_pullbackMap (glueTransition φ ψ).hom (annulusDeformation X) _).trans
      (congrArg _ (annulusDeformation_zero X w)))
    (fun w ↦ (fiberMap_pullbackMap (glueTransition φ ψ).hom (annulusDeformation X) _).trans <|
      (congrArg _ (annulusDeformation_one X w)).trans <|
        (fiberMap_pullbackMap (glueTransition φ ψ).hom (circleToAnnulus X) _).symm.trans
          (fiberMap_clutchingAut_hom (F.pullback (inclOne X))
            ((pullbackFunctor (circleToAnnulus X)).mapIso (glueTransition φ ψ)) w).symm)
  exact ⟨isoGlue φ ψ hU hV hUV ≪≫ e⟩

end TauCeti.FiniteRankBundleCore

end
