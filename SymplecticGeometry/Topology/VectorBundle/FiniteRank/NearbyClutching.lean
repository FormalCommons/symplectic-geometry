/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Clutching
public import Mathlib.Analysis.SpecificLimits.Normed
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.SMul

/-!
# Nearby clutching functions give isomorphic clutchings

Let `E` be a finite-rank core over a paracompact R₁ space `X`, with fibres over a complete normed
`ℝ`-algebra `𝕜`, and let `f₀`, `f₁` be automorphisms of its pullback to `X × Circle`. If at every
point `w` the fibre maps satisfy `‖f₀(w)⁻¹ ∘ f₁(w) - 1‖ < 1`, then the clutchings of `E` by `f₀`
and by `f₁` are isomorphic.

The straight segment `(1 - t) f₀ + t f₁`, for `t ∈ [0, 1]`, is invertible at each point: after
`f₀⁻¹` it is `1 - t (1 - f₀⁻¹ f₁)`, a unit by the Neumann series
(`TauCeti.FiniteRankBundleCore.isIso_of_norm_conj_lt_one`). It is an
automorphism of the pullback of `E` to `(X × I) × Circle` with the fibre maps of `f₀` at time `0`
and of `f₁` at time `1`, so `TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_of_homotopic`
applies. This is the step of [Hatcher2017, §2.1] that clutching functions close enough to each
other are homotopic.

The fibre maps are read in the chart of `E` at each point. Since invertibility does not depend on
the chart, the criteria also take the estimate after a change of coordinates `U` at each point,
`‖U⁻¹ f₀⁻¹ f₁ U - 1‖ < 1`; this lets it be checked in finitely many charts of a compact base.

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.isIso_of_norm_conj_lt_one`: a morphism `f₁` of finite-rank cores
  is an isomorphism if, for an isomorphism `f₀`, some conjugate of `f₀⁻¹ f₁` is within `1` of the
  identity at every point;
* `TauCeti.FiniteRankBundleCore.segmentHom f₀ f₁`: the morphism of the pullback of `E` to
  `(X × I) × Circle` with fibre map `(1 - t) f₀(x, z) + t f₁(x, z)` at `((x, t), z)`, built with
  the multiplication of morphisms by continuous scalar functions
  (`TauCeti.FiniteRankBundleCore.fiberMap_smul`);
* `TauCeti.FiniteRankBundleCore.isIso_segmentHom_of_norm_conj_lt_one` and
  `TauCeti.FiniteRankBundleCore.isIso_segmentHom`: it is invertible when `‖U⁻¹ f₀⁻¹ f₁ U - 1‖ < 1`
  for some `U` at each point, in particular when `‖f₀⁻¹ f₁ - 1‖ < 1` everywhere;
* `TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_of_norm_conj_lt_one` and
  `TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_of_norm_lt_one`: nearby clutching
  functions give isomorphic clutchings.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1 (clutching functions over
  `X × S²`).
-/

public section

noncomputable section

open CategoryTheory

open scoped unitInterval

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]
  {E : FiniteRankBundleCore 𝕜 X}

/-- A morphism `f₁ : A ⟶ D` of finite-rank cores is an isomorphism if, for an isomorphism
`f₀ : A ≅ D`, at every point `x` some change of coordinates `U` brings `f₀⁻¹ ∘ f₁` within
distance less than `1` of the identity: `‖U⁻¹ ∘ f₀⁻¹ ∘ f₁ ∘ U - 1‖ < 1`. -/
theorem isIso_of_norm_conj_lt_one [CompleteSpace 𝕜] {B : Type*} [TopologicalSpace B]
    {A D : FiniteRankBundleCore 𝕜 B} (f₀ : A ≅ D) (f₁ : A ⟶ D)
    (h : ∀ x, ∃ U : ((Fin A.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜))ˣ,
      ‖↑U⁻¹ * ((f₀.inv.fiberMap x).comp (f₁.fiberMap x)) * ↑U - 1‖ < 1) :
    IsIso f₁ := by
  refine (isIso_iff_bijective _).2 fun x ↦ ?_
  obtain ⟨U, hU⟩ := h x
  -- By the Neumann series, `f₀⁻¹ ∘ f₁` is a unit of the ring of endomorphisms of the fibre.
  have hc : IsUnit (1 - (1 - ↑U⁻¹ * ((f₀.inv.fiberMap x).comp (f₁.fiberMap x)) * ↑U)) :=
    isUnit_one_sub_of_norm_lt_one (by rwa [norm_sub_rev])
  rw [sub_sub_cancel, Units.isUnit_mul_units, Units.isUnit_units_mul] at hc
  have hf : f₁.fiberMap x =
      (isoFiberEquiv f₀ x : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp
        ((f₀.inv.fiberMap x).comp (f₁.fiberMap x)) := by
    rw [toContinuousLinearMap_isoFiberEquiv, ← ContinuousLinearMap.comp_assoc,
      fiberMap_inv_hom_id, ContinuousLinearMap.id_comp]
  rw [hf, ContinuousLinearMap.coe_comp]
  exact (isoFiberEquiv f₀ x).bijective.comp
    (ContinuousLinearEquiv.unitsEquiv 𝕜 _ hc.unit).bijective

/-- The pullback of `E` to `(X × I) × Circle`, through `X × I`, on which the segment between two
clutching functions lives. -/
local notation "P" E => (FiniteRankBundleCore.pullback (FiniteRankBundleCore.pullback E
  (ContinuousMap.fst : C(X × I, X))) (ContinuousMap.fst : C((X × I) × Circle, X × I)))

/-- The pullback of `E` to `X × Circle`, on which the clutching functions live. -/
local notation "Q" E => (FiniteRankBundleCore.pullback E (ContinuousMap.fst : C(X × Circle, X)))

/-- A morphism of the pullback of `E` to `X × Circle`, pulled back to `(X × I) × Circle` along
`((x, t), z) ↦ (x, z)`. The pullback of `E` to `(X × I) × Circle` through `X × I` is by definition
its pullback along this map, with the same charts and transitions; the type ascription records
this. -/
private def pullbackForgetTime (f : (Q E) ⟶ (Q E)) : (P E) ⟶ (P E) :=
  pullbackMap f (ContinuousMap.fst.prodMap (.id Circle))

private theorem fiberMap_pullbackForgetTime (f : (Q E) ⟶ (Q E)) (b : (X × I) × Circle) :
    (pullbackForgetTime f).fiberMap b = f.fiberMap (b.1.1, b.2) :=
  fiberMap_pullbackMap f _ b

/-- An isomorphism of the pullback of `E` to `X × Circle`, pulled back to `(X × I) × Circle`
along `((x, t), z) ↦ (x, z)`. -/
private def pullbackForgetTimeIso (f : (Q E) ≅ (Q E)) : (P E) ≅ (P E) where
  hom := pullbackForgetTime f.hom
  inv := pullbackForgetTime f.inv
  hom_inv_id := hom_ext fun b ↦ by
    rw [fiberMap_comp, fiberMap_pullbackForgetTime, fiberMap_pullbackForgetTime,
      fiberMap_hom_inv_id, fiberMap_id]
    -- The two identities are those of `Fin (Q E).rank → 𝕜` and `Fin (P E).rank → 𝕜`: both
    -- ranks are that of `E` by definition.
    rfl
  inv_hom_id := hom_ext fun b ↦ by
    rw [fiberMap_comp, fiberMap_pullbackForgetTime, fiberMap_pullbackForgetTime,
      fiberMap_inv_hom_id, fiberMap_id]
    -- As above, the ranks of the two pullbacks are that of `E` by definition.
    rfl

private theorem pullbackForgetTimeIso_inv (f : (Q E) ≅ (Q E)) :
    (pullbackForgetTimeIso f).inv = pullbackForgetTime f.inv :=
  (rfl)

variable [NormedAlgebra ℝ 𝕜]

variable (𝕜 X) in
/-- The time `t ∈ I` of a point `((x, t), z)`, as a scalar. -/
private def time : C((X × I) × Circle, 𝕜) :=
  ⟨fun b ↦ algebraMap ℝ 𝕜 b.1.2, by fun_prop⟩

/-- The segment between two morphisms `f₀` and `f₁` of the pullback of `E` to `X × Circle`: the
morphism of its pullback to `(X × I) × Circle` with fibre map `(1 - t) f₀(x, z) + t f₁(x, z)` at
`((x, t), z)` (`fiberMap_segmentHom`). -/
def segmentHom (f₀ f₁ : (Q E) ⟶ (Q E)) : (P E) ⟶ (P E) :=
  (1 - time 𝕜 X) • pullbackForgetTime f₀ + time 𝕜 X • pullbackForgetTime f₁

@[simp]
theorem fiberMap_segmentHom (f₀ f₁ : (Q E) ⟶ (Q E)) (b : (X × I) × Circle) :
    (segmentHom f₀ f₁).fiberMap b = (1 - algebraMap ℝ 𝕜 b.1.2) • f₀.fiberMap (b.1.1, b.2) +
      algebraMap ℝ 𝕜 b.1.2 • f₁.fiberMap (b.1.1, b.2) := by
  rw [segmentHom, fiberMap_add, fiberMap_smul, fiberMap_smul, fiberMap_pullbackForgetTime,
    fiberMap_pullbackForgetTime, ContinuousMap.sub_apply, ContinuousMap.one_apply, time,
    ContinuousMap.coe_mk]

theorem fiberMap_segmentHom_zero (f₀ f₁ : (Q E) ⟶ (Q E)) (w : X × Circle) :
    (segmentHom f₀ f₁).fiberMap ((w.1, 0), w.2) = f₀.fiberMap w := by
  simp [fiberMap_segmentHom]

theorem fiberMap_segmentHom_one (f₀ f₁ : (Q E) ⟶ (Q E)) (w : X × Circle) :
    (segmentHom f₀ f₁).fiberMap ((w.1, 1), w.2) = f₁.fiberMap w := by
  simp [fiberMap_segmentHom]

variable [CompleteSpace 𝕜]

/-- The segment from an automorphism `f₀` to a morphism `f₁` is invertible if at every point `w`
some change of coordinates `U` brings `f₀⁻¹ ∘ f₁` within distance less than `1` of the identity:
`‖U⁻¹ ∘ f₀⁻¹ ∘ f₁ ∘ U - 1‖ < 1`. Invertibility does not depend on the coordinates, so the estimate
may be checked in any chart. -/
theorem isIso_segmentHom_of_norm_conj_lt_one (f₀ : (Q E) ≅ (Q E)) (f₁ : (Q E) ⟶ (Q E))
    (h : ∀ w, ∃ U : ((Fin (Q E).rank → 𝕜) →L[𝕜] (Fin (Q E).rank → 𝕜))ˣ,
      ‖↑U⁻¹ * ((f₀.inv.fiberMap w).comp (f₁.fiberMap w)) * ↑U - 1‖ < 1) :
    IsIso (segmentHom f₀.hom f₁) := by
  refine isIso_of_norm_conj_lt_one (pullbackForgetTimeIso f₀) _ fun b ↦ ?_
  obtain ⟨U, hU⟩ := h (b.1.1, b.2)
  refine ⟨U, ?_⟩
  set s := algebraMap ℝ 𝕜 b.1.2 with hs_def
  have hs : ‖s‖ ≤ 1 := by
    rw [hs_def, norm_algebraMap', Real.norm_eq_abs, abs_of_nonneg b.1.2.property.1]
    exact b.1.2.property.2
  rw [pullbackForgetTimeIso_inv, fiberMap_pullbackForgetTime, fiberMap_segmentHom,
    ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul,
    fiberMap_hom_inv_id, ← ContinuousLinearMap.one_def]
  -- The goal is stated in the endomorphisms of `Fin (P E).rank → 𝕜`; state it in those of
  -- `Fin (Q E).rank → 𝕜`, the same ring since both ranks are that of `E` by definition.
  change ‖(↑U⁻¹ : (Fin (Q E).rank → 𝕜) →L[𝕜] (Fin (Q E).rank → 𝕜)) *
    ((1 - s) • 1 + s • (f₀.inv.fiberMap (b.1.1, b.2)).comp (f₁.fiberMap (b.1.1, b.2))) * ↑U -
      1‖ < 1
  -- At time `s`, `f₀⁻¹ ∘ ((1 - s) f₀ + s f₁) - 1 = s (f₀⁻¹ ∘ f₁ - 1)`, in any coordinates.
  have he : (↑U⁻¹ : (Fin (Q E).rank → 𝕜) →L[𝕜] (Fin (Q E).rank → 𝕜)) *
      ((1 - s) • 1 + s • (f₀.inv.fiberMap (b.1.1, b.2)).comp (f₁.fiberMap (b.1.1, b.2))) * ↑U -
        1 = s • (↑U⁻¹ * ((f₀.inv.fiberMap (b.1.1, b.2)).comp (f₁.fiberMap (b.1.1, b.2))) * ↑U -
          1) := by
    ext v : 1
    have hU : (↑U⁻¹ : (Fin (Q E).rank → 𝕜) →L[𝕜] (Fin (Q E).rank → 𝕜))
        ((↑U : (Fin (Q E).rank → 𝕜) →L[𝕜] (Fin (Q E).rank → 𝕜)) v) = v := by
      rw [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
    simp only [sub_apply, mul_apply_eq_comp, add_apply, smul_apply, one_apply_eq_self, map_add,
      map_smul, hU]
    module
  rw [he, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hs).trans_lt hU

/-- The segment from an automorphism `f₀` to a morphism `f₁` is invertible if `f₀⁻¹ ∘ f₁` is
everywhere within distance less than `1` of the identity. -/
theorem isIso_segmentHom (f₀ : (Q E) ≅ (Q E)) (f₁ : (Q E) ⟶ (Q E))
    (h : ∀ w, ‖(f₀.inv.fiberMap w).comp (f₁.fiberMap w) - .id 𝕜 _‖ < 1) :
    IsIso (segmentHom f₀.hom f₁) :=
  isIso_segmentHom_of_norm_conj_lt_one f₀ f₁ fun w ↦ ⟨1, by
    rw [inv_one, Units.val_one, one_mul, mul_one, ContinuousLinearMap.one_def]; exact h w⟩

/-- Let `X` be paracompact and R₁, and let `f₀` and `f₁` be automorphisms of the pullback of `E`
to `X × Circle`. If at every point `w` some change of coordinates `U` brings the fibre map of
`f₀⁻¹ ∘ f₁` within distance less than `1` of the identity, `‖U⁻¹ ∘ f₀⁻¹ ∘ f₁ ∘ U - 1‖ < 1`, then
the clutchings of `E` by `f₀` and by `f₁` are isomorphic. -/
theorem nonempty_iso_clutching_of_norm_conj_lt_one [ParacompactSpace X] [R1Space X]
    {f₀ f₁ : (Q E) ≅ (Q E)}
    (h : ∀ w, ∃ U : ((Fin (Q E).rank → 𝕜) →L[𝕜] (Fin (Q E).rank → 𝕜))ˣ,
      ‖↑U⁻¹ * ((f₀.inv.fiberMap w).comp (f₁.hom.fiberMap w)) * ↑U - 1‖ < 1) :
    Nonempty (E.clutching f₀ ≅ E.clutching f₁) :=
  haveI := isIso_segmentHom_of_norm_conj_lt_one f₀ f₁.hom h
  E.nonempty_iso_clutching_of_homotopic (asIso (segmentHom f₀.hom f₁.hom))
    (fiberMap_segmentHom_zero f₀.hom f₁.hom) (fiberMap_segmentHom_one f₀.hom f₁.hom)

/-- **Nearby clutching functions give isomorphic clutchings.** Let `X` be paracompact and R₁, for
instance compact Hausdorff, and let `f₀` and `f₁` be automorphisms of the pullback of `E` to
`X × Circle`. If at every point `w` the fibre map of `f₀⁻¹ ∘ f₁` is within distance less than `1`
of the identity in operator norm, then the clutchings of `E` by `f₀` and by `f₁` are
isomorphic. -/
theorem nonempty_iso_clutching_of_norm_lt_one [ParacompactSpace X] [R1Space X]
    {f₀ f₁ : (Q E) ≅ (Q E)}
    (h : ∀ w, ‖(f₀.inv.fiberMap w).comp (f₁.hom.fiberMap w) - .id 𝕜 _‖ < 1) :
    Nonempty (E.clutching f₀ ≅ E.clutching f₁) :=
  nonempty_iso_clutching_of_norm_conj_lt_one fun w ↦ ⟨1, by
    rw [inv_one, Units.val_one, one_mul, mul_one, ContinuousLinearMap.one_def]; exact h w⟩

end TauCeti.FiniteRankBundleCore

end
