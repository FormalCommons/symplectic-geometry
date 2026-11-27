/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Clutching
public import Mathlib.Analysis.SpecificLimits.Normed
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.SMul
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.CompactCharts
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic

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
* `TauCeti.FiniteRankBundleCore.exists_isIso_add_smul`: over a compact Hausdorff base, `a + c b` is
  an isomorphism for an isomorphism `a` and all small enough scalars `c`;
* `TauCeti.FiniteRankBundleCore.pullbackForgetTime` and
  `TauCeti.FiniteRankBundleCore.pullbackForgetTimeIso`: a morphism or an isomorphism of the
  pullback of `E` to `X × Circle`, pulled back to `(X × I) × Circle` along `((x, t), z) ↦ (x, z)`,
  as a homotopy that does not depend on the time;
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

/-- **Invertibility is open over a compact base.** Over a compact Hausdorff base, for an
isomorphism `a` and any morphism `b` of finite-rank cores, `a + c b` is an isomorphism for every
scalar `c` small enough. -/
theorem exists_isIso_add_smul [CompleteSpace 𝕜] [CompactSpace X] [T2Space X]
    {A D : FiniteRankBundleCore 𝕜 X} (a : A ⟶ D) [IsIso a] (b : A ⟶ D) :
    ∃ ε > 0, ∀ c : 𝕜, ‖c‖ < ε → IsIso (a + ContinuousMap.const X c • b) := by
  obtain ⟨C, hC⟩ := exists_norm_conj_fiberMap_le (b ≫ inv a)
  set C' := max C 1
  have hC' : 0 < C' := lt_max_of_lt_right one_pos
  refine ⟨1 / C', by positivity, fun c hc ↦ ?_⟩
  refine isIso_of_norm_conj_lt_one (asIso a) _ fun x ↦ ?_
  obtain ⟨U, hU⟩ := hC x
  refine ⟨U, ?_⟩
  -- After `a⁻¹`, the morphism `a + c b` is `1 + c (a⁻¹ ∘ b)`, in any coordinates.
  have he : ↑U⁻¹ * (((asIso a).inv.fiberMap x).comp
      ((a + ContinuousMap.const X c • b).fiberMap x)) * ↑U - 1 =
        c • (↑U⁻¹ * (b ≫ inv a).fiberMap x * ↑U) := by
    simp only [asIso_inv, fiberMap_add, fiberMap_smul, ContinuousMap.const_apply,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul, ← fiberMap_comp,
      IsIso.hom_inv_id, fiberMap_id, ← ContinuousLinearMap.one_def]
    simp [mul_add, add_mul]
  rw [he, norm_smul]
  calc ‖c‖ * ‖↑U⁻¹ * (b ≫ inv a).fiberMap x * ↑U‖ ≤ ‖c‖ * C' :=
        mul_le_mul_of_nonneg_left (hU.trans (le_max_left _ _)) (norm_nonneg _)
    _ < 1 / C' * C' := mul_lt_mul_of_pos_right hc hC'
    _ = 1 := by field_simp

/-- A morphism of the pullback of `E` to `X × Circle`, pulled back to `(X × I) × Circle` along
`((x, t), z) ↦ (x, z)`, where the homotopies of `nonempty_iso_clutching_of_homotopic` live. The
pullback of `E` to `(X × I) × Circle` through `X × I` is by definition its pullback along this map,
with the same charts and transitions; the type ascription records this. -/
def pullbackForgetTime (f : E.circlePullback ⟶ E.circlePullback) :
    (E.pullback (ContinuousMap.fst : C(X × I, X))).circlePullback ⟶
      (E.pullback (ContinuousMap.fst : C(X × I, X))).circlePullback :=
  pullbackMap f (ContinuousMap.fst.prodMap (.id Circle))

theorem pullbackForgetTime_def (f : E.circlePullback ⟶ E.circlePullback) :
    pullbackForgetTime f = pullbackMap f (ContinuousMap.fst.prodMap (.id Circle)) :=
  (rfl)

@[simp]
theorem fiberMap_pullbackForgetTime (f : E.circlePullback ⟶ E.circlePullback)
    (b : (X × I) × Circle) :
    (pullbackForgetTime f).fiberMap b = f.fiberMap (b.1.1, b.2) :=
  fiberMap_pullbackMap f _ b

@[simp]
theorem pullbackForgetTime_id :
    pullbackForgetTime (𝟙 E.circlePullback) =
      𝟙 (E.pullback (ContinuousMap.fst : C(X × I, X))).circlePullback :=
  (pullbackFunctor (ContinuousMap.fst.prodMap (.id Circle))).map_id _

@[simp]
theorem pullbackForgetTime_comp (f g : E.circlePullback ⟶ E.circlePullback) :
    pullbackForgetTime (f ≫ g) = pullbackForgetTime f ≫ pullbackForgetTime g :=
  (pullbackFunctor (ContinuousMap.fst.prodMap (.id Circle))).map_comp f g

/-- An isomorphism of the pullback of `E` to `X × Circle`, pulled back to `(X × I) × Circle`
along `((x, t), z) ↦ (x, z)`: its morphisms are the pullbacks `pullbackForgetTime` of those of the
isomorphism. -/
def pullbackForgetTimeIso (f : E.circlePullback ≅ E.circlePullback) :
    (E.pullback (ContinuousMap.fst : C(X × I, X))).circlePullback ≅
      (E.pullback (ContinuousMap.fst : C(X × I, X))).circlePullback :=
  (pullbackFunctor (ContinuousMap.fst.prodMap (.id Circle))).mapIso f

@[simp]
theorem pullbackForgetTimeIso_hom (f : E.circlePullback ≅ E.circlePullback) :
    (pullbackForgetTimeIso f).hom = pullbackForgetTime f.hom :=
  (rfl)

@[simp]
theorem pullbackForgetTimeIso_inv (f : E.circlePullback ≅ E.circlePullback) :
    (pullbackForgetTimeIso f).inv = pullbackForgetTime f.inv :=
  (rfl)

theorem fiberMap_pullbackForgetTimeIso_hom (f : E.circlePullback ≅ E.circlePullback)
    (b : (X × I) × Circle) :
    (pullbackForgetTimeIso f).hom.fiberMap b = f.hom.fiberMap (b.1.1, b.2) := by
  rw [pullbackForgetTimeIso_hom, fiberMap_pullbackForgetTime]

variable [NormedAlgebra ℝ 𝕜]

variable (𝕜 X) in
/-- The time `t ∈ I` of a point `((x, t), z)`, as a scalar. -/
private def time : C((X × I) × Circle, 𝕜) :=
  ⟨fun b ↦ algebraMap ℝ 𝕜 b.1.2, by fun_prop⟩

/-- The segment between two morphisms `f₀` and `f₁` of the pullback of `E` to `X × Circle`: the
morphism of its pullback to `(X × I) × Circle` with fibre map `(1 - t) f₀(x, z) + t f₁(x, z)` at
`((x, t), z)` (`fiberMap_segmentHom`). -/
def segmentHom (f₀ f₁ : E.circlePullback ⟶ E.circlePullback) :
    (E.pullback (ContinuousMap.fst : C(X × I, X))).circlePullback ⟶
      (E.pullback (ContinuousMap.fst : C(X × I, X))).circlePullback :=
  (1 - time 𝕜 X) • pullbackForgetTime f₀ + time 𝕜 X • pullbackForgetTime f₁

@[simp]
theorem fiberMap_segmentHom (f₀ f₁ : E.circlePullback ⟶ E.circlePullback) (b : (X × I) × Circle) :
    (segmentHom f₀ f₁).fiberMap b = (1 - algebraMap ℝ 𝕜 b.1.2) • f₀.fiberMap (b.1.1, b.2) +
      algebraMap ℝ 𝕜 b.1.2 • f₁.fiberMap (b.1.1, b.2) := by
  rw [segmentHom, fiberMap_add, fiberMap_smul, fiberMap_smul, fiberMap_pullbackForgetTime,
    fiberMap_pullbackForgetTime, ContinuousMap.sub_apply, ContinuousMap.one_apply, time,
    ContinuousMap.coe_mk]

theorem fiberMap_segmentHom_zero (f₀ f₁ : E.circlePullback ⟶ E.circlePullback) (w : X × Circle) :
    (segmentHom f₀ f₁).fiberMap ((w.1, 0), w.2) = f₀.fiberMap w := by
  simp [fiberMap_segmentHom]

theorem fiberMap_segmentHom_one (f₀ f₁ : E.circlePullback ⟶ E.circlePullback) (w : X × Circle) :
    (segmentHom f₀ f₁).fiberMap ((w.1, 1), w.2) = f₁.fiberMap w := by
  simp [fiberMap_segmentHom]

variable [CompleteSpace 𝕜]

/-- The segment from an automorphism `f₀` to a morphism `f₁` is invertible if at every point `w`
some change of coordinates `U` brings `f₀⁻¹ ∘ f₁` within distance less than `1` of the identity:
`‖U⁻¹ ∘ f₀⁻¹ ∘ f₁ ∘ U - 1‖ < 1`. Invertibility does not depend on the coordinates, so the estimate
may be checked in any chart. -/
theorem isIso_segmentHom_of_norm_conj_lt_one (f₀ : E.circlePullback ≅ E.circlePullback)
    (f₁ : E.circlePullback ⟶ E.circlePullback)
    (h : ∀ w, ∃ U : ((Fin E.circlePullback.rank → 𝕜) →L[𝕜] (Fin E.circlePullback.rank → 𝕜))ˣ,
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
  -- The goal is stated in the endomorphisms of `Fin r → 𝕜`, `r` the rank of the pullback of `E`
  -- to `(X × I) × Circle`; state it in those of `Fin E.circlePullback.rank → 𝕜`, the same ring
  -- since both ranks are that of `E` by definition.
  change ‖(↑U⁻¹ : (Fin E.circlePullback.rank → 𝕜) →L[𝕜] (Fin E.circlePullback.rank → 𝕜)) *
    ((1 - s) • 1 + s • (f₀.inv.fiberMap (b.1.1, b.2)).comp (f₁.fiberMap (b.1.1, b.2))) * ↑U -
      1‖ < 1
  -- At time `s`, `f₀⁻¹ ∘ ((1 - s) f₀ + s f₁) - 1 = s (f₀⁻¹ ∘ f₁ - 1)`, in any coordinates.
  have he : (↑U⁻¹ : (Fin E.circlePullback.rank → 𝕜) →L[𝕜] (Fin E.circlePullback.rank → 𝕜)) *
      ((1 - s) • 1 + s • (f₀.inv.fiberMap (b.1.1, b.2)).comp (f₁.fiberMap (b.1.1, b.2))) * ↑U -
        1 = s • (↑U⁻¹ * ((f₀.inv.fiberMap (b.1.1, b.2)).comp (f₁.fiberMap (b.1.1, b.2))) * ↑U -
          1) := by
    ext v : 1
    simp only [sub_apply, mul_apply_eq_comp, add_apply, smul_apply, one_apply_eq_self, map_add,
      map_smul, ContinuousLinearMap.units_inv_apply_apply]
    module
  rw [he, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hs).trans_lt hU

/-- The segment from an automorphism `f₀` to a morphism `f₁` is invertible if `f₀⁻¹ ∘ f₁` is
everywhere within distance less than `1` of the identity. -/
theorem isIso_segmentHom (f₀ : E.circlePullback ≅ E.circlePullback)
    (f₁ : E.circlePullback ⟶ E.circlePullback)
    (h : ∀ w, ‖(f₀.inv.fiberMap w).comp (f₁.fiberMap w) - .id 𝕜 _‖ < 1) :
    IsIso (segmentHom f₀.hom f₁) :=
  isIso_segmentHom_of_norm_conj_lt_one f₀ f₁ fun w ↦ ⟨1, by
    rw [inv_one, Units.val_one, one_mul, mul_one, ContinuousLinearMap.one_def]; exact h w⟩

/-- Let `X` be paracompact and R₁, and let `f₀` and `f₁` be automorphisms of the pullback of `E`
to `X × Circle`. If at every point `w` some change of coordinates `U` brings the fibre map of
`f₀⁻¹ ∘ f₁` within distance less than `1` of the identity, `‖U⁻¹ ∘ f₀⁻¹ ∘ f₁ ∘ U - 1‖ < 1`, then
the clutchings of `E` by `f₀` and by `f₁` are isomorphic. -/
theorem nonempty_iso_clutching_of_norm_conj_lt_one [ParacompactSpace X] [R1Space X]
    {f₀ f₁ : E.circlePullback ≅ E.circlePullback}
    (h : ∀ w, ∃ U : ((Fin E.circlePullback.rank → 𝕜) →L[𝕜] (Fin E.circlePullback.rank → 𝕜))ˣ,
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
    {f₀ f₁ : E.circlePullback ≅ E.circlePullback}
    (h : ∀ w, ‖(f₀.inv.fiberMap w).comp (f₁.hom.fiberMap w) - .id 𝕜 _‖ < 1) :
    Nonempty (E.clutching f₀ ≅ E.clutching f₁) :=
  nonempty_iso_clutching_of_norm_conj_lt_one fun w ↦ ⟨1, by
    rw [inv_one, Units.val_one, one_mul, mul_one, ContinuousLinearMap.one_def]; exact h w⟩

end TauCeti.FiniteRankBundleCore

end
