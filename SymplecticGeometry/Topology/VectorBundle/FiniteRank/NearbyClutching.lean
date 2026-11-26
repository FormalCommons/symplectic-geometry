/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Clutching
public import SymplecticGeometry.Analysis.Normed.Ring.Units
public import SymplecticGeometry.Topology.VectorBundle.FiniteRank.SMul

/-!
# Nearby clutching functions give isomorphic clutchings

Let `E` be a finite-rank core over a paracompact R₁ space `X`, with fibres over a complete normed
`ℝ`-algebra `𝕜`, and let `f₀`, `f₁` be automorphisms of its pullback to `X × Circle`. If at every
point `w` the fibre maps satisfy `‖f₀(w)⁻¹ ∘ f₁(w) - 1‖ < 1`, then the clutchings of `E` by `f₀`
and by `f₁` are isomorphic.

The straight segment `(1 - t) f₀ + t f₁`, for `t ∈ [0, 1]`, is invertible at each point
(`Units.isUnit_one_sub_smul_add_smul_of_norm_lt_one`, by the Neumann series). It is an
automorphism of the pullback of `E` to `(X × I) × Circle` with the fibre maps of `f₀` at time `0`
and of `f₁` at time `1`, so `TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_of_homotopic`
applies. This is the step of [Hatcher2017, §2.1] that clutching functions close enough to each
other are homotopic.

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.segmentHom f₀ f₁`: the morphism of the pullback of `E` to
  `(X × I) × Circle` with fibre map `(1 - t) f₀(x, z) + t f₁(x, z)` at `((x, t), z)`, built with
  the multiplication of morphisms by continuous scalar functions
  (`TauCeti.FiniteRankBundleCore.fiberMap_smul`);
* `TauCeti.FiniteRankBundleCore.isIso_segmentHom`: it is invertible when `‖f₀⁻¹ f₁ - 1‖ < 1`
  everywhere;
* `TauCeti.FiniteRankBundleCore.nonempty_iso_clutching_of_norm_lt_one`: nearby clutching
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
theorem isIso_segmentHom_of_conj (f₀ : (Q E) ≅ (Q E)) (f₁ : (Q E) ⟶ (Q E))
    (h : ∀ w, ∃ U : ((Fin (Q E).rank → 𝕜) →L[𝕜] (Fin (Q E).rank → 𝕜))ˣ,
      ‖↑U⁻¹ * ((f₀.inv.fiberMap w).comp (f₁.fiberMap w)) * ↑U - 1‖ < 1) :
    IsIso (segmentHom f₀.hom f₁) := by
  refine (isIso_iff_bijective _).2 fun b ↦ ?_
  -- The fibre maps of `f₀` at `(x, z)`, as a unit of the ring of endomorphisms of the fibre.
  -- The closing `rfl`s identify the identity of the fibre of the pullback with the unit of this
  -- ring: the rank of a pullback is that of `E` by definition.
  let a : ((Fin E.rank → 𝕜) →L[𝕜] (Fin E.rank → 𝕜))ˣ :=
    ⟨f₀.hom.fiberMap (b.1.1, b.2), f₀.inv.fiberMap (b.1.1, b.2),
      by rw [ContinuousLinearMap.mul_def, ← fiberMap_comp, f₀.inv_hom_id, fiberMap_id]; rfl,
      by rw [ContinuousLinearMap.mul_def, ← fiberMap_comp, f₀.hom_inv_id, fiberMap_id]; rfl⟩
  have ht : ‖algebraMap ℝ 𝕜 b.1.2‖ ≤ 1 := by
    rw [norm_algebraMap', Real.norm_eq_abs, abs_of_nonneg b.1.2.property.1]
    exact b.1.2.property.2
  obtain ⟨U, hU⟩ := h (b.1.1, b.2)
  have hunit := a.isUnit_one_sub_smul_add_smul_of_norm_conj_lt_one U
    (b := f₁.fiberMap (b.1.1, b.2)) hU ht
  rw [← fiberMap_segmentHom] at hunit
  exact (ContinuousLinearEquiv.unitsEquiv 𝕜 _ hunit.unit).bijective

/-- The segment from an automorphism `f₀` to a morphism `f₁` is invertible if `f₀⁻¹ ∘ f₁` is
everywhere within distance less than `1` of the identity. -/
theorem isIso_segmentHom (f₀ : (Q E) ≅ (Q E)) (f₁ : (Q E) ⟶ (Q E))
    (h : ∀ w, ‖(f₀.inv.fiberMap w).comp (f₁.fiberMap w) - .id 𝕜 _‖ < 1) :
    IsIso (segmentHom f₀.hom f₁) :=
  isIso_segmentHom_of_conj f₀ f₁ fun w ↦ ⟨1, by
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
  haveI := isIso_segmentHom_of_conj f₀ f₁.hom h
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
