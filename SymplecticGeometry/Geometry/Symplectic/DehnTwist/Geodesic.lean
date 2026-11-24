/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.Codisc
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.ModelSpace

/-!
# Euclidean coordinates on the cotangent bundle of the sphere

Let `E = ℝⁿ⁺¹` (`EuclideanSpace ℝ (Fin (n + 1))`) and let `Sⁿ ⊆ E` be its unit sphere, with
Mathlib's manifold structure modelled on `𝓡 n` and Tau Ceti's round metric. A covector `z` at
`q ∈ Sⁿ` is represented by a unique vector `p ∈ E` orthogonal to `q` such that
`z v = ⟪p, dι v⟫` for every tangent vector `v`, where `ι : Sⁿ → E` is the inclusion: `p` is the
image in `E` of the metric dual of `z`. This identifies `T*Sⁿ` with the submanifold
`{(q, p) | ‖q‖ = 1, ⟪q, p⟫ = 0}` of `E × E`, the description of `T*Sⁿ` in which the model Dehn
twist is written down.

## Main definitions

* `SymplecticGeometry.cotangentMk q p`: the covector `v ↦ ⟪p, dι v⟫` at `q`, defined for every
  `p ∈ E`.
* `SymplecticGeometry.cotangentCoord z`: the pair `(q, p) ∈ E × E` with `p ⊥ q` representing `z`.
* `SymplecticGeometry.cotangentNorm z`: the norm `‖p‖` of its second coordinate.

## Main results

* `SymplecticGeometry.cotangentCoord_cotangentMk`: `cotangentMk q p` has coordinates
  `(q, p - ⟪q, p⟫ q)`, the orthogonal projection of `p` onto the tangent hyperplane.
* `SymplecticGeometry.cotangentMk_cotangentCoord`: a covector is recovered from its coordinates.
* `SymplecticGeometry.range_cotangentCoord`: the coordinates fill out
  `{(q, p) | ‖q‖ = 1, ⟪q, p⟫ = 0}`.
* `SymplecticGeometry.contMDiff_cotangentMk`, `SymplecticGeometry.contMDiff_cotangentCoord`: both
  maps are smooth.
* `SymplecticGeometry.cotangentNorm_eq_norm`: `‖p‖` is the norm of `z` for the round metric.
* `SymplecticGeometry.isCompact_setOf_cotangentNorm_le`: the sets `{z | ‖p‖ ≤ r}` are compact.

## Implementation notes

`cotangentMk` pulls the covector `⟪p, ·⟫` of `E` back along the differential of the inclusion, so
its smoothness is `TauCeti.CotangentBundle.contMDiff_mk_comp_mfderiv`. The second coordinate of
`cotangentCoord z` is the image under `TauCeti.sphereTangentEquiv` of the Riesz dual
`Riemannian.Tensor.rieszDual` of `z` for the round metric. Its smoothness comes from its
expansion `∑ⱼ z (∇hⱼ) eⱼ` in the standard basis `eⱼ` of `E`, where `∇hⱼ` is the round gradient
of the height function `hⱼ = ⟪eⱼ, ·⟫`, read in `E` by
`TauCeti.mvfderiv_coe_mgradient_inner_coe_sphere`. This proof adapts that of
`TauCeti.contMDiff_sphereTangentEquiv_symm`, which expands in the same basis against the same
round gradients to show that the inverse direction is smooth.

## References

* [P. Seidel, *A long exact sequence for symplectic Floer cohomology*][Seidel2003], §1, where the
  model Dehn twist is written in these coordinates.
* [V. I. Arnold, *Some remarks on symplectic monodromy of Milnor fibrations*][Arnold1995], one of
  the early sources on twists of `T*Sⁿ`.
-/

public section

noncomputable section

namespace SymplecticGeometry

open Bundle Metric Set TauCeti
open scoped Manifold ContDiff InnerProductSpace EuclideanSpace

variable {n : ℕ}

/-- The Euclidean space `ℝⁿ⁺¹` containing the unit sphere `Sⁿ`. -/
local notation "𝔼" n => EuclideanSpace ℝ (Fin (n + 1))

/-- The unit sphere `Sⁿ` of `ℝⁿ⁺¹`. -/
local notation "𝕊" n => sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The covector `v ↦ ⟪p, dι v⟫` at a point `q` of the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`, where `ι` is the
inclusion of the sphere. Only the component of `p` orthogonal to `q` matters
(`cotangentCoord_cotangentMk`). -/
def cotangentMk (q : 𝕊 n) (p : 𝔼 n) : CotangentBundle (𝓡 n) (𝕊 n) :=
  TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) q
    (innerSL ℝ p ∘L mvfderiv (𝓡 n) ((↑) : (𝕊 n) → 𝔼 n) q)

theorem cotangentMk_def (q : 𝕊 n) (p : 𝔼 n) :
    cotangentMk q p = TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) q
      (innerSL ℝ p ∘L mvfderiv (𝓡 n) ((↑) : (𝕊 n) → 𝔼 n) q) :=
  (rfl)

/-- The base point of `cotangentMk q p` is `q`. -/
@[simp]
theorem proj_cotangentMk (q : 𝕊 n) (p : 𝔼 n) : (cotangentMk q p).proj = q :=
  (rfl)

/-- The value of `cotangentMk q p` on a tangent vector `v` is `⟪p, dι v⟫`. -/
theorem cotangentMk_snd_apply (q : 𝕊 n) (p : 𝔼 n) (v : TangentSpace (𝓡 n) q) :
    (cotangentMk q p).snd v = ⟪p, mvfderiv (𝓡 n) ((↑) : (𝕊 n) → 𝔼 n) q v⟫_ℝ := by
  rw [cotangentMk_def, ContinuousLinearMap.comp_apply, innerSL_apply_apply]

/-- The Euclidean coordinates `(q, p) ∈ ℝⁿ⁺¹ × ℝⁿ⁺¹` of a covector `z` on the unit sphere: `q` is
its base point and `p`, orthogonal to `q`, is the image in `ℝⁿ⁺¹` of the round-metric dual of
`z`, so that `z v = ⟪p, dι v⟫` (`inner_cotangentCoord_snd`). -/
def cotangentCoord (z : CotangentBundle (𝓡 n) (𝕊 n)) : (𝔼 n) × 𝔼 n :=
  ((z.proj : 𝔼 n),
    (sphereTangentEquiv z.proj (Riemannian.Tensor.rieszDual (I := 𝓡 n) z.proj z.snd) : 𝔼 n))

/-- The first coordinate of a covector is its base point. -/
@[simp]
theorem cotangentCoord_fst (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    (cotangentCoord z).1 = z.proj :=
  (rfl)

/-- The second coordinate of a covector is the image in `ℝⁿ⁺¹` of its round-metric dual. -/
theorem cotangentCoord_snd (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    (cotangentCoord z).2 =
      sphereTangentEquiv z.proj (Riemannian.Tensor.rieszDual (I := 𝓡 n) z.proj z.snd) :=
  (rfl)

/-- The second coordinate of a covector lies in the tangent hyperplane `(ℝ ∙ q)ᗮ`. -/
theorem cotangentCoord_snd_mem (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    (cotangentCoord z).2 ∈ (ℝ ∙ (z.proj : 𝔼 n))ᗮ :=
  (sphereTangentEquiv z.proj _).property

/-- The second coordinate of a covector is orthogonal to its base point. -/
@[simp]
theorem inner_proj_cotangentCoord_snd (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    ⟪(z.proj : 𝔼 n), (cotangentCoord z).2⟫_ℝ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.1 (cotangentCoord_snd_mem z)

/-- The second coordinate `p` of a covector `z` represents it: `z v = ⟪p, dι v⟫`. -/
theorem inner_cotangentCoord_snd (z : CotangentBundle (𝓡 n) (𝕊 n))
    (v : TangentSpace (𝓡 n) z.proj) :
    ⟪(cotangentCoord z).2, mvfderiv (𝓡 n) ((↑) : (𝕊 n) → 𝔼 n) z.proj v⟫_ℝ =
      z.snd v := by
  rw [mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv, cotangentCoord_snd, ← Submodule.coe_inner,
    LinearIsometryEquiv.inner_map_map, Riemannian.Tensor.inner_rieszDual]

/-- The second coordinate of a covector `z` is the unique `u ⊥ q` with `z v = ⟪u, dι v⟫`. -/
theorem cotangentCoord_snd_eq {z : CotangentBundle (𝓡 n) (𝕊 n)} {u : 𝔼 n}
    (hu : ⟪(z.proj : 𝔼 n), u⟫_ℝ = 0)
    (hz : ∀ v, z.snd v = ⟪u, mvfderiv (𝓡 n) ((↑) : (𝕊 n) → 𝔼 n) z.proj v⟫_ℝ) :
    (cotangentCoord z).2 = u := by
  have hu' : u ∈ (ℝ ∙ (z.proj : 𝔼 n))ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.2 hu
  have h : (sphereTangentEquiv z.proj).symm ⟨u, hu'⟩ =
      Riemannian.Tensor.rieszDual (I := 𝓡 n) z.proj z.snd := by
    refine Riemannian.Tensor.eq_rieszDual_iff_inner_eq.2 fun w ↦ ?_
    rw [hz, mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv, ← LinearIsometryEquiv.inner_map_map
      (sphereTangentEquiv z.proj), LinearIsometryEquiv.apply_symm_apply, Submodule.coe_inner]
  rw [cotangentCoord_snd, ← h, LinearIsometryEquiv.apply_symm_apply]

/-- The coordinates of `cotangentMk q p` are `q` and the projection `p - ⟪q, p⟫ q` of `p` onto the
tangent hyperplane at `q`. -/
@[simp]
theorem cotangentCoord_cotangentMk (q : 𝕊 n) (p : 𝔼 n) :
    cotangentCoord (cotangentMk q p) = ((q : 𝔼 n), p - ⟪(q : 𝔼 n), p⟫_ℝ • (q : 𝔼 n)) := by
  have hq : ⟪(q : 𝔼 n), (q : 𝔼 n)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere q, one_pow]
  rw [cotangentMk_def]
  refine Prod.ext rfl (cotangentCoord_snd_eq ?_ fun v ↦ ?_)
  · rw [inner_sub_right, real_inner_smul_right, hq, mul_one, sub_self]
  · rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_sub_left, real_inner_smul_left,
      inner_coe_mvfderiv_subtypeVal_sphere, mul_zero, sub_zero]

/-- A covector is the covector `cotangentMk` of its coordinates. -/
@[simp]
theorem cotangentMk_cotangentCoord (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentMk z.proj (cotangentCoord z).2 = z :=
  CotangentBundle.ext rfl fun v ↦ inner_cotangentCoord_snd z v

/-- A covector is determined by its coordinates. -/
theorem cotangentCoord_injective : Function.Injective (cotangentCoord (n := n)) := by
  intro z w h
  have h1 : z.proj = w.proj := Subtype.ext (by simpa using congrArg Prod.fst h)
  rw [← cotangentMk_cotangentCoord z, ← cotangentMk_cotangentCoord w, h1, ← h]

/-- The coordinates identify `T*Sⁿ` with `{(q, p) | ‖q‖ = 1, ⟪q, p⟫ = 0}`. -/
theorem range_cotangentCoord :
    range (cotangentCoord (n := n)) = {x | ‖x.1‖ = 1 ∧ ⟪x.1, x.2⟫_ℝ = 0} := by
  ext x
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rintro ⟨z, rfl⟩
    exact ⟨norm_eq_of_mem_sphere z.proj, inner_proj_cotangentCoord_snd z⟩
  · refine ⟨cotangentMk ⟨x.1, mem_sphere_zero_iff_norm.2 h₁⟩ x.2, ?_⟩
    rw [cotangentCoord_cotangentMk]
    simp [h₂]

/-- `(q, p) ↦ cotangentMk q p` is smooth on `Sⁿ × ℝⁿ⁺¹`. -/
theorem contMDiff_cotangentMk :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, 𝔼 n)) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun x : (𝕊 n) × 𝔼 n ↦ cotangentMk x.1 x.2) := by
  have hΨ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, 𝔼 n)) (𝓘(ℝ, 𝔼 n).prod 𝓘(ℝ, (𝔼 n) →L[ℝ] ℝ)) ∞
      (fun x : (𝕊 n) × 𝔼 n ↦ (CotangentBundle.modelSpaceDiffeomorph (𝔼 n)).symm
        ((x.1 : 𝔼 n), innerSL ℝ x.2)) :=
    (CotangentBundle.modelSpaceDiffeomorph (𝔼 n)).symm.contMDiff.comp
      ((contMDiff_coe_sphere.comp contMDiff_fst).prodMk_space
        ((innerSL ℝ).contDiff.contMDiff.comp contMDiff_snd))
  refine (CotangentBundle.contMDiff_mk_comp_mfderiv (f := ((↑) : (𝕊 n) → 𝔼 n)) (n := ω)
    (fun _ ↦ by simp) hΨ contMDiff_fst contMDiff_coe_sphere (by simp)).congr fun x ↦ ?_
  rw [CotangentBundle.modelSpaceDiffeomorph_symm_apply, cotangentMk_def]
  exact CotangentBundle.ext rfl fun v ↦
    congrArg (innerSL ℝ x.2) (mvfderiv_apply_eq_mfderiv_apply _ x.1 v)

/-- In the standard basis `eⱼ` of `ℝⁿ⁺¹`, the `j`-th component of the second coordinate of `z` is
the value of `z` on the round gradient of the height function `⟪eⱼ, ·⟫`. -/
private theorem inner_basisFun_cotangentCoord_snd (z : CotangentBundle (𝓡 n) (𝕊 n))
    (j : Fin (n + 1)) :
    ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ j, (cotangentCoord z).2⟫_ℝ =
      z.snd (Manifold.mgradient (𝓡 n)
        (fun q : 𝕊 n ↦ ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ j, (q : 𝔼 n)⟫_ℝ) z.proj) := by
  rw [← inner_cotangentCoord_snd, mvfderiv_coe_mgradient_inner_coe_sphere, inner_sub_right,
    real_inner_smul_right, real_inner_comm (z.proj : 𝔼 n) (cotangentCoord z).2,
    inner_proj_cotangentCoord_snd, mul_zero, sub_zero, real_inner_comm]

/-- The coordinates `z ↦ (q, p)` are smooth on `T*Sⁿ`. -/
theorem contMDiff_cotangentCoord :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n) ∞
      (cotangentCoord (n := n)) := by
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  have hproj : ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) (𝓡 n) ∞
      (fun z : CotangentBundle (𝓡 n) (𝕊 n) ↦ z.proj) :=
    contMDiff_proj _
  have hgrad (j : Fin (n + 1)) :
      ContMDiff (𝓡 n) (𝓡 n).tangent ∞
        (fun q : 𝕊 n ↦ (⟨q, Manifold.mgradient (𝓡 n)
          (fun r : 𝕊 n ↦ ⟪b j, (r : 𝔼 n)⟫_ℝ) q⟩ : TangentBundle (𝓡 n) (𝕊 n))) := by
    have hh : ContMDiff (𝓡 n) 𝓘(ℝ) (∞ + 1) (fun r : 𝕊 n ↦ ⟪b j, (r : 𝔼 n)⟫_ℝ) :=
      ((innerSL ℝ (b j)).contDiff.contMDiff.comp contMDiff_coe_sphere).of_le le_top
    exact Manifold.contMDiff_mgradient hh
  have hcoeff (j : Fin (n + 1)) :
      ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ) ∞
        (fun z : CotangentBundle (𝓡 n) (𝕊 n) ↦ ⟪b j, (cotangentCoord z).2⟫_ℝ) := by
    refine ContMDiff.congr (fun z ↦ ?_) fun z ↦ inner_basisFun_cotangentCoord_snd z j
    exact ContMDiffAt.clm_bundle_apply_scalar (contMDiff_id z) ((hgrad j).comp hproj z)
  refine (contMDiff_coe_sphere.comp hproj).prodMk_space ?_
  have hsum : ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, 𝔼 n) ∞
      (fun z ↦ ∑ j, ⟪b j, (cotangentCoord z).2⟫_ℝ • b j) :=
    contMDiff_finsetSum fun j _ ↦ (hcoeff j).smul contMDiff_const
  exact hsum.congr fun z ↦ (b.sum_repr' _).symm

/-- The norm `‖p‖` of the second coordinate of a covector on the unit sphere. It is the norm of
the covector for the round metric (`cotangentNorm_eq_norm`). -/
def cotangentNorm (z : CotangentBundle (𝓡 n) (𝕊 n)) : ℝ :=
  ‖(cotangentCoord z).2‖

theorem cotangentNorm_def (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentNorm z = ‖(cotangentCoord z).2‖ :=
  (rfl)

theorem cotangentNorm_nonneg (z : CotangentBundle (𝓡 n) (𝕊 n)) : 0 ≤ cotangentNorm z :=
  norm_nonneg _

/-- The norm `‖p‖` of the coordinates of a covector is its norm for the round metric. -/
theorem cotangentNorm_eq_norm (z : CotangentBundle (𝓡 n) (𝕊 n)) : cotangentNorm z = ‖z.snd‖ := by
  rw [cotangentNorm_def, cotangentCoord_snd, Submodule.norm_coe, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map]

theorem continuous_cotangentNorm : Continuous (cotangentNorm (n := n)) :=
  continuous_norm.comp (continuous_snd.comp contMDiff_cotangentCoord.continuous)

/-- The covectors on the unit sphere with `‖p‖ ≤ r` form a compact set. -/
theorem isCompact_setOf_cotangentNorm_le (r : ℝ) :
    IsCompact {z : CotangentBundle (𝓡 n) (𝕊 n) | cotangentNorm z ≤ r} := by
  simpa only [cotangentNorm_eq_norm] using CotangentBundle.isCompact_setOf_norm_snd_le r

end SymplecticGeometry

end
