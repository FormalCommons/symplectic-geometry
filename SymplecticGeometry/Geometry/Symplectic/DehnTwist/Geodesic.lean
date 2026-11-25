/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Diffeomorph.Cotangent
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Geodesic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Cotangent.InnerProduct
public import TauCeti.Geometry.Symplectic.Cotangent.Liouville
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Cotangent
import Mathlib.Analysis.SpecialFunctions.Sqrt
import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.Codisc
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.ModelSpace
import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# Euclidean coordinates and the normalized geodesic flow on the cotangent bundle of the sphere

Let `E = ℝⁿ⁺¹` (`EuclideanSpace ℝ (Fin (n + 1))`) and let `Sⁿ ⊆ E` be its unit sphere, with
Mathlib's manifold structure modelled on `𝓡 n` and Tau Ceti's round metric. A covector `z` at
`q ∈ Sⁿ` is represented by a unique vector `p ∈ E` orthogonal to `q` such that
`z v = ⟪p, dι v⟫` for every tangent vector `v`, where `ι : Sⁿ → E` is the inclusion: `p` is the
image in `E` of the metric dual of `z`. This identifies `T*Sⁿ` with the submanifold
`{(q, p) | ‖q‖ = 1, ⟪q, p⟫ = 0}` of `E × E`, the description of `T*Sⁿ` in which the model Dehn
twist is written down. In these coordinates the file defines the normalized geodesic flow, which
moves a covector off the zero section at unit speed along the great circle of its base point and
direction.

## Main definitions

* `SymplecticGeometry.cotangentMk q p`: the covector `v ↦ ⟪p, dι v⟫` at `q`, defined for every
  `p ∈ E`.
* `SymplecticGeometry.cotangentCoord z`: the pair `(q, p) ∈ E × E` with `p ⊥ q` representing `z`.
* `SymplecticGeometry.cotangentNorm z`: the norm `‖p‖` of its second coordinate.
* `SymplecticGeometry.antipodal`: the cotangent lift of the antipodal map of `Sⁿ`.
* `SymplecticGeometry.geodesicFlow t`: the normalized geodesic flow, the identity on the zero
  section.

## Main results

* `SymplecticGeometry.cotangentCoord_cotangentMk`: `cotangentMk q p` has coordinates
  `(q, p - ⟪q, p⟫ q)`, the orthogonal projection of `p` onto the tangent hyperplane;
  `SymplecticGeometry.cotangentCoord_cotangentMk_of_inner_eq_zero`: for `p ⊥ q` they are `(q, p)`.
* `SymplecticGeometry.cotangentMk_cotangentCoord`: a covector is recovered from its coordinates.
* `SymplecticGeometry.range_cotangentCoord`: the coordinates fill out
  `{(q, p) | ‖q‖ = 1, ⟪q, p⟫ = 0}`.
* `SymplecticGeometry.contMDiff_cotangentMk`, `SymplecticGeometry.contMDiff_cotangentCoord`: both
  maps are smooth. `SymplecticGeometry.contMDiff_of_contMDiff_cotangentCoord_comp`: a map into
  `T*Sⁿ` is smooth when its coordinates are.
* `SymplecticGeometry.cotangentNorm_eq_norm`: `‖p‖` is the norm of `z` for the round metric.
* `SymplecticGeometry.contMDiffAt_cotangentNorm`: `‖p‖` is smooth off the zero section.
* `SymplecticGeometry.isCompact_setOf_cotangentNorm_le`: the sets `{z | ‖p‖ ≤ r}` are compact;
  `SymplecticGeometry.isCompact_setOf_cotangentNorm_coe_le`: so is their trace on an open set
  that contains them.
* `SymplecticGeometry.cotangentCoord_zeroSection`: the zero covector at `q` has coordinates
  `(q, 0)`; `SymplecticGeometry.antipodal_zeroSection`: `antipodal` sends it to the zero covector
  at `-q`.
* `SymplecticGeometry.mpullback_cotangentCoord`: the coordinates, read in `E × E*` through
  `TauCeti.cotangentInnerEquiv`, pull the form `∑ⱼ pⱼ dqⱼ` (`TauCeti.cotangentLiouvilleForm`)
  back to the Liouville form of `T*Sⁿ`.
* `SymplecticGeometry.cotangentCoord_cotangent_unitSphereDiffeomorph`: the cotangent lift of the
  diffeomorphism of the sphere induced by a linear isometry `e` of `E` acts by
  `(q, p) ↦ (e q, e p)`; `SymplecticGeometry.cotangentCoord_cotangent_orthogonal` is its case of
  an orthogonal matrix `A`, and
  `SymplecticGeometry.cotangentCoord_antipodal`: `antipodal` acts by `(q, p) ↦ (-q, -p)`.
* `SymplecticGeometry.cotangentCoord_geodesicFlow`: off the zero section the flow moves `(q, p)` to
  `(cos t • q + (sin t / ‖p‖) • p, cos t • p - (sin t * ‖p‖) • q)`.
* `SymplecticGeometry.geodesicFlow_zero`, `SymplecticGeometry.geodesicFlow_add`,
  `SymplecticGeometry.geodesicFlow_two_pi`: it is a flow, periodic of period `2π`;
  `SymplecticGeometry.cotangentNorm_geodesicFlow`: it preserves `‖p‖`; and
  `SymplecticGeometry.geodesicFlow_pi`: off the zero section, its time-`π` map is `antipodal`.
* `SymplecticGeometry.not_exists_continuous_eqOn_geodesicFlow`: for `sin t ≠ 0` and `n ≥ 1`, no
  continuous map of `T*Sⁿ` agrees with the time-`t` map off the zero section.
* `SymplecticGeometry.isMIntegralCurve_geodesicFlow`: off the zero section, the orbits of the flow
  are integral curves of the Hamiltonian vector field of `cotangentNorm` for the canonical
  symplectic form; `SymplecticGeometry.eval₂_symplecticForm_eq_stdSymplecticForm` gives that form
  in the coordinates `(q, p)`, and `SymplecticGeometry.fst_mfderiv_cotangentCoord` the differential
  of `q`.
* `SymplecticGeometry.liouvilleForm_apply_eq_inner_cotangentCoord`,
  `SymplecticGeometry.mpullback_liouvilleForm_apply_eq_inner_cotangentCoord`: the Liouville form
  and its pullbacks in the coordinates `(q, p)`, as `⟪p, δq⟫`; and
  `SymplecticGeometry.inner_fst_mfderiv_cotangentCoord_add_inner_snd`: the differentials satisfy
  `⟪δq, p⟫ + ⟪q, δp⟫ = 0`.
* `HasFDerivAt.mfderiv_comp_cotangentCoord_apply`: the chain rule through `cotangentCoord`;
  `SymplecticGeometry.mvfderiv_comp_cotangentNorm_sq`: the differential of `z ↦ k (μ z ^ 2)`, on
  all of `T*Sⁿ`.

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

The Liouville form evaluates a covector on the differential of the base point, and the first
coordinate is the base point read in `E`, so `mpullback_cotangentCoord` is the chain rule for
`ι ∘ π`. Cotangent lifts are Tau Ceti's `Diffeomorph.cotangent`, which sends a covector `p` at `x`
to `p ∘ (dh_x)⁻¹`; for a linear isometry `e` this is the covector of `e p` at `e q`, with no
inverse.

The base point of `geodesicFlow t z` is Tau Ceti's great circle `TauCeti.sphereGreatCircle`
through `q` and `p / ‖p‖`. Every identity about the flow is checked on coordinates, where it
reduces to the addition formulas for `cos` and `sin`, and transported back by
`cotangentCoord_injective`. It
has no continuous extension across the zero section: along the rays `s • u` and `s • (-u)`,
`s > 0`, at a point `q` with `u ⊥ q`, the base points of the images are constant and differ, while
both rays tend to the zero covector at `q`.

The Hamiltonian statement is checked in the same coordinates. Pulling the linear Liouville form
back by `cotangentCoord` (`mpullback_cotangentCoord`) and commuting the pullback with the exterior
derivative (`TauCeti.mpullback_mextDeriv`) writes `ω = -dλ` as `∑ⱼ dqⱼ ∧ dpⱼ` on the coordinate
differentials. The velocity of an orbit at `(q, p)` reads `(p / ‖p‖, -‖p‖ q)`, so its contraction
with `ω` sends a tangent vector with coordinate differentials `(δq, δp)` to
`⟪p, δp⟫ / ‖p‖ + ‖p‖ ⟪q, δq⟫`. The second term vanishes since `δq ⊥ q`, and the first is `dμ`, so
`TauCeti.SmoothTwoForm.hamiltonianVectorField_eq_iff_of_isInvertible_flat` identifies the velocity
with `X_μ`.

## References

* [P. Seidel, *A long exact sequence for symplectic Floer cohomology*][Seidel2003], §1, where the
  model Dehn twist is written in these coordinates with the normalized geodesic flow.
* [V. I. Arnold, *Some remarks on symplectic monodromy of Milnor fibrations*][Arnold1995], one of
  the early sources on twists of `T*Sⁿ`.
-/

public section

noncomputable section

namespace SymplecticGeometry

open Bundle Metric Set TauCeti TauCeti.Manifold
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

/-- For `p` orthogonal to `q`, the coordinates of `cotangentMk q p` are `(q, p)`. -/
theorem cotangentCoord_cotangentMk_of_inner_eq_zero {q : 𝕊 n} {p : 𝔼 n}
    (h : ⟪(q : 𝔼 n), p⟫_ℝ = 0) : cotangentCoord (cotangentMk q p) = ((q : 𝔼 n), p) := by
  rw [cotangentCoord_cotangentMk, h, zero_smul, sub_zero]

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
  · exact ⟨cotangentMk ⟨x.1, mem_sphere_zero_iff_norm.2 h₁⟩ x.2,
      cotangentCoord_cotangentMk_of_inner_eq_zero h₂⟩

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

/-- A map into `T*Sⁿ` is smooth as soon as its coordinates `(q, p)` are smooth maps into
`ℝⁿ⁺¹ × ℝⁿ⁺¹`. -/
theorem contMDiff_of_contMDiff_cotangentCoord_comp {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] {f : M → CotangentBundle (𝓡 n) (𝕊 n)}
    (hf : ContMDiff I 𝓘(ℝ, (𝔼 n) × 𝔼 n) ∞ (cotangentCoord ∘ f)) :
    ContMDiff I ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞ f := by
  have : Fact (Module.finrank ℝ (𝔼 n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hq : ContMDiff I 𝓘(ℝ, 𝔼 n) ∞ (Prod.fst ∘ cotangentCoord ∘ f) :=
    contDiff_fst.contMDiff.comp hf
  have hp : ContMDiff I 𝓘(ℝ, 𝔼 n) ∞ (Prod.snd ∘ cotangentCoord ∘ f) :=
    contDiff_snd.contMDiff.comp hf
  refine (contMDiff_cotangentMk.comp
    ((hq.codRestrict_sphere fun x ↦ (f x).proj.property).prodMk hp)).congr fun x ↦ ?_
  exact (cotangentMk_cotangentCoord (f x)).symm

/-- The norm `‖p‖` of the second coordinate of a covector on the unit sphere. It is the norm of
the covector for the round metric (`cotangentNorm_eq_norm`). -/
def cotangentNorm (z : CotangentBundle (𝓡 n) (𝕊 n)) : ℝ :=
  ‖(cotangentCoord z).2‖

theorem cotangentNorm_def (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentNorm z = ‖(cotangentCoord z).2‖ :=
  (rfl)

/-- The norm of `cotangentMk q p` is that of the projection `p - ⟪q, p⟫ q` of `p` onto the
tangent hyperplane at `q`. -/
@[simp]
theorem cotangentNorm_cotangentMk (q : 𝕊 n) (p : 𝔼 n) :
    cotangentNorm (cotangentMk q p) = ‖p - ⟪(q : 𝔼 n), p⟫_ℝ • (q : 𝔼 n)‖ := by
  rw [cotangentNorm_def, cotangentCoord_cotangentMk]

theorem cotangentNorm_nonneg (z : CotangentBundle (𝓡 n) (𝕊 n)) : 0 ≤ cotangentNorm z :=
  norm_nonneg _

/-- The norm `‖p‖` of the coordinates of a covector is its norm for the round metric. -/
theorem cotangentNorm_eq_norm (z : CotangentBundle (𝓡 n) (𝕊 n)) : cotangentNorm z = ‖z.snd‖ := by
  rw [cotangentNorm_def, cotangentCoord_snd, Submodule.norm_coe, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map]

/-- The zero covector at `q` has the coordinates `(q, 0)`. -/
@[simp]
theorem cotangentCoord_zeroSection (q : 𝕊 n) :
    cotangentCoord (zeroSection (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) q) = ((q : 𝔼 n), 0) :=
  Prod.ext (by rw [cotangentCoord_fst, zeroSection_proj]) <|
    cotangentCoord_snd_eq (inner_zero_right _) fun v ↦ by
      rw [inner_zero_left, zeroSection_snd, zero_apply]

/-- The zero covectors have norm `0`. -/
@[simp]
theorem cotangentNorm_zeroSection (q : 𝕊 n) :
    cotangentNorm (zeroSection (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) q) = 0 := by
  rw [cotangentNorm_def, cotangentCoord_zeroSection, norm_zero]

theorem continuous_cotangentNorm : Continuous (cotangentNorm (n := n)) :=
  continuous_norm.comp (continuous_snd.comp contMDiff_cotangentCoord.continuous)

/-- Off the zero section, `cotangentNorm` is smooth. -/
theorem contMDiffAt_cotangentNorm {z : CotangentBundle (𝓡 n) (𝕊 n)} (hz : cotangentNorm z ≠ 0) :
    ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ) ∞ cotangentNorm z :=
  (CotangentBundle.contMDiffAt_norm_snd
      ((norm_ne_zero_iff (a := z.snd)).1 ((cotangentNorm_eq_norm z).symm.trans_ne hz))
    ).congr_of_eventuallyEq (Filter.Eventually.of_forall cotangentNorm_eq_norm)

/-- The covectors on the unit sphere with `‖p‖ ≤ r` form a compact set. -/
theorem isCompact_setOf_cotangentNorm_le (r : ℝ) :
    IsCompact {z : CotangentBundle (𝓡 n) (𝕊 n) | cotangentNorm z ≤ r} := by
  simpa only [cotangentNorm_eq_norm] using CotangentBundle.isCompact_setOf_norm_snd_le r

/-- For an open set `U ⊇ {z | ‖p‖ ≤ r}` of `T*Sⁿ`, the points of `U` with `‖p‖ ≤ r` form a
compact subset of `U`. -/
theorem isCompact_setOf_cotangentNorm_coe_le
    {U : TopologicalSpace.Opens (CotangentBundle (𝓡 n) (𝕊 n))} {r : ℝ}
    (hU : {z : CotangentBundle (𝓡 n) (𝕊 n) | cotangentNorm z ≤ r} ⊆ (U : Set _)) :
    IsCompact {z : U | cotangentNorm (z : CotangentBundle (𝓡 n) (𝕊 n)) ≤ r} :=
  Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_setOf_cotangentNorm_le r)
    (by rwa [Subtype.range_coe])

/-- The first coordinate of the differential of `cotangentCoord` is the differential of the
inclusion `Sⁿ → ℝⁿ⁺¹` applied to the differential of the bundle projection: the first
coordinate of `cotangentCoord z` is the base point of `z`. -/
theorem fst_mfderiv_cotangentCoord (x : CotangentBundle (𝓡 n) (𝕊 n))
    (w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) x) :
    (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
        cotangentCoord x w).1 =
      mvfderiv (𝓡 n) ((↑) : (𝕊 n) → 𝔼 n) x.proj
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) (𝓡 n) TotalSpace.proj x
          w) := by
  have hΨ : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      𝓘(ℝ, (𝔼 n) × 𝔼 n) cotangentCoord x :=
    contMDiff_cotangentCoord.mdifferentiableAt (by simp)
  have hfst := hΨ.mvfderiv_fst_apply w
  have hproj := mfderiv_comp_apply x (g := ((↑) : (𝕊 n) → 𝔼 n))
    (contMDiff_coe_sphere.mdifferentiableAt one_ne_zero)
    ((contMDiff_proj (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ)).mdifferentiableAt
      one_ne_zero : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) (𝓡 n)
        (π (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ)) x)
    w
  have hcomp : (fun z ↦ (cotangentCoord (n := n) z).1) =
      ((↑) : (𝕊 n) → 𝔼 n) ∘ TotalSpace.proj :=
    funext fun z ↦ by simp [cotangentCoord_fst]
  rw [hcomp, mvfderiv_apply_eq_mfderiv_apply] at hfst
  rw [mvfderiv_apply_eq_mfderiv_apply, ← hproj, hfst, mvfderiv_apply_eq_mfderiv_apply]

/-- The differential of `cotangentCoord` followed by Tau Ceti's identification
`TauCeti.cotangentInnerEquiv` is that identification applied to the differential of
`cotangentCoord`. -/
theorem mfderiv_cotangentInnerEquiv_comp_cotangentCoord_apply (z : CotangentBundle (𝓡 n) (𝕊 n))
    (u : TangentSpace ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) z) :
    mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      𝓘(ℝ, (𝔼 n) × StrongDual ℝ (𝔼 n)) (TauCeti.cotangentInnerEquiv ∘ cotangentCoord) z u =
    TauCeti.cotangentInnerEquiv (V := 𝔼 n)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
        cotangentCoord z u) := by
  refine (mfderiv_comp_apply z (g := ⇑(TauCeti.cotangentInnerEquiv (V := 𝔼 n)))
    (TauCeti.cotangentInnerEquiv (V := 𝔼 n)).mdifferentiableAt
    (contMDiff_cotangentCoord.mdifferentiableAt (by simp)) u).trans ?_
  rw [ContinuousLinearEquiv.mfderiv_eq]
  -- The coercion of `cotangentInnerEquiv` to a linear map, applied to a tangent vector of the
  -- model space, is the equivalence itself; the types differ only by `TangentSpace`.
  rfl

/-- The coordinates `cotangentCoord`, followed by Tau Ceti's identification
`(q, p) ↦ (q, ⟪p, ·⟫)` of `ℝⁿ⁺¹ × ℝⁿ⁺¹` with `ℝⁿ⁺¹ × (ℝⁿ⁺¹)*`, pull the linear Liouville form
`TauCeti.cotangentLiouvilleForm`, the form `∑ⱼ pⱼ dqⱼ`, back to the Liouville form of `T*Sⁿ`. -/
theorem mpullback_cotangentCoord :
    TauCeti.mpullback ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        𝓘(ℝ, (𝔼 n) × StrongDual ℝ (𝔼 n)) (TauCeti.cotangentInnerEquiv ∘ cotangentCoord)
        (fun x ↦ TauCeti.cotangentLiouvilleForm x) =
      (CotangentBundle.liouvilleForm (𝓡 n) (𝕊 n)).val := by
  funext z
  ext v
  -- The form has the type of a model-space form only up to unfolding `TangentSpace`, so the
  -- evaluation lemmas are applied by unification rather than by `rw`.
  refine ((TauCeti.mpullback_apply _ _ z v).trans
    (TauCeti.cotangentLiouvilleForm_apply _ _)).trans ?_
  rw [CotangentBundle.liouvilleForm_apply, Function.comp_apply,
    TauCeti.cotangentInnerEquiv_apply_snd_apply, ← inner_cotangentCoord_snd,
    mfderiv_cotangentInnerEquiv_comp_cotangentCoord_apply]
  exact congrArg _ ((TauCeti.cotangentInnerEquiv_apply_fst _).trans
    (fst_mfderiv_cotangentCoord z (v 0)))

/-- The cotangent lift of the diffeomorphism of `Sⁿ` induced by a linear isometry `e` of `ℝⁿ⁺¹`
acts in coordinates by `(q, p) ↦ (e q, e p)`. -/
@[simp]
theorem cotangentCoord_cotangent_unitSphereDiffeomorph (e : (𝔼 n) ≃ₗᵢ[ℝ] 𝔼 n)
    (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentCoord ((e.unitSphereDiffeomorph (n := n) (k := n) ∞).cotangent z) =
      (e (cotangentCoord z).1, e (cotangentCoord z).2) := by
  refine Prod.ext ?_ (cotangentCoord_snd_eq ?_ fun w ↦ ?_)
  · rw [cotangentCoord_fst, Diffeomorph.proj_cotangent,
      LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply, cotangentCoord_fst]
  · rw [Diffeomorph.proj_cotangent, LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
      LinearIsometryEquiv.inner_map_map, inner_proj_cotangentCoord_snd]
  obtain ⟨v, rfl⟩ := ((e.unitSphereDiffeomorph (n := n) (k := n) ∞).isInvertible_mfderiv (by simp)
    (x := z.proj)).surjective w
  have key := LinearIsometryEquiv.mvfderiv_coe_sphere_unitSphereEquiv (n := n) (k := n) e z.proj v
  rw [← LinearIsometryEquiv.coe_unitSphereDiffeomorph (n := n) (k := n) (m := ∞)] at key
  rw [Diffeomorph.cotangent_snd_apply_mfderiv, ← inner_cotangentCoord_snd,
    Diffeomorph.proj_cotangent, key, LinearIsometryEquiv.inner_map_map]

/-- The cotangent lift of the diffeomorphism of `Sⁿ` induced by an orthogonal matrix `A` acts in
coordinates by `(q, p) ↦ (A q, A p)`. -/
theorem cotangentCoord_cotangent_orthogonal (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
    (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentCoord ((orthogonalToDiffSphere n ∞ A).cotangent z) =
      (Matrix.UnitaryGroup.toLinearIsometryEquiv A (cotangentCoord z).1,
        Matrix.UnitaryGroup.toLinearIsometryEquiv A (cotangentCoord z).2) := by
  rw [orthogonalToDiffSphere_apply, LinearIsometryEquiv.unitSphereDiffHom_apply,
    cotangentCoord_cotangent_unitSphereDiffeomorph]

/-- The antipodal map of `T*Sⁿ`: the cotangent lift of the diffeomorphism `x ↦ -x` of the unit
sphere, induced by `-1 ∈ O(n + 1)`. -/
def antipodal : CotangentBundle (𝓡 n) (𝕊 n) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)⟯ CotangentBundle (𝓡 n) (𝕊 n) :=
  (orthogonalToDiffSphere n ∞ (-1)).cotangent

theorem antipodal_def :
    antipodal (n := n) = (orthogonalToDiffSphere n ∞ (-1)).cotangent :=
  (rfl)

/-- The antipodal map of `T*Sⁿ` acts in coordinates by `(q, p) ↦ (-q, -p)`. -/
@[simp]
theorem cotangentCoord_antipodal (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentCoord (antipodal z) = -cotangentCoord z := by
  rw [antipodal_def, cotangentCoord_cotangent_orthogonal]
  ext <;> simp [Unitary.coe_neg, Matrix.neg_mulVec]

/-- The antipodal map of `T*Sⁿ` preserves the norm `‖p‖`. -/
@[simp]
theorem cotangentNorm_antipodal (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentNorm (antipodal z) = cotangentNorm z := by
  rw [cotangentNorm_def, cotangentNorm_def, cotangentCoord_antipodal, Prod.snd_neg, norm_neg]

/-- The antipodal map of `T*Sⁿ` sends the zero covector at `q` to the zero covector at `-q`. -/
@[simp]
theorem antipodal_zeroSection (q : 𝕊 n) :
    antipodal (zeroSection (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) q) =
      zeroSection (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (fun x : 𝕊 n ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) (-q) :=
  cotangentCoord_injective <| by simp

/-- The normalized geodesic flow of `T*Sⁿ`. Off the zero section it moves a covector with
coordinates `(q, p)` for time `t` along the great circle through `q` in the direction `p / ‖p‖`,
to the covector with coordinates `(cos t • q + (sin t / ‖p‖) • p, cos t • p - (sin t * ‖p‖) • q)`
(`cotangentCoord_geodesicFlow`): the geodesic flow of the round metric, reparametrized to unit
speed on every sphere bundle `{‖p‖ = r}`. On the zero section it is the identity. -/
def geodesicFlow (t : ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) : CotangentBundle (𝓡 n) (𝕊 n) :=
  if hz : cotangentNorm z = 0 then z else
    cotangentMk (sphereGreatCircle z.proj
      (⟨‖(cotangentCoord z).2‖⁻¹ • (cotangentCoord z).2,
        mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (𝕜 := ℝ)
          (norm_ne_zero_iff.1 ((cotangentNorm_def z).symm.trans_ne hz)))⟩ : 𝕊 n)
      ((real_inner_smul_right _ _ _).trans
        (mul_eq_zero_of_right _ (inner_proj_cotangentCoord_snd z))) t)
      (Real.cos t • (cotangentCoord z).2 - (Real.sin t * cotangentNorm z) • (z.proj : 𝔼 n))

theorem geodesicFlow_def (t : ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    geodesicFlow t z = (if hz : cotangentNorm z = 0 then z else
      cotangentMk (sphereGreatCircle z.proj
        (⟨‖(cotangentCoord z).2‖⁻¹ • (cotangentCoord z).2,
          mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (𝕜 := ℝ)
            (norm_ne_zero_iff.1 ((cotangentNorm_def z).symm.trans_ne hz)))⟩ : 𝕊 n)
        ((real_inner_smul_right _ _ _).trans
          (mul_eq_zero_of_right _ (inner_proj_cotangentCoord_snd z))) t)
        (Real.cos t • (cotangentCoord z).2 - (Real.sin t * cotangentNorm z) • (z.proj : 𝔼 n)) :
          CotangentBundle (𝓡 n) (𝕊 n)) :=
  (rfl)

/-- The normalized geodesic flow fixes the zero section. -/
theorem geodesicFlow_of_cotangentNorm_eq_zero {z : CotangentBundle (𝓡 n) (𝕊 n)}
    (hz : cotangentNorm z = 0) (t : ℝ) : geodesicFlow t z = z := by
  rw [geodesicFlow_def, dite_eq_left hz]

/-- Off the zero section, the normalized geodesic flow moves `(q, p)` to
`(cos t • q + (sin t / ‖p‖) • p, cos t • p - (sin t * ‖p‖) • q)`. -/
theorem cotangentCoord_geodesicFlow {z : CotangentBundle (𝓡 n) (𝕊 n)}
    (hz : cotangentNorm z ≠ 0) (t : ℝ) :
    cotangentCoord (geodesicFlow t z) =
      (Real.cos t • (cotangentCoord z).1 + (Real.sin t / ‖(cotangentCoord z).2‖) •
          (cotangentCoord z).2,
        Real.cos t • (cotangentCoord z).2 -
          (Real.sin t * ‖(cotangentCoord z).2‖) • (cotangentCoord z).1) := by
  have hN : ‖(cotangentCoord z).2‖ ≠ 0 := (cotangentNorm_def z).symm.trans_ne hz
  have hqq : ⟪(z.proj : 𝔼 n), (z.proj : 𝔼 n)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow]
  have hpp : ⟪(cotangentCoord z).2, (cotangentCoord z).2⟫_ℝ = ‖(cotangentCoord z).2‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have hpq : ⟪(cotangentCoord z).2, (z.proj : 𝔼 n)⟫_ℝ = 0 := by
    rw [real_inner_comm, inner_proj_cotangentCoord_snd]
  rw [geodesicFlow_def, dite_eq_right hz, cotangentCoord_cotangentMk_of_inner_eq_zero]
  · rw [coe_sphereGreatCircle, Subtype.coe_mk, smul_smul, cotangentNorm_def, cotangentCoord_fst,
      ← div_eq_mul_inv]
  · rw [coe_sphereGreatCircle, Subtype.coe_mk, smul_smul, cotangentNorm_def]
    simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hqq,
      hpp, hpq, inner_proj_cotangentCoord_snd]
    field_simp
    ring

/-- The normalized geodesic flow preserves the norm `‖p‖`. -/
@[simp]
theorem cotangentNorm_geodesicFlow (t : ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    cotangentNorm (geodesicFlow t z) = cotangentNorm z := by
  by_cases hz : cotangentNorm z = 0
  · rw [geodesicFlow_of_cotangentNorm_eq_zero hz]
  have hpq : ⟪(cotangentCoord z).2, (z.proj : 𝔼 n)⟫_ℝ = 0 := by
    rw [real_inner_comm, inner_proj_cotangentCoord_snd]
  rw [cotangentNorm_def, cotangentCoord_geodesicFlow hz, cotangentNorm_def, cotangentCoord_fst]
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hpq,
    norm_eq_of_mem_sphere, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  linear_combination ‖(cotangentCoord z).2‖ ^ 2 * Real.cos_sq_add_sin_sq t

/-- At time `0` the normalized geodesic flow is the identity. -/
@[simp]
theorem geodesicFlow_zero (z : CotangentBundle (𝓡 n) (𝕊 n)) : geodesicFlow 0 z = z := by
  by_cases hz : cotangentNorm z = 0
  · exact geodesicFlow_of_cotangentNorm_eq_zero hz 0
  refine cotangentCoord_injective ?_
  rw [cotangentCoord_geodesicFlow hz]
  ext <;> simp

/-- The flow property of the normalized geodesic flow. -/
theorem geodesicFlow_add (s t : ℝ) (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    geodesicFlow (s + t) z = geodesicFlow s (geodesicFlow t z) := by
  by_cases hz : cotangentNorm z = 0
  · simp only [geodesicFlow_of_cotangentNorm_eq_zero hz]
  have hz' : cotangentNorm (geodesicFlow t z) ≠ 0 := by rwa [cotangentNorm_geodesicFlow]
  have hN : ‖(cotangentCoord z).2‖ ≠ 0 := (cotangentNorm_def z).symm.trans_ne hz
  refine cotangentCoord_injective ?_
  have hnorm : ‖(cotangentCoord (geodesicFlow t z)).2‖ = ‖(cotangentCoord z).2‖ := by
    rw [← cotangentNorm_def, ← cotangentNorm_def, cotangentNorm_geodesicFlow]
  rw [cotangentCoord_geodesicFlow hz', hnorm, cotangentCoord_geodesicFlow hz,
    cotangentCoord_geodesicFlow hz, Real.cos_add, Real.sin_add]
  ext1 <;> dsimp only <;> match_scalars <;> field_simp <;> ring

/-- After time `2π` the normalized geodesic flow returns every covector to itself. -/
@[simp]
theorem geodesicFlow_two_pi (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    geodesicFlow (2 * Real.pi) z = z := by
  by_cases hz : cotangentNorm z = 0
  · exact geodesicFlow_of_cotangentNorm_eq_zero hz _
  refine cotangentCoord_injective ?_
  rw [cotangentCoord_geodesicFlow hz]
  ext <;> simp

/-- Off the zero section, after time `π` the normalized geodesic flow is the antipodal map. -/
theorem geodesicFlow_pi {z : CotangentBundle (𝓡 n) (𝕊 n)} (hz : cotangentNorm z ≠ 0) :
    geodesicFlow Real.pi z = antipodal z := by
  refine cotangentCoord_injective ?_
  rw [cotangentCoord_geodesicFlow hz, cotangentCoord_antipodal]
  ext1 <;> simp

/-- For `sin t ≠ 0`, that is `t` not a multiple of `π`, the normalized geodesic flow at time `t`
has no continuous extension across the zero section of `T*Sⁿ`, `n ≥ 1`: covectors `± s • u` at
`q`, with `u ⊥ q` and `s → 0⁺`, all tend to the zero covector at `q`, while their images have the
distinct base points `cos t • q ± (sin t / ‖u‖) • u`. -/
theorem not_exists_continuous_eqOn_geodesicFlow [NeZero n] {t : ℝ} (ht : Real.sin t ≠ 0) :
    ¬ ∃ g : CotangentBundle (𝓡 n) (𝕊 n) → CotangentBundle (𝓡 n) (𝕊 n), Continuous g ∧
      EqOn g (geodesicFlow t) {z | cotangentNorm z ≠ 0} := by
  rintro ⟨g, hg, hgz⟩
  -- a point `q` of the sphere and a nonzero `u ⊥ q`, which exists since `n ≥ 1`
  let q : 𝕊 n := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hq : (q : 𝔼 n) ≠ 0 := ne_zero_of_mem_unit_sphere q
  have : Fact (Module.finrank ℝ (𝔼 n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hbot : (ℝ ∙ (q : 𝔼 n))ᗮ ≠ ⊥ := by
    rw [Ne, ← Submodule.finrank_eq_zero (R := ℝ),
      Submodule.finrank_orthogonal_span_singleton (n := n) hq]
    exact NeZero.ne n
  obtain ⟨u, hu_mem, hu⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hqu : ⟪(q : 𝔼 n), u⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 hu_mem
  -- along the ray `s • v`, `s > 0`, the base point of `g` is constant, hence also at `s = 0`
  have key (v : 𝔼 n) (hv : v ≠ 0) (hqv : ⟪(q : 𝔼 n), v⟫_ℝ = 0) :
      ((g (cotangentMk q 0)).proj : 𝔼 n) = Real.cos t • (q : 𝔼 n) + (Real.sin t / ‖v‖) • v := by
    have hf : Continuous fun s : ℝ ↦ ((g (cotangentMk q (s • v))).proj : 𝔼 n) :=
      continuous_subtypeVal.comp (FiberBundle.continuous_proj _ _ |>.comp
        (hg.comp ((contMDiff_cotangentMk.continuous.comp
          (continuous_const.prodMk (continuous_id.smul continuous_const))))))
    have hsub : Ioi (0 : ℝ) ⊆ {s | ((g (cotangentMk q (s • v))).proj : 𝔼 n) =
        Real.cos t • (q : 𝔼 n) + (Real.sin t / ‖v‖) • v} := fun s (hs : 0 < s) ↦ by
      have hcoord : cotangentCoord (cotangentMk q (s • v)) = ((q : 𝔼 n), s • v) :=
        cotangentCoord_cotangentMk_of_inner_eq_zero (by rw [real_inner_smul_right, hqv, mul_zero])
      have hnorm : ‖s • v‖ = s * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
      have hz : cotangentNorm (cotangentMk q (s • v)) ≠ 0 := by
        rw [cotangentNorm_def, hcoord, hnorm]
        exact mul_ne_zero hs.ne' (norm_ne_zero_iff.2 hv)
      rw [mem_ofPred_eq, hgz hz, ← cotangentCoord_fst, cotangentCoord_geodesicFlow hz, hcoord,
        hnorm, smul_smul]
      field_simp
    have h0 := (isClosed_eq hf continuous_const).closure_subset_iff.2 hsub
      (by rw [closure_Ioi]; exact self_mem_Ici)
    simpa using h0
  have h := (key u hu hqu).symm.trans (key (-u) (neg_ne_zero.2 hu) (by rw [inner_neg_right, hqu,
    neg_zero]))
  rw [norm_neg, smul_neg, add_right_inj, ← sub_eq_zero, sub_neg_eq_add, ← two_smul ℝ,
    smul_smul, smul_eq_zero] at h
  rcases h with h | h
  · exact mul_ne_zero two_ne_zero (div_ne_zero ht (norm_ne_zero_iff.2 hu)) h
  · exact hu h

/-- The orbit `t ↦ geodesicFlow t z` of a covector under the normalized geodesic flow is smooth;
it is constant when `z` lies on the zero section. -/
theorem contMDiff_geodesicFlow (z : CotangentBundle (𝓡 n) (𝕊 n)) :
    ContMDiff 𝓘(ℝ) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (geodesicFlow · z) := by
  by_cases hz : cotangentNorm z = 0
  · simp only [geodesicFlow_of_cotangentNorm_eq_zero hz]
    exact contMDiff_const
  simp only [geodesicFlow_def, dite_eq_right hz]
  refine contMDiff_cotangentMk.comp (f := fun t ↦ (_, _)) (ContMDiff.prodMk ?_ ?_)
  · refine ContMDiff.of_le ?_ le_top
    exact contMDiff_sphereGreatCircle _ _ ((real_inner_smul_right _ _ _).trans
      (mul_eq_zero_of_right _ (inner_proj_cotangentCoord_snd z)))
  · exact ((Real.contDiff_cos.smul contDiff_const).sub
      ((Real.contDiff_sin.mul contDiff_const).smul contDiff_const)).contMDiff

/-- **The canonical symplectic form in the coordinates `(q, p)`.** The differential of
`cotangentCoord` carries the canonical symplectic form of `T*Sⁿ` to the standard form
`ω₀((δq, δp), (δq', δp')) = ⟪δq, δp'⟫ - ⟪δp, δq'⟫` (`TauCeti.stdSymplecticForm`) of
`ℝⁿ⁺¹ × ℝⁿ⁺¹`: the form `∑ⱼ dqⱼ ∧ dpⱼ` restricted to the image of `T*Sⁿ`. -/
theorem eval₂_symplecticForm_eq_stdSymplecticForm (z : CotangentBundle (𝓡 n) (𝕊 n))
    (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) z) :
    SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)) z v w =
      stdSymplecticForm
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
          cotangentCoord z v)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
          cotangentCoord z w) := by
  have hΦ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      𝓘(ℝ, (𝔼 n) × StrongDual ℝ (𝔼 n)) ∞ (TauCeti.cotangentInnerEquiv ∘ cotangentCoord) :=
    (TauCeti.cotangentInnerEquiv (V := 𝔼 n)).contDiff.contMDiff.comp contMDiff_cotangentCoord
  have hL : IsSmoothBundleForm (I := 𝓘(ℝ, (𝔼 n) × StrongDual ℝ (𝔼 n))) (F := ℝ)
      (V := Trivial ((𝔼 n) × StrongDual ℝ (𝔼 n)) ℝ) 1
      (fun x ↦ TauCeti.cotangentLiouvilleForm x) :=
    (isSmoothBundleForm_def 1 _).mpr
      ((isSmoothForm_modelSpace_iff.mpr contDiff_cotangentLiouvilleForm).contMDiff)
  have h1 : mextDeriv (I := 𝓘(ℝ, (𝔼 n) × StrongDual ℝ (𝔼 n)))
      (fun x ↦ TauCeti.cotangentLiouvilleForm x) (TauCeti.cotangentInnerEquiv (cotangentCoord z)) =
      extDeriv TauCeti.cotangentLiouvilleForm (TauCeti.cotangentInnerEquiv (cotangentCoord z)) :=
    mextDeriv_eq_extDeriv _ _
  rw [SmoothBundleForm.eval₂_apply, CotangentBundle.symplecticForm_eq_neg_mextDeriv,
    ← mpullback_cotangentCoord, ← mpullback_mextDeriv (hΦ.of_le (by simp)) hL, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, mpullback_apply, Function.comp_apply, h1]
  refine (neg_extDeriv_cotangentLiouvilleForm_apply _ _).trans ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mfderiv_cotangentInnerEquiv_comp_cotangentCoord_apply,
    mfderiv_cotangentInnerEquiv_comp_cotangentCoord_apply]
  exact isSymplectomorphism_cotangentInnerEquiv.apply _ _

/-- The differential of the first coordinate `q` of a covector is orthogonal to `q`, as the base
point stays on the unit sphere. -/
theorem inner_fst_mfderiv_cotangentCoord (x : CotangentBundle (𝓡 n) (𝕊 n))
    (w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) x) :
    ⟪(cotangentCoord x).1,
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
        cotangentCoord x w).1⟫_ℝ = 0 := by
  rw [fst_mfderiv_cotangentCoord, cotangentCoord_fst]
  exact inner_coe_mvfderiv_subtypeVal_sphere _ _

/-- The chain rule through `cotangentCoord`: if `g` has the derivative `L` at the coordinates
of `x`, then the differential of `g ∘ cotangentCoord` at `x` is `L` applied to the differential
of `cotangentCoord`. -/
theorem _root_.HasFDerivAt.mfderiv_comp_cotangentCoord_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ((𝔼 n) × 𝔼 n) → F} {L : ((𝔼 n) × 𝔼 n) →L[ℝ] F}
    {x : CotangentBundle (𝓡 n) (𝕊 n)} (hg : HasFDerivAt g L (cotangentCoord x))
    (w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) x) :
    mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, F) (g ∘ cotangentCoord) x
        w =
      L (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
        cotangentCoord x w) := by
  rw [mfderiv_comp_apply x hg.differentiableAt.mdifferentiableAt
    (contMDiff_cotangentCoord.mdifferentiableAt (by simp)), hg.hasMFDerivAt.mfderiv]
  -- The two sides differ only in how the tangent space of the model space `F` is written.
  rfl

/-- The differentials `(δq, δp)` of the coordinates of a covector satisfy
`⟪δq, p⟫ + ⟪q, δp⟫ = 0`, as `p` stays orthogonal to `q`. -/
theorem inner_fst_mfderiv_cotangentCoord_add_inner_snd (x : CotangentBundle (𝓡 n) (𝕊 n))
    (w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) x) :
    ⟪(mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
        cotangentCoord x w).1, (cotangentCoord x).2⟫_ℝ +
      ⟪(cotangentCoord x).1,
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
          cotangentCoord x w).2⟫_ℝ = 0 := by
  have hg := (hasFDerivAt_fst (p := cotangentCoord x)).inner ℝ
    (hasFDerivAt_snd (p := cotangentCoord x))
  rw [ContinuousLinearMap.fst_prod_snd, ContinuousLinearMap.comp_id] at hg
  have hcomp : (fun y : (𝔼 n) × 𝔼 n ↦ ⟪y.1, y.2⟫_ℝ) ∘ cotangentCoord (n := n) = fun _ ↦ 0 :=
    funext fun z ↦ by simp [cotangentCoord_fst]
  have h := hg.mfderiv_comp_cotangentCoord_apply w
  rw [hcomp, mfderiv_const, zero_apply] at h
  exact (add_comm _ _).trans ((fderivInnerCLM_apply _ _ _).symm.trans h.symm)

/-- The Liouville form in the coordinates `(q, p)`: it sends a tangent vector at a covector to
`⟪p, δq⟫`, where `δq` is the differential of the first coordinate. -/
theorem liouvilleForm_apply_eq_inner_cotangentCoord (y : CotangentBundle (𝓡 n) (𝕊 n))
    (v : Fin 1 → TangentSpace ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) y) :
    (CotangentBundle.liouvilleForm (𝓡 n) (𝕊 n)).val y v =
      ⟪(cotangentCoord y).2,
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
          cotangentCoord y (v 0)).1⟫_ℝ := by
  rw [CotangentBundle.liouvilleForm_apply, fst_mfderiv_cotangentCoord, inner_cotangentCoord_snd]

/-- The pullback of the Liouville form by a map `h` of `T*Sⁿ` that is differentiable at `z`, in
the coordinates `(q, p)`: it sends a tangent vector at `z` to `⟪p', δq'⟫`, where `(q', p')` are
the coordinates of `h z` and `δq'` is the differential of `q' ∘ h`. -/
theorem mpullback_liouvilleForm_apply_eq_inner_cotangentCoord
    {h : CotangentBundle (𝓡 n) (𝕊 n) → CotangentBundle (𝓡 n) (𝕊 n)}
    {z : CotangentBundle (𝓡 n) (𝕊 n)}
    (hh : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) h z)
    (v : Fin 1 → TangentSpace ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) z) :
    mpullback ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) h
        (CotangentBundle.liouvilleForm (𝓡 n) (𝕊 n)).val z v =
      ⟪(cotangentCoord (h z)).2,
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
          (cotangentCoord ∘ h) z (v 0)).1⟫_ℝ := by
  rw [mpullback_apply, liouvilleForm_apply_eq_inner_cotangentCoord, mfderiv_comp_apply z
    (contMDiff_cotangentCoord.mdifferentiableAt (by simp)) hh]

/-- Off the zero section, the differential of the norm `μ = ‖p‖` is `δp ↦ ⟪p, δp⟫ / ‖p‖`, read
through the differential of `cotangentCoord`. -/
theorem mvfderiv_cotangentNorm {x : CotangentBundle (𝓡 n) (𝕊 n)} (hx : cotangentNorm x ≠ 0)
    (w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) x) :
    mvfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) cotangentNorm x w =
      ⟪(cotangentCoord x).2,
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
          cotangentCoord x w).2⟫_ℝ / cotangentNorm x := by
  have h2 : ‖(cotangentCoord x).2‖ ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hg := ((hasFDerivAt_snd (p := cotangentCoord x)).norm_sq).sqrt h2
  have hcomp : cotangentNorm (n := n) = (fun y : (𝔼 n) × 𝔼 n ↦ √(‖y.2‖ ^ 2)) ∘ cotangentCoord :=
    funext fun z ↦ by simp [cotangentNorm_def, Real.sqrt_sq (norm_nonneg _)]
  have key (u : (𝔼 n) × 𝔼 n) :
      ((1 / (2 * √(‖(cotangentCoord x).2‖ ^ 2))) • 2 • (innerSL ℝ (cotangentCoord x).2).comp
        (ContinuousLinearMap.snd ℝ (𝔼 n) (𝔼 n))) u =
      ⟪(cotangentCoord x).2, u.2⟫_ℝ / cotangentNorm x := by
    simp only [Real.sqrt_sq (norm_nonneg _), one_div, mul_inv_rev, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', coe_innerSL_apply,
      nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, cotangentNorm_def]
    field_simp
  rw [mvfderiv_apply_eq_mfderiv_apply]
  conv_lhs => rw [hcomp]
  rw [hg.mfderiv_comp_cotangentCoord_apply]
  exact key _

/-- For a `C¹` function `k`, the differential of `z ↦ k (μ z ^ 2)`, `μ = cotangentNorm`, is
`δp ↦ k' (μ ^ 2) * 2 ⟪p, δp⟫`, read through the differential of `cotangentCoord`. Unlike
`mvfderiv_cotangentNorm`, this holds on the zero section too. -/
theorem mvfderiv_comp_cotangentNorm_sq {k : ℝ → ℝ} (hk : ContDiff ℝ 1 k)
    (x : CotangentBundle (𝓡 n) (𝕊 n))
    (w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) x) :
    mvfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        (fun z ↦ k (cotangentNorm z ^ 2)) x w =
      deriv k (cotangentNorm x ^ 2) * (2 * ⟪(cotangentCoord x).2,
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
          cotangentCoord x w).2⟫_ℝ) := by
  have hg := (hk.differentiable one_ne_zero _).hasDerivAt.hasFDerivAt.comp _
    (hasFDerivAt_snd (p := cotangentCoord x)).norm_sq
  have hcomp : (fun z ↦ k (cotangentNorm z ^ 2)) =
      (k ∘ fun y : (𝔼 n) × 𝔼 n ↦ ‖y.2‖ ^ 2) ∘ cotangentCoord (n := n) :=
    funext fun z ↦ by rw [Function.comp_apply, Function.comp_apply, cotangentNorm_def]
  have key (u : (𝔼 n) × 𝔼 n) :
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv k (‖(cotangentCoord x).2‖ ^ 2))).comp
        (2 • (innerSL ℝ (cotangentCoord x).2).comp (ContinuousLinearMap.snd ℝ (𝔼 n) (𝔼 n)))) u =
      deriv k (‖(cotangentCoord x).2‖ ^ 2) * (2 * ⟪(cotangentCoord x).2, u.2⟫_ℝ) := by
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.coe_snd',
      innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, nsmul_eq_mul]
    ring
  have h := hg.mfderiv_comp_cotangentCoord_apply w
  rw [← hcomp] at h
  rw [mvfderiv_apply_eq_mfderiv_apply, h, cotangentNorm_def]
  exact key _

/-- Off the zero section, the velocity of the orbit `t ↦ geodesicFlow t z` at a covector with
coordinates `(q, p)` reads `(p / ‖p‖, -‖p‖ q)` in coordinates. -/
theorem mfderiv_cotangentCoord_curveVelocity_geodesicFlow {z : CotangentBundle (𝓡 n) (𝕊 n)}
    (hz : cotangentNorm z ≠ 0) (t : ℝ) :
    mfderiv ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 𝓘(ℝ, (𝔼 n) × 𝔼 n)
        cotangentCoord (geodesicFlow t z)
        (curveVelocity ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
          (geodesicFlow · z) t) =
      ((cotangentNorm z)⁻¹ • (cotangentCoord (geodesicFlow t z)).2,
        -(cotangentNorm z • (cotangentCoord (geodesicFlow t z)).1)) := by
  have hΨ : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      𝓘(ℝ, (𝔼 n) × 𝔼 n) cotangentCoord (geodesicFlow t z) :=
    contMDiff_cotangentCoord.mdifferentiableAt (by simp)
  have h := hasDerivAt_comp_curve hΨ (hasMFDerivAt_curveVelocity
    ((contMDiff_geodesicFlow z).mdifferentiableAt (x := t) (by simp)))
  have hF : HasDerivAt (cotangentCoord ∘ (geodesicFlow · z))
      (-Real.sin t • (cotangentCoord z).1 +
          (Real.cos t / ‖(cotangentCoord z).2‖) • (cotangentCoord z).2,
        -Real.sin t • (cotangentCoord z).2 -
          (Real.cos t * ‖(cotangentCoord z).2‖) • (cotangentCoord z).1) t := by
    rw [show cotangentCoord ∘ (geodesicFlow · z) = _ from
      funext fun s ↦ cotangentCoord_geodesicFlow hz s]
    exact (((Real.hasDerivAt_cos t).smul_const _).add
      (((Real.hasDerivAt_sin t).div_const _).smul_const _)).prodMk
      (((Real.hasDerivAt_cos t).smul_const _).sub
        (((Real.hasDerivAt_sin t).mul_const _).smul_const _))
  have hN : ‖(cotangentCoord z).2‖ ≠ 0 := (cotangentNorm_def z).symm.trans_ne hz
  rw [← mvfderiv_apply_eq_mfderiv_apply, h.unique hF, cotangentCoord_geodesicFlow hz,
    cotangentNorm_def]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> match_scalars <;> field_simp

/-- **The normalized geodesic flow is the Hamiltonian flow of the norm.** Off the zero section,
the orbit `t ↦ geodesicFlow t z` is an integral curve of the Hamiltonian vector field of
`cotangentNorm` for the canonical symplectic form `ω = -dλ` of `T*Sⁿ`, with Tau Ceti's convention
`ι_(X_μ) ω = dμ`. -/
theorem isMIntegralCurve_geodesicFlow {z : CotangentBundle (𝓡 n) (𝕊 n)}
    (hz : cotangentNorm z ≠ 0) :
    IsMIntegralCurve (geodesicFlow · z) fun w ↦
      (CotangentBundle.symplecticForm (𝓡 n) (𝕊 n)).hamiltonianVectorField cotangentNorm w := by
  refine isMIntegralCurve_iff_curveVelocity_eq.mpr fun t ↦
    ⟨(contMDiff_geodesicFlow z).mdifferentiableAt (by simp), ?_⟩
  have hx : cotangentNorm (geodesicFlow t z) ≠ 0 := by rwa [cotangentNorm_geodesicFlow]
  symm
  rw [SmoothTwoForm.hamiltonianVectorField_eq_iff_of_isInvertible_flat
    (CotangentBundle.isSymplectic_symplecticForm.isNondegenerate.isInvertible_flat _)]
  intro w
  rw [eval₂_symplecticForm_eq_stdSymplecticForm]
  refine (stdSymplecticForm_apply _ _).trans ?_
  rw [mfderiv_cotangentCoord_curveVelocity_geodesicFlow hz, mvfderiv_cotangentNorm hx,
    real_inner_smul_left, inner_neg_left, real_inner_smul_left, inner_fst_mfderiv_cotangentCoord,
    cotangentNorm_geodesicFlow]
  field_simp
  ring

end SymplecticGeometry

end
