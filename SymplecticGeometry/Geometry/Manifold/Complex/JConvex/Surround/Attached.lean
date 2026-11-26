/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import SymplecticGeometry.Topology.MetricSpace.Tube

/-!
# Discs attached J-orthogonally to a domain

Let `M` be a complex manifold modelled on `E`, seen as a real manifold, `φ : M → ℝ` a function
and `W = {φ ≤ 0}`. A disc in `M` is given by a map `ι : F → M` from a real normed space: the
disc is `ι '' closedBall 0 1` and its boundary sphere is `ι '' sphere 0 1`.

The disc is **attached J-orthogonally** to `W` (`SymplecticGeometry.IsJOrthogonallyAttached`)
when the open disc lies outside `W`, the boundary sphere lies on `∂W = {φ = 0}`, the disc
crosses `∂W` transversally there, continuing into `W` (`dφ(dι_x(x)) < 0` for `‖x‖ = 1`), and
multiplication by `i` maps the tangent space of the disc into the kernel of `dφ` along the
sphere. The last condition says that the boundary sphere is tangent to the complex tangencies of
`∂W`, and that `i` times the radial direction of the disc is tangent to `∂W`.

This is Cieliebak–Eliashberg's notion: their Definition 2.22 calls a totally real submanifold
`L` J-orthogonal to a hypersurface `Σ` when, at each point `p` of `L ∩ Σ`, `J (T_p L) ⊆ T_p Σ`
and `T_p L ⊄ T_p Σ`, and their §7.9 says that an embedding of a disc attaches it J-orthogonally
to `W` when it maps the disc into the complement of the interior of `W`, meets `∂W` exactly in
the image of the boundary sphere, and is J-orthogonal to `∂W` there. The four fields are these
conditions for `W = {φ ≤ 0}` and `∂W = {φ = 0}`, with the transversality written as a sign of
`dφ` on the radial direction: `φ ∘ ι` vanishes on the sphere, so at a point `x` of the sphere
its derivative vanishes on the sphere's tangent space, and it is positive inside the sphere, so
its derivative on the radial vector `x` is `≤ 0`; hence `ι` is transverse to `{φ = 0}` at `x`
exactly when this radial derivative is negative. Being an embedding and being totally real are
not fields: the J-convex surrounding (Cieliebak–Eliashberg, Theorem 8.4) asks for them as
separate hypotheses.

## Main results

* `SymplecticGeometry.IsJOrthogonallyAttached.image_closedBall_inter`: the disc meets `W`
  exactly in its boundary sphere.
* `SymplecticGeometry.IsJOrthogonallyAttached.exists_lt_forall_neg`: for `C¹` data, just
  beyond the sphere the map `ι` takes values in `{φ < 0}`.
* `SymplecticGeometry.IsJOrthogonallyAttached.comp`: the condition persists when `φ` is
  replaced by `f ∘ φ`, for `f` with `f 0 = 0`, positive on `(0, ∞)`, and with positive derivative
  at `0`.
* `SymplecticGeometry.IsJOrthogonallyAttached.comp_linearIsometry`: it persists under
  precomposition of the disc with a linear isometry.

The model case, `SymplecticGeometry.isJOrthogonallyAttached_model`, is in
`SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Shape`, with the model disc and
the model level.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Definition 2.22 (J-orthogonality to a hypersurface), §7.9 (discs attached J-orthogonally) and
  Theorem 8.4 (the J-convex surrounding of such a disc).
-/

public section

noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (E) in
/-- A disc `ι '' closedBall 0 1`, given by `ι : F → M`, is **attached J-orthogonally** to the
domain `{φ ≤ 0}` of a complex manifold `M` when the open disc lies in `{φ > 0}`, the boundary
sphere lies in `{φ = 0}`, the derivative of `φ` along the outward radial direction of the disc
is negative on the sphere (so the disc meets `{φ = 0}` transversally), and along the sphere,
multiplication by `i` maps the tangent space of the disc into the kernel of `dφ`.

These are the conditions of Cieliebak–Eliashberg, *From Stein to Weinstein and Back*, §7.9, for
an attachment that is J-orthogonal in the sense of their Definition 2.22. -/
structure IsJOrthogonallyAttached (φ : M → ℝ) (ι : F → M) : Prop where
  /-- The open disc lies outside the domain. -/
  pos : ∀ x : F, ‖x‖ < 1 → 0 < φ (ι x)
  /-- The boundary sphere lies on the boundary of the domain. -/
  eq_zero : ∀ x : F, ‖x‖ = 1 → φ (ι x) = 0
  /-- Along the sphere, `φ` decreases in the outward radial direction of the disc. -/
  mvfderiv_mfderiv_self_neg : ∀ x : F, ‖x‖ = 1 →
    mvfderiv 𝓘(ℝ, E) φ (ι x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι x x) < 0
  /-- Along the sphere, `i` times a tangent vector of the disc lies in the kernel of `dφ`. -/
  mvfderiv_I_smul_mfderiv : ∀ x : F, ‖x‖ = 1 → ∀ v : F,
    mvfderiv 𝓘(ℝ, E) φ (ι x) (Complex.I • (show E from mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι x v)) = 0

namespace IsJOrthogonallyAttached

variable {φ : M → ℝ} {ι : F → M}

/-- The disc meets the domain `{φ ≤ 0}` exactly in its boundary sphere. -/
theorem image_closedBall_inter (h : IsJOrthogonallyAttached E φ ι) :
    ι '' closedBall 0 1 ∩ {y | φ y ≤ 0} = ι '' sphere 0 1 := by
  ext y
  simp only [mem_inter_iff, mem_image, mem_closedBall, mem_sphere, dist_zero_right,
    mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hφ⟩
    refine ⟨x, hx.eq_or_lt.resolve_right fun hx' ↦ ?_, rfl⟩
    exact (h.pos x hx').not_ge hφ
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.le, rfl⟩, (h.eq_zero x hx).le⟩

/-- The disc map `ι` is differentiable at each point of the unit sphere. -/
theorem mdifferentiableAt (h : IsJOrthogonallyAttached E φ ι) {x : F} (hx : ‖x‖ = 1) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) ι x := by
  by_contra hι
  have := h.mvfderiv_mfderiv_self_neg x hx
  rw [mfderiv_zero_of_not_mdifferentiableAt hι] at this
  exact this.ne ((congrArg (mvfderiv 𝓘(ℝ, E) φ (ι x)) (zero_apply x)).trans
    (map_zero _))

/-- The function `φ` is differentiable at each point of the boundary sphere of the disc. -/
theorem mdifferentiableAt_apply (h : IsJOrthogonallyAttached E φ ι) {x : F} (hx : ‖x‖ = 1) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) φ (ι x) := by
  by_contra hφ
  have := h.mvfderiv_mfderiv_self_neg x hx
  rw [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hφ] at this
  simp at this

/-- **The extended disc enters the domain beyond the sphere.** For `C¹` maps `φ` and `ι`, with
`F` finite-dimensional, there is `r > 1` such that `φ (ι x) < 0` whenever `1 < ‖x‖ < r`. -/
theorem exists_lt_forall_neg [FiniteDimensional ℝ F] (h : IsJOrthogonallyAttached E φ ι)
    (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 1 φ) (hι : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) 1 ι) :
    ∃ r > 1, ∀ x : F, 1 < ‖x‖ → ‖x‖ < r → φ (ι x) < 0 := by
  set g : F → ℝ := φ ∘ ι
  have hg : ContDiff ℝ 1 g := contMDiff_iff_contDiff.1 (hφ.comp hι)
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  -- The radial derivative of `g` is negative on the sphere.
  have hneg : ∀ x : F, ‖x‖ = 1 → fderiv ℝ g x x < 0 := by
    intro x hx
    have h1 := mvfderiv_comp_apply x (h.mdifferentiableAt_apply hx) (h.mdifferentiableAt hx) x
    rw [mvfderiv_eq_fderiv] at h1
    exact h1 ▸ h.mvfderiv_mfderiv_self_neg x hx
  -- By compactness of the sphere, it stays negative on `t • x` for `t` near `1`.
  have hcont : Continuous fun p : F × ℝ ↦ fderiv ℝ g (p.2 • p.1) p.1 :=
    ((hg.continuous_fderiv one_ne_zero).comp (continuous_snd.smul continuous_fst)).clm_apply
      continuous_fst
  obtain ⟨δ, hδ, huv⟩ := (isCompact_sphere (0 : F) 1).exists_prod_ball_subset (y := (1 : ℝ))
    (U := {p : F × ℝ | fderiv ℝ g (p.2 • p.1) p.1 < 0}) (isOpen_lt hcont continuous_const)
    (by rintro ⟨x, t⟩ ⟨hx, rfl⟩; simpa using hneg x (by simpa using hx))
  refine ⟨1 + δ, by linarith, fun y hy1 hyr ↦ ?_⟩
  have hy0 : ‖y‖ ≠ 0 := by positivity
  set x : F := ‖y‖⁻¹ • y
  have hx : ‖x‖ = 1 := by simp [x, norm_smul, hy0]
  have hxy : ‖y‖ • x = y := by simp [x, smul_smul, hy0]
  -- Along the ray through `x`, `g` is strictly decreasing on `[1, ‖y‖]`.
  have hderiv (t : ℝ) : HasDerivAt (g ∘ fun s : ℝ ↦ s • x) (fderiv ℝ g (t • x) x) t := by
    simpa using (hgd (t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
  have hanti : StrictAntiOn (g ∘ fun s : ℝ ↦ s • x) (Icc 1 ‖y‖) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t _ ↦ (hderiv t).continuousAt.continuousWithinAt) fun t ht ↦ ?_
    rw [interior_Icc] at ht
    rw [(hderiv t).deriv]
    have hmem : (x, t) ∈ sphere (0 : F) 1 ×ˢ ball 1 δ := by
      refine ⟨by simpa using hx, ?_⟩
      rw [Real.ball_eq_Ioo]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact huv hmem
  have := hanti ⟨le_rfl, hy1.le⟩ ⟨hy1.le, le_rfl⟩ hy1
  simpa [g, hxy, h.eq_zero x hx] using this

/-- **Reparametrizing the function.** If `f : ℝ → ℝ` vanishes at `0`, is positive on `(0, ∞)`
and has a positive derivative at `0`, then a disc attached J-orthogonally to `{φ ≤ 0}` is
attached J-orthogonally to `{f ∘ φ ≤ 0}`. -/
theorem comp (h : IsJOrthogonallyAttached E φ ι) {f : ℝ → ℝ} {f' : ℝ} (hf0 : f 0 = 0)
    (hfpos : ∀ a, 0 < a → 0 < f a) (hf : HasDerivAt f f' 0) (hf' : 0 < f') :
    IsJOrthogonallyAttached E (f ∘ φ) ι := by
  -- Along the sphere, `d(f ∘ φ) = f' • dφ`.
  have key {x : F} (hx : ‖x‖ = 1) (w : TangentSpace 𝓘(ℝ, E) (ι x)) :
      mvfderiv 𝓘(ℝ, E) (f ∘ φ) (ι x) w = f' * mvfderiv 𝓘(ℝ, E) φ (ι x) w := by
    have hfx : HasDerivAt f f' (φ (ι x)) := h.eq_zero x hx ▸ hf
    rw [mvfderiv_comp_apply _ hfx.differentiableAt.mdifferentiableAt (h.mdifferentiableAt_apply hx),
      mvfderiv_eq_fderiv, hfx.hasFDerivAt.fderiv]
    simp [mvfderiv, mul_comm]
  refine ⟨fun x hx ↦ hfpos _ (h.pos x hx), fun x hx ↦ by simp [h.eq_zero x hx, hf0],
    fun x hx ↦ ?_, fun x hx v ↦ ?_⟩
  · rw [key hx]
    exact mul_neg_of_pos_of_neg hf' (h.mvfderiv_mfderiv_self_neg x hx)
  · refine (key hx _).trans ?_
    rw [h.mvfderiv_I_smul_mfderiv x hx v, mul_zero]

/-- **Reparametrizing the disc.** A disc attached J-orthogonally stays so after precomposition
with a linear isometry. -/
theorem comp_linearIsometry (h : IsJOrthogonallyAttached E φ ι) {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] (e : F' →ₗᵢ[ℝ] F) :
    IsJOrthogonallyAttached E φ (ι ∘ e) := by
  have key {x : F'} (hx : ‖x‖ = 1) (v : TangentSpace 𝓘(ℝ, F') x) :
      mfderiv 𝓘(ℝ, F') 𝓘(ℝ, E) (ι ∘ e) x v = mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι (e x) (e v) := by
    have := mfderiv_comp_apply x (h.mdifferentiableAt (by simpa using hx))
      e.toContinuousLinearMap.mdifferentiableAt v
    rw [e.toContinuousLinearMap.mfderiv_eq] at this
    exact this
  refine ⟨fun x hx ↦ h.pos (e x) (by simpa using hx),
    fun x hx ↦ h.eq_zero (e x) (by simpa using hx),
    fun x hx ↦ ?_, fun x hx v ↦ ?_⟩
  · have hx' : ‖e x‖ = 1 := by simpa using hx
    exact key hx x ▸ h.mvfderiv_mfderiv_self_neg (e x) hx'
  · have hx' : ‖e x‖ = 1 := by simpa using hx
    exact key hx v ▸ h.mvfderiv_I_smul_mfderiv (e x) hx' (e v)

end IsJOrthogonallyAttached

end SymplecticGeometry

end
