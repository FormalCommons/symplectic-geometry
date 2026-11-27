/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import SymplecticGeometry.Topology.MetricSpace.Tube
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

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
* `SymplecticGeometry.IsJOrthogonallyAttached.fderiv_comp_apply_self_neg`: on the sphere, the
  radial derivative of `φ ∘ ι` is negative.
* `SymplecticGeometry.IsJOrthogonallyAttached.exists_lt_forall_neg`: for `C¹` data, just
  beyond the sphere the map `ι` takes values in `{φ < 0}`.
* `SymplecticGeometry.IsJOrthogonallyAttached.comp`: the condition persists when `φ` is
  replaced by `f ∘ φ`, for `f` with `f 0 = 0`, positive on `(0, ∞)`, and with positive derivative
  at `0`.
* `SymplecticGeometry.IsJOrthogonallyAttached.comp_of_mfderiv_apply_self_eq_smul`: it persists
  under precomposition of the disc with a map `σ : F' → F` that maps the open unit ball into the
  open unit ball and the unit sphere into the unit sphere, and whose differential sends each
  point `x` of the sphere to a positive multiple of `σ x`. When `σ` fixes the sphere pointwise,
  this covers the radial maps `x ↦ τ x • x` with `τ = 1` on the sphere, `0 < 1 + dτ_x x` there
  and `‖τ x • x‖ < 1` on the open ball.
* `SymplecticGeometry.IsJOrthogonallyAttached.comp_linearIsometry`: in particular, it persists
  under precomposition of the disc with a linear isometry.
* `SymplecticGeometry.IsJOrthogonallyAttached.congr_of_eventuallyEq`: only the germs of `φ` at
  the points of the sphere and the sign of `φ` on the open disc matter.
* `SymplecticGeometry.IsJOrthogonallyAttached.map_partialDiffeomorph`: the condition is carried
  by a partial diffeomorphism `Φ`, defined on the disc and with complex linear differential along
  the sphere, to the disc `Φ ∘ ι` and the function `φ ∘ Φ.symm`. This is the chain rule, with
  Tau Ceti's `PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply`.

For a diffeomorphism `σ`, Tau Ceti already gives the other properties of `ι ∘ σ` that a
reparametrization needs: it is a smooth embedding when `ι` is
(`TauCeti.isSmoothEmbedding_comp_diffeomorph`), and its tangent images are those of `ι`
(`Diffeomorph.range_mfderiv_comp_diffeomorph`). For a bijection `σ` of `F` that maps the open
unit ball onto itself and fixes the unit sphere pointwise,
`Equiv.image_closedBall_eq_of_eqOn_sphere` (in `SymplecticGeometry.Topology.MetricSpace.Ball`)
shows that `ι ∘ σ` and `ι` give the same disc.

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

/-- On the unit sphere, the radial derivative of `φ ∘ ι` at `x` is `dφ (dι_x x)`. -/
theorem fderiv_comp_apply_self (h : IsJOrthogonallyAttached E φ ι) {x : F} (hx : ‖x‖ = 1) :
    fderiv ℝ (φ ∘ ι) x x = mvfderiv 𝓘(ℝ, E) φ (ι x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι x x) := by
  have h1 := mvfderiv_comp_apply x (h.mdifferentiableAt_apply hx) (h.mdifferentiableAt hx) x
  rwa [mvfderiv_eq_fderiv] at h1

/-- On the unit sphere, the radial derivative of `φ ∘ ι` is negative. -/
theorem fderiv_comp_apply_self_neg (h : IsJOrthogonallyAttached E φ ι) {x : F} (hx : ‖x‖ = 1) :
    fderiv ℝ (φ ∘ ι) x x < 0 :=
  h.fderiv_comp_apply_self hx ▸ h.mvfderiv_mfderiv_self_neg x hx

/-- **The extended disc enters the domain beyond the sphere.** For `C¹` maps `φ` and `ι`, with
`F` finite-dimensional, there is `r > 1` such that `φ (ι x) < 0` whenever `1 < ‖x‖ < r`. -/
theorem exists_lt_forall_neg [FiniteDimensional ℝ F] (h : IsJOrthogonallyAttached E φ ι)
    (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 1 φ) (hι : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) 1 ι) :
    ∃ r > 1, ∀ x : F, 1 < ‖x‖ → ‖x‖ < r → φ (ι x) < 0 := by
  set g : F → ℝ := φ ∘ ι
  have hg : ContDiff ℝ 1 g := contMDiff_iff_contDiff.1 (hφ.comp hι)
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  -- The radial derivative of `g` is negative on the sphere.
  have hneg : ∀ x : F, ‖x‖ = 1 → fderiv ℝ g x x < 0 := fun _ ↦ h.fderiv_comp_apply_self_neg
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

/-- **Reparametrizing the disc.** Let `σ : F' → F` map the open unit ball into the open unit ball
and the unit sphere into the unit sphere, and have, at each point `x` of the sphere, a differential
that sends the radial vector `x` to a positive multiple of `σ x`. Then a disc attached
J-orthogonally stays so after precomposition with `σ`. -/
theorem comp_of_mfderiv_apply_self_eq_smul (h : IsJOrthogonallyAttached E φ ι) {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {σ : F' → F}
    (hball : ∀ x : F', ‖x‖ < 1 → ‖σ x‖ < 1) (hsphere : ∀ x : F', ‖x‖ = 1 → ‖σ x‖ = 1)
    (hrad : ∀ x : F', ‖x‖ = 1 → ∃ c : ℝ, 0 < c ∧ mfderiv 𝓘(ℝ, F') 𝓘(ℝ, F) σ x x = c • σ x) :
    IsJOrthogonallyAttached E φ (ι ∘ σ) := by
  -- Along the sphere, `d(ι ∘ σ)_x = dι_{σ x} ∘ dσ_x`.
  have key {x : F'} (hx : ‖x‖ = 1) (v : TangentSpace 𝓘(ℝ, F') x) :
      mfderiv 𝓘(ℝ, F') 𝓘(ℝ, E) (ι ∘ σ) x v =
        mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι (σ x) (mfderiv 𝓘(ℝ, F') 𝓘(ℝ, F) σ x v) := by
    -- `σ` is differentiable at `x`, since otherwise its differential would vanish there.
    have hσ : MDifferentiableAt 𝓘(ℝ, F') 𝓘(ℝ, F) σ x := by
      by_contra hσ
      obtain ⟨c, hc, hcx⟩ := hrad x hx
      rw [mfderiv_zero_of_not_mdifferentiableAt hσ] at hcx
      have h0 : c • σ x = 0 := hcx.symm
      simp only [smul_eq_zero, hc.ne', false_or] at h0
      simpa [h0] using hsphere x hx
    exact mfderiv_comp_apply x (h.mdifferentiableAt (hsphere x hx)) hσ v
  refine ⟨fun x hx ↦ h.pos (σ x) (hball x hx), fun x hx ↦ h.eq_zero (σ x) (hsphere x hx),
    fun x hx ↦ ?_, fun x hx v ↦ ?_⟩
  · obtain ⟨c, hc, hcx⟩ := hrad x hx
    have t : mvfderiv 𝓘(ℝ, E) φ (ι (σ x))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι (σ x) (mfderiv 𝓘(ℝ, F') 𝓘(ℝ, F) σ x x)) < 0 := by
      -- `hcx` gives `c • σ x` with the scalar action of `F`, not of the tangent space.
      have e : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι (σ x) (c • σ x : F) =
          c • mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι (σ x) (σ x) :=
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ι (σ x)).map_smul c (σ x)
      rw [hcx, e, map_smul, smul_eq_mul]
      exact mul_neg_of_pos_of_neg hc (h.mvfderiv_mfderiv_self_neg (σ x) (hsphere x hx))
    exact key hx x ▸ t
  · exact key hx v ▸ h.mvfderiv_I_smul_mfderiv (σ x) (hsphere x hx) _

/-- **Reparametrizing the disc by an isometry.** A disc attached J-orthogonally stays so after
precomposition with a linear isometry. -/
theorem comp_linearIsometry (h : IsJOrthogonallyAttached E φ ι) {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] (e : F' →ₗᵢ[ℝ] F) :
    IsJOrthogonallyAttached E φ (ι ∘ e) :=
  h.comp_of_mfderiv_apply_self_eq_smul (fun x hx ↦ by simpa using hx)
    (fun x hx ↦ by simpa using hx) fun x _ ↦
      ⟨1, one_pos, by
        rw [← e.coe_toContinuousLinearMap, ContinuousLinearMap.mfderiv_eq]
        -- The left side lives in the tangent space `TangentSpace 𝓘(ℝ, F) (e x)`, which is `F`.
        exact (one_smul ℝ _).symm⟩

/-- **Local agreement near the sphere.** If `θ` agrees with `ψ` near each point of the boundary
sphere and is positive on the open disc, then a disc attached J-orthogonally to `{ψ ≤ 0}` is
attached J-orthogonally to `{θ ≤ 0}`. -/
theorem congr_of_eventuallyEq {ψ θ : M → ℝ} (h : IsJOrthogonallyAttached E ψ ι)
    (hθ : ∀ x : F, ‖x‖ = 1 → θ =ᶠ[𝓝 (ι x)] ψ) (hpos : ∀ x : F, ‖x‖ < 1 → 0 < θ (ι x)) :
    IsJOrthogonallyAttached E θ ι :=
  ⟨hpos, fun x hx ↦ (hθ x hx).eq_of_nhds.trans (h.eq_zero x hx),
    fun x hx ↦ ((hθ x hx).mvfderiv_eq (I := 𝓘(ℝ, E))) ▸ h.mvfderiv_mfderiv_self_neg x hx,
    fun x hx v ↦ ((hθ x hx).mvfderiv_eq (I := 𝓘(ℝ, E))) ▸ h.mvfderiv_I_smul_mfderiv x hx v⟩

/-- **Carrying an attachment through a chart.** Let `Φ` be a partial diffeomorphism from a
complex manifold `N` modelled on `E'` to `M`, defined on the disc `ι '' closedBall 0 1`, whose
differential commutes with multiplication by `i` along the boundary sphere. If the disc `ι` is
attached J-orthogonally to `{ψ ≤ 0}` in `N`, then `Φ ∘ ι` is attached J-orthogonally to
`{ψ ∘ Φ.symm ≤ 0}` in `M`. -/
theorem map_partialDiffeomorph {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {N : Type*} [TopologicalSpace N] [ChartedSpace E' N] {ψ : N → ℝ} {ι : F → N}
    (h : IsJOrthogonallyAttached E' ψ ι) {n : WithTop ℕ∞} (hn : n ≠ 0)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E') 𝓘(ℝ, E) N M n) (hsrc : ι '' closedBall 0 1 ⊆ Φ.source)
    (hI : ∀ x : F, ‖x‖ = 1 → ∀ w : E', mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) Φ (ι x) (Complex.I • w) =
      Complex.I • (show E from mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) Φ (ι x) w)) :
    IsJOrthogonallyAttached E (ψ ∘ Φ.symm) (Φ ∘ ι) := by
  have hmem {x : F} (hx : ‖x‖ ≤ 1) : ι x ∈ Φ.source :=
    hsrc ⟨x, by simpa using hx, rfl⟩
  have hval {x : F} (hx : ‖x‖ ≤ 1) : (ψ ∘ Φ.symm) ((Φ ∘ ι) x) = ψ (ι x) :=
    congrArg ψ (Φ.left_inv (hmem hx))
  -- Along the sphere, `d(ψ ∘ Φ.symm)` at `Φ (ι x)` undoes `dΦ`, and `d(Φ ∘ ι) = dΦ ∘ dι`.
  have hψ {x : F} (hx : ‖x‖ = 1) (w : TangentSpace 𝓘(ℝ, E') (ι x)) :
      mvfderiv 𝓘(ℝ, E) (ψ ∘ Φ.symm) (Φ (ι x)) (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) Φ (ι x) w) =
        mvfderiv 𝓘(ℝ, E') ψ (ι x) w := by
    rw [mvfderiv_comp_apply_of_eq _ (h.mdifferentiableAt_apply hx)
      (Φ.symm.mdifferentiableAt hn (Φ.map_source (hmem hx.le))) (Φ.left_inv (hmem hx.le))]
    exact congrArg _ (Φ.mfderiv_symm_apply_mfderiv_apply hn (hmem hx.le) w)
  have hι {x : F} (hx : ‖x‖ = 1) (v : F) :
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (Φ ∘ ι) x v =
        mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) Φ (ι x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E') ι x v) :=
    mfderiv_comp_apply x (Φ.mdifferentiableAt hn (hmem hx.le)) (h.mdifferentiableAt hx) v
  refine ⟨fun x hx ↦ hval hx.le ▸ h.pos x hx, fun x hx ↦ hval hx.le ▸ h.eq_zero x hx,
    fun x hx ↦ ?_, fun x hx v ↦ ?_⟩
  · rw [hι hx, Function.comp_apply, hψ hx]
    exact h.mvfderiv_mfderiv_self_neg x hx
  · rw [hι hx, Function.comp_apply]
    refine (congrArg _ (hI x hx _)).symm.trans ?_
    exact (hψ hx _).trans (h.mvfderiv_I_smul_mfderiv x hx v)

end IsJOrthogonallyAttached

end SymplecticGeometry

end
