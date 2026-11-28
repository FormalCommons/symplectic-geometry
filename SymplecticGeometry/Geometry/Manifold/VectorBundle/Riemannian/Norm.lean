/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.ContMDiff.Sqrt
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Smoothness of the norm of a section of a Riemannian bundle

For a `C^n` Riemannian metric on a vector bundle `E`, Mathlib's `ContMDiffWithinAt.inner_bundle`
says that the inner product of two `C^n` maps into the total space over a common base map is
`C^n`. This file deduces that the norm `‖v m‖` of such a map is `C^n` where `v` does not vanish
(`ContMDiffWithinAt.norm_bundle` and its variants), as the square root of `⟪v m, v m⟫`.
Dividing such a map by its norm, where it does not vanish, gives a `C^n` map
(`ContMDiffWithinAt.inv_norm_smul_bundle` and its variants), by Tau Ceti's
`ContMDiffWithinAt.smul_totalSpace`.

For a `C^n` section `t` of such a bundle, the points where `t` does not vanish form an open set
`Bundle.nonzeroOpens ht`, and `y ↦ log ‖t y‖²` is a `C^n` function on it, `Bundle.logNormSq ht`,
since the square norm is `C^n` (Tau Ceti's `TauCeti.contMDiff_norm_sq_bundle`).
-/

public section

open Bundle
open scoped Manifold ContDiff

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContMDiffRiemannianBundle IB n F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {v : ∀ x, E (b x)} {s : Set M} {x : M}

/-- The norm of a map into a Riemannian bundle that is `C^n` within a set at a point where it does
not vanish is `C^n` within that set there. -/
theorem ContMDiffWithinAt.norm_bundle
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hx : v x ≠ 0) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ ‖v m‖) s x :=
  ((hv.inner_bundle hv).sqrt (inner_self_ne_zero.2 hx)).congr
    (fun _ _ ↦ norm_eq_sqrt_real_inner _) (norm_eq_sqrt_real_inner _)

/-- The norm of a map into a Riemannian bundle that is `C^n` at a point where it does not vanish
is `C^n` there. -/
theorem ContMDiffAt.norm_bundle
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x)
    (hx : v x ≠ 0) :
    ContMDiffAt IM 𝓘(ℝ) n (fun m ↦ ‖v m‖) x :=
  ContMDiffWithinAt.norm_bundle hv hx

/-- The norm of a map into a Riemannian bundle that is `C^n` on a set where it does not vanish is
`C^n` there. -/
theorem ContMDiffOn.norm_bundle
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s)
    (hs : ∀ x ∈ s, v x ≠ 0) :
    ContMDiffOn IM 𝓘(ℝ) n (fun m ↦ ‖v m‖) s :=
  fun x hx ↦ (hv x hx).norm_bundle (hs x hx)

/-- The norm of a nowhere-vanishing `C^n` map into a Riemannian bundle is `C^n`. -/
theorem ContMDiff.norm_bundle
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)))
    (h : ∀ x, v x ≠ 0) :
    ContMDiff IM 𝓘(ℝ) n (fun m ↦ ‖v m‖) :=
  fun x ↦ (hv x).norm_bundle (h x)

/-- Dividing a map into a Riemannian bundle that is `C^n` within a set at a point where it does
not vanish by its norm gives a map that is `C^n` within that set there. -/
theorem ContMDiffWithinAt.inv_norm_smul_bundle
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hx : v x ≠ 0) :
    ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n
      (fun m ↦ ((‖v m‖⁻¹ • v m : E (b m)) : TotalSpace F E)) s x :=
  ((hv.norm_bundle hx).inv₀ (norm_ne_zero_iff.2 hx)).smul_totalSpace hv

/-- Dividing a map into a Riemannian bundle that is `C^n` at a point where it does not vanish by
its norm gives a map that is `C^n` there. -/
theorem ContMDiffAt.inv_norm_smul_bundle
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x)
    (hx : v x ≠ 0) :
    ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ ((‖v m‖⁻¹ • v m : E (b m)) : TotalSpace F E)) x :=
  ContMDiffWithinAt.inv_norm_smul_bundle hv hx

/-- Dividing a map into a Riemannian bundle that is `C^n` on a set where it does not vanish by
its norm gives a map that is `C^n` there. -/
theorem ContMDiffOn.inv_norm_smul_bundle
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s)
    (hs : ∀ x ∈ s, v x ≠ 0) :
    ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ ((‖v m‖⁻¹ • v m : E (b m)) : TotalSpace F E)) s :=
  fun x hx ↦ (hv x hx).inv_norm_smul_bundle (hs x hx)

/-- Dividing a nowhere-vanishing `C^n` map into a Riemannian bundle by its norm gives a `C^n`
map. -/
theorem ContMDiff.inv_norm_smul_bundle
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)))
    (h : ∀ x, v x ≠ 0) :
    ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ ((‖v m‖⁻¹ • v m : E (b m)) : TotalSpace F E)) :=
  fun x ↦ (hv x).inv_norm_smul_bundle (h x)

namespace Bundle

variable {t : Π y, E y}

/-- The open set of the points where a `C^n` section `t` of a Riemannian bundle does not
vanish. -/
def nonzeroOpens (ht : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n fun y ↦ TotalSpace.mk' F y (t y)) :
    TopologicalSpace.Opens B :=
  ⟨{y | t y ≠ 0}, by
    have h : Continuous fun y ↦ ‖t y‖ ^ 2 :=
      ((TauCeti.contMDiff_norm_sq_bundle IB n F E).comp ht).continuous
    simpa only [ne_eq, pow_eq_zero_iff two_ne_zero, norm_eq_zero] using
      isOpen_ne_fun h (continuous_const (y := (0 : ℝ)))⟩

@[simp]
theorem mem_nonzeroOpens
    {ht : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n fun y ↦ TotalSpace.mk' F y (t y)} {y : B} :
    y ∈ nonzeroOpens ht ↔ t y ≠ 0 :=
  Iff.rfl

/-- For a `C^n` section `t` of a Riemannian bundle, the function `y ↦ log ‖t y‖²` as a `C^n`
function on the open set `nonzeroOpens ht` where `t` does not vanish. -/
noncomputable def logNormSq
    (ht : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n fun y ↦ TotalSpace.mk' F y (t y)) :
    C^n⟮IB, nonzeroOpens ht; 𝓘(ℝ), ℝ⟯ :=
  ⟨fun y ↦ Real.log (‖t y‖ ^ 2),
    (((TauCeti.contMDiff_norm_sq_bundle IB n F E).comp ht).comp contMDiff_subtypeVal).log
      fun y ↦ pow_ne_zero 2 (norm_ne_zero_iff.2 y.property)⟩

@[simp]
theorem logNormSq_apply
    (ht : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n fun y ↦ TotalSpace.mk' F y (t y))
    (y : nonzeroOpens ht) :
    logNormSq ht y = Real.log (‖t y‖ ^ 2) :=
  (rfl)

/-- `logNormSq ht` is the restriction of `y ↦ log ‖t y‖²` to `nonzeroOpens ht`. -/
theorem coe_logNormSq
    (ht : ContMDiff IB (IB.prod 𝓘(ℝ, F)) n fun y ↦ TotalSpace.mk' F y (t y)) :
    ⇑(logNormSq ht) = (fun y ↦ Real.log (‖t y‖ ^ 2)) ∘ Subtype.val :=
  funext fun y ↦ logNormSq_apply ht y

end Bundle
