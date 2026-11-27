/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Normed.Operator.ComplexLinearPart
public import TauCeti.Analysis.Complex.Wirtinger.Basic

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.LinearCombination
import TauCeti.Analysis.Calculus.FDeriv.Comp

/-!
# Basic facts of Wirtinger calculus

Facts about the Wirtinger derivatives `∂` and `\bar∂` that Tau Ceti's
`TauCeti.Analysis.Complex.Wirtinger.Basic` does not state.

## Main results

* `TauCeti.wirtingerDeriv_of_notMem_tsupport`: `∂g` vanishes off the topological support of `g`.
  The proof is that of Tau Ceti's `TauCeti.conjWirtingerDeriv_of_notMem_tsupport`, for `∂` in
  place of `\bar∂`.
* `ContDiff.conjWirtingerDeriv_apply` and `ContDiff.wirtingerDeriv_apply`: the Wirtinger
  derivatives of a `C^(m+1)` map, evaluated on a fixed vector, are `C^m`; the global forms of
  Tau Ceti's `ContDiffAt.conjWirtingerDeriv_apply` and `ContDiffAt.wirtingerDeriv_apply`.
* `ContDiffAt.conjWirtingerDeriv`: for `g` of class `C^(m+1)` at `x`, the map `y ↦ \bar∂g(y)`
  into the complex-antilinear operators is `C^m` at `x`, not only its values on a fixed vector.
* `ContDiffAt.differentiableAt_conjWirtingerDeriv`,
  `ContDiffAt.fderiv_conjWirtingerDeriv_apply_apply`: for `g` real `C²` at `x`, the map
  `y ↦ \bar∂g(y)` is differentiable at `x`, with derivative
  `a ↦ (u ↦ (D²g(x)(a, u) + I • D²g(x)(a, I • u)) / 2)`.
* `ContDiffAt.norm_fderiv_fderiv_apply_add_apply_I_smul_le`: for such `g`, the vector
  `D²g(x)(v, v) + D²g(x)(I • v, I • v)` has norm at most `4 ‖D\bar∂g(x)‖ ‖v‖²`, since by the
  symmetry of `D²g` it is `2 D\bar∂g(x)(v)(v) - 2 I • D\bar∂g(x)(I • v)(v)`.
* `TauCeti.fderiv_complexAntilinearPartL_fderiv`,
  `TauCeti.norm_fderiv_complexAntilinearPartL_fderiv`: at every point, the derivative of
  `y ↦ complexAntilinearPartL (Dg(y))`, a map into the real-linear operators, is that of `\bar∂g`
  followed by the isometric inclusion of the complex-antilinear operators into the real-linear
  ones; so the two derivatives have the same norm.
-/

public section

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {g : V → W}

/-- The Wirtinger derivative vanishes off the topological support. -/
theorem wirtingerDeriv_of_notMem_tsupport {z : V} (hz : z ∉ tsupport g) :
    wirtingerDeriv g z = 0 := by
  ext b
  simp [wirtingerDeriv_apply, fderiv_of_notMem_tsupport ℝ hz]

section ContDiff

variable {m n : WithTop ℕ∞}

/-- The conjugate Wirtinger derivative of a `C^(m+1)` map, evaluated on a fixed vector, is
`C^m`. -/
theorem _root_.ContDiff.conjWirtingerDeriv_apply (hg : ContDiff ℝ n g) (hmn : m + 1 ≤ n)
    (v : V) : ContDiff ℝ m (fun z ↦ conjWirtingerDeriv g z v) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ hg.contDiffAt.conjWirtingerDeriv_apply hmn v

/-- The Wirtinger derivative of a `C^(m+1)` map, evaluated on a fixed vector, is `C^m`. -/
theorem _root_.ContDiff.wirtingerDeriv_apply (hg : ContDiff ℝ n g) (hmn : m + 1 ≤ n) (v : V) :
    ContDiff ℝ m (fun z ↦ wirtingerDeriv g z v) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ hg.contDiffAt.wirtingerDeriv_apply hmn v

end ContDiff

section DerivConj

open Complex

variable {x : V}

/-- The conjugate Wirtinger derivative of a map `C^(m+1)` at `x`, as a map into the
complex-antilinear operators, is `C^m` at `x`. -/
theorem _root_.ContDiffAt.conjWirtingerDeriv {m n : WithTop ℕ∞} (hg : ContDiffAt ℝ n g x)
    (hmn : m + 1 ≤ n) : ContDiffAt ℝ m (TauCeti.conjWirtingerDeriv g) x := by
  have h : TauCeti.conjWirtingerDeriv g =
      fun y ↦ ContinuousLinearMap.complexAntilinearPartCLM (fderiv ℝ g y) :=
    funext fun y ↦ by simp [conjWirtingerDeriv_eq_complexAntilinearPart]
  rw [h]
  exact ContinuousLinearMap.complexAntilinearPartCLM.contDiff.contDiffAt.comp x
    (hg.fderiv_right hmn)

/-- For `g` real `C²` at `x`, the conjugate Wirtinger derivative `y ↦ \bar∂g(y)` is
differentiable at `x`. -/
theorem _root_.ContDiffAt.differentiableAt_conjWirtingerDeriv (hg : ContDiffAt ℝ 2 g x) :
    DifferentiableAt ℝ (conjWirtingerDeriv g) x :=
  (hg.conjWirtingerDeriv (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-- For `g` real `C²` at `x`, the derivative of `y ↦ \bar∂g(y)` at `x` in the direction `a`,
applied to `u`, is `(D²g(x)(a, u) + I • D²g(x)(a, I • u)) / 2`. -/
theorem _root_.ContDiffAt.fderiv_conjWirtingerDeriv_apply_apply (hg : ContDiffAt ℝ 2 g x)
    (a u : V) :
    fderiv ℝ (conjWirtingerDeriv g) x a u =
      (2 : ℂ)⁻¹ • (fderiv ℝ (fderiv ℝ g) x a u + I • fderiv ℝ (fderiv ℝ g) x a (I • u)) := by
  let ev : (V →L⋆[ℂ] W) →L[ℝ] W :=
    (ContinuousLinearMap.apply' W (starRingEnd ℂ) u).restrictScalars ℝ
  have h₁ : HasFDerivAt (fun y ↦ conjWirtingerDeriv g y u)
      (ev.comp (fderiv ℝ (conjWirtingerDeriv g) x)) x :=
    ev.hasFDerivAt.comp x hg.differentiableAt_conjWirtingerDeriv.hasFDerivAt
  have h := DFunLike.congr_fun (h₁.unique (hg.hasFDerivAt_conjWirtingerDeriv_apply u)) a
  simpa [ev] using h

/-- For `g` real `C²` at `x`, the vector `D²g(x)(v, v) + D²g(x)(I • v, I • v)`, which vanishes
for complex `C²` maps, is bounded by the derivative of `\bar∂g` at `x`:
it is `2 D\bar∂g(x)(v)(v) - 2 I • D\bar∂g(x)(I • v)(v)`. -/
theorem _root_.ContDiffAt.norm_fderiv_fderiv_apply_add_apply_I_smul_le (hg : ContDiffAt ℝ 2 g x)
    (v : V) :
    ‖fderiv ℝ (fderiv ℝ g) x v v + fderiv ℝ (fderiv ℝ g) x (I • v) (I • v)‖ ≤
      4 * ‖fderiv ℝ (conjWirtingerDeriv g) x‖ * ‖v‖ ^ 2 := by
  set E₂ := fderiv ℝ (fderiv ℝ g) x
  set DB := fderiv ℝ (conjWirtingerDeriv g) x
  have hDB (a b : V) : DB a b = (2 : ℂ)⁻¹ • (E₂ a b + I • E₂ a (I • b)) :=
    hg.fderiv_conjWirtingerDeriv_apply_apply a b
  have hsym : E₂ v (I • v) = E₂ (I • v) v := hg.isSymmSndFDerivAt (by simp) v (I • v)
  have hX : E₂ v v + E₂ (I • v) (I • v) = (2 : ℂ) • DB v v - (2 : ℂ) • I • DB (I • v) v := by
    rw [hDB, hDB, hsym]
    simp only [smul_add, smul_smul]
    match_scalars
    · ring
    · linear_combination I_mul_I
    · ring
  have hle (a : V) : ‖DB a v‖ ≤ ‖DB‖ * ‖a‖ * ‖v‖ := (DB a).le_of_opNorm_le (DB.le_opNorm a) v
  have h₃ := hle v
  have h₄ := hle (I • v)
  rw [norm_smul, norm_I, one_mul] at h₄
  rw [hX]
  calc ‖(2 : ℂ) • DB v v - (2 : ℂ) • I • DB (I • v) v‖
      ≤ 2 * ‖DB v v‖ + 2 * ‖DB (I • v) v‖ := by
        refine (norm_sub_le _ _).trans_eq ?_
        simp [norm_smul]
    _ ≤ 4 * ‖DB‖ * ‖v‖ ^ 2 := by linarith

end DerivConj

section DerivAntilinearPart

open ContinuousLinearMap

/-- The derivative of `y ↦ complexAntilinearPartL (Dg(y))`, a map into the real-linear
operators, is the derivative of `\bar∂g`, a map into the complex-antilinear operators, followed
by the inclusion `ContinuousLinearMap.restrictScalarsₛₗLI` of these into the real-linear
operators. This holds at every point: both sides vanish where `\bar∂g` is not differentiable. -/
theorem fderiv_complexAntilinearPartL_fderiv (g : V → W) (x : V) :
    fderiv ℝ (fun y ↦ complexAntilinearPartL (fderiv ℝ g y)) x =
      restrictScalarsₛₗLI.toContinuousLinearMap ∘L fderiv ℝ (conjWirtingerDeriv g) x := by
  set ι : (V →L⋆[ℂ] W) →L[ℝ] V →L[ℝ] W := restrictScalarsₛₗLI.toContinuousLinearMap
  have h : (fun y ↦ complexAntilinearPartL (fderiv ℝ g y)) = ι ∘ conjWirtingerDeriv g := by
    funext y
    rw [← restrictScalarsₛₗLI_comp_complexAntilinearPartCLM]
    simp [ι, conjWirtingerDeriv_eq_complexAntilinearPart]
  rw [h]
  exact ι.fderiv_comp_left_of_leftInverse complexAntilinearPartCLM (fun f ↦ by simp [ι]) _ x

/-- The derivatives of `y ↦ complexAntilinearPartL (Dg(y))` and of `\bar∂g` have the same
operator norm. -/
theorem norm_fderiv_complexAntilinearPartL_fderiv (g : V → W) (x : V) :
    ‖fderiv ℝ (fun y ↦ complexAntilinearPartL (fderiv ℝ g y)) x‖ =
      ‖fderiv ℝ (conjWirtingerDeriv g) x‖ := by
  rw [fderiv_complexAntilinearPartL_fderiv, LinearIsometry.norm_toContinuousLinearMap_comp]

end DerivAntilinearPart

end TauCeti

end
