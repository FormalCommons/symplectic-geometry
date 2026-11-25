/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Analysis.Complex.Euclidean.Space
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Localization.WeightOneForm
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.PartialDiffeomorph
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.GroupAction.InvariantCutoff
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Invariant cut-offs and cut-off model one-forms at a fixed point, in the weight chart

The localizing one-form of the Duistermaat–Heckman formula is glued from model forms near the
fixed points and an averaged form elsewhere. This file gives the cut-offs of that gluing.

* `SymplecticGeometry.exists_smul_invariant_cutoff_weightChart`: let `Φ` be a smooth partial
  diffeomorphism from `StdSpace (Fin n)` to a Hausdorff manifold `M` with a `G`-action, equivariant
  in the form that `SymplecticGeometry.exists_weightChart` gives, where `g` multiplies each
  complex coordinate by a unit complex number. Then for `0 ≤ a < b` with `closedBall 0 b` in the
  source, some smooth `ρ : M → [0, 1]`, invariant under `G`, equals `1` on `Φ '' closedBall 0 a`
  and has its support in `Φ '' closedBall 0 b`. Since the action preserves the norm in the chart,
  this is a case of `PartialDiffeomorph.exists_smul_invariant_cutoff`.

A form on the chart, pulled back to `M` and multiplied by such a cut-off, is a smooth form on `M`
(`TauCeti.IsSmoothForm.fun_smul_mpullback`), and it is invariant when the form is invariant on
the support of the cut-off (`TauCeti.mpullback_fun_smul_eq_self`). For the model one-form
`θₖ = SymplecticGeometry.weightOneForm k`, this gives the pieces of the localizing one-form at
the fixed points:

* `SymplecticGeometry.cutoffWeightOneForm Φ hρ hs k`: the smooth one-form
  `x ↦ ρ x • ((Φ⁻¹)^* θₖ) x` on `M`, for a smooth `ρ` with `tsupport ρ ⊆ Φ.target`;
* `SymplecticGeometry.mpullback_smul_cutoffWeightOneForm`: it is invariant under each `g` that
  acts in the chart by `uⱼ ↦ χⱼ(g) uⱼ` and preserves `ρ`, since `θₖ` is invariant under the
  rotations `TauCeti.weightRotation` (`SymplecticGeometry.mpullback_weightRotation_weightOneForm`);
* `SymplecticGeometry.cutoffWeightOneForm_apply_weightChart`: on a vector field `X` that `dΦ`
  relates to the generator of the rotations by the angles `2π kⱼ`, its value at `Φ z` is
  `ρ (Φ z) * (2π ∑ⱼ kⱼ² (xⱼ² + yⱼ²))`; it vanishes where `ρ` does
  (`SymplecticGeometry.cutoffWeightOneForm_apply_of_eq_zero`), so it is nonnegative on `X` when
  `ρ` is (`SymplecticGeometry.cutoffWeightOneForm_apply_nonneg`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.6
-/

public section

noncomputable section

open Set Metric Real
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section InvariantCutoff

variable [T2Space M] {G : Type*} [Group G] [MulAction G M]

/-- **An invariant cut-off in the weight chart.** Let `Φ` be a smooth partial diffeomorphism from
`StdSpace (Fin n)` to a Hausdorff manifold `M` with a `G`-action, equivariant as the weight chart
of `SymplecticGeometry.exists_weightChart` is: in the complex coordinates
`z = complexToRealEuclidean (Fin n) u`, `g` sends `Φ z` to `Φ` of `uₖ ↦ χₖ(g) uₖ`, for
maps `χₖ : G → S¹`. For `0 ≤ a < b` with `closedBall 0 b` in the source of `Φ`, there is a
smooth function `ρ : M → ℝ` with values in `[0, 1]`, invariant under `G`, equal to `1` on
`Φ '' closedBall 0 a`, and whose support lies in `Φ '' closedBall 0 b`. -/
theorem exists_smul_invariant_cutoff_weightChart {n : ℕ} (χ : Fin n → G → Circle)
    (Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I (StdSpace (Fin n)) M ∞)
    (hequiv : ∀ g : G, ∀ u : Fin n → ℂ, TauCeti.complexToRealEuclidean (Fin n) u ∈ Φ.source →
      TauCeti.complexToRealEuclidean (Fin n) (fun k ↦ (χ k g : ℂ) * u k) ∈ Φ.source ∧
        Φ (TauCeti.complexToRealEuclidean (Fin n) fun k ↦ (χ k g : ℂ) * u k) =
          g • Φ (TauCeti.complexToRealEuclidean (Fin n) u))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : closedBall (0 : StdSpace (Fin n)) b ⊆ Φ.source) :
    ∃ ρ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ ρ ∧ (∀ x, ρ x ∈ Icc 0 1) ∧
      (∀ (g : G) x, ρ (g • x) = ρ x) ∧ EqOn ρ 1 (Φ '' closedBall 0 a) ∧
      tsupport ρ ⊆ Φ '' closedBall 0 b := by
  refine Φ.exists_smul_invariant_cutoff (fun g z hz ↦ ?_) ha hab hb
  set e := TauCeti.complexToRealEuclidean (Fin n)
  obtain ⟨u, rfl⟩ : ∃ u, e u = z := ⟨e.symm z, e.apply_symm_apply z⟩
  obtain ⟨hs, hΦ⟩ := hequiv g u hz
  refine ⟨_, hs, ?_, hΦ⟩
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_complexToRealEuclidean,
    norm_sq_complexToRealEuclidean]
  simp

end InvariantCutoff

/-! ### The cut-off model one-form -/

section CutoffWeightOneForm

open TauCeti

variable [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
  (Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace ι) I (StdSpace ι) M ∞) {ρ : M → ℝ}
  (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hs : tsupport ρ ⊆ Φ.target) (k : ι → ℝ)

/-- The model one-form `θₖ = ∑ⱼ kⱼ (xⱼ dyⱼ - yⱼ dxⱼ)` (`SymplecticGeometry.weightOneForm k`) read
on `M` through a smooth partial diffeomorphism `Φ` from `StdSpace ι` to `M`, and cut off by a
smooth function `ρ` whose support lies in the image of `Φ`: the smooth one-form
`x ↦ ρ x • ((Φ⁻¹)^* θₖ) x`, which is zero where `ρ` is. -/
def cutoffWeightOneForm : SmoothForm I M ℝ 1 :=
  ⟨fun x ↦ ρ x • TauCeti.mpullback I 𝓘(ℝ, StdSpace ι) Φ.symm (weightOneForm k).val x,
    (TauCeti.IsSmoothForm.fun_smul_mpullback Φ.symm
      (isSmoothForm_modelSpace_iff.1 (weightOneForm k).isSmoothForm) hρ
      (by simpa using hs)).mem_smoothBundleForms⟩

theorem cutoffWeightOneForm_val :
    (cutoffWeightOneForm Φ hρ hs k).val =
      fun x ↦ ρ x • TauCeti.mpullback I 𝓘(ℝ, StdSpace ι) Φ.symm (weightOneForm k).val x :=
  (rfl)

/-- Where the cut-off `ρ` vanishes, so does the cut-off model one-form. -/
theorem cutoffWeightOneForm_apply_of_eq_zero {x : M} (hx : ρ x = 0)
    (v : Fin 1 → TangentSpace I x) : (cutoffWeightOneForm Φ hρ hs k).val x v = 0 := by
  simp [cutoffWeightOneForm_val, hx]

variable {Φ} in
/-- On a vector field `X` that the differential of `Φ` relates, at `z`, to the generator
`weightGenerator ((2π) • k)` of the rotations by the angles `2π kⱼ`, the cut-off model one-form
takes at `Φ z` the value `ρ (Φ z) * (2π ∑ⱼ kⱼ² (xⱼ(z)² + yⱼ(z)²))`. -/
theorem cutoffWeightOneForm_apply_weightChart {X : (x : M) → TangentSpace I x} {z : StdSpace ι}
    (hz : z ∈ Φ.source)
    (hX : mfderiv 𝓘(ℝ, StdSpace ι) I Φ z
      (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))) = X (Φ z)) :
    (cutoffWeightOneForm Φ hρ hs k).val (Φ z) ![X (Φ z)] =
      ρ (Φ z) * (2 * π * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2)) := by
  rw [cutoffWeightOneForm_val, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    TauCeti.mpullback_apply]
  congr 1
  have hv : (fun i ↦ mfderiv I 𝓘(ℝ, StdSpace ι) Φ.symm (Φ z) (![X (Φ z)] i)) =
      ![EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))] := by
    funext i
    rw [Fin.fin_one_eq_zero i, Matrix.cons_val_zero, Matrix.cons_val_zero, ← hX]
    exact Φ.mfderiv_symm_apply_mfderiv_apply (by simp) hz _
  rw [hv, Φ.symm_toPartialEquiv, Φ.left_inv hz]
  -- `hv` lists the vectors as points of `StdSpace ι`, the lemma as tangent vectors at `z`.
  exact weightOneForm_apply_weightGenerator_two_pi_mul k z

/-- The cut-off model one-form is nonnegative on a vector field `X` that the differential of `Φ`
relates, at each point of the source, to the generator `weightGenerator ((2π) • k)`, when the
cut-off `ρ` is nonnegative. -/
theorem cutoffWeightOneForm_apply_nonneg {X : (x : M) → TangentSpace I x}
    (hX : ∀ z ∈ Φ.source, mfderiv 𝓘(ℝ, StdSpace ι) I Φ z
      (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))) = X (Φ z))
    (hρ₀ : ∀ x, 0 ≤ ρ x) (x : M) : 0 ≤ (cutoffWeightOneForm Φ hρ hs k).val x ![X x] := by
  by_cases hx : ρ x = 0
  · rw [cutoffWeightOneForm_apply_of_eq_zero Φ hρ hs k hx]
  obtain ⟨z, hz, rfl⟩ : x ∈ Φ '' Φ.source := by
    rw [Φ.toPartialEquiv.image_source_eq_target]
    exact hs (subset_tsupport ρ hx)
  rw [cutoffWeightOneForm_apply_weightChart hρ hs k hz (hX z hz)]
  exact mul_nonneg (hρ₀ _) (by positivity)

variable {Φ} in
/-- **The cut-off model one-form is invariant.** Let `g` act on `M` smoothly, preserving `ρ`,
and in the chart, in the complex coordinates `z = complexToRealEuclidean ι u`, by
`uⱼ ↦ χⱼ(g) uⱼ`, for maps `χⱼ : G → S¹`, as on the weight chart of
`SymplecticGeometry.exists_weightChart`. Then `g` preserves the cut-off model one-form. -/
theorem mpullback_smul_cutoffWeightOneForm {G : Type*} [SMul G M] (χ : ι → G → Circle) (g : G)
    (hequiv : ∀ u : ι → ℂ, TauCeti.complexToRealEuclidean ι u ∈ Φ.source →
      TauCeti.complexToRealEuclidean ι (fun j ↦ (χ j g : ℂ) * u j) ∈ Φ.source ∧
        Φ (TauCeti.complexToRealEuclidean ι fun j ↦ (χ j g : ℂ) * u j) =
          g • Φ (TauCeti.complexToRealEuclidean ι u))
    (hg : ContMDiff I I ∞ fun x : M ↦ g • x) (hρg : ∀ x, ρ (g • x) = ρ x) :
    SmoothForm.mpullback (fun x : M ↦ g • x) hg (cutoffWeightOneForm Φ hρ hs k) =
      cutoffWeightOneForm Φ hρ hs k := by
  -- In the chart, `g` is the rotation `R` by the angles `arg (χⱼ g)`.
  set R : StdSpace ι → StdSpace ι := fun z ↦
    EuclideanSpace.sumEquivProd.symm
      (TauCeti.weightRotation (fun j ↦ Complex.arg (χ j g)) (EuclideanSpace.sumEquivProd z))
  have hRsmooth : ContMDiff 𝓘(ℝ, StdSpace ι) 𝓘(ℝ, StdSpace ι) ∞ R :=
    contMDiff_iff_contDiff.2 (by fun_prop)
  have hR {w : StdSpace ι} (hw : w ∈ Φ.source) : R w ∈ Φ.source ∧ Φ (R w) = g • Φ w := by
    set e := TauCeti.complexToRealEuclidean ι
    obtain ⟨u, rfl⟩ : ∃ u, e u = w := ⟨e.symm w, e.apply_symm_apply w⟩
    have hRe : R (e u) = e fun j ↦ (χ j g : ℂ) * u j := by
      simp only [R, e, TauCeti.weightRotation_sumEquivProd_complexToRealEuclidean,
        ContinuousLinearEquiv.symm_apply_apply, ← Circle.coe_exp, Circle.exp_arg]
    rw [hRe]
    exact hequiv u hw
  -- Near a point of the target, `Φ⁻¹ ∘ (g • ·)` is `R ∘ Φ⁻¹`.
  have hcomm {x : M} (hx : x ∈ Φ.target) : (Φ.symm ∘ fun x ↦ g • x) =ᶠ[𝓝 x] R ∘ Φ.symm := by
    filter_upwards [Φ.open_target.mem_nhds hx] with y hy
    obtain ⟨h₁, h₂⟩ := hR (Φ.map_target hy)
    rw [Φ.right_inv hy] at h₂
    rw [Function.comp_apply, Function.comp_apply, ← h₂, Φ.symm_toPartialEquiv, Φ.left_inv h₁]
  have hφ (x : M) (hx : ρ x ≠ 0) :
      TauCeti.mpullback I I (fun x ↦ g • x)
          (TauCeti.mpullback I 𝓘(ℝ, StdSpace ι) Φ.symm (weightOneForm k).val) x =
        TauCeti.mpullback I 𝓘(ℝ, StdSpace ι) Φ.symm (weightOneForm k).val x := by
    have hxt : x ∈ Φ.target := hs (subset_tsupport ρ hx)
    have hgx : g • x ∈ Φ.target := by
      obtain ⟨h₁, h₂⟩ := hR (Φ.map_target hxt)
      rw [Φ.right_inv hxt] at h₂
      exact h₂ ▸ Φ.map_source h₁
    have hθ := congrArg Subtype.val
      (mpullback_weightRotation_weightOneForm k fun j ↦ Complex.arg (χ j g))
    rw [SmoothForm.coe_mpullback] at hθ
    rw [← TauCeti.mpullback_comp_at (hg.mdifferentiableAt (by simp))
        (Φ.symm.mdifferentiableAt (by simp) (by simpa using hgx)),
      (hcomm hxt).mpullback_eq,
      TauCeti.mpullback_comp_at (Φ.symm.mdifferentiableAt (by simp) (by simpa using hxt))
        (hRsmooth.mdifferentiableAt (by simp)), hθ]
  refine Subtype.ext ?_
  rw [SmoothForm.coe_mpullback, cutoffWeightOneForm_val]
  exact TauCeti.mpullback_fun_smul_eq_self hρg hφ

end CutoffWeightOneForm

end SymplecticGeometry

end
