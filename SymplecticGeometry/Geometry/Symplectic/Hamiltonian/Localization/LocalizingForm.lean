/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Analysis.Complex.Euclidean.Space
public import SymplecticGeometry.Geometry.Manifold.GroupAction.Circle
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Localization.WeightOneForm
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.WeightModel.NormalForm
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.PartitionOfUnity
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.GroupAction.InvariantCutoff
import SymplecticGeometry.Geometry.Manifold.GroupAction.InvariantOneForm
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Localization.Weights
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
import SymplecticGeometry.Topology.Algebra.ConstMulAction
import SymplecticGeometry.Topology.OpenPartialHomeomorph.Separation
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Symplectic.Manifold.NeighborhoodGerm
import SymplecticGeometry.Analysis.Complex.Euclidean.Space

/-!
# The localizing one-form of a circle action

The localizing one-form of the Duistermaat–Heckman formula is glued from model forms near the
fixed points and an averaged form elsewhere. This file gives the cut-offs of that gluing, the
cut-off model forms, and the glued form.

* `SymplecticGeometry.exists_smul_invariant_cutoff_weightChart`: let `Φ` be a smooth partial
  diffeomorphism from `StdSpace (Fin n)` to a Hausdorff manifold `M` with a `G`-action, equivariant
  in the form that `SymplecticGeometry.exists_weightChart` gives, where `g` multiplies each
  complex coordinate by a unit complex number. Then for `0 ≤ a < b` with `closedBall 0 b` in the
  source, some smooth `ρ : M → [0, 1]`, invariant under `G`, equals `1` on `Φ '' closedBall 0 a`
  and has its support in `Φ '' closedBall 0 b`. Since the action preserves the norm in the chart,
  this is a case of `PartialDiffeomorph.exists_smul_invariant_cutoff`.

A form on the chart, pulled back to `M` and multiplied by such a cut-off, is a smooth form on `M`
(`TauCeti.isSmoothForm_fun_smul_mpullback`), and it is invariant when the form is invariant on
the support of the cut-off (`TauCeti.mpullback_fun_smul_eq_self`). For the model one-form
`θₖ = SymplecticGeometry.weightOneForm k`, this gives the pieces of the localizing one-form at
the fixed points:

* `SymplecticGeometry.cutoffWeightOneForm Φ hρ hs k`: the smooth one-form
  `x ↦ ρ x • ((Φ⁻¹)^* θₖ) x` on `M`, for a smooth `ρ` with `tsupport ρ ⊆ Φ.target`;
* `SymplecticGeometry.mpullback_smul_cutoffWeightOneForm`: it is invariant under each `g` that
  acts in the chart by `uⱼ ↦ χⱼ(g) uⱼ` and preserves `ρ`, since `θₖ` is invariant under the
  rotations `TauCeti.weightRotation` (`SymplecticGeometry.mpullback_weightRotation_weightOneForm`);
* `SymplecticGeometry.mpullback_symm_weightOneForm_apply_weightChart`: before the cut-off, on a
  vector field `X` that `dΦ` relates to the generator of the rotations by the angles `2π k'ⱼ`,
  the value of `(Φ⁻¹)^* θₖ` at `Φ z` is `2π ∑ⱼ kⱼ k'ⱼ (xⱼ² + yⱼ²)`;
* `SymplecticGeometry.cutoffWeightOneForm_apply_weightChart`: on a vector field `X` that `dΦ`
  relates to the generator of the rotations by the angles `2π k'ⱼ`, its value at `Φ z` is
  `ρ (Φ z) * (2π ∑ⱼ kⱼ k'ⱼ (xⱼ² + yⱼ²))`, and `ρ (Φ z) * (2π ∑ⱼ kⱼ² (xⱼ² + yⱼ²))` for `k' = k`
  (`SymplecticGeometry.cutoffWeightOneForm_apply_weightChart_self`); it vanishes where `ρ` does
  (`SymplecticGeometry.cutoffWeightOneForm_apply_of_eq_zero`), so it is nonnegative on `X` where
  `ρ` is (`SymplecticGeometry.cutoffWeightOneForm_apply_nonneg`); where `ρ` is nonzero and no
  `kⱼ` is zero, it vanishes on `X` only at `z = 0`
  (`SymplecticGeometry.cutoffWeightOneForm_apply_weightChart_eq_zero_iff`);
* `SymplecticGeometry.mextDerivₗ_cutoffWeightOneForm_apply_of_eventuallyEq_one`: near a point
  where `ρ = 1`, the form is `(Φ⁻¹)^* θₖ`, so its exterior derivative there is `(Φ⁻¹)^* dθₖ`, by
  naturality of `d` (`TauCeti.mextDerivₗ_apply_eq_of_eventuallyEq_mpullback`);
* `SymplecticGeometry.mextDerivₗ_cutoffWeightOneForm_half_apply_of_eventuallyEq_one`: if `Φ`
  pulls a two-form `σ` back to the standard form `ω₀`, then for `kⱼ = 1/2`, where `dθₖ = ω₀`,
  the exterior derivative is `σ` at such a point.

The localizing one-form is `θ = ∑ᵢ ρᵢ (Φᵢ⁻¹)^* θ_{kᵢ} + (1 - ∑ᵢ ρᵢ) β`, for weight charts `Φᵢ`
at the fixed points, invariant cut-offs `ρᵢ` with pairwise disjoint supports, and an invariant
one-form `β` with `β(X) > 0` off the fixed points
(`SymplecticGeometry.exists_invariant_smoothForm_apply_circle_nonneg`):

* `SymplecticGeometry.exists_localizingForm_of_weightCharts`: for finitely many weight charts
  with distinct centres and nonzero weights, on a σ-compact Hausdorff manifold with a smooth
  circle action, such a `θ` is invariant, `θ(X) ≥ 0` with equality exactly at the fixed points,
  and `θ` is the pulled-back model form near the centre of each chart;
* `SymplecticGeometry.exists_localizingForm`: for a Hamiltonian circle action with isolated fixed
  points on a compact symplectic manifold, the same, with the weight charts of
  `SymplecticGeometry.exists_weightChart_fundamentalVectorField` at all the fixed points, which
  are finitely many (`finite_fixedPoints`) and have nonzero weights
  (`SymplecticGeometry.apply_circlePeriodOneGenerator_ne_zero_of_isolated`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.6
* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac Operators*, Grundlehren der
  mathematischen Wissenschaften 298, Springer, 1992, §7.2
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
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), TauCeti.norm_sq_complexToRealEuclidean,
    TauCeti.norm_sq_complexToRealEuclidean]
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
    (isSmoothForm_fun_smul_mpullback hρ Φ.symm.open_source (by simpa using hs)
      (fun _ hx ↦ Φ.symm.contMDiffAt hx)
      (weightOneForm k).isSmoothForm).mem_smoothBundleForms⟩

theorem cutoffWeightOneForm_val :
    (cutoffWeightOneForm Φ hρ hs k).val =
      fun x ↦ ρ x • TauCeti.mpullback I 𝓘(ℝ, StdSpace ι) Φ.symm (weightOneForm k).val x :=
  (rfl)

/-- Where the cut-off `ρ` vanishes, so does the cut-off model one-form. -/
theorem cutoffWeightOneForm_apply_of_eq_zero {x : M} (hx : ρ x = 0)
    (v : Fin 1 → TangentSpace I x) : (cutoffWeightOneForm Φ hρ hs k).val x v = 0 := by
  simp [cutoffWeightOneForm_val, hx]

omit [IsManifold I ∞ M] in
variable {Φ} in
/-- On a vector field `X` that the differential of `Φ` relates, at `z`, to the generator
`weightGenerator ((2π) • k')` of the rotations by the angles `2π k'ⱼ`, for weights `k'` that need
not be those of the form, the model one-form read through `Φ`, `(Φ⁻¹)^* θₖ`, takes at `Φ z` the
value `2π ∑ⱼ kⱼ k'ⱼ (xⱼ(z)² + yⱼ(z)²)`. -/
theorem mpullback_symm_weightOneForm_apply_weightChart (k' : ι → ℝ)
    {X : (x : M) → TangentSpace I x} {z : StdSpace ι} (hz : z ∈ Φ.source)
    (hX : mfderiv 𝓘(ℝ, StdSpace ι) I Φ z
      (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k') (EuclideanSpace.sumEquivProd z))) = X (Φ z)) :
    TauCeti.mpullback I 𝓘(ℝ, StdSpace ι) Φ.symm (weightOneForm k).val (Φ z) ![X (Φ z)] =
      2 * π * ∑ j, k j * k' j * (z.x j ^ 2 + z.y j ^ 2) := by
  rw [TauCeti.mpullback_apply_one]
  have hv : mfderiv I 𝓘(ℝ, StdSpace ι) Φ.symm (Φ z) (X (Φ z)) =
      EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k') (EuclideanSpace.sumEquivProd z)) := by
    rw [← hX]
    exact Φ.mfderiv_symm_apply_mfderiv_apply (by simp) hz _
  rw [hv, Φ.symm_toPartialEquiv, Φ.left_inv hz]
  -- `hv` gives the vector as a point of `StdSpace ι`, the lemmas as a tangent vector at `z`.
  exact (weightOneForm_apply_weightGenerator_smul k k' (2 * π) z).trans
    (congrArg _ (weightOneForm_apply_weightGenerator k k' z))

variable {Φ} in
/-- On a vector field `X` that the differential of `Φ` relates, at `z`, to the generator
`weightGenerator ((2π) • k')` of the rotations by the angles `2π k'ⱼ`, for weights `k'` that need
not be those of the form, the cut-off model one-form `ρ (Φ⁻¹)^* θₖ` takes at `Φ z` the value
`ρ (Φ z) * (2π ∑ⱼ kⱼ k'ⱼ (xⱼ(z)² + yⱼ(z)²))`. -/
theorem cutoffWeightOneForm_apply_weightChart (k' : ι → ℝ) {X : (x : M) → TangentSpace I x}
    {z : StdSpace ι} (hz : z ∈ Φ.source)
    (hX : mfderiv 𝓘(ℝ, StdSpace ι) I Φ z
      (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k') (EuclideanSpace.sumEquivProd z))) = X (Φ z)) :
    (cutoffWeightOneForm Φ hρ hs k).val (Φ z) ![X (Φ z)] =
      ρ (Φ z) * (2 * π * ∑ j, k j * k' j * (z.x j ^ 2 + z.y j ^ 2)) := by
  rw [cutoffWeightOneForm_val, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    mpullback_symm_weightOneForm_apply_weightChart k k' hz hX]

variable {Φ} in
/-- On a vector field `X` that the differential of `Φ` relates, at `z`, to the generator
`weightGenerator ((2π) • k)` of the rotations by the angles `2π kⱼ`, the cut-off model one-form
takes at `Φ z` the value `ρ (Φ z) * (2π ∑ⱼ kⱼ² (xⱼ(z)² + yⱼ(z)²))`. -/
theorem cutoffWeightOneForm_apply_weightChart_self {X : (x : M) → TangentSpace I x}
    {z : StdSpace ι} (hz : z ∈ Φ.source)
    (hX : mfderiv 𝓘(ℝ, StdSpace ι) I Φ z
      (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))) = X (Φ z)) :
    (cutoffWeightOneForm Φ hρ hs k).val (Φ z) ![X (Φ z)] =
      ρ (Φ z) * (2 * π * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2)) := by
  simp only [cutoffWeightOneForm_apply_weightChart hρ hs k k hz hX, sq]

/-- The cut-off model one-form is nonnegative on a vector field `X` that the differential of `Φ`
relates, at each point of the source, to the generator `weightGenerator ((2π) • k)`, at each
point `x` where the cut-off `ρ` is nonnegative. -/
theorem cutoffWeightOneForm_apply_nonneg {X : (x : M) → TangentSpace I x}
    (hX : ∀ z ∈ Φ.source, mfderiv 𝓘(ℝ, StdSpace ι) I Φ z
      (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))) = X (Φ z))
    {x : M} (hρ₀ : 0 ≤ ρ x) : 0 ≤ (cutoffWeightOneForm Φ hρ hs k).val x ![X x] := by
  by_cases hx : ρ x = 0
  · rw [cutoffWeightOneForm_apply_of_eq_zero Φ hρ hs k hx]
  obtain ⟨z, hz, rfl⟩ : x ∈ Φ '' Φ.source := by
    rw [Φ.toPartialEquiv.image_source_eq_target]
    exact hs (subset_tsupport ρ hx)
  rw [cutoffWeightOneForm_apply_weightChart_self hρ hs k hz (hX z hz)]
  exact mul_nonneg hρ₀ (by positivity)

variable {Φ} in
/-- When no weight `kⱼ` is zero, the cut-off model one-form vanishes, on a vector field `X` that
the differential of `Φ` relates at `z` to the generator `weightGenerator ((2π) • k)`, at a point
`Φ z` where the cut-off `ρ` is nonzero only if `z = 0`. -/
theorem cutoffWeightOneForm_apply_weightChart_eq_zero_iff (hk : ∀ j, k j ≠ 0)
    {X : (x : M) → TangentSpace I x} {z : StdSpace ι} (hz : z ∈ Φ.source)
    (hX : mfderiv 𝓘(ℝ, StdSpace ι) I Φ z
      (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))) = X (Φ z))
    (hρz : ρ (Φ z) ≠ 0) :
    (cutoffWeightOneForm Φ hρ hs k).val (Φ z) ![X (Φ z)] = 0 ↔ z = 0 := by
  rw [cutoffWeightOneForm_apply_weightChart_self hρ hs k hz hX,
    ← weightOneForm_apply_weightGenerator_two_pi_mul, mul_eq_zero, or_iff_right hρz,
    weightOneForm_apply_weightGenerator_eq_zero_iff hk]

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

/-! ### The exterior derivative where the cut-off is `1` -/

variable {Φ} in
/-- Where the cut-off `ρ` is `1` near `x`, the exterior derivative of the cut-off model one-form
at `x` is the pullback `(Φ⁻¹)^* dθₖ` of the exterior derivative of the model one-form. -/
theorem mextDerivₗ_cutoffWeightOneForm_apply_of_eventuallyEq_one {x : M}
    (hx : ρ =ᶠ[𝓝 x] 1) :
    (mextDerivₗ I 1 (cutoffWeightOneForm Φ hρ hs k)).val x =
      TauCeti.mpullback I 𝓘(ℝ, StdSpace ι) Φ.symm
        (mextDerivₗ 𝓘(ℝ, StdSpace ι) 1 (weightOneForm k)).val x := by
  have hxt : x ∈ Φ.target := hs (subset_tsupport ρ (by simp [hx.self_of_nhds]))
  rw [mpullback_apply_eq_compContinuousLinearMap]
  refine mextDerivₗ_apply_eq_of_eventuallyEq_mpullback
    ((Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds hxt)).of_le (by simp)) ?_
  filter_upwards [hx] with y hy
  simp only [cutoffWeightOneForm_val, hy, Pi.one_apply, one_smul]

variable {Φ} in
/-- **On a symplectic chart, the cut-off model one-form is a primitive of the symplectic form
where the cut-off is `1`.** If `Φ` pulls `σ` back to the standard form `ω₀` on its source and the
cut-off `ρ` is `1` near `x`, then the exterior derivative of the cut-off model one-form with the
weights `kⱼ = 1/2` is `σ` at `x`, since `d θ_{1/2} = ω₀`. -/
theorem mextDerivₗ_cutoffWeightOneForm_half_apply_of_eventuallyEq_one {σ : SmoothTwoForm I M}
    (hσ : SmoothTwoForm.IsSymplecticMapOn (stdForm ι).constSmooth σ Φ Φ.source) {x : M}
    (hx : ρ =ᶠ[𝓝 x] 1) :
    (mextDerivₗ I 1 (cutoffWeightOneForm Φ hρ hs fun _ ↦ 1 / 2)).val x = σ.val x := by
  have hxt : x ∈ Φ.target := hs (subset_tsupport ρ (by simp [hx.self_of_nhds]))
  refine SmoothBundleForm.apply_eq_of_eval₂_eq fun v w ↦ ?_
  rw [SmoothBundleForm.eval₂_apply,
    mextDerivₗ_cutoffWeightOneForm_apply_of_eventuallyEq_one hρ hs _ hx,
    TauCeti.mpullback_apply, mextDerivₗ_weightOneForm_half_apply,
    ← (Φ.isSymplecticMapOn_symm hσ (by simp)).apply hxt v w]
  exact (SymplecticForm.constSmooth_apply _ _ _ _).symm

end CutoffWeightOneForm

/-! ### Gluing the model one-forms -/

section Gluing

open TauCeti

variable [T2Space M]

/-- Invariant cut-offs at the centres of finitely many weight charts with distinct centres: each
is supported in the image of its chart, equals `1` on the image of a ball about `0`, and no two
of them are nonzero at the same point. -/
private theorem exists_smul_invariant_cutoffs_weightCharts {G : Type*} [Group G] [MulAction G M]
    {ι : Type*} [Finite ι] {n : ι → ℕ} (χ : ∀ i, Fin (n i) → G → Circle)
    (Φ : ∀ i, PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin (n i))) I (StdSpace (Fin (n i))) M ∞)
    (hequiv : ∀ i (g : G) (u : Fin (n i) → ℂ),
      complexToRealEuclidean (Fin (n i)) u ∈ (Φ i).source →
      complexToRealEuclidean (Fin (n i)) (fun j ↦ (χ i j g : ℂ) * u j) ∈ (Φ i).source ∧
        Φ i (complexToRealEuclidean (Fin (n i)) fun j ↦ (χ i j g : ℂ) * u j) =
          g • Φ i (complexToRealEuclidean (Fin (n i)) u))
    (h0 : ∀ i, (0 : StdSpace (Fin (n i))) ∈ (Φ i).source)
    (hinj : Function.Injective fun i ↦ Φ i 0) :
    ∃ ρ : ι → M → ℝ, (∀ i, ContMDiff I 𝓘(ℝ) ∞ (ρ i)) ∧ (∀ i x, ρ i x ∈ Icc 0 1) ∧
      (∀ i (g : G) x, ρ i (g • x) = ρ i x) ∧ (∀ i, tsupport (ρ i) ⊆ (Φ i).target) ∧
      (∀ i j x, ρ i x ≠ 0 → ρ j x ≠ 0 → i = j) ∧
      ∀ i, ∃ s > 0, ball 0 s ⊆ (Φ i).source ∧ ∀ z ∈ ball 0 s, ρ i (Φ i z) = 1 := by
  -- Balls about `0` in the sources with pairwise disjoint images under the charts.
  obtain ⟨c, hc0, hc, hdisj⟩ := OpenPartialHomeomorph.exists_pairwise_disjoint_image_ball
    (fun i ↦ (Φ i).toOpenPartialHomeomorph) h0 hinj
  have hb (i : ι) : closedBall (0 : StdSpace (Fin (n i))) (c i / 2) ⊆ ball 0 (c i) :=
    closedBall_subset_ball (by linarith [hc0 i])
  choose ρ hρ h01 hinv h1 hsupp using fun i ↦
    exists_smul_invariant_cutoff_weightChart (χ i) (Φ i) (hequiv i) (a := c i / 4)
      (b := c i / 2) (by linarith [hc0 i]) (by linarith [hc0 i]) ((hb i).trans (hc i))
  have hsU (i : ι) : tsupport (ρ i) ⊆ (Φ i).target ∩ Φ i '' ball 0 (c i) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hsupp i hx
    exact ⟨(Φ i).map_source (hc i (hb i hz)), mem_image_of_mem _ (hb i hz)⟩
  refine ⟨ρ, hρ, h01, hinv, fun i ↦ (hsU i).trans inter_subset_left, fun i j x hi hj ↦ ?_,
    fun i ↦ ⟨c i / 4, by linarith [hc0 i], ?_, fun z hz ↦ ?_⟩⟩
  · by_contra hij
    exact Set.disjoint_left.1 (hdisj hij) (hsU i (subset_tsupport _ hi)).2
      (hsU j (subset_tsupport _ hj)).2
  · exact (ball_subset_ball (by linarith [hc0 i])).trans (hc i)
  · exact h1 i (mem_image_of_mem _ (ball_subset_closedBall hz))

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [MulAction Circle M] [ContMDiffSMul (𝓡 1) I ∞ Circle M]

/-- **Gluing model one-forms along weight charts.** Let the circle act smoothly on a σ-compact
Hausdorff manifold `M` without boundary, with `X` the fundamental vector field of the period-one
generator `circlePeriodOneGenerator`. Let `Φᵢ`, for `i` in a finite type, be smooth partial
diffeomorphisms from `StdSpace (Fin nᵢ)` to `M`, defined at `0`, with pairwise distinct centres
`Φᵢ 0`, such that

* in the complex coordinates `z = complexToRealEuclidean (Fin nᵢ) u`, `g` sends `Φᵢ z` to `Φᵢ` of
  `uⱼ ↦ χᵢⱼ(g) uⱼ`, for maps `χᵢⱼ : S¹ → S¹`;
* the differential of `Φᵢ` sends the generator of the rotations by the angles `2π kᵢⱼ` to `X`;
* the weights `kᵢⱼ` are nonzero.

Then there is a smooth one-form `θ` on `M`, invariant under the action, with `θ(X) ≥ 0`, with
equality exactly at the fixed points, and equal on the image under `Φᵢ` of a ball about `0` to
the pullback `(Φᵢ⁻¹)^* θ_{kᵢ}` of the model one-form `weightOneForm kᵢ`. -/
theorem exists_localizingForm_of_weightCharts [SigmaCompactSpace M] {ι : Type*} [Finite ι]
    {n : ι → ℕ}
    (χ : ∀ i, Fin (n i) → Circle → Circle)
    (Φ : ∀ i, PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin (n i))) I (StdSpace (Fin (n i))) M ∞)
    (k : ∀ i, Fin (n i) → ℝ)
    (hequiv : ∀ i (g : Circle) (u : Fin (n i) → ℂ),
      complexToRealEuclidean (Fin (n i)) u ∈ (Φ i).source →
      complexToRealEuclidean (Fin (n i)) (fun j ↦ (χ i j g : ℂ) * u j) ∈ (Φ i).source ∧
        Φ i (complexToRealEuclidean (Fin (n i)) fun j ↦ (χ i j g : ℂ) * u j) =
          g • Φ i (complexToRealEuclidean (Fin (n i)) u))
    (hX : ∀ i, ∀ z ∈ (Φ i).source, mfderiv 𝓘(ℝ, StdSpace (Fin (n i))) I (Φ i) z
      (EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k i) (EuclideanSpace.sumEquivProd z))) =
          fundamentalVectorField I circlePeriodOneGenerator (Φ i z))
    (h0 : ∀ i, (0 : StdSpace (Fin (n i))) ∈ (Φ i).source)
    (hinj : Function.Injective fun i ↦ Φ i 0) (hk : ∀ i j, k i j ≠ 0) :
    ∃ θ : SmoothForm I M ℝ 1,
      (∀ g : Circle, SmoothForm.mpullback (g • ·)
        (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) g) θ = θ) ∧
      (∀ x, 0 ≤ θ.val x ![fundamentalVectorField I circlePeriodOneGenerator x]) ∧
      (∀ x, θ.val x ![fundamentalVectorField I circlePeriodOneGenerator x] = 0 ↔
        x ∈ MulAction.fixedPoints Circle M) ∧
      ∀ i, ∃ s > 0, ball 0 s ⊆ (Φ i).source ∧
        ∀ x ∈ Φ i '' ball 0 s, θ.val x =
          TauCeti.mpullback I 𝓘(ℝ, StdSpace (Fin (n i))) (Φ i).symm
            (weightOneForm (k i)).val x := by
  have := Fintype.ofFinite ι
  obtain ⟨ρ, hρ, h01, hinv, hsupp, hdisj, h1⟩ :=
    exists_smul_invariant_cutoffs_weightCharts χ Φ hequiv h0 hinj
  obtain ⟨β, hβinv, hβ⟩ := exists_invariant_smoothForm_apply_circle_nonneg (I := I) (M := M)
  let τ : ι → SmoothForm I M ℝ 1 := fun i ↦ cutoffWeightOneForm (Φ i) (hρ i) (hsupp i) (k i)
  let f : C^∞⟮I, M; ℝ⟯ :=
    ⟨fun x ↦ 1 - ∑ i, ρ i x, contMDiff_const.sub (ContMDiff.sum fun i _ ↦ hρ i)⟩
  set X := fundamentalVectorField I circlePeriodOneGenerator (M := M)
  -- At each point at most one cut-off is nonzero, so their sum is at most `1`.
  have hone {x : M} {i : ι} (hi : ρ i x ≠ 0) (j : ι) (hj : j ≠ i) : ρ j x = 0 :=
    by_contra fun h ↦ hj (hdisj j i x h hi)
  have hsum_le (x : M) : ∑ i, ρ i x ≤ 1 := by
    by_cases h : ∃ i, ρ i x ≠ 0
    · obtain ⟨i, hi⟩ := h
      rw [Finset.sum_eq_single i (fun j _ hj ↦ hone hi j hj) (by simp)]
      exact (h01 i x).2
    · push Not at h
      simp [h]
  have hval (x : M) : (∑ i, τ i + SmoothForm.funSMulₗ f β).val x =
      ∑ i, (τ i).val x + (1 - ∑ i, ρ i x) • β.val x := by
    rw [SmoothForm.add_toRoughForm, SmoothForm.coe_funSMulₗ]
    simp [f]
  have hvalX (x : M) : (∑ i, τ i + SmoothForm.funSMulₗ f β).val x ![X x] =
      ∑ i, (τ i).val x ![X x] + (1 - ∑ i, ρ i x) * β.val x ![X x] := by
    simp [hval]
  have hτ (i : ι) (x : M) : 0 ≤ (τ i).val x ![X x] :=
    cutoffWeightOneForm_apply_nonneg (Φ i) (hρ i) (hsupp i) (k i) (hX i) (h01 i x).1
  have hβX (x : M) : 0 ≤ (1 - ∑ i, ρ i x) * β.val x ![X x] :=
    mul_nonneg (by linarith [hsum_le x]) (hβ x).1
  refine ⟨∑ i, τ i + SmoothForm.funSMulₗ f β, fun g ↦ ?_, fun x ↦ ?_,
    fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩, fun i ↦ ?_⟩
  · -- Each piece is invariant.
    rw [map_add, map_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ ↦
        mpullback_smul_cutoffWeightOneForm (hρ i) (hsupp i) (k i) (χ i) g (hequiv i g) _
          (hinv i g)
    · refine Subtype.ext ?_
      rw [SmoothForm.coe_mpullback, SmoothForm.coe_funSMulₗ]
      refine TauCeti.mpullback_fun_smul_eq_self (fun x ↦ ?_) fun x _ ↦ ?_
      · simp [f, hinv]
      · have h := congrArg Subtype.val (hβinv g)
        rw [SmoothForm.coe_mpullback] at h
        exact congrFun h x
  · rw [hvalX]
    exact add_nonneg (Finset.sum_nonneg fun i _ ↦ hτ i x) (hβX x)
  · -- Off the fixed points, `β(X) > 0`; so if `θ(X) = 0`, some cut-off is `1`, and the model
    -- form vanishes on `X` only at the centre of its chart, which is fixed.
    by_contra hfix
    rw [hvalX] at hx
    obtain ⟨hτ0, hβ0⟩ :=
      (add_eq_zero_iff_of_nonneg (Finset.sum_nonneg fun i _ ↦ hτ i x) (hβX x)).1 hx
    have hβpos : β.val x ![X x] ≠ 0 := fun h ↦ hfix ((hβ x).2.1 h)
    have hs1 : ∑ i, ρ i x = 1 := by
      have := (mul_eq_zero.1 hβ0).resolve_right hβpos
      linarith
    obtain ⟨i, hi⟩ : ∃ i, ρ i x ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hs1
    obtain ⟨z, hz, rfl⟩ : x ∈ Φ i '' (Φ i).source := by
      rw [(Φ i).toPartialEquiv.image_source_eq_target]
      exact hsupp i (subset_tsupport _ hi)
    have hτi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hτ j _).1 hτ0 i (Finset.mem_univ _)
    obtain rfl : z = 0 :=
      (cutoffWeightOneForm_apply_weightChart_eq_zero_iff (hρ i) (hsupp i) (k i) (hk i) hz
        (hX i z hz) hi).1 hτi
    refine hfix fun g ↦ ?_
    have hu : (fun j ↦ (χ i j g : ℂ) * (0 : Fin (n i) → ℂ) j) = 0 := by
      funext j
      simp
    have h := (hequiv i g 0 (by rw [map_zero]; exact h0 i)).2
    rw [hu, map_zero] at h
    exact h.symm
  · rw [show X x = 0 from mem_fixedPoints_circle_iff_fundamentalVectorField_eq_zero.1 hx,
      show (![0] : Fin 1 → TangentSpace I x) = 0 by simp, ContinuousAlternatingMap.map_zero]
  · -- Near the centre of `Φ i`, only the `i`-th cut-off is nonzero, and it is `1`.
    obtain ⟨s, hs, hss, hs1⟩ := h1 i
    refine ⟨s, hs, hss, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hi : ρ i (Φ i z) = 1 := hs1 z hz
    have hj := hone (x := Φ i z) (i := i) (by rw [hi]; exact one_ne_zero)
    rw [hval, Finset.sum_eq_single i (fun j _ hj' ↦ by
        simp [τ, cutoffWeightOneForm_val, hj j hj']) (by simp),
      Finset.sum_eq_single i (fun j _ hj' ↦ hj j hj') (by simp), hi]
    simp [τ, cutoffWeightOneForm_val, hi]


/-- **The localizing one-form.** Let the circle act smoothly on a compact symplectic manifold
`(M, σ)` without boundary, preserving `σ`, with a moment map `μ` in the sign
`d⟨μ, ξ⟩ = -ι_{ξ_M} σ`, and with isolated fixed points; let `X` be the fundamental vector field
of the period-one generator `ξ₁ = circlePeriodOneGenerator`. Then there is a smooth one-form `θ`
on `M`, invariant under the action, with `θ(X) ≥ 0`, with equality exactly at the fixed points,
and such that at each fixed point `p` there is a weight chart `Φ` at `p` of radius `r`
(`SymplecticGeometry.IsWeightChart`), whose weights
`kⱼ = αⱼ(ξ₁)` are nonzero, and a radius `0 < s ≤ r` such that on `Φ '' ball 0 s` the form `θ`
is the pullback `(Φ⁻¹)^* θₖ` of the model one-form `weightOneForm k`. -/
theorem exists_localizingForm [CompactSpace M] {σ : SmoothTwoForm I M}
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) g) σ = σ)
    (hiso : ∀ p ∈ MulAction.fixedPoints Circle M,
      ∀ᶠ x in 𝓝[≠] p, x ∉ MulAction.fixedPoints Circle M) :
    ∃ θ : SmoothForm I M ℝ 1,
      (∀ g : Circle, SmoothForm.mpullback (g • ·)
        (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) g) θ = θ) ∧
      (∀ x, 0 ≤ θ.val x ![fundamentalVectorField I circlePeriodOneGenerator x]) ∧
      (∀ x, θ.val x ![fundamentalVectorField I circlePeriodOneGenerator x] = 0 ↔
        x ∈ MulAction.fixedPoints Circle M) ∧
      ∀ p ∈ MulAction.fixedPoints Circle M,
        ∃ (n : ℕ) (χ : Fin n → Circle →ₜ* Circle)
          (α : Fin n → StrongDual ℝ (EuclideanSpace ℝ (Fin 1)))
          (Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I (StdSpace (Fin n)) M ∞) (r s : ℝ),
          IsWeightChart σ μ p χ α Φ r ∧
          (∀ j, α j circlePeriodOneGenerator ≠ 0) ∧ 0 < s ∧ s ≤ r ∧
          ∀ x ∈ Φ '' ball 0 s, θ.val x = TauCeti.mpullback I 𝓘(ℝ, StdSpace (Fin n)) Φ.symm
            (weightOneForm fun j ↦ α j circlePeriodOneGenerator).val x := by
  have : ContinuousSMul Circle M := ContMDiffSMul.continuousSMul (I := 𝓡 1) (I' := I) ∞
  have := (finite_fixedPoints hiso).to_subtype
  choose n χ α Φ r hW using fun p : MulAction.fixedPoints Circle M ↦
    exists_weightChart_fundamentalVectorField hμ hσ hG (p := p.val) p.property
  have hk (p : MulAction.fixedPoints Circle M) (j : Fin (n p)) :
      α p j circlePeriodOneGenerator ≠ 0 :=
    apply_circlePeriodOneGenerator_ne_zero_of_isolated (fun j ↦ χ p j) (α p)
      (hW p).apply_mulInvariantExp (Φ p).toOpenPartialHomeomorph
      (fun g u hu ↦ ((hW p).equivariant g u hu).2) (hW p).zero_mem_source (hW p).apply_zero
      (hiso p.val p.property) j
  obtain ⟨θ, hinv, hnonneg, hzero, hloc⟩ := exists_localizingForm_of_weightCharts
    (fun p j ↦ χ p j) Φ (fun p j ↦ α p j circlePeriodOneGenerator) (fun p ↦ (hW p).equivariant)
    (fun p z hz ↦ by
      simpa only [Pi.smul_def, smul_eq_mul] using
        (hW p).mfderiv_weightGenerator z hz circlePeriodOneGenerator)
    (fun p ↦ (hW p).zero_mem_source)
    (fun p q h ↦ Subtype.ext ((hW p).apply_zero.symm.trans (h.trans (hW q).apply_zero))) hk
  refine ⟨θ, hinv, hnonneg, hzero, fun p hp ↦ ?_⟩
  obtain ⟨s, hs, -, hθ⟩ := hloc ⟨p, hp⟩
  refine ⟨n ⟨p, hp⟩, χ _, α _, Φ _, r _, min s (r ⟨p, hp⟩), hW ⟨p, hp⟩, hk _,
    lt_min hs (hW _).radius_pos, min_le_right _ _,
    fun x hx ↦ hθ x (image_mono (ball_subset_ball (min_le_left _ _)) hx)⟩
end Gluing

end SymplecticGeometry

end
