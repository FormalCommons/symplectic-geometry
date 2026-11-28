/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Analysis.Normed.Module.ContinuousInverse
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Hamiltonian vector fields read in a chart of the maximal atlas

Let `σ` be a two-form on a manifold `M` modelled on a finite-dimensional space `E`, and let `e` be
a chart of the `C^1` maximal atlas of `M`. Read in `e`, at a coordinate `z` of the target, `σ`
becomes the bilinear form `(u, w) ↦ σ_x(d(e⁻¹)_z u, d(e⁻¹)_z w)` on `E`, with `x = e.symm z`; its
flat map is `TauCeti.SmoothTwoForm.flatInChart σ e z`. When `σ` is nondegenerate this flat map is
invertible on the chart target, and its inverse
`TauCeti.SmoothTwoForm.inverseFlatInChart σ e z : (E →L[ℝ] ℝ) →L[ℝ] E` turns differentials into
vectors: in coordinates, a vector `v` with `σ_x(v, ·) = dK_x` is `J z (d(K ∘ e⁻¹)_z)` with
`J = inverseFlatInChart σ e`. In particular this holds for the Hamiltonian vector field of any
function. Closedness of `σ` plays no role.

Tau Ceti reads `σ` and Hamiltonian vector fields in the preferred chart `chartAt` of a point, in
`TauCeti.Geometry.Symplectic.Floer.Chart`; here `e` is any chart of the maximal atlas, as the
Morse and birth–death charts of `TauCeti.MorseChart` are.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.isInvertible_flatInChart`: the flat map in the chart is
  invertible on the chart target.
* `TauCeti.SmoothTwoForm.IsNondegenerate.flatInChart_inverseFlatInChart_apply`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.inverseFlatInChart_flatInChart_apply`: on the chart
  target, `inverseFlatInChart σ e z` and `flatInChart σ e z` are mutually inverse.
* `TauCeti.SmoothTwoForm.IsNondegenerate.mvfderiv_eq_inverseFlatInChart_fderiv`: a vector `v` with
  `σ_x(v, ·) = dK_x`, read in the chart, is `J z (d(K ∘ e⁻¹)_z)`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.mvfderiv_hamiltonianVectorField`: the Hamiltonian vector
  field of `G`, read in the chart, is `J z (d(G ∘ e⁻¹)_z)`.
* `TauCeti.SmoothTwoForm.continuousOn_flatInChart`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.continuousOn_inverseFlatInChart`: both depend
  continuously on `z` in the chart target.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_ball_norm_inverseFlatInChart_le`: on a ball
  around `e p`, `‖J z‖ ≤ B` and `‖ℓ‖ ≤ B' * ‖J z ℓ‖`.

These are the chart readings that the cut-off step of Cieliebak–Eliashberg's Lemma 12.9 uses to
write the difference of two Liouville fields as a Hamiltonian field in a Morse or birth–death
chart.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Lemma 12.9
-/

public section

open Set Metric
open scoped Manifold Topology ContDiff

namespace TauCeti

namespace SmoothTwoForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {σ : SmoothTwoForm 𝓘(ℝ, E) M} {e : OpenPartialHomeomorph M E} {z : E}

/-- The flat map of a two-form `σ` read in a chart `e` at a coordinate `z`: the bilinear form
`(u, w) ↦ σ_x(d(e⁻¹)_z u, d(e⁻¹)_z w)` on the model space, with `x = e.symm z`, curried. -/
noncomputable def flatInChart (σ : SmoothTwoForm 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.flatL ℝ E ℝ (σ.val (e.symm z))).bilinearComp
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z)

/-- The flat map in a chart unfolds as the currying of `σ` at `e.symm z`, composed on both sides
with `d(e⁻¹)_z`. -/
theorem flatInChart_def (σ : SmoothTwoForm 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E) (z : E) :
    σ.flatInChart e z = ((ContinuousAlternatingMap.flatL ℝ E ℝ (σ.val (e.symm z))).bilinearComp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z) : E →L[ℝ] E →L[ℝ] ℝ) :=
  (rfl)

/-- The flat map in a chart evaluates as `σ` at `e.symm z` on the images under `d(e⁻¹)_z`. -/
@[simp]
theorem flatInChart_apply (σ : SmoothTwoForm 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (z u w : E) :
    σ.flatInChart e z u w = SmoothBundleForm.eval₂ σ (e.symm z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z w) := by
  rw [flatInChart_def, SmoothBundleForm.eval₂_apply]
  exact ContinuousAlternatingMap.flatL_apply_apply (E := E) (σ.val (e.symm z)) _ _

/-- The inverse of the flat map of `σ` read in the chart `e` at `z`, which turns a covector of
the model space into a vector. It is the inverse of `flatInChart σ e z` when that is invertible,
as on the chart target for a nondegenerate `σ`, and zero otherwise. -/
noncomputable def inverseFlatInChart (σ : SmoothTwoForm 𝓘(ℝ, E) M)
    (e : OpenPartialHomeomorph M E) (z : E) : (E →L[ℝ] ℝ) →L[ℝ] E :=
  (σ.flatInChart e z).inverse

/-- The inverse flat map in a chart unfolds as `ContinuousLinearMap.inverse` of the flat map. -/
theorem inverseFlatInChart_def (σ : SmoothTwoForm 𝓘(ℝ, E) M) (e : OpenPartialHomeomorph M E)
    (z : E) : σ.inverseFlatInChart e z = (σ.flatInChart e z).inverse :=
  (rfl)

/-- On the chart target, the flat map in the chart takes the images of two tangent vectors at
`e.symm z` under `de`, read in the model space, to the value of `σ` on them. -/
theorem flatInChart_mvfderiv_mvfderiv (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M)
    (hz : z ∈ e.target) (v w : TangentSpace 𝓘(ℝ, E) (e.symm z)) :
    σ.flatInChart e z (mvfderiv 𝓘(ℝ, E) e (e.symm z) v)
        (mvfderiv 𝓘(ℝ, E) e (e.symm z) w) = SmoothBundleForm.eval₂ σ (e.symm z) v w := by
  have h := e.mfderiv_symm_apply_mfderiv_apply_of_mem_maximalAtlas he hz
  rw [flatInChart_apply, mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
  exact congrArg₂ _ (h v) (h w)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- For a nondegenerate `σ`, the flat map read in a chart of the `C^1` maximal atlas is invertible
at every point of the chart target. -/
theorem IsNondegenerate.isInvertible_flatInChart (hσ : σ.IsNondegenerate)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) (hz : z ∈ e.target) :
    (σ.flatInChart e z).IsInvertible := by
  obtain ⟨A, hA⟩ := isInvertible_mfderiv_chart_symm he hz
  rw [flatInChart_def, ← flat_def, ← hA]
  exact (hσ.isInvertible_flat (e.symm z)).bilinearComp (V := E) (V' := E) (W := E) (W' := E) A A

/-- For a nondegenerate `σ` and `z` in the target of a chart `e` of the `C^1` maximal atlas, the
flat map in the chart undoes its inverse at `z`. -/
theorem IsNondegenerate.flatInChart_inverseFlatInChart_apply (hσ : σ.IsNondegenerate)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) (hz : z ∈ e.target) (ℓ : E →L[ℝ] ℝ) :
    σ.flatInChart e z (σ.inverseFlatInChart e z ℓ) = ℓ := by
  rw [inverseFlatInChart_def, (hσ.isInvertible_flatInChart he hz).self_apply_inverse]

/-- For a nondegenerate `σ` and `z` in the target of a chart `e` of the `C^1` maximal atlas, the
inverse flat map in the chart undoes the flat map at `z`. -/
theorem IsNondegenerate.inverseFlatInChart_flatInChart_apply (hσ : σ.IsNondegenerate)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) (hz : z ∈ e.target) (u : E) :
    σ.inverseFlatInChart e z (σ.flatInChart e z u) = u := by
  rw [inverseFlatInChart_def, (hσ.isInvertible_flatInChart he hz).inverse_apply_self]

/-- **A vector with prescribed contraction, read in a chart.** Let `σ` be nondegenerate, `e` a
chart of the `C^1` maximal atlas and `z` a point of its target, with `x = e.symm z`. If a tangent
vector `v` at `x` satisfies `σ_x(v, ·) = dK_x`, then `de_x v = J z (d(K ∘ e⁻¹)_z)`, with
`J = inverseFlatInChart σ e`. -/
theorem IsNondegenerate.mvfderiv_eq_inverseFlatInChart_fderiv (hσ : σ.IsNondegenerate)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) (hz : z ∈ e.target) {K : M → ℝ}
    {v : TangentSpace 𝓘(ℝ, E) (e.symm z)}
    (hv : ∀ w, SmoothBundleForm.eval₂ σ (e.symm z) v w = mvfderiv 𝓘(ℝ, E) K (e.symm z) w) :
    mvfderiv 𝓘(ℝ, E) e (e.symm z) v = σ.inverseFlatInChart e z (fderiv ℝ (K ∘ e.symm) z) := by
  have hx := e.map_target hz
  rw [← hσ.inverseFlatInChart_flatInChart_apply he hz (mvfderiv 𝓘(ℝ, E) e (e.symm z) v)]
  congr 1
  have hK := mfderiv_eq_fderiv_comp_of_eqOn (f := K) (h := K ∘ e.symm) he
    (fun y hy ↦ by simp [e.left_inv hy]) hx
  rw [e.right_inv hz] at hK
  ext w
  have hAB := e.mfderiv_apply_mfderiv_symm_apply_of_mem_maximalAtlas he hz w
  rw [← mvfderiv_apply_eq_mfderiv_apply] at hAB
  conv_lhs => rw [← hAB]
  conv_rhs => rw [← hAB]
  rw [flatInChart_mvfderiv_mvfderiv he hz, hv, mvfderiv_apply_eq_mfderiv_apply,
    mvfderiv_apply_eq_mfderiv_apply, hK]
  exact (ContinuousLinearMap.comp_apply _ _ _).symm

/-- **The Hamiltonian vector field read in a chart.** For a nondegenerate `σ`, a chart `e` of the
maximal atlas and `z` in its target, the Hamiltonian vector field of any function `G` at
`x = e.symm z`, pushed forward by `de_x`, is `J z (d(G ∘ e⁻¹)_z)`, with
`J = inverseFlatInChart σ e`. -/
theorem IsNondegenerate.mvfderiv_hamiltonianVectorField (hσ : σ.IsNondegenerate)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) (hz : z ∈ e.target) (G : M → ℝ) :
    mvfderiv 𝓘(ℝ, E) e (e.symm z) (σ.hamiltonianVectorField G (e.symm z)) =
      σ.inverseFlatInChart e z (fderiv ℝ (G ∘ e.symm) z) :=
  hσ.mvfderiv_eq_inverseFlatInChart_fderiv he hz
    (eval₂_hamiltonianVectorField_of_isInvertible (hσ.isInvertible_flat _) G)

/-- The flat map of `σ` read in a chart of the `C^1` maximal atlas depends continuously on the
point of the chart target. -/
theorem continuousOn_flatInChart (σ : SmoothTwoForm 𝓘(ℝ, E) M)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) :
    ContinuousOn (σ.flatInChart e) e.target := by
  refine continuousOn_clm_apply.2 fun u ↦ continuousOn_clm_apply.2 fun w ↦ ?_
  refine ((σ.isSmoothForm.of_le (by simp)).continuousOn_apply_mfderiv e.open_target
    (contMDiffOn_symm_of_mem_maximalAtlas he) u w).congr fun z _ ↦ ?_
  rw [flatInChart_apply, SmoothBundleForm.eval₂_apply]

/-- For a nondegenerate `σ`, the inverse of the flat map read in a chart of the `C^1` maximal
atlas depends continuously on the point of the chart target. -/
theorem IsNondegenerate.continuousOn_inverseFlatInChart (hσ : σ.IsNondegenerate)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) :
    ContinuousOn (σ.inverseFlatInChart e) e.target := fun z hz ↦
  (continuousOn_flatInChart σ he z hz).clm_inverse_of_eventually_isInvertible
    (hσ.isInvertible_flatInChart he hz)
    (eventually_nhdsWithin_of_forall fun _ hy ↦ hσ.isInvertible_flatInChart he hy)

/-- **Local bounds for the inverse flat map in a chart.** For a nondegenerate `σ`, a chart `e` of
the `C^1` maximal atlas and `p` in its source, there are `r > 0`, `B` and `B'` such that the ball
of radius `r` around `e p` lies in the chart target and, at each of its points `z`,
`J = inverseFlatInChart σ e` satisfies `‖J z‖ ≤ B` and `‖ℓ‖ ≤ B' * ‖J z ℓ‖` for every covector
`ℓ`. -/
theorem IsNondegenerate.exists_ball_norm_inverseFlatInChart_le (hσ : σ.IsNondegenerate)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M) {p : M} (hp : p ∈ e.source) :
    ∃ r > 0, ∃ B B' : ℝ, ball (e p) r ⊆ e.target ∧ ∀ z ∈ ball (e p) r,
      ‖σ.inverseFlatInChart e z‖ ≤ B ∧
        ∀ ℓ : E →L[ℝ] ℝ, ‖ℓ‖ ≤ B' * ‖σ.inverseFlatInChart e z ℓ‖ := by
  have hp' := e.map_source hp
  have hn := e.open_target.mem_nhds hp'
  have h₁ : ∀ᶠ z in 𝓝 (e p), ‖σ.inverseFlatInChart e z‖ < ‖σ.inverseFlatInChart e (e p)‖ + 1 :=
    (((hσ.continuousOn_inverseFlatInChart he).continuousAt hn).norm
      (E := (E →L[ℝ] ℝ) →L[ℝ] E)).eventually
      (gt_mem_nhds (lt_add_one _))
  have h₂ : ∀ᶠ z in 𝓝 (e p), ‖σ.flatInChart e z‖ < ‖σ.flatInChart e (e p)‖ + 1 :=
    (((continuousOn_flatInChart σ he).continuousAt hn).norm
      (E := E →L[ℝ] E →L[ℝ] ℝ)).eventually
      (gt_mem_nhds (lt_add_one _))
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.1 (h₁.and (h₂.and hn))
  refine ⟨r, hr, ‖σ.inverseFlatInChart e (e p)‖ + 1, ‖σ.flatInChart e (e p)‖ + 1,
    fun z hz ↦ (h z hz).2.2, fun z hz ↦ ⟨(h z hz).1.le, fun ℓ ↦ ?_⟩⟩
  obtain ⟨-, hS, hzt⟩ := h z hz
  calc ‖ℓ‖ = ‖σ.flatInChart e z (σ.inverseFlatInChart e z ℓ)‖ := by
        rw [hσ.flatInChart_inverseFlatInChart_apply he hzt]
    _ ≤ ‖σ.flatInChart e z‖ * ‖σ.inverseFlatInChart e z ℓ‖ := (σ.flatInChart e z).le_opNorm _
    _ ≤ _ := by gcongr

end FiniteDimensional

end SmoothTwoForm

end TauCeti

end
