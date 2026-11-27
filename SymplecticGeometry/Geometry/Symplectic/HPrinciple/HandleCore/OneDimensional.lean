/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.CubeCompression
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.ProdFiberContraction
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.NormedSpace
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.HomotopyOperator
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import SymplecticGeometry.Geometry.Symplectic.HPrinciple.HandleCore.Homotopy
import TauCeti.Analysis.Calculus.FDeriv.NormalSegment
import TauCeti.Topology.Order.Sublevel
import TauCeti.Topology.UnitInterval

/-!
# The handle-core lemma for a one-dimensional core

Let `D = (Fin 1 → ℝ) × F` with the sup norm, `F` finite-dimensional, with the cube
`Q = closedBall 0 1` and the attaching faces `A = sphere 0 1 ×ˢ closedBall 0 1`. Let `τ` be a
smooth family of two-forms on `D`, over a parameter space `L`, nondegenerate on `Q` for the
parameters of a compact `K ⊆ L`, and closed on a fixed open neighbourhood `W` of `A` for those
parameters. `SymplecticGeometry.exists_homotopy_exact_of_closed_near_attaching_fin_one` deforms
`τ`, smoothly in the parameter and in time, through forms nondegenerate on `Q` and fixed near `A`,
to forms exact on all of `D`; parameters for which `τ` is already exact near `Q` stay exact near
`Q`. This is the case `m = 1` of the handle-core lemma (McDuff–Salamon, Lemma 7.3.2).

## The construction

Write `Φ ((u, v), s) = (u, s • v)` for the fibrewise contraction onto the core and `h` for the
homotopy operator. Since the core is one-dimensional, `τ' := d (h (Φ^* τ))` equals
`τ - h (Φ^* dτ)` (`SymplecticGeometry.mextDerivₗ_homotopyOperator_mpullback_prodFiberContraction`),
so `τ'` is exact on `D`, and differs from `τ` by a term that

* vanishes at the points whose fibre segment to the core stays in `W`, where `τ` is closed, which
  is the case on an open neighbourhood `T` of `A`, and so on the part of `Q` next to `A`;
* is at most `‖v‖ · sup ‖dτ‖` at `(u, v) ∈ Q`
  (`SymplecticGeometry.norm_homotopyOperator_mpullback_prodFiberContraction_apply_le`).

Let `r` be a nondegeneracy margin of `τ` over `K × Q`
(`SymplecticGeometry.IsSmoothFamily.exists_pos_forall_nondegenerate`). The compression
`c s` of `SymplecticGeometry.exists_cubeCompression` squeezes `Q` into the union of the part next to
`A` and a tube `‖v‖ < δ` so thin that there `‖τ' - τ‖ < r`. The homotopy is
`σ (λ, t) = (c (a t))^* ((1 - b t) • τ λ + b t • τ' λ)` for smooth steps `a` and `b`, with `b`
starting once `a` has reached `1`: first the cube is compressed, then `τ` is moved to `τ'` on the
compressed cube. Every `c s` is a diffeomorphism fixing a neighbourhood of `A`, so the forms stay
nondegenerate on `Q` and equal to `τ` near `A`; and `σ (λ, 1) = c 1 ^* d (h (Φ^* τ λ))` is exact.
This last step is shared with the handle-core lemma for a core of any dimension, and proved once
in `SymplecticGeometry.exists_homotopy_exact_of_isotopy`.

This differs from McDuff–Salamon's proof, which patches the primitives given near the two ends of
the core across a band around it, and lengthens the band by a zig-zag
(here `SymplecticGeometry.exists_wiggling_diffeotopy`) to make the error small. The contraction
along the fibres gives one primitive, on all of `D`, of a form close to `τ` near the core, so no
patching and no zig-zag are needed. In their place comes Eliashberg–Mishachev's compression
argument (§10.2): pull back along embeddings that squeeze the cube into the region where the
approximating exact form is close to `τ`, then interpolate. The primitive of the final form is
`c 1 ^* h (Φ^* τ λ)`, which depends smoothly on `λ`.

Only the closedness of `τ` on `W` is used near `A`; a primitive there gives it
(`SmoothForm.mextDerivₗ_apply_eq_zero_of_eventuallyEq_mextDerivₗ`).

## Main results

* `SymplecticGeometry.exists_homotopy_exact_of_closed_near_attaching_fin_one`

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 7.3.2.
* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2.
-/

public section

open Set Metric Filter TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {F L : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup L] [NormedSpace ℝ L]

/-- **The handle-core lemma for a one-dimensional core.** On `D = (Fin 1 → ℝ) × F` with the sup
norm, `F` finite-dimensional, let `Q = closedBall 0 1` be the cube and
`A = sphere 0 1 ×ˢ closedBall 0 1` its attaching faces. Let `τ` be a smooth family of two-forms on
`D` over a normed space `L`, and `K ⊆ L` compact, such that for `λ ∈ K` the form `τ λ` is
nondegenerate on `Q` and closed on the open set `W ⊇ A`. Then there is a smooth family
`σ` of two-forms over `L × [0, 1]` with `σ (λ, 0) = τ λ` such that:

* `σ (λ, t)` is nondegenerate on `Q` for `λ ∈ K` and every `t`;
* `σ (λ, t) = τ λ` on a neighbourhood `W'` of `A`, the same for all `λ ∈ K` and all `t`;
* `σ (λ, 1)` is exact on `D`, for every `λ`;
* if `τ λ` has a primitive on a neighbourhood of `Q`, then so does every `σ (λ, t)`. -/
theorem exists_homotopy_exact_of_closed_near_attaching_fin_one {K : Set L} (hK : IsCompact K)
    {τ : L → SmoothTwoForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F)}
    (hτ : IsSmoothFamily 𝓘(ℝ, L) τ)
    (hnd : ∀ l ∈ K, ∀ x ∈ closedBall (0 : (Fin 1 → ℝ) × F) 1,
      ((τ l).bilinFormAt x).Nondegenerate)
    {W : Set ((Fin 1 → ℝ) × F)} (hW : IsOpen W)
    (hAW : sphere (0 : Fin 1 → ℝ) 1 ×ˢ closedBall (0 : F) 1 ⊆ W)
    (hτW : ∀ l ∈ K, ∀ x ∈ W, (mextDerivₗ 𝓘(ℝ, (Fin 1 → ℝ) × F) 2 (τ l)).val x = 0) :
    ∃ σ : L × unitInterval → SmoothTwoForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F),
      IsSmoothFamily (𝓘(ℝ, L).prod (𝓡∂ 1)) σ ∧
      (∀ l, σ (l, 0) = τ l) ∧
      (∀ l ∈ K, ∀ t, ∀ x ∈ closedBall (0 : (Fin 1 → ℝ) × F) 1,
        ((σ (l, t)).bilinFormAt x).Nondegenerate) ∧
      (∃ W' ∈ 𝓝ˢ (sphere (0 : Fin 1 → ℝ) 1 ×ˢ closedBall (0 : F) 1), ∀ l ∈ K, ∀ t,
        ∀ x ∈ W', (σ (l, t)).val x = (τ l).val x) ∧
      (∀ l, ∃ γ : SmoothForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F) ℝ 1,
        mextDerivₗ 𝓘(ℝ, (Fin 1 → ℝ) × F) 1 γ = σ (l, 1)) ∧
      ∀ l, (∃ V ∈ 𝓝ˢ (closedBall (0 : (Fin 1 → ℝ) × F) 1),
          ∃ γ : SmoothForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F) ℝ 1,
            ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (Fin 1 → ℝ) × F) 1 γ).val x = (τ l).val x) →
        ∀ t, ∃ V ∈ 𝓝ˢ (closedBall (0 : (Fin 1 → ℝ) × F) 1),
          ∃ γ : SmoothForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F) ℝ 1,
            ∀ x ∈ V, (mextDerivₗ 𝓘(ℝ, (Fin 1 → ℝ) × F) 1 γ).val x = (σ (l, t)).val x := by
  have hΦ := contMDiff_prodFiberContraction (Fin 1 → ℝ) F
  -- `τ' l = d (β' l)`, with `β' l = h (Φ^* τ l)`, is exact, and equals `τ l - η l` with
  -- `η l = h (Φ^* d (τ l))`.
  set β' : L → SmoothForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F) ℝ 1 := fun l ↦
    SmoothForm.homotopyOperator (SmoothForm.mpullback _ hΦ (τ l))
  set η : L → SmoothTwoForm 𝓘(ℝ, (Fin 1 → ℝ) × F) ((Fin 1 → ℝ) × F) := fun l ↦
    SmoothForm.homotopyOperator (SmoothForm.mpullback _ hΦ (mextDerivₗ _ 2 (τ l))) with hηdef
  have hτη (l : L) : mextDerivₗ _ 1 (β' l) = τ l - η l :=
    mextDerivₗ_homotopyOperator_mpullback_prodFiberContraction (k := 1) (by simp) (τ l)
  have hβ' : IsSmoothFamily 𝓘(ℝ, L) β' := (hτ.mpullback _ hΦ).homotopyOperator
  -- The points whose fibre segment to the core stays in `W` form an open neighbourhood of `A`.
  set T : Set ((Fin 1 → ℝ) × F) := {x | ∀ s : unitInterval, (x.1, (s : ℝ) • x.2) ∈ W} with hTdef
  have hT : IsOpen T := by
    convert (isOpen_normalSegmentDomain hW).preimage
      ((continuous_const (y := (1 : ℝ))).prodMk continuous_id) using 1
    ext x
    simp [hTdef, unitInterval]
  have hAT : sphere (0 : Fin 1 → ℝ) 1 ×ˢ closedBall (0 : F) 1 ⊆ T := fun x hx s ↦ by
    refine hAW ⟨hx.1, mem_closedBall_zero_iff.2 ?_⟩
    rw [← prodFiberScaling_snd (fun _ ↦ (s : ℝ)), norm_prodFiberScaling_snd]
    exact (mul_le_of_le_one_left (norm_nonneg _) (unitInterval.abs_coe_le_one s)).trans
      (mem_closedBall_zero_iff.1 hx.2)
  -- On `T`, the error term `η` vanishes, since `τ` is closed on `W`.
  have hηT : ∀ l ∈ K, ∀ x ∈ T, (η l).val x = 0 := by
    intro l hl x hx
    simp only [hηdef, SmoothForm.coe_homotopyOperator, SmoothForm.coe_mpullback]
    exact homotopyOperator_mpullback_prodFiberContraction_apply_eq_zero fun s ↦ hτW l hl _ (hx s)
  -- By compactness of the cube, `T` contains the part of it where `‖u‖ > 1 - ε`.
  obtain ⟨ε, hε, hε₁, hεT⟩ : ∃ ε, 0 < ε ∧ ε < 1 ∧
      ∀ x ∈ closedBall (0 : (Fin 1 → ℝ) × F) 1, 1 - ε < ‖x.1‖ → x ∈ T := by
    have := isCompact_iff_compactSpace.1 (isCompact_closedBall (0 : (Fin 1 → ℝ) × F) 1)
    obtain ⟨δ, hδ, hδT⟩ := exists_pos_sublevel_subset_of_mem_nhdsSet
      (f := fun x : closedBall (0 : (Fin 1 → ℝ) × F) 1 ↦ 1 - ‖x.val.1‖) (by fun_prop)
      (A := {x | x.val ∈ sphere (0 : Fin 1 → ℝ) 1 ×ˢ closedBall (0 : F) 1})
      (fun x hx ↦ by
        have hx₁ := mem_closedBall_zero_iff.1 x.property
        refine sub_pos.2 (lt_of_le_of_ne ((norm_fst_le x.val).trans hx₁) fun h ↦ hx ⟨?_, ?_⟩)
        · exact mem_sphere_zero_iff_norm.2 h
        · exact mem_closedBall_zero_iff.2 ((norm_snd_le x.val).trans hx₁))
      ((hT.preimage continuous_subtypeVal).mem_nhdsSet.2 fun x hx ↦ hAT hx)
    refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), (min_le_right _ _).trans_lt (by norm_num),
      fun x hx hx₁ ↦ hδT (a := ⟨x, hx⟩) ?_⟩
    have := min_le_left δ (1 / 2)
    simp only [mem_ofPred_eq]
    linarith
  -- On the cube, the error term is bounded by `‖v‖ * C`.
  obtain ⟨C, hC⟩ := hτ.mextDeriv.exists_norm_val_le hK (isCompact_closedBall (0 : _) 1)
  have hηQ : ∀ l ∈ K, ∀ y ∈ closedBall (0 : (Fin 1 → ℝ) × F) 1,
      @norm (((Fin 1 → ℝ) × F) [⋀^Fin 2]→L[ℝ] ℝ) _ ((η l).val y) ≤ ‖y.2‖ * C := by
    intro l hl y hy
    simp only [hηdef, SmoothForm.coe_homotopyOperator, SmoothForm.coe_mpullback]
    refine norm_homotopyOperator_mpullback_prodFiberContraction_apply_le _ y fun s ↦ hC l hl _ ?_
    rw [← prodFiberScaling_snd (fun _ ↦ (s : ℝ)), ← prodFiberScaling_fst (fun _ ↦ (s : ℝ)) y]
    exact mapsTo_prodFiberScaling_closedBall (fun _ ↦ unitInterval.abs_coe_le_one s) 1 hy
  -- The nondegeneracy margin, and the width of the tube.
  obtain ⟨r, hr, hnd'⟩ := hτ.exists_pos_forall_nondegenerate hK (isCompact_closedBall _ _) hnd
  have hC₁ : 0 < |C| + 1 := by positivity
  set δ := r / (|C| + 1) with hδdef
  have hδ : 0 < δ := div_pos hr hC₁
  obtain ⟨ψ, hψ, hψpos, hψ0, hψA, hψQ, hψ1⟩ :=
    exists_cubeCompression (E := Fin 1 → ℝ) (F := F) hε hε₁ hδ
  -- The shared homotopy, along the compressions, from `τ` to `τ'`.
  have hU : IsOpen (T ∩ {x : (Fin 1 → ℝ) × F | 1 - ε / 2 < ‖x.1‖}) :=
    hT.inter (isOpen_lt continuous_const continuous_fst.norm)
  refine exists_homotopy_exact_of_isotopy hτ hr hnd' hβ'
    (e := fun q ↦ prodFiberScaling (fun u ↦ ψ (q.1.2, u)) q.2)
    (contMDiff_prodFiberScaling_family (ψ := fun q : (L × unitInterval) × (Fin 1 → ℝ) ↦
      ψ (q.1.2, q.2)) (hψ.contMDiff.comp
        ((contMDiff_subtypeVal_Icc.comp (contMDiff_snd.comp contMDiff_fst)).prodMk_space
          contMDiff_snd)))
    (fun p x ↦ (isLocalDiffeomorph_prodFiberScaling (hψ.comp (contDiff_const.prodMk contDiff_id))
      (fun u ↦ (hψpos _).1.ne')).isInvertible_mfderiv (by simp) x)
    (fun _ x ↦ hψ0 x) (fun p ↦ hψQ p.2) hU (fun x hx ↦ ⟨hAT hx, ?_⟩) (fun p x hx ↦ hψA _ x hx.2)
    (fun l hl x hx ↦ ?_) (fun l hl x hx ↦ ?_)
  · rw [mem_ofPred_eq, mem_sphere_zero_iff_norm.1 hx.1]
    linarith
  · rw [hτη, SmoothBundleForm.sub_apply, hηT l hl x hx.1, sub_zero]
  · set y := prodFiberScaling (fun u ↦ ψ (1, u)) x
    have hyQ : y ∈ closedBall (0 : (Fin 1 → ℝ) × F) 1 := hψQ _ hx
    have hηy : @norm (((Fin 1 → ℝ) × F) [⋀^Fin 2]→L[ℝ] ℝ) _ ((η l).val y) < r := by
      rcases hψ1 hx with htube | hslab
      · calc _ ≤ ‖y.2‖ * C := hηQ l hl y hyQ
          _ ≤ ‖y.2‖ * (|C| + 1) :=
            mul_le_mul_of_nonneg_left ((le_abs_self C).trans (by linarith)) (norm_nonneg _)
          _ < δ * (|C| + 1) := mul_lt_mul_of_pos_right htube hC₁
          _ = r := by rw [hδdef, div_mul_cancel₀ _ hC₁.ne']
      · rw [hηT l hl y (hεT y hyQ hslab)]
        exact (norm_zero (E := ((Fin 1 → ℝ) × F) [⋀^Fin 2]→L[ℝ] ℝ)).trans_lt hr
    -- Stated in `D [⋀^Fin 2]→L[ℝ] ℝ`, whose instances give the norm, rather than in the tangent
    -- space that the values are stated in, so that it applies; the two types agree by definition.
    have hsub (u v : ((Fin 1 → ℝ) × F) [⋀^Fin 2]→L[ℝ] ℝ) : ‖u - v - u‖ = ‖v‖ := by
      rw [sub_sub_cancel_left, norm_neg]
    rw [hτη, SmoothBundleForm.sub_apply]
    exact (hsub _ _).trans_lt hηy

end SymplecticGeometry

end
