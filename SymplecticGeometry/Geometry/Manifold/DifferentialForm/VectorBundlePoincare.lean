/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Relative.Basic
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.HomotopyOperator
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# The relative Poincaré operator at the zero section, on fibrewise star-shaped sets, for families

On the total space of a smooth vector bundle `V → B`, let `P` be Tau Ceti's relative Poincaré
operator `TauCeti.vectorBundlePoincareHomotopy`, and `ρ = 0 ∘ π` the retraction onto the zero
section. For a `C¹` form `η` of positive degree, Tau Ceti's cochain-homotopy identity
`TauCeti.mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv`
gives `d (P η) = η - ρ^* η - P (d η)`. At a zero vector `0_b`, the form `P (d η)` vanishes, and
`ρ^* η` vanishes as soon as the pullback of `η` along the zero section vanishes at `b`. So there
`d (P η) = η`, without `η` being closed (in the namespace `TauCeti`,
`mextDeriv_vectorBundlePoincareHomotopy_zeroSection_of_mpullback_zeroSection_apply_eq_zero`).
This is the pointwise form of Tau Ceti's
`TauCeti.mextDeriv_vectorBundlePoincareHomotopy_of_mpullback_zeroSection_eq_zero`, which assumes
`η` closed and gives the identity everywhere.

For a form closed only on part of the total space, the identity still holds there. If `d η`
vanishes on a set `W` that fibre scaling by every `t ∈ [0, 1]` maps into itself, then `P (d η)`
vanishes on `W`, so `d (P η) = η - ρ^* η` on `W`, and `d (P η) = η` there when `η` pulls back to
zero on the zero section. This localizes Tau Ceti's
`TauCeti.mextDeriv_vectorBundlePoincareHomotopy`.

Applied slice by slice to a family of one-forms `η_t`, the functions `P η_t` form a smooth
function of `(t, v)`, since the homotopy operator preserves smooth families
(`SymplecticGeometry.IsSmoothFamily.homotopyOperator`). This is
`TauCeti.exists_contMDiff_mextDeriv_ofFunction_eq_of_mpullback_zeroSection`.

## Main results

* `mextDeriv_vectorBundlePoincareHomotopy_zeroSection_of_mpullback_zeroSection_apply_eq_zero`:
  `d (P η) = η` at the zero vector `0_b` when the pullback of `η` along the zero section vanishes
  at `b`.
* `mextDeriv_vectorBundlePoincareHomotopy_apply_of_forall_mextDeriv_eq_zero`: `d (P η) = η - ρ^* η`
  on a set stable under fibre scaling where `d η` vanishes.
* `mextDeriv_vectorBundlePoincareHomotopy_apply_eq_of_forall_mextDeriv_eq_zero`: there
  `d (P η) = η`, when the pullback of `η` along the zero section vanishes.
* `TauCeti.exists_contMDiff_mextDeriv_ofFunction_eq_of_mpullback_zeroSection`: a smooth function
  of `(t, v)` vanishing on the zero section whose slices have differential `η_t` at the zero
  vectors where the restriction of `η_t` to the zero section vanishes.

## References

* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001Lectures], §6.2
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

open SymplecticGeometry

variable {B FV : Type*} {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V]
  [VectorBundle ℝ FV V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

/-- **The relative Poincaré operator at the zero section.** Let `η` be a `C¹` form of positive
degree on the total space of a `C²` vector bundle over a `C²` base, and let `b` be a point of the
base at which the pullback of `η` along the zero section vanishes. Then the exterior derivative
of the relative Poincaré operator of `η` equals `η` at the zero vector `0_b`. The form `η` need
not be closed. -/
theorem mextDeriv_vectorBundlePoincareHomotopy_zeroSection_of_mpullback_zeroSection_apply_eq_zero
    [IsManifold IB 2 B] [ContMDiffVectorBundle 2 FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) {b : B}
    (hb : mpullback IB (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V) η b = 0) :
    mextDeriv (vectorBundlePoincareHomotopy η) (zeroSection FV V b) = η (zeroSection FV V b) := by
  have h := congrFun
    (mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv hη)
    (zeroSection FV V b)
  rw [Pi.add_apply, vectorBundlePoincareHomotopy_zeroSection, add_zero, Pi.sub_apply,
    mpullback_zeroSection_comp_proj, mpullback_apply_eq_zero, sub_zero] at h
  · exact h
  · rwa [zeroSection_proj]

/-- **The relative Poincaré identity where the form is closed.** Let `η` be a `C¹` form of
positive degree on the total space of a `C²` vector bundle over a `C²` base, and let `W` be a set
of the total space that fibre scaling by each `t ∈ [0, 1]` maps into itself. If `d η` vanishes on
`W`, then `d (P η) = η - ρ^* η` at every point of `W`, where `P` is the relative Poincaré operator
and `ρ = 0 ∘ π` is the retraction onto the zero section. -/
theorem mextDeriv_vectorBundlePoincareHomotopy_apply_of_forall_mextDeriv_eq_zero
    [IsManifold IB 2 B] [ContMDiffVectorBundle 2 FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) {W : Set (TotalSpace FV V)}
    (hW : ∀ z ∈ W, ∀ t, vectorBundleFiberScaling FV V (z, t) ∈ W)
    (hclosed : ∀ z ∈ W, mextDeriv η z = 0) {z : TotalSpace FV V} (hz : z ∈ W) :
    mextDeriv (vectorBundlePoincareHomotopy η) z =
      η z - mpullback (IB.prod 𝓘(ℝ, FV)) (IB.prod 𝓘(ℝ, FV))
        (zeroSection FV V ∘ TotalSpace.proj) η z := by
  have h := congrFun
    (mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv hη) z
  -- `P (d η)` vanishes at `z`, since `d η` vanishes along the scaled points `t • z ∈ W`.
  have hP : vectorBundlePoincareHomotopy (mextDeriv η) z = 0 := by
    rw [vectorBundlePoincareHomotopy_def]
    refine homotopyOperator_apply_eq_zero fun t v ↦ ?_
    rw [mpullback_apply, hclosed _ (hW z hz t), ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  rwa [Pi.add_apply, hP, add_zero, Pi.sub_apply] at h

/-- **The relative Poincaré operator as a local primitive.** Let `η` be a `C¹` form of positive
degree on the total space of a `C²` vector bundle over a `C²` base whose pullback along the zero
section vanishes, and let `W` be a set of the total space that fibre scaling by each `t ∈ [0, 1]`
maps into itself. If `d η` vanishes on `W`, then `d (P η) = η` at every point of `W`, where `P`
is the relative Poincaré operator. -/
theorem mextDeriv_vectorBundlePoincareHomotopy_apply_eq_of_forall_mextDeriv_eq_zero
    [IsManifold IB 2 B] [ContMDiffVectorBundle 2 FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η)
    (hi : mpullback IB (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V) η = 0) {W : Set (TotalSpace FV V)}
    (hW : ∀ z ∈ W, ∀ t, vectorBundleFiberScaling FV V (z, t) ∈ W)
    (hclosed : ∀ z ∈ W, mextDeriv η z = 0) {z : TotalSpace FV V} (hz : z ∈ W) :
    mextDeriv (vectorBundlePoincareHomotopy η) z = η z := by
  rw [mextDeriv_vectorBundlePoincareHomotopy_apply_of_forall_mextDeriv_eq_zero hη hW hclosed hz,
    mpullback_zeroSection_comp_proj, hi, mpullback_zero, Pi.zero_apply, sub_zero]

variable [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ FV V IB]

/-- **Fibre-scaling primitives of a family of one-forms on a vector bundle.** Let `η_t`,
`t ∈ ℝ`, be the slices of a smooth one-form `η` on `ℝ × V`, for a smooth vector bundle
`V → B`. There is a smooth function `G` on `ℝ × V` that vanishes on `ℝ ×` the zero section,
such that `d G_t = η_t` at the zero vector `0_b` whenever the pullback of `η_t` along the zero
section vanishes at `b`. -/
theorem exists_contMDiff_mextDeriv_ofFunction_eq_of_mpullback_zeroSection
    (η : SmoothForm (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, FV))) (ℝ × TotalSpace FV V) F 1) :
    ∃ G : ℝ × TotalSpace FV V → F,
      ContMDiff (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, FV))) 𝓘(ℝ, F) ∞ G ∧
      (∀ t b, G (t, zeroSection FV V b) = 0) ∧
      ∀ t b, (SmoothForm.mpullback (zeroSection FV V) (contMDiff_zeroSection ℝ V)
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) η)).val b = 0 →
        mextDeriv (RoughForm.ofFunction (IB.prod 𝓘(ℝ, FV)) fun v ↦ G (t, v))
            (zeroSection FV V b) =
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) η).val
            (zeroSection FV V b) := by
  set ηt : ℝ → SmoothForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F 1 :=
    fun t ↦ SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) η
  have hH : ContMDiff ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV)) ∞
      (vectorBundleFiberScaling FV V) :=
    contMDiff_vectorBundleFiberScaling
  have hη : IsSmoothFamily 𝓘(ℝ, ℝ) ηt := isSmoothFamily_mpullback_prodMk η
  obtain ⟨Ω, hΩ⟩ := isSmoothFamily_def.mp (hη.mpullback _ hH).homotopyOperator
  -- The slice of `Ω` at `t`, as a function, is the relative Poincaré operator of `η_t`.
  have hG (t : ℝ) : RoughForm.ofFunction (IB.prod 𝓘(ℝ, FV)) (fun v ↦ Ω.val (t, v) 0) =
      vectorBundlePoincareHomotopy (ηt t).val := by
    have h := congrArg Subtype.val (hΩ t)
    rw [SmoothForm.coe_mpullback, SmoothForm.coe_homotopyOperator,
      SmoothForm.coe_mpullback] at h
    rw [vectorBundlePoincareHomotopy_def, ← h]
    funext v
    ext w
    rw [RoughForm.ofFunction_apply, mpullback_apply]
    exact congrArg (Ω.val (t, v)) (Subsingleton.elim _ _)
  refine ⟨fun p ↦ Ω.val p 0, ?_, fun t b ↦ ?_, fun t b hb ↦ ?_⟩
  · exact Ω.contMDiff_apply_zero
  · have h := congrFun (hG t) (zeroSection FV V b)
    rw [vectorBundlePoincareHomotopy_zeroSection] at h
    simpa [RoughForm.ofFunction_apply] using congrArg (· 0) h
  · rw [hG t]
    refine mextDeriv_vectorBundlePoincareHomotopy_zeroSection_of_mpullback_zeroSection_apply_eq_zero
      ((ηt t).isSmoothForm.of_le (by simp)) ?_
    rw [← SmoothForm.coe_mpullback _ (contMDiff_zeroSection ℝ V)]
    exact hb

end TauCeti

end
