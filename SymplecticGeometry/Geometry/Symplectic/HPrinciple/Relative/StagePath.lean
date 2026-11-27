/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.TwoForm.Basic
import SymplecticGeometry.Geometry.Manifold.DeRham.Map
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The path of a stage of the relative h-principle

A stage of the parametric relative h-principle deforms a family of two-forms `τ l` on `M`, with
closed forms `α l` and one-forms `β l` such that `τ l = α l + d β l` near a sublevel set. Its path
is given by an explicit formula. Let `e : (S × [0, 1]) × M → M` be smooth, with slices
`e_{q, t} := e ((q, t), ·)`, let `s : Λ → S`, let `B'` be a family of one-forms over `S` and let
`ρ : M → ℝ` be a smooth cutoff. With the smooth time steps `A := TauCeti.collaredFirstHalf` and
`C := TauCeti.collaredSecondHalf` (`C` leaves `0` only once `A` has reached `1`),

  `stagePath (l, t) = e_{s l, A t}^* τ l + C t • ρ • e_{s l, 1}^* (α l + d (B' (s l)) - τ l)`.

The path first moves `τ l` by the isotopy, then interpolates, where `ρ = 1`, towards
`e_{s l, 1}^* (α l + d (B' (s l)))`.

This file defines the path and reads off its formula the properties that a stage needs, one
parameter `l` at a time:

* `SymplecticGeometry.stagePath_zero`: at time `0` the path is `τ l`;
* `SymplecticGeometry.stagePath_one_eqOn`: at time `1`, where `ρ = 1`, the path is
  `e_{s l, 1}^* α l + d (e_{s l, 1}^* B' (s l))`;
* `SymplecticGeometry.stagePath_eqOn_nhdsSet`: on an open set fixed by the isotopy on which
  `τ l = α l + d (B (s l))` and `B' (s l) = B (s l)`, the path is constant, and the moved forms
  `e_{s l, 1}^* α l` and `e_{s l, 1}^* B' (s l)` are `α l` and `B (s l)`;
* `SymplecticGeometry.stagePath_of_mem`: if `α l` is closed and `τ l = α l + d (B' (s l))` on all
  of `M`, then the path runs through closed forms cohomologous to `α l` and ends at
  `e_{s l, 1}^* α l + d (e_{s l, 1}^* B' (s l))`.

The time steps are those of `SymplecticGeometry.exists_homotopy_exact_of_isotopy`
(`HandleCore/Homotopy.lean`), which uses the same isotopy-then-interpolation scheme. The family
of two-forms is called `τ` here, as in that file, since `ω` is notation in the scope `ContDiff`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-principle*][EliashbergMishachev2002],
  §10.2.
-/

public section

open Set Filter TauCeti
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {Λ S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The path of a stage of the relative h-principle: for the smooth time steps
`A := TauCeti.collaredFirstHalf` and `C := TauCeti.collaredSecondHalf` and the slices
`e_{q, t} := e ((q, t), ·)`,

  `stagePath (l, t) = e_{s l, A t}^* τ l + C t • ρ • e_{s l, 1}^* (α l + d (B' (s l)) - τ l)`. -/
noncomputable def stagePath {e : (S × unitInterval) × M → M}
    (he : ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ e) {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (s : Λ → S) (τ α : Λ → SmoothTwoForm I M)
    (B' : S → SmoothForm I M ℝ 1) (p : Λ × unitInterval) : SmoothTwoForm I M :=
  SmoothForm.mpullback (fun x ↦ e ((s p.1, collaredFirstHalf (n := ∞) le_rfl p.2), x))
      (he.comp (contMDiff_const.prodMk contMDiff_id)) (τ p.1) +
    (collaredSecondHalf (n := ∞) le_rfl p.2 : ℝ) • SmoothForm.funSMulₗ ⟨ρ, hρ⟩
      (SmoothForm.mpullback (fun x ↦ e ((s p.1, 1), x))
        (he.comp (contMDiff_const.prodMk contMDiff_id))
        (α p.1 + mextDerivₗ I 1 (B' (s p.1)) - τ p.1))

variable {e : (S × unitInterval) × M → M}
  (he : ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ e) {ρ : M → ℝ}
  (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (s : Λ → S) (τ α : Λ → SmoothTwoForm I M)
  (B' : S → SmoothForm I M ℝ 1)

/-- The definition of `SymplecticGeometry.stagePath`. -/
theorem stagePath_def (p : Λ × unitInterval) :
    stagePath he hρ s τ α B' p =
      SmoothForm.mpullback (fun x ↦ e ((s p.1, collaredFirstHalf (n := ∞) le_rfl p.2), x))
          (he.comp (contMDiff_const.prodMk contMDiff_id)) (τ p.1) +
        (collaredSecondHalf (n := ∞) le_rfl p.2 : ℝ) • SmoothForm.funSMulₗ ⟨ρ, hρ⟩
          (SmoothForm.mpullback (fun x ↦ e ((s p.1, 1), x))
            (he.comp (contMDiff_const.prodMk contMDiff_id))
            (α p.1 + mextDerivₗ I 1 (B' (s p.1)) - τ p.1)) :=
  (rfl)

/-- The value of the path at a point. -/
theorem stagePath_apply (p : Λ × unitInterval) (x : M) :
    (stagePath he hρ s τ α B' p).val x =
      (SmoothForm.mpullback (fun x ↦ e ((s p.1, collaredFirstHalf (n := ∞) le_rfl p.2), x))
          (he.comp (contMDiff_const.prodMk contMDiff_id)) (τ p.1)).val x +
        ((collaredSecondHalf (n := ∞) le_rfl p.2 : ℝ) * ρ x) •
          (SmoothForm.mpullback (fun x ↦ e ((s p.1, 1), x))
            (he.comp (contMDiff_const.prodMk contMDiff_id))
            (α p.1 + mextDerivₗ I 1 (B' (s p.1)) - τ p.1)).val x := by
  rw [stagePath_def, SmoothForm.add_toRoughForm, Pi.add_apply, SetLike.val_smul, Pi.smul_apply,
    mul_smul]
  -- `rw` does not see through the bundling of `ρ` as a smooth map, which `exact` unfolds.
  exact congrArg (_ + _ • ·) (congrFun (SmoothForm.coe_funSMulₗ _ _) x)

/-- At time `0` the path is `τ l`, when the isotopy starts at the identity. -/
theorem stagePath_zero {l : Λ} (he₀ : ∀ x, e ((s l, 0), x) = x) :
    stagePath he hρ s τ α B' (l, 0) = τ l := by
  rw [stagePath_def, collaredFirstHalf_zero, collaredSecondHalf_zero, Set.Icc.coe_zero, zero_smul,
    add_zero, SmoothForm.mpullback_congr _ contMDiff_id (funext he₀),
    SmoothForm.mpullback_id, LinearMap.id_apply]

/-- At time `1`, on a set where `ρ = 1`, the path is `e₁^* α l + d (e₁^* B' (s l))`, for the end
`e₁ := e ((s l, 1), ·)` of the isotopy. -/
theorem stagePath_one_eqOn {N' : Set M} (hρN' : ∀ x ∈ N', ρ x = 1) (l : Λ) :
    ∀ x ∈ N', (stagePath he hρ s τ α B' (l, 1)).val x =
      (SmoothForm.mpullback (fun x ↦ e ((s l, 1), x))
          (he.comp (contMDiff_const.prodMk contMDiff_id)) (α l) +
        mextDerivₗ I 1 (SmoothForm.mpullback (fun x ↦ e ((s l, 1), x))
          (he.comp (contMDiff_const.prodMk contMDiff_id)) (B' (s l)))).val x := by
  intro x hx
  rw [stagePath_apply, collaredFirstHalf_one, collaredSecondHalf_one, Set.Icc.coe_one,
    hρN' x hx, one_mul, one_smul, ← Pi.add_apply, ← SmoothForm.add_toRoughForm, ← map_add,
    add_sub_cancel, SmoothForm.mextDerivₗ_mpullback, ← map_add]

/-- On an open set `V` that every slice `e ((s l, t), ·)` fixes, and on which
`τ l = α l + d (B (s l))` and `B' (s l) = B (s l)`, the path is constant in time, equal to `τ l`,
and the moved forms `e₁^* α l` and `e₁^* B' (s l)` are `α l` and `B (s l)`, for the end
`e₁ := e ((s l, 1), ·)` of the isotopy. -/
theorem stagePath_eqOn_nhdsSet {l : Λ} {V : Set M} (hV : IsOpen V)
    (heV : ∀ t, ∀ x ∈ V, e ((s l, t), x) = x) {B : S → SmoothForm I M ℝ 1}
    (hB'V : ∀ x ∈ V, (B' (s l)).val x = (B (s l)).val x)
    (hτV : ∀ x ∈ V, (τ l).val x = (α l + mextDerivₗ I 1 (B (s l))).val x) :
    (∀ t, ∀ x ∈ V, (stagePath he hρ s τ α B' (l, t)).val x = (τ l).val x) ∧
      (∀ x ∈ V, (SmoothForm.mpullback (fun x ↦ e ((s l, 1), x))
        (he.comp (contMDiff_const.prodMk contMDiff_id)) (α l)).val x = (α l).val x) ∧
      ∀ x ∈ V, (SmoothForm.mpullback (fun x ↦ e ((s l, 1), x))
        (he.comp (contMDiff_const.prodMk contMDiff_id)) (B' (s l))).val x =
          (B (s l)).val x := by
  -- A slice of `e` fixes `V`, which is open, so pullback along it does not change a form there.
  have hid (t : unitInterval) {k : ℕ} (θ : SmoothForm I M ℝ k) {x : M} (hx : x ∈ V) :
      (SmoothForm.mpullback (fun x ↦ e ((s l, t), x))
        (he.comp (contMDiff_const.prodMk contMDiff_id)) θ).val x = θ.val x :=
    SmoothForm.mpullback_apply_eq_self_of_eventuallyEq_id _
      (eventually_of_mem (hV.mem_nhds hx) (heV t)) θ
  refine ⟨fun t x hx ↦ ?_, fun x hx ↦ hid 1 _ hx, fun x hx ↦ (hid 1 _ hx).trans (hB'V x hx)⟩
  -- `d (B' (s l)) = d (B (s l))` on the open set `V`, so the correction vanishes there.
  have hd : (mextDerivₗ I 1 (B' (s l))).val x = (mextDerivₗ I 1 (B (s l))).val x := by
    rw [mextDerivₗ_apply, mextDerivₗ_apply]
    exact mextDeriv_congr_of_eventuallyEq (eventually_of_mem (hV.mem_nhds hx) hB'V)
  rw [stagePath_apply]
  dsimp only
  rw [hid _ _ hx, hid 1 _ hx, SmoothBundleForm.sub_apply, SmoothBundleForm.add_apply, hd,
    ← SmoothBundleForm.add_apply, ← hτV x hx, sub_self, smul_zero, add_zero]

/-- For a parameter `l` with `τ l = α l + d (B' (s l))` on all of `M` and `α l` closed, and an
isotopy starting at the identity, the path runs through closed forms cohomologous to `α l`, and
ends at `e₁^* α l + d (e₁^* B' (s l))`, for the end `e₁ := e ((s l, 1), ·)` of the isotopy. -/
theorem stagePath_of_mem {l : Λ} (he₀ : ∀ x, e ((s l, 0), x) = x)
    (hα : mextDerivₗ I 2 (α l) = 0) (hτ : τ l = α l + mextDerivₗ I 1 (B' (s l))) :
    (∀ t, mextDerivₗ I 2 (stagePath he hρ s τ α B' (l, t)) = 0 ∧
        stagePath he hρ s τ α B' (l, t) - α l ∈ exactForms I M 2) ∧
      stagePath he hρ s τ α B' (l, 1) =
        SmoothForm.mpullback (fun x ↦ e ((s l, 1), x))
            (he.comp (contMDiff_const.prodMk contMDiff_id)) (α l) +
          mextDerivₗ I 1 (SmoothForm.mpullback (fun x ↦ e ((s l, 1), x))
            (he.comp (contMDiff_const.prodMk contMDiff_id)) (B' (s l))) := by
  -- The correction vanishes, so the path is the pullback of `τ l` along the isotopy.
  have hpath (t : unitInterval) : stagePath he hρ s τ α B' (l, t) =
      SmoothForm.mpullback (fun x ↦ e ((s l, collaredFirstHalf (n := ∞) le_rfl t), x))
        (he.comp (contMDiff_const.prodMk contMDiff_id)) (τ l) := by
    rw [stagePath_def, ← hτ, sub_self, map_zero, map_zero, smul_zero, add_zero]
  have hτc : τ l ∈ closedForms I M 2 :=
    hτ ▸ add_mem ((mem_closedForms_iff_mextDerivₗ_eq_zero I _).2 hα)
      (mextDerivₗ_mem_closedForms I 1 _)
  refine ⟨fun t ↦ ⟨?_, ?_⟩, ?_⟩
  · rw [hpath, ← mem_closedForms_iff_mextDerivₗ_eq_zero]
    exact SmoothForm.mpullback_mem_closedForms _ _ hτc
  · -- `τ l - e_{A t}^* τ l` is exact along the isotopy, and `τ l - α l = d (B' (s l))`.
    have hex := SmoothForm.mpullback_slice_zero_sub_mpullback_slice_mem_exactForms
      (F := fun q : unitInterval × M ↦ e ((s l, q.1), q.2))
      (he.comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd))
      (collaredFirstHalf (n := ∞) le_rfl t) hτc
    rw [SmoothForm.mpullback_congr _ contMDiff_id (funext he₀), SmoothForm.mpullback_id,
      LinearMap.id_apply] at hex
    have hsplit : stagePath he hρ s τ α B' (l, t) - α l =
        -(τ l - SmoothForm.mpullback (fun x ↦ e ((s l, collaredFirstHalf (n := ∞) le_rfl t), x))
          (he.comp (contMDiff_const.prodMk contMDiff_id)) (τ l)) +
        mextDerivₗ I 1 (B' (s l)) := by
      rw [hpath]
      nth_rw 2 [hτ]
      abel
    rw [hsplit]
    refine add_mem (neg_mem hex) ?_
    rw [exactForms_succ]
    exact LinearMap.mem_range_self _ _
  · rw [hpath, collaredFirstHalf_one, hτ, map_add, SmoothForm.mextDerivₗ_mpullback]

end SymplecticGeometry

end
