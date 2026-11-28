/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Manifold.Morse.Core.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Topology
public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import SymplecticGeometry.Geometry.Manifold.DeRham.Map
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.HomotopyOperator
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.Geometry.Manifold.SmoothTransition
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
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
  `e_{s l, 1}^* α l + d (e_{s l, 1}^* B' (s l))`;
* `SymplecticGeometry.stagePath_isNondegenerate`: if the slices of `e` are local diffeomorphisms,
  `ρ` takes values in `[0, 1]`, `τ l` is nondegenerate, and the interpolations
  `τ l + r • (α l + d (B' (s l)) - τ l)`, `r ∈ [0, 1]`, are nondegenerate at `e_{s l, 1} x`
  wherever `ρ x ≠ 0`, then the path is nondegenerate at all times;
* `SymplecticGeometry.exists_mextDerivₗ_eq_endPullback_sub`: if `α l` is closed, then
  `e_{s l, 1}^* α l - α l = d γ` for a one-form `γ` that vanishes on every set fixed by all slices
  `e_{s l, t}`; it is `TauCeti.SmoothForm.exists_mextDerivₗ_eq_mpullback_sub_of_homotopy` for
  the isotopy `(x, t) ↦ e_{s l, t} x`.

Two lemmas give the regularity of the path in the parameter `(l, t)`, for a smooth family `B'`
over `S`:

* `SymplecticGeometry.isSmoothFamily_stagePath`: the path is a smooth family over `L × [0, 1]`
  when `L` is a manifold, `τ` and `α` are smooth families over `L` and `s` is smooth;
* `SymplecticGeometry.continuous_tangentEquiv_symm_stagePath`: the path is continuous into the
  frame topology of a covering frame system of the two-forms when `τ` and `α` are, `s` is
  continuous, and `M` and `S` have finite-dimensional models.

`SymplecticGeometry.exists_stagePath` builds the data `e` and `ρ` of a stage from a band core `c`
and a family `Φ` of isotopies that displaces the cubes of `c` into a region `U` where every
interpolation `τ l + r • (α l + d (B' (s l)) - τ l)`, `r ∈ [0, 1]`, is nondegenerate, for `l` in a
compact set `K`. Its isotopy first compresses `{g ≤ b}` towards `{g ≤ a}` and the cubes
(`SymplecticGeometry.BandCore.exists_compression_of_subset`), into the open set of points that
`Φ` sends into `U` for all `l ∈ K` at once, and then applies `Φ`; its cutoff is `1` near
`{g ≤ b}` and supported where the end of that isotopy lands in `U`, so that the path is
nondegenerate for every `l ∈ K` by `SymplecticGeometry.stagePath_isNondegenerate`: at each point
it is the pullback, along a local diffeomorphism, of `τ l` or of one of these interpolations.

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
    add_zero, SmoothForm.mpullback_eq_self_of_eq_id _ (funext he₀)]

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
    rw [SmoothForm.mpullback_eq_self_of_eq_id _ (funext he₀)] at hex
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

/-- The path is nondegenerate at all times for a parameter `l`, if the slices `e ((s l, t), ·)`
are local diffeomorphisms, `ρ` takes values in `[0, 1]`, `τ l` is nondegenerate, and at every
point `x` with `ρ x ≠ 0` each interpolation `τ l + r • (α l + d (B' (s l)) - τ l)`,
`r ∈ [0, 1]`, is nondegenerate at `e ((s l, 1), x)`. -/
theorem stagePath_isNondegenerate {l : Λ}
    (hed : ∀ t, IsLocalDiffeomorph I I ∞ fun x ↦ e ((s l, t), x))
    (hρI : ∀ x, ρ x ∈ Icc (0 : ℝ) 1) (hnd : (τ l).IsNondegenerate)
    (hint : ∀ x, ρ x ≠ 0 → ∀ r ∈ Icc (0 : ℝ) 1,
      ((τ l + r • (α l + mextDerivₗ I 1 (B' (s l)) - τ l)).bilinFormAt
        (e ((s l, 1), x))).Nondegenerate)
    (t : unitInterval) : (stagePath he hρ s τ α B' (l, t)).IsNondegenerate := by
  refine SmoothTwoForm.isNondegenerate_def.2 fun x ↦ ?_
  -- At `x` the path is the pullback along `e_{s l, A t}` of the form `σ`.
  set A := collaredFirstHalf (n := ∞) le_rfl
  set C := collaredSecondHalf (n := ∞) le_rfl
  set r : ℝ := (C t : ℝ) * ρ x with hr_def
  set σ := τ l + r • (α l + mextDerivₗ I 1 (B' (s l)) - τ l) with hσ_def
  have hAC (h : (C t : ℝ) ≠ 0) : A t = 1 :=
    collaredFirstHalf_eq_one_of_collaredSecondHalf_ne_zero le_rfl
      fun h' ↦ h (by rw [h', Set.Icc.coe_zero])
  have hval : (SmoothForm.mpullback (fun x ↦ e ((s l, A t), x))
      (he.comp (contMDiff_const.prodMk contMDiff_id)) σ).val x =
      (stagePath he hρ s τ α B' (l, t)).val x := by
    rw [stagePath_apply]
    rcases eq_or_ne (C t : ℝ) 0 with h0 | h0
    · have hr0 : r = 0 := by rw [hr_def, h0, zero_mul]
      rw [hσ_def, hr0, zero_smul, add_zero]
      simp only [A, C, h0, zero_mul, zero_smul, add_zero]
    · have hA := hAC h0
      simp only [A] at hA ⊢
      simp only [hA, hσ_def, hr_def, map_add, map_smul, SmoothBundleForm.add_apply,
        SmoothBundleForm.smul_apply, map_sub, SmoothBundleForm.sub_apply]
      abel
  have hpull : mpullback I I (fun x ↦ e ((s l, A t), x)) σ.val x =
      (stagePath he hρ s τ α B' (l, t)).val x := by
    rw [← hval, SmoothForm.coe_mpullback]
  refine (SmoothTwoForm.nondegenerate_bilinFormAt_iff_of_isInvertible_mfderiv
    ((hed (A t) x).isInvertible_mfderiv (by simp)) hpull).1 ?_
  by_cases hr : r = 0
  · rw [hσ_def, hr, zero_smul, add_zero]
    exact SmoothTwoForm.isNondegenerate_def.1 hnd _
  -- Otherwise `C t ≠ 0`, so `A t = 1`, and `ρ x ≠ 0`.
  rw [hAC (left_ne_zero_of_mul hr)]
  exact hint x (right_ne_zero_of_mul hr) r (unitInterval.mul_mem (C t).property (hρI x))

/-- The moved closed form differs from `α l` by an exact form whose primitive vanishes on `V`: for
an isotopy starting at the identity whose slices `e ((s l, t), ·)` fix a set `V`, and a closed
form `α l`, there is a one-form `γ` with `d γ = e₁^* α l - α l` and `γ = 0` on `V`, for the end
`e₁ := e ((s l, 1), ·)` of the isotopy. It is the case of the isotopy `(x, t) ↦ e ((s l, t), x)`
of `TauCeti.SmoothForm.exists_mextDerivₗ_eq_mpullback_sub_of_homotopy`. -/
theorem exists_mextDerivₗ_eq_endPullback_sub {l : Λ} (he₀ : ∀ x, e ((s l, 0), x) = x)
    (hα : mextDerivₗ I 2 (α l) = 0) {V : Set M} (heV : ∀ t, ∀ x ∈ V, e ((s l, t), x) = x) :
    ∃ γ : SmoothForm I M ℝ 1,
      mextDerivₗ I 1 γ = SmoothForm.mpullback (fun x ↦ e ((s l, 1), x))
          (he.comp (contMDiff_const.prodMk contMDiff_id)) (α l) - α l ∧
        ∀ x ∈ V, γ.val x = 0 := by
  obtain ⟨γ, hγ, hγ0⟩ := SmoothForm.exists_mextDerivₗ_eq_mpullback_sub_of_homotopy
    (f := fun x ↦ e ((s l, 1), x)) (Φ := fun p ↦ e ((s l, p.2), p.1))
    (he.comp (contMDiff_const.prodMk contMDiff_id))
    (he.comp ((contMDiff_const.prodMk contMDiff_snd).prodMk contMDiff_fst)) he₀ (fun _ ↦ rfl) hα
  exact ⟨γ, hγ, fun x hx ↦ hγ0 x fun t ↦ heV t x hx⟩

section Smooth

variable {EL HL L : Type*} [NormedAddCommGroup EL] [NormedSpace ℝ EL] [TopologicalSpace HL]
  {J : ModelWithCorners ℝ EL HL} [TopologicalSpace L] [ChartedSpace HL L] [IsManifold J ∞ L]

/-- The path of a stage is a smooth family over `L × [0, 1]`, for a manifold `L` of parameters,
when `τ` and `α` are smooth families over `L`, `B'` is a smooth family over `S` and `s : L → S`
is smooth. -/
theorem isSmoothFamily_stagePath {e : (S × unitInterval) × M → M}
    (he : ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ e) {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) {s : L → S} (hs : ContMDiff J 𝓘(ℝ, S) ∞ s)
    {τ α : L → SmoothTwoForm I M} (hτ : IsSmoothFamily J τ)
    (hα : IsSmoothFamily J α) {B' : S → SmoothForm I M ℝ 1}
    (hB' : IsSmoothFamily 𝓘(ℝ, S) B') :
    IsSmoothFamily (J.prod (𝓡∂ 1)) (stagePath he hρ s τ α B') := by
  have hA := (collaredFirstHalf (n := ∞) le_rfl).contMDiff
  have hC : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ fun t ↦ (collaredSecondHalf (n := ∞) le_rfl t : ℝ) :=
    contMDiff_subtypeVal_Icc.comp (collaredSecondHalf (n := ∞) le_rfl).contMDiff
  have hs' : ContMDiff (J.prod (𝓡∂ 1)) 𝓘(ℝ, S) ∞ fun p : L × unitInterval ↦ s p.1 :=
    hs.comp contMDiff_fst
  -- The first term: `τ l` pulled back along the isotopy run at the speed `A`.
  have h₁ := (hτ.comp Prod.fst contMDiff_fst).mpullback_family
    (f := fun q : (L × unitInterval) × M ↦
      e ((s q.1.1, collaredFirstHalf (n := ∞) le_rfl q.1.2), q.2))
    (he.comp (((hs'.comp contMDiff_fst).prodMk
      (hA.comp (contMDiff_snd.comp contMDiff_fst))).prodMk contMDiff_snd))
  -- The second term: the correction pulled back along the end of the isotopy, cut off by `ρ`.
  have h₂ := ((((hα.comp Prod.fst contMDiff_fst).add
      (hB'.mextDeriv.comp (fun p : L × unitInterval ↦ s p.1) hs')).sub
      (hτ.comp Prod.fst contMDiff_fst)).mpullback_family
    (f := fun q : (L × unitInterval) × M ↦ e ((s q.1.1, 1), q.2))
    (he.comp (((hs'.comp contMDiff_fst).prodMk contMDiff_const).prodMk
      contMDiff_snd))).funSMul ⟨ρ, hρ⟩ |>.fun_smul (hC.comp contMDiff_snd)
  convert h₁.add h₂ using 1
  exact funext (stagePath_def he hρ s τ α B')

end Smooth

section Continuous

open _root_.Bundle

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ S] [TopologicalSpace Λ] {ι : Type*}
  (fr : ι → Trivialization (E [⋀^Fin 2]→L[ℝ] ℝ)
    (π (E [⋀^Fin 2]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x)))
  [∀ j, MemTrivializationAtlas (fr j)]
  (W : ι → TopologicalSpace.Opens M) (hW : ∀ j, (W j : Set M) ⊆ (fr j).baseSet)

/-- The path of a stage is continuous into the frame topology of a covering frame system of the
two-forms on `M`, when `M` and `S` have finite-dimensional models, `τ` and `α` are continuous into
that topology, `s : Λ → S` is continuous and `B'` is a smooth family over `S`. -/
theorem continuous_tangentEquiv_symm_stagePath (hcover : ∀ x, ∃ j, x ∈ W j)
    {e : (S × unitInterval) × M → M}
    (he : ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ e) {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) {s : Λ → S} (hs : Continuous s)
    {τ α : Λ → SmoothTwoForm I M}
    (hτ : let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
      Continuous fun l ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (τ l))
    (hα : let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
      Continuous fun l ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (α l))
    {B' : S → SmoothForm I M ℝ 1} (hB' : IsSmoothFamily 𝓘(ℝ, S) B') :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
    Continuous fun p ↦ Bundle.ContMDiffTwoForm.tangentEquiv.symm (stagePath he hρ s τ α B' p) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
  let _ := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
  let _ := ContMDiffSection.continuousSMul_frameTopology (𝕜 := ℝ) (I := I)
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) fr W hW
  let F : C^∞⟮(𝓘(ℝ, S).prod (𝓡∂ 1)).prod I, (S × unitInterval) × M; I, M⟯ := ⟨e, he⟩
  have hT := Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_mpullback_prod fr W hW fr W hW
    F hcover
  have hA := (collaredFirstHalf (n := ∞) le_rfl).contMDiff.continuous
  have hC : Continuous fun t ↦ (collaredSecondHalf (n := ∞) le_rfl t : ℝ) :=
    continuous_subtypeVal.comp (collaredSecondHalf (n := ∞) le_rfl).contMDiff.continuous
  -- The first term, `τ l` pulled back along the isotopy run at the speed `A`.
  have h₁ := hT.comp ((hτ.comp continuous_fst).prodMk
    ((hs.comp continuous_fst).prodMk (hA.comp continuous_snd)))
  -- The correction `α l - τ l + d (B' (s l))`, pulled back along the end of the isotopy.
  have h₂ := hT.comp (((hα.sub hτ).comp continuous_fst).prodMk
    ((hs.comp continuous_fst).prodMk
      (continuous_const (X := Λ × unitInterval) (y := (1 : unitInterval)))))
  have he₁ : ContMDiff (𝓘(ℝ, S).prod I) I ∞ fun q : S × M ↦ e ((q.1, 1), q.2) :=
    he.comp ((contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd)
  have h₃ := ((hB'.mextDeriv.mpullback_family he₁).continuous_tangentEquiv_symm fr W hW).comp
    (hs.comp (continuous_fst (X := Λ) (Y := unitInterval)))
  refine (h₁.add ((hC.comp continuous_snd).smul
    ((Bundle.ContMDiffTwoForm.continuous_tangentEquiv_symm_smul fr W hW ⟨ρ, hρ⟩).comp
      (h₂.add h₃)))).congr fun p ↦ ?_
  simp only [Pi.add_apply, Pi.smul_apply', Pi.sub_apply, Function.comp_apply, stagePath_def,
    map_add, map_sub, map_smul, LinearEquiv.apply_symm_apply, F, ContMDiffMap.coeFn_mk]
  abel_nf

end Continuous

section Exists

variable [FiniteDimensional ℝ E] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace Λ] {g : M → ℝ} {a₀ a b : ℝ}

/-- **The isotopy and cutoff of a stage.** Let `c` be a band core of a continuous `g` for the
levels `a₀`, `a`, `b`, let `K ⊆ Λ` be compact, `s : Λ → S` continuous, and `τ l` nondegenerate for
`l ∈ K`. Let `Φ : (S × [0, 1]) × M → M` be a smooth family of isotopies from the identity by local
diffeomorphisms, fixing an open set `N₁ ⊇ {g ≤ a}`. Let `U ⊆ Λ × M` be open, containing
`K × N₁` and the points `(l, Φ ((s l, 1), y))` for `l ∈ K` and `y` in the cubes of `c`, such that
for `(l, x) ∈ U` with `l ∈ K` and `r ∈ [0, 1]` the form `τ l + r • (α l + d (B' (s l)) - τ l)` is
nondegenerate at `x`.

Then there are a smooth family `e` of isotopies from the identity by local diffeomorphisms, a
smooth `ρ : M → [0, 1]`, an open neighbourhood `V ⊆ N₁` of `{g ≤ a}` fixed by every slice of `e`,
and an open `N' ⊇ {g ≤ b}` on which `ρ = 1`, such that `stagePath (l, t)` is nondegenerate for
`l ∈ K` and every `t`. -/
theorem exists_stagePath (c : BandCore I g a₀ a b) (hg : Continuous g) {K : Set Λ}
    (hK : IsCompact K) {s : Λ → S} (hs : Continuous s) {τ α : Λ → SmoothTwoForm I M}
    (hnd : ∀ l ∈ K, (τ l).IsNondegenerate) {B' : S → SmoothForm I M ℝ 1}
    {Φ : (S × unitInterval) × M → M} (hΦ : ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ Φ)
    (hΦd : ∀ p, IsLocalDiffeomorph I I ∞ fun x ↦ Φ (p, x)) (hΦ₀ : ∀ q x, Φ ((q, 0), x) = x)
    {N₁ : Set M} (hN₁ : IsOpen N₁) (haN₁ : {x | g x ≤ a} ⊆ N₁)
    (hΦN₁ : ∀ p, ∀ x ∈ N₁, Φ (p, x) = x)
    {U : Set (Λ × M)} (hU : IsOpen U) (hKN₁ : K ×ˢ N₁ ⊆ U)
    (hUc : ∀ l ∈ K, ∀ y ∈ c.cubes, (l, Φ ((s l, 1), y)) ∈ U)
    (hUnd : ∀ p ∈ U, p.1 ∈ K → ∀ r ∈ Icc (0 : ℝ) 1,
      ((τ p.1 + r • (α p.1 + mextDerivₗ I 1 (B' (s p.1)) - τ p.1)).bilinFormAt
        p.2).Nondegenerate) :
    ∃ (e : (S × unitInterval) × M → M) (he : ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ e)
      (ρ : M → ℝ) (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (V N' : Set M),
      (∀ p, IsLocalDiffeomorph I I ∞ fun x ↦ e (p, x)) ∧ (∀ q x, e ((q, 0), x) = x) ∧
      IsOpen V ∧ V ∈ 𝓝ˢ {x | g x ≤ a} ∧ V ⊆ N₁ ∧ (∀ p, ∀ x ∈ V, e (p, x) = x) ∧
      IsOpen N' ∧ {x | g x ≤ b} ⊆ N' ∧ (∀ x, ρ x ∈ Icc (0 : ℝ) 1) ∧ (∀ x ∈ N', ρ x = 1) ∧
      ∀ l ∈ K, ∀ t, (stagePath he hρ s τ α B' (l, t)).IsNondegenerate := by
  -- The points sent into `U` over all of `K` by a continuous family of maps form an open set.
  have hopen (h : Λ × M → M) (hh : Continuous h) : IsOpen {x | ∀ l ∈ K, (l, h (l, x)) ∈ U} :=
    isOpen_iff_mem_nhds.2 fun x hx ↦ hK.eventually_forall_of_forall_eventually
      (P := fun x l ↦ (l, h (l, x)) ∈ U) fun l hl ↦
        ((continuous_snd.prodMk (hh.comp (continuous_snd.prodMk continuous_fst))).continuousAt
          (x := (x, l))).preimage_mem_nhds (hU.mem_nhds (hx l hl))
  -- Step 1: the open set to compress into.
  set W := {x | ∀ l ∈ K, (l, Φ ((s l, 1), x)) ∈ U}
  have hW : IsOpen W := hopen (fun p ↦ Φ ((s p.1, 1), p.2))
    (hΦ.continuous.comp (((hs.comp continuous_fst).prodMk continuous_const).prodMk
      continuous_snd))
  have haW : {x | g x ≤ a} ∪ c.cubes ⊆ W := by
    rintro x (hx | hx) l hl
    · rw [hΦN₁ _ x (haN₁ hx)]
      exact hKN₁ ⟨hl, haN₁ hx⟩
    · exact hUc l hl x hx
  -- Step 2: the compression.
  obtain ⟨f, F, ⟨V₀, hV₀, hFV₀⟩, hfW⟩ := c.exists_compression_of_subset hW haW
  -- Step 3: the isotopy of the stage, the compression followed by the displacement.
  set e : (S × unitInterval) × M → M := fun p ↦ Φ (p.1, F (p.1.2, p.2)) with he_def
  have he : ContMDiff ((𝓘(ℝ, S).prod (𝓡∂ 1)).prod I) I ∞ e :=
    hΦ.comp (contMDiff_fst.prodMk
      (F.contMDiff.comp ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd)))
  have hed (p : S × unitInterval) : IsLocalDiffeomorph I I ∞ fun x ↦ e (p, x) :=
    fun x ↦ IsLocalDiffeomorphAt.comp I M
      ((F.isSmoothEmbedding p.2).isImmersion.isLocalDiffeomorph rfl (by simp) x) (hΦd p _)
  have he₁ (q : S) (x : M) : e ((q, 1), x) = Φ ((q, 1), f x) := by
    simp only [he_def, SmoothIsotopy.apply_one]
  -- Step 4: the cutoff, supported where the end of the isotopy sends every `l ∈ K` into `U`.
  set W₁ := {x | ∀ l ∈ K, (l, e ((s l, 1), x)) ∈ U}
  have hW₁ : IsOpen W₁ := hopen (fun p ↦ e ((s p.1, 1), p.2))
    (he.continuous.comp (((hs.comp continuous_fst).prodMk continuous_const).prodMk
      continuous_snd))
  have hbW₁ : {x | g x ≤ b} ⊆ W₁ := fun x hx l hl ↦ by
    rw [he₁]
    exact hfW hx l hl
  obtain ⟨θ, hθW₁, hθ₁, hθI⟩ :=
    (isClosed_le hg continuous_const).exists_contMDiffMap_tsupport_subset_eventually_eq_one I hW₁
      hbW₁
  obtain ⟨N', hN', hbN', hθN'⟩ := eventually_nhdsSet_iff_exists.1 hθ₁
  refine ⟨e, he, θ, θ.contMDiff, interior V₀ ∩ N₁, N', hed, fun q x ↦ ?_, isOpen_interior.inter hN₁,
    inter_mem (isOpen_interior.mem_nhdsSet.2 (subset_interior_iff_mem_nhdsSet.2 hV₀))
      (hN₁.mem_nhdsSet.2 haN₁), inter_subset_right, fun p x hx ↦ ?_, hN', hbN', hθI, hθN',
    fun l hl t ↦ ?_⟩
  · simp only [he_def, SmoothIsotopy.apply_zero, ContMDiffMap.id_apply, hΦ₀]
  · simp only [he_def, hFV₀ _ x (interior_subset hx.1), hΦN₁ _ x hx.2]
  -- Step 5: nondegeneracy, where `θ x ≠ 0` puts `x` in `W₁`.
  exact stagePath_isNondegenerate he θ.contMDiff s τ α B' (fun t ↦ hed (s l, t)) hθI (hnd l hl)
    (fun x hx r hr ↦ hUnd (l, e ((s l, 1), x)) (hθW₁ (subset_tsupport _ hx) l hl) hl r hr) t

end Exists

end SymplecticGeometry

end
