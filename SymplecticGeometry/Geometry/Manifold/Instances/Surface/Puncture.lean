/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.Genus
public import SymplecticGeometry.Geometry.Manifold.Diffeomorph.NestedOpens
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.Restrict
import TauCeti.Geometry.Manifold.Connected

/-!
# Punctures of the closed surface of genus `g`

Write `cⱼ = ClosedSurface.ball g j 0` for the centre of the `j`-th coordinate ball of the closed
surface of genus `g`. This file defines the open sets over which an induction on the genus
computes the fundamental groups of the punctured closed surfaces:

* `ClosedSurface.puncture g n`, the complement of `c₀, …, cₙ₋₁`;
* `ClosedSurface.tailPuncture g n`, the complement of `c₁, …, cₙ`, which contains the whole
  ball `0`.

Since the surface of genus `g + 1` is the connected sum of the torus with the surface of genus
`g` along its ball `0`, and its ball `j` is the ball `j + 1` of genus `g`
(`ClosedSurface.succDiffeomorph_ball`), removing `n` centres from the surface of genus `g + 1`
removes the centres `c₁, …, cₙ` from the second summand. In the language of
`TauCeti.ConnectedSum.restrictRightHomeomorph`, whose target is the open set
`range inl ∪ inr '' U` of the connected sum, this says that `puncture (g + 1) n` is that target
for `U = tailPuncture g n` (`ClosedSurface.image_succDiffeomorph_puncture`), and the punctured
second summand of the sum of the torus with `U` is `puncture g (n + 1)`
(`ClosedSurface.imageVal_puncture_codRestrict_ball`).

All these sets are complements of finite sets in a connected surface, so they are path
connected, by Tau Ceti's `TauCeti.isPathConnected_compl_of_finite_of_one_lt_rank`.

## Main definitions

* `SymplecticGeometry.ClosedSurface.puncture g n`: the closed surface of genus `g` with the
  centres of the balls `0, …, n - 1` removed.
* `SymplecticGeometry.ClosedSurface.tailPuncture g n`: the closed surface of genus `g` with the
  centres of the balls `1, …, n` removed.

## Main results

* `SymplecticGeometry.ClosedSurface.puncture_zero`, `SymplecticGeometry.ClosedSurface.puncture_one`:
  no puncture is the whole surface, and one puncture is Tau Ceti's
  `TauCeti.ConnectedSum.puncture` of the ball `0`.
* `SymplecticGeometry.ClosedSurface.isPathConnected_puncture`,
  `SymplecticGeometry.ClosedSurface.isPathConnected_tailPuncture`: both are path connected.
* `SymplecticGeometry.ClosedSurface.image_succDiffeomorph_puncture`: `puncture (g + 1) n` is the
  part of the connected sum made of the punctured torus and the points of `tailPuncture g n`.
* `SymplecticGeometry.ClosedSurface.imageVal_puncture_codRestrict_ball`: the punctured second
  summand of the connected sum of the torus with `tailPuncture g n` is `puncture g (n + 1)`.

## References

* [A. A. Kosinski, *Differential Manifolds*][Kosinski1993] (connected sums of manifolds).
-/

public section

noncomputable section

open Set Function Topology TopologicalSpace TauCeti

namespace SymplecticGeometry.ClosedSurface

variable (g n : ℕ)

/-- The closed surface of genus `g` with the centres `ball g j 0` of its balls `j < n` removed,
as an open subset. -/
def puncture : Opens (ClosedSurface g) :=
  ⟨((fun j ↦ ball g j 0) '' Iio n)ᶜ, ((finite_Iio n).image _).isClosed.isOpen_compl⟩

/-- The closed surface of genus `g` with the centres `ball g (j + 1) 0` of its balls
`1, …, n` removed, as an open subset. It contains the ball `0`
(`ClosedSurface.ball_zero_mem_tailPuncture`). -/
def tailPuncture : Opens (ClosedSurface g) :=
  ⟨((fun j ↦ ball g (j + 1) 0) '' Iio n)ᶜ, ((finite_Iio n).image _).isClosed.isOpen_compl⟩

theorem coe_puncture : (puncture g n : Set (ClosedSurface g)) = ((fun j ↦ ball g j 0) '' Iio n)ᶜ :=
  (rfl)

theorem coe_tailPuncture :
    (tailPuncture g n : Set (ClosedSurface g)) = ((fun j ↦ ball g (j + 1) 0) '' Iio n)ᶜ :=
  (rfl)

variable {g n}

theorem mem_puncture {x : ClosedSurface g} : x ∈ puncture g n ↔ ∀ j < n, x ≠ ball g j 0 := by
  rw [← SetLike.mem_coe, coe_puncture]
  simp [eq_comm]

theorem mem_tailPuncture {x : ClosedSurface g} :
    x ∈ tailPuncture g n ↔ ∀ j < n, x ≠ ball g (j + 1) 0 := by
  rw [← SetLike.mem_coe, coe_tailPuncture]
  simp [eq_comm]

variable (g) in
/-- With no centre removed, `puncture g 0` is the whole surface. -/
@[simp]
theorem puncture_zero : puncture g 0 = ⊤ := by
  ext x
  simp [mem_puncture]

variable (g) in
/-- With one centre removed, `puncture g 1` is the punctured summand
`TauCeti.ConnectedSum.puncture (ball g 0)`, along which the next torus is summed. -/
theorem puncture_one : puncture g 1 = ConnectedSum.puncture (ball g 0) :=
  SetLike.ext fun x ↦ by simp [mem_puncture]

variable (g) in
/-- Removing more centres gives a smaller set. -/
theorem puncture_antitone : Antitone (puncture g) :=
  fun _ _ hmn _ hx ↦ mem_puncture.2 fun j hj ↦ mem_puncture.1 hx j (hj.trans_le hmn)

/-- The base point lies in each `puncture g n`. For `n = 1` this is
`ClosedSurface.basePoint_mem_puncture`, read along `ClosedSurface.puncture_one`. -/
@[simp]
theorem basePoint_mem_puncture' : basePoint g ∈ puncture g n :=
  mem_puncture.2 fun j _ h ↦ basePoint_notMem_range_ball j ⟨0, h.symm⟩

/-- A point `ball g j v` lies in `puncture g n` exactly when it is not a centre, or its ball is
not among the balls `0, …, n - 1`. -/
@[simp]
theorem ball_mem_puncture_iff {j : ℕ} {v : EuclideanSpace ℝ (Fin 2)} :
    ball g j v ∈ puncture g n ↔ v ≠ 0 ∨ n ≤ j := by
  simp only [mem_puncture, ne_eq, ball_eq_ball_iff, not_and]
  constructor
  · intro h
    by_contra! hc
    exact h j hc.2 rfl hc.1
  · rintro (hv | hn) k hk rfl
    · exact hv
    · omega

/-- A point `ball g j v` lies in `tailPuncture g n` exactly when it is not a centre, or its ball
is not among the balls `1, …, n`. -/
@[simp]
theorem ball_mem_tailPuncture_iff {j : ℕ} {v : EuclideanSpace ℝ (Fin 2)} :
    ball g j v ∈ tailPuncture g n ↔ v ≠ 0 ∨ j = 0 ∨ n < j := by
  simp only [mem_tailPuncture, ne_eq, ball_eq_ball_iff, not_and]
  constructor
  · intro h
    by_contra! hc
    exact h (j - 1) (by omega) (by omega) hc.1
  · rintro (hv | hj | hn) k hk rfl
    · exact hv
    · omega
    · omega

/-- The ball `0` lies in `tailPuncture g n`. -/
theorem ball_zero_mem_tailPuncture (v : EuclideanSpace ℝ (Fin 2)) :
    ball g 0 v ∈ tailPuncture g n :=
  ball_mem_tailPuncture_iff.2 (Or.inr (Or.inl rfl))

/-- Removing the centre of the ball `0` from `tailPuncture g n` gives `puncture g (n + 1)`. -/
theorem puncture_succ_eq_tailPuncture_inf :
    puncture g (n + 1) = tailPuncture g n ⊓ ConnectedSum.puncture (ball g 0) := by
  refine SetLike.ext fun x ↦ ?_
  simp only [mem_puncture, Opens.mem_inf, mem_tailPuncture, ConnectedSum.mem_puncture]
  exact ⟨fun h ↦ ⟨fun j hj ↦ h (j + 1) (by omega), h 0 (by omega)⟩,
    fun h j hj ↦ j.casesOn (fun _ ↦ h.2) (fun j hj ↦ h.1 j (by omega)) hj⟩

/-- The set `puncture g (n + 1)` lies in `tailPuncture g n`. -/
theorem puncture_succ_le_tailPuncture : puncture g (n + 1) ≤ tailPuncture g n := by
  rw [puncture_succ_eq_tailPuncture_inf]
  exact inf_le_left

variable (g n)

/-- The closed surface of genus `g` with finitely many centres removed is path connected. -/
theorem isPathConnected_puncture : IsPathConnected (puncture g n : Set (ClosedSurface g)) :=
  isPathConnected_compl_of_finite_of_one_lt_rank (E := EuclideanSpace ℝ (Fin 2))
    (Module.one_lt_rank_of_one_lt_finrank (by simp)) ((finite_Iio n).image _)

theorem isPathConnected_tailPuncture :
    IsPathConnected (tailPuncture g n : Set (ClosedSurface g)) :=
  isPathConnected_compl_of_finite_of_one_lt_rank (E := EuclideanSpace ℝ (Fin 2))
    (Module.one_lt_rank_of_one_lt_finrank (by simp)) ((finite_Iio n).image _)

instance : PathConnectedSpace (puncture g n) :=
  isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_puncture g n)

instance : PathConnectedSpace (tailPuncture g n) :=
  isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_tailPuncture g n)

/-- **Punctures of the sum with a torus.** Read as the connected sum of the torus with the closed
surface of genus `g` along its ball `0`, the closed surface of genus `g + 1` with `n` centres
removed is the punctured torus together with the points of `tailPuncture g n`: the target of
`TauCeti.ConnectedSum.restrictRightHomeomorph` for `U = tailPuncture g n`. -/
theorem image_succDiffeomorph_puncture :
    succDiffeomorph '' (puncture (g + 1) n : Set (ClosedSurface (g + 1))) =
      range (ConnectedSum.inl EuclideanTorus.ball (ball g 0)) ∪
        ConnectedSum.inr _ _ '' {y | (y : ClosedSurface g) ∈ (tailPuncture g n : Set _)} := by
  refine compl_injective ?_
  rw [ConnectedSum.compl_range_inl_union_image_inr EuclideanTorus.ball_injective
    ball_zero_mem_tailPuncture]
  ext p
  obtain ⟨x, rfl⟩ : ∃ x, succDiffeomorph x = p := succDiffeomorph.surjective p
  have hinj : Injective (succDiffeomorph (g := g)) := succDiffeomorph.injective
  rw [mem_compl_iff, hinj.mem_set_image]
  simp only [SetLike.mem_coe, mem_puncture, mem_image, mem_ofPred_eq, mem_tailPuncture,
    not_forall, not_not, exists_prop]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨ball g (j + 1) 0, ?_⟩, ⟨j, hj, rfl⟩, ?_⟩
    · exact ConnectedSum.mem_puncture.2 (ball_zero_zero_notMem_range_ball j ⟨0, ·⟩)
    · rw [succDiffeomorph_ball, ConnectedSum.inrBall_apply]
      exact congrArg _ (Subtype.ext (by rw [ConnectedSum.coe_punctureBall]))
  · rintro ⟨y, ⟨j, hj, hy⟩, hyx⟩
    refine ⟨j, hj, hinj ?_⟩
    rw [← hyx, succDiffeomorph_ball, ConnectedSum.inrBall_apply]
    exact congrArg _ (Subtype.ext (by rw [hy, ConnectedSum.coe_punctureBall]))

/-- **The punctured second summand.** In the connected sum of the torus with `tailPuncture g n`,
along the ball `0` corestricted to it, the second summand punctured at the centre of that ball
is, read in the closed surface of genus `g`, the set `puncture g (n + 1)`. -/
theorem imageVal_puncture_codRestrict_ball :
    Opens.imageVal (ConnectedSum.puncture
      (codRestrict (ball g 0) (tailPuncture g n) ball_zero_mem_tailPuncture)) =
        puncture g (n + 1) := by
  refine SetLike.ext fun x ↦ ?_
  rw [puncture_succ_eq_tailPuncture_inf, Opens.mem_imageVal, Opens.mem_inf]
  simp only [ConnectedSum.mem_puncture, ne_eq, Subtype.ext_iff, val_codRestrict_apply,
    exists_prop]

end SymplecticGeometry.ClosedSurface

end
