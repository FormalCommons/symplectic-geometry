/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Circle.Loop
public import TauCeti.Topology.Homotopy.AddCircle

/-!
# Loops and maps from `AddCircle p`

Tau Ceti reads a map `f : C(AddCircle p, X)` as the loop `f.toLoop`, `t ↦ f (t * p)`, at `f 0`.
This file adds the inverse construction and the behaviour of `toLoop` under composition.

* `ContinuousMap.toLoop_comp`: the loop of `f ∘ g` is the image under `f` of the loop of `g`.
* `Path.toAddCircle p γ`, for `0 < p`: a loop `γ` at `x` read as a map from `AddCircle p`, sending
  `t * p` to `γ t`. It is Tau Ceti's `Path.toCircle` composed with Mathlib's
  `AddCircle.homeomorphCircle`, and `ContinuousMap.toLoop_toAddCircle` and
  `ContinuousMap.toAddCircle_toLoop` show that it is inverse to `toLoop`. The lemmas follow
  Tau Ceti's `Path.toCircle_refl` and `ContinuousMap.toBasedLoop_toCircle`, which do the same
  for `Circle`.

## Main definitions

* `Path.toAddCircle`: a loop at `x`, read as a map from `AddCircle p`.

## Main results

* `ContinuousMap.toLoop_comp`: `(f.comp g).toLoop = g.toLoop.map f.continuous`.
* `ContinuousMap.toLoop_toAddCircle`: the loop of `γ.toAddCircle p` is `γ`.
* `ContinuousMap.toAddCircle_toLoop`: a map `f : C(AddCircle p, X)` is recovered from its loop.
-/

public section

noncomputable section

open scoped unitInterval

variable {p : ℝ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace ContinuousMap

/-- The loop of `f ∘ g` is the image under `f` of the loop of `g`. -/
theorem toLoop_comp (f : C(X, Y)) (g : C(AddCircle p, X)) :
    (f.comp g).toLoop = g.toLoop.map f.continuous := by
  ext t
  exact (toLoop_apply _ t).trans (by simp)

end ContinuousMap

namespace Path

variable [Fact (0 < p)] {x : X}

variable (p) in
/-- A loop `γ` at `x`, read as a map from the circle `AddCircle p`: the point `t * p`, for
`t ∈ [0, 1]`, goes to `γ t`. -/
def toAddCircle (γ : Path x x) : C(AddCircle p, X) :=
  γ.toCircle.comp (AddCircle.homeomorphCircle (Fact.out : 0 < p).ne')

theorem toAddCircle_def (γ : Path x x) :
    γ.toAddCircle p = γ.toCircle.comp (AddCircle.homeomorphCircle (Fact.out : 0 < p).ne') :=
  (rfl)

/-- The point `t * p` of the circle goes to `γ t`. -/
@[simp]
theorem toAddCircle_apply_mul (γ : Path x x) (t : I) :
    γ.toAddCircle p ((t * p : ℝ) : AddCircle p) = γ t := by
  have hp : (p : ℝ) ≠ 0 := (Fact.out : 0 < p).ne'
  rw [toAddCircle_def, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass,
    AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
    show 2 * Real.pi / p * (t * p) = 2 * Real.pi * t by field_simp, γ.toCircle_exp]

/-- The point `s ∈ [0, p)` of the circle goes to `γ (s / p)`. -/
theorem toAddCircle_coe_of_mem_Ico (γ : Path x x) {s : ℝ} (hs : s ∈ Set.Ico 0 p) :
    γ.toAddCircle p (s : AddCircle p) = γ.extend (s / p) := by
  have hp : 0 < p := Fact.out
  have ht : s / p ∈ I := ⟨div_nonneg hs.1 hp.le, (div_le_one hp).2 hs.2.le⟩
  have h := γ.toAddCircle_apply_mul (p := p) ⟨s / p, ht⟩
  rw [← γ.extend_extends', div_mul_cancel₀ _ hp.ne'] at h
  exact h

/-- On the circle, `γ.toAddCircle p` is `s ↦ γ (s / p)` on `[0, p)`, descended to `AddCircle p`. -/
theorem coe_toAddCircle (γ : Path x x) :
    ⇑(γ.toAddCircle p) = AddCircle.liftIco p 0 fun s ↦ γ.extend (s / p) := by
  funext θ
  obtain ⟨s, hs, rfl⟩ : ∃ s ∈ Set.Ico 0 p, (s : AddCircle p) = θ :=
    ⟨_, by simpa using (AddCircle.equivIco p 0 θ).property, AddCircle.coe_equivIco⟩
  rw [toAddCircle_coe_of_mem_Ico _ hs, AddCircle.liftIco_zero_coe_apply hs]

/-- The base point `0` of the circle goes to the base point of the loop. -/
@[simp]
theorem toAddCircle_zero (γ : Path x x) : γ.toAddCircle p 0 = x := by
  simpa using γ.toAddCircle_apply_mul (p := p) 0

/-- The constant loop at `x` is the constant map from the circle. -/
@[simp]
theorem toAddCircle_refl (x : X) :
    (Path.refl x).toAddCircle p = ContinuousMap.const (AddCircle p) x := by
  ext θ
  obtain ⟨t, rfl⟩ := AddCircle.surjective_ofUnitInterval θ
  simp

end Path

namespace ContinuousMap

variable [Fact (0 < p)] {x : X}

/-- **Every loop is the loop of a circle map.** The loop of `γ.toAddCircle p` is `γ`, read at `x`
through `γ.toAddCircle p 0 = x`. -/
theorem toLoop_toAddCircle (γ : Path x x) :
    (γ.toAddCircle p).toLoop = γ.cast γ.toAddCircle_zero γ.toAddCircle_zero := by
  ext t
  simp

/-- A map from the circle is recovered from its loop by `Path.toAddCircle`. -/
@[simp]
theorem toAddCircle_toLoop (f : C(AddCircle p, X)) : f.toLoop.toAddCircle p = f := by
  ext θ
  obtain ⟨t, rfl⟩ := AddCircle.surjective_ofUnitInterval θ
  simp

end ContinuousMap
