/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Path
public import TauCeti.Topology.Circle.Loop
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import TauCeti.AlgebraicTopology.FundamentalGroup.FreeLoop
import TauCeti.Topology.Homotopy.Homotopic.With

/-!
# Homotopies of loops with fixed and with free base point

Two loops `γ γ' : Path x x` that are homotopic with fixed ends (`Path.Homotopic`) are also
homotopic through loops, the base point being allowed to move:
`(γ : C(I, X)).HomotopicWith γ' fun p ↦ p 0 = p 1`. This is the easy half of the comparison
between based and free homotopy classes of loops; Tau Ceti's
`Path.exists_trans_homotopic_trans_of_homotopicWith` and `Path.homotopicWith_trans_trans_symm`
give the rest. In particular a loop that is homotopic with fixed ends to the constant loop is
null-homotopic as a map from the circle, through Tau Ceti's `Path.toCircle`, which sends the
constant loop to a constant map (`Path.toCircle_refl`).

Conversely, a homotopy of loops whose base point runs along a known path `δ` gives a homotopy
with fixed ends from `γ₀ · δ` to `δ · γ₁`, by the square of the homotopy along `Path.id`
(Mathlib's `Path.Homotopic.map_trans_evalAt`). The proof is that of Tau Ceti's
`Path.exists_trans_homotopic_trans_of_homotopicWith`, which only says that some such `δ`
exists; here the track `δ` is given, so that it can be identified.

## Main results

* `Path.Homotopic.homotopicWith`: a homotopy with fixed ends is a homotopy through loops.
* `Path.Homotopic.nullhomotopic_toCircle`: a loop homotopic to the constant loop is
  null-homotopic as a map from the circle.
* `Path.trans_homotopic_trans_of_homotopy`: a homotopy of loops whose ends both follow `δ` gives
  a homotopy with fixed ends from `γ₀ · δ` to `δ · γ₁`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2 (homotopy of loops in the homotopy axiom of Theorem 2.2.12).
-/

public section

open scoped unitInterval

namespace Path.Homotopic

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Loops at `x` that are homotopic with fixed ends are homotopic through loops: a homotopy
relative to the ends keeps every intermediate map closed. -/
theorem homotopicWith {γ γ' : Path x x} (h : γ.Homotopic γ') :
    (γ : C(I, X)).HomotopicWith (γ' : C(I, X)) fun p ↦ p 0 = p 1 := by
  obtain ⟨F⟩ := h
  exact ⟨{ toHomotopy := F.toHomotopy, prop' := fun s ↦ by simp }⟩

/-- A loop at `x` that is homotopic with fixed ends to the constant loop is null-homotopic as a
map from the circle (`Path.toCircle`). -/
theorem nullhomotopic_toCircle {γ : Path x x} (h : γ.Homotopic (Path.refl x)) :
    γ.toCircle.Nullhomotopic := by
  refine ⟨x, ContinuousMap.homotopic_iff_joined.2 ?_⟩
  simpa only [Path.toCircle_refl] using h.joined_toCircle

end Path.Homotopic

namespace Path

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- A homotopy `H` from the loop `γ₀` at `x` to the loop `γ₁` at `y` whose ends both follow the
path `δ` from `x` to `y` (`H (s, 0) = H (s, 1) = δ s`) gives a homotopy with fixed ends from
`γ₀ · δ` to `δ · γ₁`. -/
theorem trans_homotopic_trans_of_homotopy {γ₀ : Path x x} {γ₁ : Path y y}
    (H : (γ₀ : C(I, X)).Homotopy γ₁) (δ : Path x y) (h₀ : ∀ s, H (s, 0) = δ s)
    (h₁ : ∀ s, H (s, 1) = δ s) : (γ₀.trans δ).Homotopic (δ.trans γ₁) := by
  -- The square of `H` along `Path.id : 0 ⟶ 1`, whose tracks at `0` and `1` are both `δ`.
  have h := (Path.Homotopic.map_trans_evalAt H Path.id).pathCast
    (show x = (γ₀ : C(I, X)) 0 by simp) (show y = (γ₁ : C(I, X)) 1 by simp)
  convert h using 1 <;> ext t
  · simp only [Path.trans_apply, Path.cast_coe, Path.map_coe, Function.comp_apply, Path.id,
      ContinuousMap.Homotopy.evalAt_apply]
    split_ifs
    · rfl
    · exact (h₁ _).symm
  · simp only [Path.trans_apply, Path.cast_coe, Path.map_coe, Function.comp_apply, Path.id,
      ContinuousMap.Homotopy.evalAt_apply]
    split_ifs
    · exact (h₀ _).symm
    · rfl

end Path

end
