/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange

/-!
# The class of a loop in the fundamental group

Mathlib's `FundamentalGroup.mapOfEq f h : π₁(X, x) →* π₁(Y, y)`, for `f : C(X, Y)` and
`h : f x = y`, sends the class of a loop `γ` at `x` to the class of the loop `f ∘ γ`, read at
`y` through `h`. This file states that on the class of a loop, as a rewrite rule, to go with
`FundamentalGroup.mapOfEq_apply`, which states it on an element of `π₁(X, x)` in the
fundamental groupoid. It also states how concatenation and reversal of loops, and the change
of base point along a path, read on their classes. Finally it reads any path, not only a loop,
as an element of `π₁(X, x)`, by joining its end points to `x` along chosen paths.

## Main results

* `FundamentalGroup.mapOfEq_fromPath_mk`: `mapOfEq f h` sends the class of `γ` to the class of
  `(γ.map f.continuous).cast h.symm h.symm`.
* `FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_fromPath_mk`: the change of base point
  along `γ`, read backwards, sends the class of a loop `g` to the class of `γ · g · γ⁻¹`.
* `FundamentalGroup.fromPath_trans`, `FundamentalGroup.fromPath_symm`: the class of a
  concatenation of loops is the product of their classes, in the reverse order, and the class of
  a reversed loop is the inverse.

## Main definitions

* `FundamentalGroup.ofPath x p`: the class in `π₁(X, x)` of a path `p`, its end points joined to
  `x` along chosen paths. It reverses concatenation (`FundamentalGroup.ofPath_trans`), is
  invariant under homotopy (`FundamentalGroup.ofPath_congr`) and casts, and on loops at `x` is a
  conjugation of their classes (`FundamentalGroup.ofPath_loop`).
-/

public section

namespace FundamentalGroup

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- The map `π₁(X, x) → π₁(Y, y)` induced by `f : C(X, Y)` with `f x = y` sends the class of a
loop `γ` at `x` to the class of the loop `f ∘ γ`, cast to a loop at `y`. -/
theorem mapOfEq_fromPath_mk (f : C(X, Y)) (h : f x = y) (γ : Path x x) :
    mapOfEq f h (fromPath (Path.Homotopic.Quotient.mk γ)) =
      fromPath (Path.Homotopic.Quotient.mk ((γ.map f.continuous).cast h.symm h.symm)) := by
  rw [mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]

/-- The inverse of the change of base point along a path `γ` from `x₀` to `x₁` sends the class of
a loop `g` at `x₁` to the class of the loop `γ · g · γ⁻¹` at `x₀`. -/
theorem fundamentalGroupMulEquivOfPath_symm_fromPath_mk {x₀ x₁ : X} (γ : Path x₀ x₁)
    (g : Path x₁ x₁) :
    (fundamentalGroupMulEquivOfPath γ).symm (fromPath (Path.Homotopic.Quotient.mk g)) =
      fromPath (Path.Homotopic.Quotient.mk (γ.trans (g.trans γ.symm))) := by
  rw [fundamentalGroupMulEquivOfPath_symm_apply, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]

/-- The concatenation `γ · δ` of two classes of loops is their product in the fundamental group, in
the reverse order: in Mathlib's `FundamentalGroup`, `g * h` is `h` followed by `g`. -/
@[simp]
theorem fromPath_trans (γ δ : Path.Homotopic.Quotient x x) :
    fromPath (γ.trans δ) = fromPath δ * fromPath γ :=
  (rfl)

/-- The reversal of a class of loops is its inverse in the fundamental group. -/
@[simp]
theorem fromPath_symm (γ : Path.Homotopic.Quotient x x) :
    fromPath γ.symm = (fromPath γ)⁻¹ :=
  (rfl)

section OfPath

variable (x) {x₁ x₂ x₃ : X}

open Classical in
/-- The class in `π₁(X, x)` of a path `p` from `x₁` to `x₂`: the loop that runs from `x` to `x₁`
along a chosen path, then along `p`, and back from `x₂` to `x` along a chosen path. It is `1` if
`x₁` is not joined to `x`. It turns concatenation into multiplication, in the reverse order
(`ofPath_trans`), and depends only on the homotopy class of `p` (`ofPath_congr`); on loops at
`x` it is a conjugation of the class of the loop (`ofPath_loop`). So equations between
concatenations of paths with different end points can be read as equations in `π₁(X, x)`. -/
noncomputable def ofPath (p : Path x₁ x₂) : FundamentalGroup X x :=
  if h : Joined x x₁ then
    fromPath ((Path.Homotopic.Quotient.mk h.somePath).trans
      ((Path.Homotopic.Quotient.mk p).trans
        (Path.Homotopic.Quotient.mk (h.trans ⟨p⟩).somePath).symm))
  else 1

variable {x}

theorem ofPath_congr {p q : Path x₁ x₂} (hpq : p.Homotopic q) : ofPath x p = ofPath x q := by
  unfold ofPath
  rw [Path.Homotopic.Quotient.eq.2 hpq]

theorem ofPath_trans (p : Path x₁ x₂) (q : Path x₂ x₃) :
    ofPath x (p.trans q) = ofPath x q * ofPath x p := by
  unfold ofPath
  by_cases h : Joined x x₁
  · rw [dite_eq_left h, dite_eq_left h, dite_eq_left (h.trans ⟨p⟩), ← fromPath_trans,
      Path.Homotopic.Quotient.mk_trans]
    have key {a b c : X} (u : Path.Homotopic.Quotient b a) (v : Path.Homotopic.Quotient a c) :
        u.symm.trans (u.trans v) = v := by
      rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
        Path.Homotopic.Quotient.refl_trans]
    simp only [Path.Homotopic.Quotient.trans_assoc, key]
  · have h₂ : ¬ Joined x x₂ := fun h₂ ↦ h (h₂.trans ⟨p.symm⟩)
    rw [dite_eq_right h, dite_eq_right h, dite_eq_right h₂, one_mul]

@[simp]
theorem ofPath_refl (x₁ : X) : ofPath x (Path.refl x₁) = 1 := by
  unfold ofPath
  split_ifs with h
  · rw [Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans,
      Path.Homotopic.Quotient.trans_symm]
    rfl
  · rfl

theorem ofPath_symm (p : Path x₁ x₂) : ofPath x p.symm = (ofPath x p)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ofPath_trans, ofPath_congr (Path.Homotopic.trans_symm p),
    ofPath_refl]

@[simp]
theorem ofPath_cast {y₁ y₂ : X} (p : Path x₁ x₂) (h₁ : y₁ = x₁) (h₂ : y₂ = x₂) :
    ofPath x (p.cast h₁ h₂) = ofPath x p := by
  subst h₁ h₂
  rfl

/-- On a loop `γ` at `x`, `ofPath x` is the conjugate of the class of `γ` by the class of the
chosen loop at `x`. -/
theorem ofPath_loop (γ : Path x x) :
    ofPath x γ = MulAut.conj (fromPath (Path.Homotopic.Quotient.mk (Joined.refl x).somePath))⁻¹
      (fromPath (Path.Homotopic.Quotient.mk γ)) := by
  unfold ofPath
  rw [dite_eq_left (Joined.refl x), fromPath_trans, fromPath_trans, fromPath_symm,
    MulAut.conj_apply, inv_inv, mul_assoc]

end OfPath

end FundamentalGroup

end
