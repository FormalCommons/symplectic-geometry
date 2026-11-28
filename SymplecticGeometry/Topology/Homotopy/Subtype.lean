/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Restricting a based contraction to a smaller subtype

Let `P` and `Q` be predicates on a topological space `X` with `Q x → P x`, and let `x₀` satisfy
`Q`. A homotopy relative to `{x₀}` from the identity of `{x // P x}` to the constant map at `x₀`
which keeps `Q` at every time restricts to a homotopy relative to `{x₀}` from the identity of
`{x // Q x}` to the constant map at `x₀` (`ContinuousMap.HomotopyRel.restrictSubtype`). So a
contraction of a subtype that keeps a smaller subtype contracts it too.

Tau Ceti's `ContinuousMap.HomotopyRel.restrictInvariant` restricts a homotopy from the identity
of `X` to an invariant set `S ⊆ X`; here the space is itself a subtype `{x // P x}`, and the
restriction is to the subtype `{x // Q x}` of `X`, not to a set of `{x // P x}`.
-/

public section

namespace ContinuousMap.HomotopyRel

variable {X : Type*} [TopologicalSpace X] {P Q : X → Prop} {x₀ : X} {hx₀ : P x₀}

/-- A homotopy relative to `{x₀}` from the identity of `{x // P x}` to the constant map at `x₀`
which keeps `Q` at every time, for a predicate `Q` stronger than `P` with `Q x₀`, restricted to a
homotopy relative to `{x₀}` from the identity of `{x // Q x}` to the constant map at `x₀`. -/
def restrictSubtype
    (H : (ContinuousMap.id {x // P x}).HomotopyRel (ContinuousMap.const _ ⟨x₀, hx₀⟩)
      {⟨x₀, hx₀⟩})
    (hQP : ∀ x, Q x → P x) (hQ₀ : Q x₀) (hH : ∀ t (x : {x // P x}), Q x → Q (H (t, x))) :
    (ContinuousMap.id {x // Q x}).HomotopyRel (ContinuousMap.const _ ⟨x₀, hQ₀⟩) {⟨x₀, hQ₀⟩} where
  toFun p := ⟨H (p.1, ⟨p.2, hQP _ p.2.property⟩), hH _ _ p.2.property⟩
  continuous_toFun := (continuous_subtypeVal.comp (H.continuous.comp
    (continuous_fst.prodMk ((continuous_subtypeVal.comp continuous_snd).subtype_mk _)))
    ).subtype_mk _
  map_zero_left x := Subtype.ext (congrArg Subtype.val (H.apply_zero ⟨x, hQP _ x.property⟩) :)
  map_one_left x := Subtype.ext (congrArg Subtype.val (H.apply_one ⟨x, hQP _ x.property⟩) :)
  prop' t x hx := by
    obtain rfl := hx
    exact Subtype.ext (congrArg Subtype.val (H.eq_fst t (x := ⟨x₀, hx₀⟩) rfl) :)

/-- The restriction of a homotopy to the subtype `{x // Q x}` takes the values of the homotopy. -/
@[simp]
theorem coe_restrictSubtype_apply
    (H : (ContinuousMap.id {x // P x}).HomotopyRel (ContinuousMap.const _ ⟨x₀, hx₀⟩)
      {⟨x₀, hx₀⟩})
    (hQP : ∀ x, Q x → P x) (hQ₀ : Q x₀) (hH : ∀ t (x : {x // P x}), Q x → Q (H (t, x)))
    (p : unitInterval × {x // Q x}) :
    (H.restrictSubtype hQP hQ₀ hH p : X) = H (p.1, ⟨p.2, hQP _ p.2.property⟩) :=
  (rfl)

end ContinuousMap.HomotopyRel

end
