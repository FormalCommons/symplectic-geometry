/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Submersion.HorizontalLiftField
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorField.Related

/-!
# The curvature of an Ehresmann connection

Let `D` be an Ehresmann connection on a map `f : P → B` (Tau Ceti's
`TauCeti.IsEhresmannConnection`). Lifting a vector field `v` on `B` horizontally gives a field
`v♯` on `P`. For two vector fields `v₁ v₂` of `B`, the curvature of `D` is the vector field
`[v₁♯, v₂♯] - [v₁, v₂]♯` on `P`, with Mathlib's Lie bracket `VectorField.mlieBracket`.

The lifts are `f`-related to the fields they lift, so by the naturality of the bracket
(`TauCeti.mfderiv_mlieBracket_of_eventually_related`) the bracket of two lifts projects to the
bracket on the base, and the curvature is vertical. Since `[v₁, v₂]♯` is the horizontal part of
`[v₁♯, v₂♯]`, the curvature is its vertical part, and it vanishes at a point exactly when the
bracket of the lifts is horizontal there.

The curvature is alternating, additive in each argument, and linear over differentiable functions
on the base: `g • v₁` has curvature `(g ∘ f) • curvature v₁ v₂`, by the Leibniz rule for the
bracket (`VectorField.mlieBracket_smul_left`) on `B` and on `P`.

Mathlib's bracket has the usual sign, and so has Guillemin–Lerman–Sternberg's (§1.3), whose
curvature is this one. McDuff–Salamon (§6.4, p. 277) write the same formula with the bracket of
the opposite sign, so their curvature is the negative of this one.

## Main definitions

* `TauCeti.IsEhresmannConnection.curvature`: the curvature of an Ehresmann connection on two
  vector fields of the base.

## Main results

* `TauCeti.IsEhresmannConnection.mfderiv_mlieBracket_horizontalLiftField`: the bracket of two
  horizontal lifts projects to the bracket of the fields on the base.
* `TauCeti.IsEhresmannConnection.curvature_mem_ker`: the curvature is vertical.
* `TauCeti.IsEhresmannConnection.curvature_eq_zero_iff_mem`: the curvature vanishes at a point
  exactly when the bracket of the two lifts is horizontal there.
* `TauCeti.IsEhresmannConnection.curvature_swap`,
  `TauCeti.IsEhresmannConnection.curvature_add_left` and
  `TauCeti.IsEhresmannConnection.curvature_smul_left`, with their right-hand versions: the
  curvature is alternating and linear over functions on the base.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.4.
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.3.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Function Bundle Filter VectorField
open scoped ContDiff Manifold

namespace TauCeti

namespace IsEhresmannConnection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I 1 P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]
  {n : ℕ∞ω} {f : P → B} {D : Π x : P, Submodule 𝕜 (TangentSpace I x)}
  (hD : IsEhresmannConnection I J n f D)

/-- The **curvature** of an Ehresmann connection `D` on `f : P → B`, on two vector fields
`v₁ v₂` of `B`: the vector field `[v₁♯, v₂♯] - [v₁, v₂]♯` on `P`, where `v♯` is the horizontal
lift of `v` and the bracket is `VectorField.mlieBracket`. -/
def curvature (v₁ v₂ : Π b : B, TangentSpace J b) : Π x : P, TangentSpace I x :=
  mlieBracket I (hD.horizontalLiftField v₁) (hD.horizontalLiftField v₂) -
    hD.horizontalLiftField (mlieBracket J v₁ v₂)

variable (v₁ v₂ : Π b : B, TangentSpace J b)

theorem curvature_def :
    hD.curvature v₁ v₂ = mlieBracket I (hD.horizontalLiftField v₁) (hD.horizontalLiftField v₂) -
      hD.horizontalLiftField (mlieBracket J v₁ v₂) :=
  (rfl)

theorem curvature_apply (x : P) :
    hD.curvature v₁ v₂ x =
      mlieBracket I (hD.horizontalLiftField v₁) (hD.horizontalLiftField v₂) x -
        hD.horizontalLiftField (mlieBracket J v₁ v₂) x :=
  (rfl)

/-- The curvature is alternating. -/
theorem curvature_swap : hD.curvature v₁ v₂ = -hD.curvature v₂ v₁ := by
  rw [curvature_def, curvature_def, mlieBracket_swap (V := hD.horizontalLiftField v₁),
    mlieBracket_swap (V := v₁), horizontalLiftField_neg, neg_sub, sub_neg_eq_add,
    neg_add_eq_sub]

theorem curvature_swap_apply (x : P) : hD.curvature v₁ v₂ x = -hD.curvature v₂ v₁ x := by
  rw [curvature_swap, Pi.neg_apply]

@[simp]
theorem curvature_self : hD.curvature v₁ v₁ = 0 := by
  simp [curvature_def, mlieBracket_self]

section Smooth

/-! ### Verticality and linearity -/

variable [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F]
  [IsManifold I 2 P] [IsManifold J 2 B]

attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField

/-- The derivative of `f` maps the bracket of the horizontal lifts of `v₁ v₂` at `x` to the
bracket of `v₁ v₂` at `f x`, for a `C^n` connection with `1 ≤ n`, `f` of class `C^(n+1)` at `x`
and `v₁ v₂` of class `C^n` at `f x`. -/
theorem mfderiv_mlieBracket_horizontalLiftField (hn : 1 ≤ n) {x : P}
    (hf : ContMDiffAt I J (n + 1) f x) {v₁ v₂ : Π b : B, TangentSpace J b}
    (hv₁ : ContMDiffAt J J.tangent n (T% v₁) (f x))
    (hv₂ : ContMDiffAt J J.tangent n (T% v₂) (f x)) :
    mfderiv I J f x (mlieBracket I (hD.horizontalLiftField v₁) (hD.horizontalLiftField v₂) x) =
      mlieBracket J v₁ v₂ (f x) :=
  mfderiv_mlieBracket_of_eventually_related hf
    (by simpa [one_add_one_eq_two] using add_le_add_left hn 1)
    (hD.mdifferentiableAt_horizontalLiftField hn hf hv₁)
    (hD.mdifferentiableAt_horizontalLiftField hn hf hv₂)
    ((hv₁.of_le hn).mdifferentiableAt one_ne_zero) ((hv₂.of_le hn).mdifferentiableAt one_ne_zero)
    (.of_forall fun y ↦ hD.mfderiv_horizontalLiftField v₁ y)
    (.of_forall fun y ↦ hD.mfderiv_horizontalLiftField v₂ y)

/-- The curvature is **vertical**: for a `C^n` connection with `1 ≤ n`, `f` of class `C^(n+1)` at
`x` and `v₁ v₂` of class `C^n` at `f x`, the curvature at `x` lies in the kernel of the
derivative of `f`. -/
theorem curvature_mem_ker (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J (n + 1) f x)
    {v₁ v₂ : Π b : B, TangentSpace J b} (hv₁ : ContMDiffAt J J.tangent n (T% v₁) (f x))
    (hv₂ : ContMDiffAt J J.tangent n (T% v₂) (f x)) :
    hD.curvature v₁ v₂ x ∈ (mfderiv I J f x).ker := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, curvature_apply, map_sub,
    hD.mfderiv_mlieBracket_horizontalLiftField hn hf hv₁ hv₂, mfderiv_horizontalLiftField,
    sub_self]

/-- The curvature vanishes at `x` exactly when the bracket of the horizontal lifts of `v₁ v₂` is
horizontal at `x`, for a `C^n` connection with `1 ≤ n`, `f` of class `C^(n+1)` at `x` and
`v₁ v₂` of class `C^n` at `f x`. -/
theorem curvature_eq_zero_iff_mem (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J (n + 1) f x)
    {v₁ v₂ : Π b : B, TangentSpace J b} (hv₁ : ContMDiffAt J J.tangent n (T% v₁) (f x))
    (hv₂ : ContMDiffAt J J.tangent n (T% v₂) (f x)) :
    hD.curvature v₁ v₂ x = 0 ↔
      mlieBracket I (hD.horizontalLiftField v₁) (hD.horizontalLiftField v₂) x ∈ D x := by
  have hlift := hD.horizontalLiftField_mem (mlieBracket J v₁ v₂) x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [curvature_apply, sub_eq_zero] at h
    rw [h]
    exact hlift
  · refine (Submodule.disjoint_def.1 (hD.isCompl_ker x).disjoint) _ ?_
      (hD.curvature_mem_ker hn hf hv₁ hv₂)
    rw [curvature_apply]
    exact (D x).sub_mem h hlift

/-- The curvature is additive in its first argument, at a point `x` where the fields are
`C^n` at `f x`, for a `C^n` connection with `1 ≤ n` and `f` of class `C^(n+1)` at `x`. -/
theorem curvature_add_left (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J (n + 1) f x)
    {v₁ v₁' : Π b : B, TangentSpace J b} (v₂ : Π b : B, TangentSpace J b)
    (hv₁ : ContMDiffAt J J.tangent n (T% v₁) (f x))
    (hv₁' : ContMDiffAt J J.tangent n (T% v₁') (f x)) :
    hD.curvature (v₁ + v₁') v₂ x = hD.curvature v₁ v₂ x + hD.curvature v₁' v₂ x := by
  simp only [curvature_apply, horizontalLiftField_add,
    mlieBracket_add_left (hD.mdifferentiableAt_horizontalLiftField hn hf hv₁)
      (hD.mdifferentiableAt_horizontalLiftField hn hf hv₁'),
    horizontalLiftField_apply,
    mlieBracket_add_left ((hv₁.of_le hn).mdifferentiableAt one_ne_zero)
      ((hv₁'.of_le hn).mdifferentiableAt one_ne_zero), map_add, Submodule.coe_add]
  abel

/-- The curvature is additive in its second argument, at a point `x` where the fields are
`C^n` at `f x`, for a `C^n` connection with `1 ≤ n` and `f` of class `C^(n+1)` at `x`. -/
theorem curvature_add_right (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J (n + 1) f x)
    (v₁ : Π b : B, TangentSpace J b) {v₂ v₂' : Π b : B, TangentSpace J b}
    (hv₂ : ContMDiffAt J J.tangent n (T% v₂) (f x))
    (hv₂' : ContMDiffAt J J.tangent n (T% v₂') (f x)) :
    hD.curvature v₁ (v₂ + v₂') x = hD.curvature v₁ v₂ x + hD.curvature v₁ v₂' x := by
  rw [curvature_swap_apply, hD.curvature_add_left hn hf v₁ hv₂ hv₂', neg_add,
    ← curvature_swap_apply, ← curvature_swap_apply]

/-- The curvature is linear over functions on the base in its first argument: for a function
`g` on `B` differentiable at `f x`, `g • v₁` has curvature `g (f x) • curvature v₁ v₂` at `x`,
for a `C^n` connection with `1 ≤ n`, `f` of class `C^(n+1)` at `x` and `v₁` of class `C^n` at
`f x`. -/
theorem curvature_smul_left (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J (n + 1) f x)
    {g : B → 𝕜} (hg : MDifferentiableAt J 𝓘(𝕜) g (f x)) {v₁ : Π b : B, TangentSpace J b}
    (v₂ : Π b : B, TangentSpace J b) (hv₁ : ContMDiffAt J J.tangent n (T% v₁) (f x)) :
    hD.curvature (g • v₁) v₂ x = g (f x) • hD.curvature v₁ v₂ x := by
  have hfx : MDifferentiableAt I J f x := hf.mdifferentiableAt (by simp)
  have hP := mlieBracket_smul_left (W := hD.horizontalLiftField v₂) (hg.comp x hfx)
    (hD.mdifferentiableAt_horizontalLiftField hn hf hv₁)
  have hB := mlieBracket_smul_left (W := v₂) hg ((hv₁.of_le hn).mdifferentiableAt one_ne_zero)
  rw [mvfderiv_comp_apply x hg hfx, mfderiv_horizontalLiftField] at hP
  rw [curvature_apply, curvature_apply, horizontalLiftField_smul, hP,
    horizontalLiftField_apply _ (mlieBracket J _ _), hB, map_add, map_smul, map_smul,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, ← horizontalLiftField_apply,
    ← horizontalLiftField_apply, comp_apply, smul_sub]
  abel

/-- The curvature is linear over functions on the base in its second argument: for a function
`g` on `B` differentiable at `f x`, `g • v₂` has curvature `g (f x) • curvature v₁ v₂` at `x`,
for a `C^n` connection with `1 ≤ n`, `f` of class `C^(n+1)` at `x` and `v₂` of class `C^n` at
`f x`. -/
theorem curvature_smul_right (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J (n + 1) f x)
    {g : B → 𝕜} (hg : MDifferentiableAt J 𝓘(𝕜) g (f x)) (v₁ : Π b : B, TangentSpace J b)
    {v₂ : Π b : B, TangentSpace J b} (hv₂ : ContMDiffAt J J.tangent n (T% v₂) (f x)) :
    hD.curvature v₁ (g • v₂) x = g (f x) • hD.curvature v₁ v₂ x := by
  rw [curvature_swap_apply, hD.curvature_smul_left hn hf hg v₁ hv₂, ← smul_neg,
    ← curvature_swap_apply]

end Smooth

end IsEhresmannConnection

end TauCeti
