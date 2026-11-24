/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.EhresmannConnection
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Basic

/-!
# Horizontal lifts of vector fields

Let `D` be an Ehresmann connection on a map `f : P → B` (Tau Ceti's
`TauCeti.IsEhresmannConnection`). Lifting the value of a vector field `V` on `B` at `f x`
horizontally at every point `x` of `P` gives a vector field on `P`, the horizontal lift of `V`.
It is horizontal, projects to `V` under the derivative of `f`, and depends linearly on `V`, over
the functions on `B` pulled back by `f`.

For a Riemannian submersion, Tau Ceti lifts tangent vectors through the metric adjoint of the
derivative (`TauCeti.IsRiemannianSubmersion.horizontalLift`). That lift is the horizontal lift
of the Ehresmann connection formed by the orthogonal complements of the vertical spaces
(`TauCeti.IsRiemannianSubmersion.horizontalLift_eq_isEhresmannConnection_horizontalLift`), so
results about general connections apply to it.

## Main definitions

* `TauCeti.IsEhresmannConnection.horizontalLiftField`: the horizontal lift of a vector field on
  the base.

## Main results

* `TauCeti.IsEhresmannConnection.horizontalLiftField_mem` and
  `TauCeti.IsEhresmannConnection.mfderiv_horizontalLiftField`: the lift is horizontal and
  projects to the field on the base; `TauCeti.IsEhresmannConnection.eq_horizontalLiftField_iff`
  characterizes it by these two properties.
* `TauCeti.IsEhresmannConnection.horizontalLiftField_add` and
  `TauCeti.IsEhresmannConnection.horizontalLiftField_smul`: the lift is additive, and linear over
  functions on the base.
* `TauCeti.IsRiemannianSubmersion.horizontalLift_eq_isEhresmannConnection_horizontalLift`: the
  horizontal lift of a Riemannian submersion is that of its orthogonal Ehresmann connection.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Function Bundle
open scoped ContDiff

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

/-- Given an Ehresmann connection `D` on `f : P → B` and a field `V` on the base `B`, the
**horizontal lift** of `V` is the field on `P` whose value at `x` is the horizontal lift to `D x`
of `V (f x)`. -/
def horizontalLiftField (V : Π b : B, TangentSpace J b) : Π x : P, TangentSpace I x :=
  fun x ↦ (hD.horizontalLift x (V (f x)) : TangentSpace I x)

variable (V W : Π b : B, TangentSpace J b)

theorem horizontalLiftField_def :
    hD.horizontalLiftField V = fun x ↦ (hD.horizontalLift x (V (f x)) : TangentSpace I x) :=
  (rfl)

@[simp]
theorem horizontalLiftField_apply (x : P) :
    hD.horizontalLiftField V x = hD.horizontalLift x (V (f x)) :=
  (rfl)

/-- The horizontal lift of a vector field is horizontal. -/
theorem horizontalLiftField_mem (x : P) : hD.horizontalLiftField V x ∈ D x := by
  rw [horizontalLiftField_apply]
  exact (hD.horizontalLift x (V (f x))).property

/-- The derivative of `f` maps the horizontal lift of `V` at `x` to `V (f x)`. -/
theorem mfderiv_horizontalLiftField (x : P) :
    mfderiv I J f x (hD.horizontalLiftField V x) = V (f x) := by
  rw [horizontalLiftField_apply, mfderiv_horizontalLift]

/-- The horizontal lift of `V` is the only vector field on `P` that is horizontal and is mapped
to `V` by the derivative of `f`. -/
theorem eq_horizontalLiftField_iff {X : Π x : P, TangentSpace I x} :
    X = hD.horizontalLiftField V ↔ ∀ x, X x ∈ D x ∧ mfderiv I J f x (X x) = V (f x) := by
  refine ⟨fun h ↦ h ▸ fun x ↦ ⟨hD.horizontalLiftField_mem V x,
    hD.mfderiv_horizontalLiftField V x⟩, fun h ↦ funext fun x ↦ ?_⟩
  rw [horizontalLiftField_apply]
  exact congrArg Subtype.val
    ((hD.eq_horizontalLift_iff (w := ⟨X x, (h x).1⟩)).2 (h x).2)

/-- The horizontal lift of `V` vanishes at the points `x` where `V (f x)` vanishes. -/
theorem horizontalLiftField_eq_zero {x : P} (hx : V (f x) = 0) :
    hD.horizontalLiftField V x = 0 := by
  rw [horizontalLiftField_apply, hx, map_zero, Submodule.coe_zero]

@[simp]
theorem horizontalLiftField_zero : hD.horizontalLiftField (0 : Π b : B, TangentSpace J b) = 0 :=
  funext fun _ ↦ hD.horizontalLiftField_eq_zero _ rfl

theorem horizontalLiftField_add :
    hD.horizontalLiftField (V + W) = hD.horizontalLiftField V + hD.horizontalLiftField W :=
  funext fun x ↦ by
    simp only [horizontalLiftField_apply, Pi.add_apply, map_add, Submodule.coe_add]

theorem horizontalLiftField_neg : hD.horizontalLiftField (-V) = -hD.horizontalLiftField V :=
  funext fun x ↦ by
    simp only [horizontalLiftField_apply, Pi.neg_apply, map_neg, Submodule.coe_neg]

theorem horizontalLiftField_sub :
    hD.horizontalLiftField (V - W) = hD.horizontalLiftField V - hD.horizontalLiftField W :=
  funext fun x ↦ by
    simp only [horizontalLiftField_apply, Pi.sub_apply, map_sub, Submodule.coe_sub]

/-- The horizontal lift is linear over functions on the base: lifting `g • V` multiplies the
lift of `V` by `g ∘ f`. -/
theorem horizontalLiftField_smul (g : B → 𝕜) :
    hD.horizontalLiftField (g • V) = (g ∘ f) • hD.horizontalLiftField V :=
  funext fun x ↦ by
    simp only [horizontalLiftField_apply, Pi.smul_apply', comp_apply, map_smul,
      Submodule.coe_smul]

theorem horizontalLiftField_const_smul (c : 𝕜) :
    hD.horizontalLiftField (c • V) = c • hD.horizontalLiftField V :=
  funext fun x ↦ by
    simp only [horizontalLiftField_apply, Pi.smul_apply, map_smul, Submodule.coe_smul]

end IsEhresmannConnection

namespace IsRiemannianSubmersion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I 1 P]
  [RiemannianBundle (fun x : P ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]
  [RiemannianBundle (fun b : B ↦ TangentSpace J b)]
  {n : ℕ∞ω} {f : P → B}

/-- The horizontal lift of a Riemannian submersion, by the metric adjoint of its derivative, is
the horizontal lift of the Ehresmann connection formed by the orthogonal complements of its
vertical spaces, such as the one given by
`Manifold.IsSubmersion.isEhresmannConnection_orthogonal_ker_mfderiv`. -/
theorem horizontalLift_eq_isEhresmannConnection_horizontalLift
    (h : IsRiemannianSubmersion I J f)
    (hD : IsEhresmannConnection I J n f (fun x ↦ (mfderiv I J f x).kerᗮ))
    (x : P) (v : TangentSpace J (f x)) :
    h.horizontalLift x v = hD.horizontalLift x v :=
  congrArg Subtype.val ((hD.eq_horizontalLift_iff
    (w := ⟨h.horizontalLift x v, h.horizontalLift_mem_orthogonal_ker x v⟩)).2
    (h.mfderiv_horizontalLift x v))

end IsRiemannianSubmersion

end TauCeti
