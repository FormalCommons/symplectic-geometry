/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Submersion.HorizontalLiftField
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import SymplecticGeometry.Algebra.Order.Monoid.NatCast
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality
import TauCeti.Geometry.Manifold.VectorField.Related
import TauCeti.Geometry.Manifold.ContMDiff.Defs
import SymplecticGeometry.Geometry.Manifold.Distribution.Frame

/-!
# The curvature of an Ehresmann connection

Let `D` be an Ehresmann connection on a map `f : P → B` (Tau Ceti's
`TauCeti.IsEhresmannConnection`). Lifting a vector field `v` on `B` horizontally gives a field
`v♯` on `P`. For two vector fields `v₁ v₂` of `B`, the curvature of `D` is the vector field
`[v₁♯, v₂♯] - [v₁, v₂]♯` on `P`, with Mathlib's Lie bracket `VectorField.mlieBracket`.

The lifts are `f`-related to the fields they lift, so by the naturality of the bracket
(`TauCeti.mfderiv_mlieBracket_of_eventually_related`) the bracket of two lifts projects to the
bracket on the base, and the curvature is vertical. The proof of
`TauCeti.IsEhresmannConnection.mfderiv_mlieBracket_horizontalLiftField` adapts that of Tau Ceti's
`TauCeti.IsRiemannianSubmersion.mfderiv_mlieBracket_horizontalLift` from the horizontal lifts of
a Riemannian submersion to those of an Ehresmann connection.

Since `[v₁, v₂]♯` is the horizontal part of `[v₁♯, v₂♯]`, the curvature is its vertical part,
and it vanishes at a point exactly when the bracket of the lifts is horizontal there.

The curvature is local: two connections that agree near `x` have the same horizontal lifts near
`x` of fields that agree near `f x`
(`TauCeti.IsEhresmannConnection.horizontalLiftField_eventuallyEq`), and the bracket at a point
only depends on the fields near it (`Filter.EventuallyEq.mlieBracket_vectorField_eq`), so the
curvatures at `x` agree.

The curvature is natural. Let `Φ : P → P'` cover `ψ : B → B'` near `x`, with derivative carrying
`D` into the horizontal spaces `D'` of a connection on `f'`. The lifts of `ψ`-related fields are
then `Φ`-related near `x`
(`TauCeti.IsEhresmannConnection.eventually_mfderiv_horizontalLiftField_eq_of_related`), and
naturality of the bracket on `P` and on `B` (`TauCeti.mfderiv_mlieBracket_of_eventually_related`)
carries the curvature of `D` at `x` to that of `D'` at `Φ x`. No invertibility of `Φ` or `ψ` is
needed.

The curvature is alternating, additive in each argument, and linear over differentiable functions
on the base: `g • v₁` has curvature `(g ∘ f) • curvature v₁ v₂`, by the Leibniz rule for the
bracket (`VectorField.mlieBracket_smul_left`) on `B` and on `P`.

Over `ℝ`, on a finite-dimensional Hausdorff base, these laws make the curvature at `x` of smooth
fields depend only on their values at `f x` (`curvature_congr`), by Tau Ceti's tensoriality
criterion `TauCeti.Manifold.eq_of_contMDiff_tensorial`. Every tangent vector of the base is the
value of a smooth global field (Tau Ceti's `FiberBundle.contMDiffExtend`), so the curvature at
`x` is a bilinear map on `TangentSpace J (f x)` with values in `TangentSpace I x`,
`curvatureTensor`; it is alternating and its values are vertical. The construction follows that
of Tau Ceti's `CovariantDerivative.curvatureTensor` from
`CovariantDerivative.curvatureOperator_congr`.

The connection is flat, its curvature vanishing at every point `x` on all fields that are `C^1`
at `f x`, exactly when `D` is involutive in the sense of Tau Ceti's
`TauCeti.IsInvolutiveDistribution`. If `D` is involutive, the bracket of two lifts is
horizontal, so the curvature, which is vertical, vanishes. Conversely, near a point the lifts of
a local frame of the tangent bundle of `B` form a local frame of `D`
(`TauCeti.IsEhresmannConnection.isDistributionFrameOn_horizontalLiftField`). The brackets of
this frame are horizontal when the curvature vanishes, and then so are those of all fields
tangent to `D`, by the local frame criterion
`TauCeti.IsDistributionFrameOn.mlieBracket_mem_of_forall_mlieBracket_mem`.

On signs: Guillemin–Lerman–Sternberg (§1.3) bracket vector fields as Mathlib does, and their
curvature agrees with `curvature`. In McDuff–Salamon (§6.4, p. 277) the bracket is minus Mathlib's,
and their curvature is `-curvature`.

## Main definitions

* `TauCeti.IsEhresmannConnection.curvature`: the curvature of an Ehresmann connection on two
  vector fields of the base.
* `TauCeti.IsEhresmannConnection.curvatureTensor`: the curvature at a point of `P`, as a
  bilinear map on the tangent space of the base.

## Main results

* `TauCeti.IsEhresmannConnection.mfderiv_mlieBracket_horizontalLiftField`: the bracket of two
  horizontal lifts projects to the bracket of the fields on the base.
* `TauCeti.IsEhresmannConnection.curvature_mem_ker`: the curvature is vertical.
* `TauCeti.IsEhresmannConnection.curvature_eq_zero_iff_mem`: the curvature vanishes at a point
  exactly when the bracket of the two lifts is horizontal there.
* `TauCeti.IsEhresmannConnection.curvature_apply_eq_of_eventuallyEq`: the curvature is local in
  the connection and in the fields.
* `TauCeti.IsEhresmannConnection.mfderiv_curvature_of_related`: a map covering another and
  carrying one connection into the other carries the curvature on related fields to the
  curvature.
* `TauCeti.IsEhresmannConnection.curvature_swap`,
  `TauCeti.IsEhresmannConnection.curvature_add_left` and
  `TauCeti.IsEhresmannConnection.curvature_smul_left`, with their right-hand versions: the
  curvature is alternating and linear over functions on the base.
* `TauCeti.IsEhresmannConnection.curvature_eq_zero_iff_isInvolutiveDistribution`: the connection
  is flat exactly when its horizontal distribution is involutive.
* `TauCeti.IsEhresmannConnection.curvature_congr`: the curvature at `x` of smooth fields depends
  only on their values at `f x`.
* `TauCeti.IsEhresmannConnection.curvatureTensor_apply` and `eq_curvatureTensor_iff`: the
  curvature tensor computes the curvature of smooth fields, and is characterized by this;
  `curvatureTensor_mem_ker`, `curvatureTensor_self` and `curvatureTensor_swap`;
  `curvatureTensor_isAlt` states that it is alternating as Mathlib's `LinearMap.IsAlt`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.4.
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.3.
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer, 2013, Chapter 8 (naturality of the Lie bracket).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.
-/

public section

noncomputable section

open Function Bundle Filter VectorField
open scoped ContDiff Manifold Topology

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
    mlieBracket_swap (V := v₁), horizontalLiftField_neg]
  abel

theorem curvature_swap_apply (x : P) : hD.curvature v₁ v₂ x = -hD.curvature v₂ v₁ x := by
  rw [curvature_swap, Pi.neg_apply]

@[simp]
theorem curvature_self : hD.curvature v₁ v₁ = 0 := by
  simp [curvature_def, mlieBracket_self]

/-- The curvature does not depend on the smoothness index at which the connection is seen. -/
theorem curvature_of_le {m : ℕ∞ω} (hmn : m ≤ n) :
    (hD.of_le hmn).curvature = hD.curvature := by
  ext v₁ v₂ : 2
  rw [curvature_def, curvature_def, hD.horizontalLiftField_of_le _ hmn,
    hD.horizontalLiftField_of_le _ hmn, hD.horizontalLiftField_of_le _ hmn]

@[simp]
theorem curvature_zero_left : hD.curvature 0 v₂ = 0 := by
  simp [curvature_def, horizontalLiftField_zero]

@[simp]
theorem curvature_zero_right : hD.curvature v₁ 0 = 0 := by
  simp [curvature_def, horizontalLiftField_zero]

section Locality

/-! ### Locality -/

variable {m : ℕ∞ω} {D' : Π x : P, Submodule 𝕜 (TangentSpace I x)}
  (hD' : IsEhresmannConnection I J m f D')

/-- **The curvature is local.** The curvature at `x` of two Ehresmann connections on `f` that
agree near `x`, on vector fields that agree near `f x`, is the same. -/
theorem curvature_apply_eq_of_eventuallyEq {x : P} (hDD' : ∀ᶠ y in 𝓝 x, D y = D' y)
    {v₁ v₁' v₂ v₂' : Π b : B, TangentSpace J b} (h₁ : v₁ =ᶠ[𝓝 (f x)] v₁')
    (h₂ : v₂ =ᶠ[𝓝 (f x)] v₂') :
    hD.curvature v₁ v₂ x = hD'.curvature v₁' v₂' x := by
  rw [curvature_apply, curvature_apply,
    (hD.horizontalLiftField_eventuallyEq hD' hDD' h₁).mlieBracket_vectorField_eq
      (hD.horizontalLiftField_eventuallyEq hD' hDD' h₂),
    hD.horizontalLiftField_apply_eq_of_eq hD' hDD'.self_of_nhds
      (h₁.mlieBracket_vectorField_eq h₂)]

end Locality

section Smooth

/-! ### Verticality and linearity -/

variable [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F]
  [IsManifold I 2 P] [IsManifold J 2 B]

attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField

/-- The derivative of `f` maps the bracket of the horizontal lifts of `v₁ v₂` at `x` to the
bracket of `v₁ v₂` at `f x`, for a `C^n` connection with `1 ≤ n`, `f` of class `C^2` at `x`
and `v₁ v₂` of class `C^1` at `f x`. -/
theorem mfderiv_mlieBracket_horizontalLiftField (hn : 1 ≤ n) {x : P}
    (hf : ContMDiffAt I J 2 f x) {v₁ v₂ : Π b : B, TangentSpace J b}
    (hv₁ : ContMDiffAt J J.tangent 1 (T% v₁) (f x))
    (hv₂ : ContMDiffAt J J.tangent 1 (T% v₂) (f x)) :
    mfderiv I J f x (mlieBracket I (hD.horizontalLiftField v₁) (hD.horizontalLiftField v₂) x) =
      mlieBracket J v₁ v₂ (f x) :=
  mfderiv_mlieBracket_of_eventually_related hf (by simp)
    (hD.mdifferentiableAt_horizontalLiftField hn hf hv₁)
    (hD.mdifferentiableAt_horizontalLiftField hn hf hv₂)
    (hv₁.mdifferentiableAt one_ne_zero) (hv₂.mdifferentiableAt one_ne_zero)
    (.of_forall fun y ↦ hD.mfderiv_horizontalLiftField v₁ y)
    (.of_forall fun y ↦ hD.mfderiv_horizontalLiftField v₂ y)

/-- The curvature is **vertical**: for a `C^n` connection with `1 ≤ n`, `f` of class `C^2` at
`x` and `v₁ v₂` of class `C^1` at `f x`, the curvature at `x` lies in the kernel of the
derivative of `f`. -/
theorem curvature_mem_ker (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    {v₁ v₂ : Π b : B, TangentSpace J b} (hv₁ : ContMDiffAt J J.tangent 1 (T% v₁) (f x))
    (hv₂ : ContMDiffAt J J.tangent 1 (T% v₂) (f x)) :
    hD.curvature v₁ v₂ x ∈ (mfderiv I J f x).ker := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, curvature_apply, map_sub,
    hD.mfderiv_mlieBracket_horizontalLiftField hn hf hv₁ hv₂, mfderiv_horizontalLiftField,
    sub_self]

/-- The curvature vanishes at `x` exactly when the bracket of the horizontal lifts of `v₁ v₂` is
horizontal at `x`, for a `C^n` connection with `1 ≤ n`, `f` of class `C^2` at `x` and
`v₁ v₂` of class `C^1` at `f x`. -/
theorem curvature_eq_zero_iff_mem (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    {v₁ v₂ : Π b : B, TangentSpace J b} (hv₁ : ContMDiffAt J J.tangent 1 (T% v₁) (f x))
    (hv₂ : ContMDiffAt J J.tangent 1 (T% v₂) (f x)) :
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
`C^1` at `f x`, for a `C^n` connection with `1 ≤ n` and `f` of class `C^2` at `x`. -/
theorem curvature_add_left (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    {v₁ v₁' : Π b : B, TangentSpace J b} (v₂ : Π b : B, TangentSpace J b)
    (hv₁ : ContMDiffAt J J.tangent 1 (T% v₁) (f x))
    (hv₁' : ContMDiffAt J J.tangent 1 (T% v₁') (f x)) :
    hD.curvature (v₁ + v₁') v₂ x = hD.curvature v₁ v₂ x + hD.curvature v₁' v₂ x := by
  simp only [curvature_apply, horizontalLiftField_add,
    mlieBracket_add_left (hD.mdifferentiableAt_horizontalLiftField hn hf hv₁)
      (hD.mdifferentiableAt_horizontalLiftField hn hf hv₁'),
    horizontalLiftField_apply,
    mlieBracket_add_left (hv₁.mdifferentiableAt one_ne_zero)
      (hv₁'.mdifferentiableAt one_ne_zero), map_add, Submodule.coe_add]
  abel

/-- The curvature is additive in its second argument, at a point `x` where the fields are
`C^1` at `f x`, for a `C^n` connection with `1 ≤ n` and `f` of class `C^2` at `x`. -/
theorem curvature_add_right (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    (v₁ : Π b : B, TangentSpace J b) {v₂ v₂' : Π b : B, TangentSpace J b}
    (hv₂ : ContMDiffAt J J.tangent 1 (T% v₂) (f x))
    (hv₂' : ContMDiffAt J J.tangent 1 (T% v₂') (f x)) :
    hD.curvature v₁ (v₂ + v₂') x = hD.curvature v₁ v₂ x + hD.curvature v₁ v₂' x := by
  rw [curvature_swap_apply, hD.curvature_add_left hn hf v₁ hv₂ hv₂', neg_add,
    ← curvature_swap_apply, ← curvature_swap_apply]

/-- The curvature is linear over functions on the base in its first argument: for a function
`g` on `B` differentiable at `f x`, `g • v₁` has curvature `g (f x) • curvature v₁ v₂` at `x`,
for a `C^n` connection with `1 ≤ n`, `f` of class `C^2` at `x` and `v₁` of class `C^1` at
`f x`. -/
theorem curvature_smul_left (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    {g : B → 𝕜} (hg : MDifferentiableAt J 𝓘(𝕜) g (f x)) {v₁ : Π b : B, TangentSpace J b}
    (v₂ : Π b : B, TangentSpace J b) (hv₁ : ContMDiffAt J J.tangent 1 (T% v₁) (f x)) :
    hD.curvature (g • v₁) v₂ x = g (f x) • hD.curvature v₁ v₂ x := by
  have hfx : MDifferentiableAt I J f x := hf.mdifferentiableAt (by simp)
  have hP := mlieBracket_smul_left (W := hD.horizontalLiftField v₂) (hg.comp x hfx)
    (hD.mdifferentiableAt_horizontalLiftField hn hf hv₁)
  have hB := mlieBracket_smul_left (W := v₂) hg (hv₁.mdifferentiableAt one_ne_zero)
  rw [mvfderiv_comp_apply x hg hfx, mfderiv_horizontalLiftField] at hP
  simp [curvature_apply, horizontalLiftField_smul, hP, hB, smul_sub]

/-- The curvature is linear over functions on the base in its second argument: for a function
`g` on `B` differentiable at `f x`, `g • v₂` has curvature `g (f x) • curvature v₁ v₂` at `x`,
for a `C^n` connection with `1 ≤ n`, `f` of class `C^2` at `x` and `v₂` of class `C^1` at
`f x`. -/
theorem curvature_smul_right (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    {g : B → 𝕜} (hg : MDifferentiableAt J 𝓘(𝕜) g (f x)) (v₁ : Π b : B, TangentSpace J b)
    {v₂ : Π b : B, TangentSpace J b} (hv₂ : ContMDiffAt J J.tangent 1 (T% v₂) (f x)) :
    hD.curvature v₁ (g • v₂) x = g (f x) • hD.curvature v₁ v₂ x := by
  rw [curvature_swap_apply, hD.curvature_smul_left hn hf hg v₁ hv₂, ← smul_neg,
    ← curvature_swap_apply]

/-! ### Flatness and involutivity -/

/-- If the horizontal distribution of a `C^n` connection, with `1 ≤ n`, is involutive, then its
curvature vanishes at every point `x` where `f` is `C^2`, on fields that are `C^1` at `f x`. -/
theorem curvature_eq_zero_of_isInvolutiveDistribution (hn : 1 ≤ n) {x : P}
    (hf : ContMDiffAt I J 2 f x) (hDi : IsInvolutiveDistribution I D)
    {v₁ v₂ : Π b : B, TangentSpace J b} (hv₁ : ContMDiffAt J J.tangent 1 (T% v₁) (f x))
    (hv₂ : ContMDiffAt J J.tangent 1 (T% v₂) (f x)) :
    hD.curvature v₁ v₂ x = 0 := by
  -- The lifts are `C^1` at `x`, so differentiable near `x`.
  have hnear {v : Π b : B, TangentSpace J b} (hv : ContMDiffAt J J.tangent 1 (T% v) (f x)) :
      ∀ᶠ y in nhds x, MDifferentiableAt I I.tangent (T% (hD.horizontalLiftField v)) y :=
    (hD.contMDiffAt_one_horizontalLiftField hn hf hv).eventually_mdifferentiableAt one_ne_zero
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.1 ((hnear hv₁).and (hnear hv₂))
  exact (hD.curvature_eq_zero_iff_mem hn hf hv₁ hv₂).2 <| hDi.mlieBracket_mem hUo
    (fun y hy ↦ (hU y hy).1.mdifferentiableWithinAt)
    (fun y hy ↦ (hU y hy).2.mdifferentiableWithinAt)
    (fun y _ ↦ hD.horizontalLiftField_mem v₁ y) (fun y _ ↦ hD.horizontalLiftField_mem v₂ y) hxU

/-- If the curvature of a `C^n` connection on a `C^(n+1)` map `f`, with `1 ≤ n`, vanishes at
every point `x` on all fields that are `C^n` at `f x`, then the horizontal distribution is
involutive. -/
theorem isInvolutiveDistribution_of_curvature_eq_zero [FiniteDimensional 𝕜 F]
    [IsManifold J (n + 1) B] (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f)
    (h : ∀ ⦃x : P⦄ ⦃v₁ v₂ : Π b : B, TangentSpace J b⦄,
      ContMDiffAt J J.tangent n (T% v₁) (f x) → ContMDiffAt J J.tangent n (T% v₂) (f x) →
        hD.curvature v₁ v₂ x = 0) :
    IsInvolutiveDistribution I D := by
  rw [isInvolutiveDistribution_iff]
  intro U hU V W hV hW hVD hWD x hx
  -- Near `f x`, take a frame `v` of the tangent bundle of `B`; its lifts are a frame of `D`.
  obtain ⟨O, hO, hxO, v, hv⟩ := isContMDiffDistribution_iff.1
    (isContMDiffDistribution_top (I := J) (M := B) (n := n)) (f x)
  have hX := hD.isDistributionFrameOn_horizontalLiftField hO hv hf
  have hOx : f ⁻¹' O ∈ nhds x := hf.continuous.continuousAt.preimage_mem_nhds (hO.mem_nhds hxO)
  have hUx := hU.mem_nhds hx
  have hvx (i : Fin (Module.finrank 𝕜 F)) : ContMDiffAt J J.tangent n (T% (v i)) (f x) :=
    (hv.contMDiffOn i).contMDiffAt (hO.mem_nhds hxO)
  -- The brackets of the frame are horizontal, since the curvature vanishes.
  exact hX.mlieBracket_mem_of_forall_mlieBracket_mem hn hOx
    (fun i j ↦ (hD.curvature_eq_zero_iff_mem hn
      ((hf x).of_le (SymplecticGeometry.two_le_add_one_of_one_le hn))
      ((hvx i).of_le hn) ((hvx j).of_le hn)).1 (h (hvx i) (hvx j)))
    (hV.mdifferentiableAt hUx) (hW.mdifferentiableAt hUx) (eventually_of_mem hUx hVD)
    (eventually_of_mem hUx hWD)

/-- **A connection is flat exactly when it is involutive.** For a `C^n` Ehresmann connection
`D` on a `C^(n+1)` map `f`, with `1 ≤ n`, the curvature vanishes at every point `x` on all
fields that are `C^1` at `f x` if and only if `D` is an involutive distribution. -/
theorem curvature_eq_zero_iff_isInvolutiveDistribution [FiniteDimensional 𝕜 F]
    [IsManifold J (n + 1) B] (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f) :
    (∀ ⦃x : P⦄ ⦃v₁ v₂ : Π b : B, TangentSpace J b⦄,
      ContMDiffAt J J.tangent 1 (T% v₁) (f x) → ContMDiffAt J J.tangent 1 (T% v₂) (f x) →
        hD.curvature v₁ v₂ x = 0) ↔ IsInvolutiveDistribution I D :=
  ⟨fun h ↦ hD.isInvolutiveDistribution_of_curvature_eq_zero hn hf
      fun _ _ _ hv₁ hv₂ ↦ h (hv₁.of_le hn) (hv₂.of_le hn),
    fun hDi _ _ _ hv₁ hv₂ ↦ hD.curvature_eq_zero_of_isInvolutiveDistribution hn
      ((hf _).of_le (SymplecticGeometry.two_le_add_one_of_one_le hn)) hDi hv₁ hv₂⟩

end Smooth

section NaturalitySmooth

/-! ### Naturality of the curvature -/

variable [IsRCLikeNormedField 𝕜] [CompleteSpace E] [CompleteSpace F]
  [IsManifold I 2 P] [IsManifold J 2 B]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {P' : Type*} [TopologicalSpace P'] [ChartedSpace H' P'] [IsManifold I' 2 P']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [CompleteSpace F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {B' : Type*} [TopologicalSpace B'] [ChartedSpace G' B'] [IsManifold J' 2 B']
  {n' : ℕ∞ω} {f' : P' → B'} {D' : Π x : P', Submodule 𝕜 (TangentSpace I' x)}
  (hD' : IsEhresmannConnection I' J' n' f' D') {Φ : P → P'} {ψ : B → B'}

attribute [local instance] IsManifold.minSmoothness_of_isRCLikeNormedField

/-- **Naturality of the curvature.** Let `D` and `D'` be `C^n` and `C^n'` Ehresmann connections,
with `1 ≤ n` and `1 ≤ n'`, on maps `f : P → B` and `f' : P' → B'` that are `C^2` at `x` and at
`Φ x`. Let `Φ : P → P'`, of class `C^2` at `x`, cover `ψ : B → B'`, of class `C^2` at `f x`,
near `x` (`f' ∘ Φ = ψ ∘ f` near `x`), with the derivative of `Φ` mapping `D` into `D'` near
`x`. If the vector fields `v₁ v₂` on `B`, `C^1` at `f x`, are `ψ`-related near `f x` to the
vector fields `v₁' v₂'` on `B'`, `C^1` at `f' (Φ x)`, then the derivative of `Φ` at `x` maps the
curvature of `D` on `v₁ v₂` at `x` to the curvature of `D'` on `v₁' v₂'` at `Φ x`. -/
theorem mfderiv_curvature_of_related (hn : 1 ≤ n) (hn' : 1 ≤ n') {x : P}
    (hf : ContMDiffAt I J 2 f x) (hf' : ContMDiffAt I' J' 2 f' (Φ x))
    (hΦ : ContMDiffAt I I' 2 Φ x) (hψ : ContMDiffAt J J' 2 ψ (f x))
    (hfΦ : f' ∘ Φ =ᶠ[𝓝 x] ψ ∘ f)
    (hΦD : ∀ᶠ y in 𝓝 x, ∀ w ∈ D y, mfderiv I I' Φ y w ∈ D' (Φ y))
    {v₁ v₂ : Π b : B, TangentSpace J b} {v₁' v₂' : Π b : B', TangentSpace J' b}
    (hv₁ : ContMDiffAt J J.tangent 1 (T% v₁) (f x))
    (hv₂ : ContMDiffAt J J.tangent 1 (T% v₂) (f x))
    (hv₁' : ContMDiffAt J' J'.tangent 1 (T% v₁') (f' (Φ x)))
    (hv₂' : ContMDiffAt J' J'.tangent 1 (T% v₂') (f' (Φ x)))
    (h₁ : ∀ᶠ b in 𝓝 (f x), mfderiv J J' ψ b (v₁ b) = v₁' (ψ b))
    (h₂ : ∀ᶠ b in 𝓝 (f x), mfderiv J J' ψ b (v₂ b) = v₂' (ψ b)) :
    mfderiv I I' Φ x (hD.curvature v₁ v₂ x) = hD'.curvature v₁' v₂' (Φ x) := by
  have hx : f' (Φ x) = ψ (f x) := hfΦ.self_of_nhds
  have hrel {v : Π b : B, TangentSpace J b} {v' : Π b : B', TangentSpace J' b}
      (h : ∀ᶠ b in 𝓝 (f x), mfderiv J J' ψ b (v b) = v' (ψ b)) :=
    hD.eventually_mfderiv_horizontalLiftField_eq_of_related hD'
      (hΦ.eventually_mdifferentiableAt two_ne_zero) (hψ.eventually_mdifferentiableAt two_ne_zero)
      hfΦ hΦD h
  -- The brackets on the base are `ψ`-related at `f x`.
  have hbr : mfderiv J J' ψ (f x) (mlieBracket J v₁ v₂ (f x)) =
      mlieBracket J' v₁' v₂' (f' (Φ x)) := by
    rw [hx]
    rw [hx] at hv₁' hv₂'
    exact mfderiv_mlieBracket_of_eventually_related hψ (by simp)
      (hv₁.mdifferentiableAt one_ne_zero) (hv₂.mdifferentiableAt one_ne_zero)
      (hv₁'.mdifferentiableAt one_ne_zero) (hv₂'.mdifferentiableAt one_ne_zero) h₁ h₂
  rw [curvature_apply, curvature_apply, map_sub,
    mfderiv_mlieBracket_of_eventually_related hΦ (by simp)
      (hD.mdifferentiableAt_horizontalLiftField hn hf hv₁)
      (hD.mdifferentiableAt_horizontalLiftField hn hf hv₂)
      (hD'.mdifferentiableAt_horizontalLiftField hn' hf' hv₁')
      (hD'.mdifferentiableAt_horizontalLiftField hn' hf' hv₂') (hrel h₁) (hrel h₂),
    hD.mfderiv_horizontalLiftField_eq_of_related hD' (hΦ.mdifferentiableAt two_ne_zero)
      (hψ.mdifferentiableAt two_ne_zero) hfΦ hΦD.self_of_nhds hbr]

end NaturalitySmooth

section Pointwise

/-! ### Pointwise dependence and the curvature tensor -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I 2 P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B] [T2Space B] [IsManifold J ∞ B]
  {n : ℕ∞ω} {f : P → B} {D : Π x : P, Submodule ℝ (TangentSpace I x)}
  (hD : IsEhresmannConnection I J n f D)

/-- The curvature is a tensor: for a `C^n` connection with `1 ≤ n` and `f` of class `C^2` at
`x`, the curvature at `x` of smooth vector fields `v₁ v₂` on the base depends only on their values
at `f x`. -/
theorem curvature_congr (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    {v₁ v₁' v₂ v₂' : Π b : B, TangentSpace J b}
    (hv₁ : CMDiff ∞ (T% v₁)) (hv₁' : CMDiff ∞ (T% v₁'))
    (hv₂ : CMDiff ∞ (T% v₂)) (hv₂' : CMDiff ∞ (T% v₂'))
    (h₁ : v₁ (f x) = v₁' (f x)) (h₂ : v₂ (f x) = v₂' (f x)) :
    hD.curvature v₁ v₂ x = hD.curvature v₁' v₂' x := by
  -- The fields are smooth, so `C^1` at `f x`.
  have h1 : (1 : ℕ∞ω) ≤ ∞ := ENat.LEInfty.out
  calc hD.curvature v₁ v₂ x = hD.curvature v₁' v₂ x :=
        Manifold.eq_of_contMDiff_tensorial (G := F) (W := TangentSpace J)
          (fun v ↦ hD.curvature v v₂ x) (f x)
          (fun hv hv' ↦ hD.curvature_add_left hn hf v₂ ((hv _).of_le h1) ((hv' _).of_le h1))
          (fun hg hv ↦ hD.curvature_smul_left hn hf (hg.mdifferentiableAt (by simp)) v₂
            ((hv _).of_le h1))
          hv₁ hv₁' h₁
    _ = hD.curvature v₁' v₂' x :=
        Manifold.eq_of_contMDiff_tensorial (G := F) (W := TangentSpace J)
          (fun v ↦ hD.curvature v₁' v x) (f x)
          (fun hv hv' ↦ hD.curvature_add_right hn hf v₁' ((hv _).of_le h1) ((hv' _).of_le h1))
          (fun hg hv ↦ hD.curvature_smul_right hn hf (hg.mdifferentiableAt (by simp)) v₁'
            ((hv _).of_le h1))
          hv₂ hv₂' h₂

/-- The **curvature tensor** of an Ehresmann connection `D` at `x`, for a `C^n` connection with
`1 ≤ n` and `f` of class `C^2` at `x`: the bilinear map on `TangentSpace J (f x)` whose value on
`v₁ (f x)` and `v₂ (f x)` is the curvature `hD.curvature v₁ v₂ x`, for smooth vector fields
`v₁ v₂` on the base (`curvatureTensor_apply`). -/
def curvatureTensor (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x) :
    TangentSpace J (f x) →ₗ[ℝ] TangentSpace J (f x) →ₗ[ℝ] TangentSpace I x :=
  have hc (c : ℝ) (s : Π b : B, TangentSpace J b) : c • s = (fun _ : B ↦ c) • s :=
    funext fun y ↦ by rw [Pi.smul_apply, Pi.smul_apply']
  LinearMap.mk₂ ℝ
    (fun u v ↦ hD.curvature (FiberBundle.contMDiffExtend J F u)
      (FiberBundle.contMDiffExtend J F v) x)
    (fun u u' v ↦ by
      rw [FiberBundle.contMDiffExtend_add]
      exact hD.curvature_add_left hn hf _ (FiberBundle.contMDiff_contMDiffExtend J F u _)
        (FiberBundle.contMDiff_contMDiffExtend J F u' _))
    (fun c u v ↦ by
      rw [FiberBundle.contMDiffExtend_smul, hc]
      exact hD.curvature_smul_left hn hf mdifferentiableAt_const _
        (FiberBundle.contMDiff_contMDiffExtend J F u _))
    (fun u v v' ↦ by
      rw [FiberBundle.contMDiffExtend_add]
      exact hD.curvature_add_right hn hf _ (FiberBundle.contMDiff_contMDiffExtend J F v _)
        (FiberBundle.contMDiff_contMDiffExtend J F v' _))
    (fun c u v ↦ by
      rw [FiberBundle.contMDiffExtend_smul, hc]
      exact hD.curvature_smul_right hn hf mdifferentiableAt_const _
        (FiberBundle.contMDiff_contMDiffExtend J F v _))

/-- The curvature tensor at `x` computes the curvature at `x` of smooth vector fields on the
base, from their values at `f x`. -/
theorem curvatureTensor_apply (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    {v₁ v₂ : Π b : B, TangentSpace J b} (hv₁ : CMDiff ∞ (T% v₁)) (hv₂ : CMDiff ∞ (T% v₂)) :
    hD.curvatureTensor hn hf (v₁ (f x)) (v₂ (f x)) = hD.curvature v₁ v₂ x :=
  hD.curvature_congr hn hf (FiberBundle.contMDiff_contMDiffExtend (n := ∞) J F _) hv₁
    (FiberBundle.contMDiff_contMDiffExtend (n := ∞) J F _) hv₂
    (FiberBundle.contMDiffExtend_apply_self J F _) (FiberBundle.contMDiffExtend_apply_self J F _)

/-- The curvature tensor is the only bilinear map on `TangentSpace J (f x)` that computes the
curvature at `x` of smooth vector fields on the base from their values at `f x`. -/
theorem eq_curvatureTensor_iff (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    (R : TangentSpace J (f x) →ₗ[ℝ] TangentSpace J (f x) →ₗ[ℝ] TangentSpace I x) :
    R = hD.curvatureTensor hn hf ↔
      ∀ v₁ v₂ : Π b : B, TangentSpace J b, CMDiff ∞ (T% v₁) → CMDiff ∞ (T% v₂) →
        R (v₁ (f x)) (v₂ (f x)) = hD.curvature v₁ v₂ x := by
  refine ⟨fun h v₁ v₂ hv₁ hv₂ ↦ h ▸ hD.curvatureTensor_apply hn hf hv₁ hv₂, fun h ↦ ?_⟩
  ext u v
  obtain ⟨v₁, hv₁, rfl⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ u
  obtain ⟨v₂, hv₂, rfl⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ v
  rw [h v₁ v₂ hv₁ hv₂, hD.curvatureTensor_apply hn hf hv₁ hv₂]

/-- The values of the curvature tensor are vertical: they lie in the kernel of the derivative
of `f` at `x`. -/
theorem curvatureTensor_mem_ker (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    (u v : TangentSpace J (f x)) :
    hD.curvatureTensor hn hf u v ∈ (mfderiv I J f x).ker := by
  obtain ⟨v₁, hv₁, rfl⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ u
  obtain ⟨v₂, hv₂, rfl⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ v
  rw [hD.curvatureTensor_apply hn hf hv₁ hv₂]
  exact hD.curvature_mem_ker hn hf ((hv₁ _).of_le ENat.LEInfty.out)
    ((hv₂ _).of_le ENat.LEInfty.out)

/-- The curvature tensor is alternating. -/
@[simp]
theorem curvatureTensor_self (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    (u : TangentSpace J (f x)) : hD.curvatureTensor hn hf u u = 0 := by
  obtain ⟨v, hv, rfl⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ u
  rw [hD.curvatureTensor_apply hn hf hv hv, curvature_self, Pi.zero_apply]

/-- The curvature tensor is an alternating bilinear map, in the sense of Mathlib's
`LinearMap.IsAlt`. -/
theorem curvatureTensor_isAlt (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x) :
    (hD.curvatureTensor hn hf).IsAlt :=
  hD.curvatureTensor_self hn hf

/-- The curvature tensor is antisymmetric. -/
theorem curvatureTensor_swap (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    (u v : TangentSpace J (f x)) :
    hD.curvatureTensor hn hf u v = -hD.curvatureTensor hn hf v u :=
  ((hD.curvatureTensor_isAlt hn hf).neg v u).symm

end Pointwise

end IsEhresmannConnection

end TauCeti
