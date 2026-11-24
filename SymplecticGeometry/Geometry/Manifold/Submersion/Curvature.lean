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
import TauCeti.Geometry.Manifold.Distribution.VectorBundle

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

The curvature is alternating, additive in each argument, and linear over differentiable functions
on the base: `g • v₁` has curvature `(g ∘ f) • curvature v₁ v₂`, by the Leibniz rule for the
bracket (`VectorField.mlieBracket_smul_left`) on `B` and on `P`.

The connection is flat, its curvature vanishing at every point `x` on all fields that are `C^n`
at `f x`, exactly when `D` is involutive in the sense of Tau Ceti's
`TauCeti.IsInvolutiveDistribution`. If `D` is involutive, the bracket of two lifts is
horizontal, so the curvature, which is vertical, vanishes. Conversely, near a point the lifts of
a local frame of the tangent bundle of `B` form a local frame of `D`
(`TauCeti.IsEhresmannConnection.isDistributionFrameOn_horizontalLiftField`); fields tangent to
`D` are combinations of it with differentiable coefficients
(`TauCeti.IsDistributionFrameOn.exists_mdifferentiableAt_coeff`), and the brackets of such
combinations are horizontal when those of the frame are, by Tau Ceti's
`TauCeti.mlieBracket_sum_smul_mem`.

On signs: Guillemin–Lerman–Sternberg (§1.3) bracket vector fields as Mathlib does, and their
curvature agrees with `curvature`. In McDuff–Salamon (§6.4, p. 277) the bracket is minus Mathlib's,
and their curvature is `-curvature`.

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
* `TauCeti.IsEhresmannConnection.curvature_eq_zero_iff_isInvolutiveDistribution`: the connection
  is flat exactly when its horizontal distribution is involutive.

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
    mlieBracket_swap (V := v₁), horizontalLiftField_neg]
  abel

theorem curvature_swap_apply (x : P) : hD.curvature v₁ v₂ x = -hD.curvature v₂ v₁ x := by
  rw [curvature_swap, Pi.neg_apply]

@[simp]
theorem curvature_self : hD.curvature v₁ v₁ = 0 := by
  simp [curvature_def, mlieBracket_self]

@[simp]
theorem curvature_zero_left : hD.curvature 0 v₂ = 0 := by
  simp [curvature_def, horizontalLiftField_zero]

@[simp]
theorem curvature_zero_right : hD.curvature v₁ 0 = 0 := by
  simp [curvature_def, horizontalLiftField_zero]

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
  simp [curvature_apply, horizontalLiftField_smul, hP, hB, smul_sub]

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

/-! ### Flatness and involutivity -/

/-- If the horizontal distribution of a `C^n` connection on a `C^(n+1)` map `f`, with `1 ≤ n`, is
involutive, then its curvature vanishes at every point `x` on fields that are `C^n` at
`f x`. -/
theorem curvature_eq_zero_of_isInvolutiveDistribution (hn : 1 ≤ n)
    (hf : ContMDiff I J (n + 1) f) (hDi : IsInvolutiveDistribution I D) {x : P}
    {v₁ v₂ : Π b : B, TangentSpace J b} (hv₁ : ContMDiffAt J J.tangent n (T% v₁) (f x))
    (hv₂ : ContMDiffAt J J.tangent n (T% v₂) (f x)) :
    hD.curvature v₁ v₂ x = 0 := by
  have h2 : (2 : ℕ∞ω) ≤ n + 1 := by
    simpa [one_add_one_eq_two] using add_le_add_left hn 1
  have hf2 : ContMDiff I J 2 f := hf.of_le h2
  -- Near `f x` the fields are `C¹`, so near `x` their lifts are differentiable.
  have hnear {v : Π b : B, TangentSpace J b} (hv : ContMDiffAt J J.tangent n (T% v) (f x)) :
      ∀ᶠ y in nhds x, MDifferentiableAt I I.tangent (T% (hD.horizontalLiftField v)) y := by
    have h1 := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 (hv.of_le hn)
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds h1] with y hy
    rw [← hD.horizontalLiftField_of_le v hn]
    exact (hD.of_le hn).mdifferentiableAt_horizontalLiftField le_rfl (hf2 y) hy
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.1 ((hnear hv₁).and (hnear hv₂))
  exact (hD.curvature_eq_zero_iff_mem hn (hf x) hv₁ hv₂).2 <| hDi.mlieBracket_mem hUo
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
  obtain ⟨c, hc, hVc⟩ := hX.exists_mdifferentiableAt_coeff hn hOx (hV.mdifferentiableAt hUx)
    (eventually_of_mem hUx hVD)
  obtain ⟨d, hd, hWd⟩ := hX.exists_mdifferentiableAt_coeff hn hOx (hW.mdifferentiableAt hUx)
    (eventually_of_mem hUx hWD)
  have hvx (i : Fin (Module.finrank 𝕜 F)) : ContMDiffAt J J.tangent n (T% (v i)) (f x) :=
    (hv.contMDiffOn i).contMDiffAt (hO.mem_nhds hxO)
  -- Near `x`, `V` and `W` are combinations of the lifts, whose brackets are horizontal.
  have hV' : V =ᶠ[nhds x]
      (∑ i, c i • hD.horizontalLiftField (v i) : Π y : P, TangentSpace I y) := by
    filter_upwards [hVc] with y hy
    simp only [Finset.sum_apply, Pi.smul_apply']
    -- The two sums differ only in the instance on `TangentSpace I y`, which unfolds to `E`.
    exact hy
  have hW' : W =ᶠ[nhds x]
      (∑ i, d i • hD.horizontalLiftField (v i) : Π y : P, TangentSpace I y) := by
    filter_upwards [hWd] with y hy
    simp only [Finset.sum_apply, Pi.smul_apply']
    -- The two sums differ only in the instance on `TangentSpace I y`, which unfolds to `E`.
    exact hy
  rw [hV'.mlieBracket_vectorField_eq hW']
  exact mlieBracket_sum_smul_mem
    (fun i _ ↦ hD.mdifferentiableAt_horizontalLiftField hn (hf x) (hvx i))
    (fun i _ ↦ hD.horizontalLiftField_mem _ x)
    (fun i _ j _ ↦ (hD.curvature_eq_zero_iff_mem hn (hf x) (hvx i) (hvx j)).1 (h (hvx i) (hvx j)))
    (fun i _ ↦ hc i) (fun i _ ↦ hd i)

/-- **A connection is flat exactly when it is involutive.** For a `C^n` Ehresmann connection
`D` on a `C^(n+1)` map `f`, with `1 ≤ n`, the curvature vanishes at every point `x` on all
fields that are `C^n` at `f x` if and only if `D` is an involutive distribution. -/
theorem curvature_eq_zero_iff_isInvolutiveDistribution [FiniteDimensional 𝕜 F]
    [IsManifold J (n + 1) B] (hn : 1 ≤ n) (hf : ContMDiff I J (n + 1) f) :
    (∀ ⦃x : P⦄ ⦃v₁ v₂ : Π b : B, TangentSpace J b⦄,
      ContMDiffAt J J.tangent n (T% v₁) (f x) → ContMDiffAt J J.tangent n (T% v₂) (f x) →
        hD.curvature v₁ v₂ x = 0) ↔ IsInvolutiveDistribution I D :=
  ⟨hD.isInvolutiveDistribution_of_curvature_eq_zero hn hf,
    fun hDi _ _ _ ↦ hD.curvature_eq_zero_of_isInvolutiveDistribution hn hf hDi⟩

end Smooth

end IsEhresmannConnection

end TauCeti
