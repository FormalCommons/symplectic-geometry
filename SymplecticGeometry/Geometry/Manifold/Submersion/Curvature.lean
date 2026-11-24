/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Submersion.HorizontalLiftField
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality
import TauCeti.Geometry.Manifold.VectorField.Related

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

Over `ℝ`, on a finite-dimensional Hausdorff base, these laws make the curvature at `x` of smooth
fields depend only on their values at `f x` (`curvature_congr`), by Tau Ceti's tensoriality
criterion `TauCeti.Manifold.eq_of_contMDiff_tensorial`. Every tangent vector of the base is the
value of a smooth global field (Tau Ceti's `FiberBundle.contMDiffExtend`), so the curvature at
`x` is a bilinear map on `TangentSpace J (f x)` with values in `TangentSpace I x`,
`curvatureTensor`; it is alternating and its values are vertical. The construction follows that
of Tau Ceti's `CovariantDerivative.curvatureTensor` from
`CovariantDerivative.curvatureOperator_congr`.

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
* `TauCeti.IsEhresmannConnection.curvature_swap`,
  `TauCeti.IsEhresmannConnection.curvature_add_left` and
  `TauCeti.IsEhresmannConnection.curvature_smul_left`, with their right-hand versions: the
  curvature is alternating and linear over functions on the base.
* `TauCeti.IsEhresmannConnection.curvature_congr`: the curvature at `x` of smooth fields depends
  only on their values at `f x`.
* `TauCeti.IsEhresmannConnection.curvatureTensor_apply` and `eq_curvatureTensor_iff`: the
  curvature tensor computes the curvature of smooth fields, and is characterized by this;
  `curvatureTensor_mem_ker`, `curvatureTensor_self` and `curvatureTensor_swap`.

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

end Smooth

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
  -- The curvature of `hD` is that of `hD` seen as a `C^1` connection.
  rw [← hD.curvature_of_le hn]
  set hD₁ := hD.of_le hn
  have hf₁ : ContMDiffAt I J (1 + 1) f x := by rwa [one_add_one_eq_two]
  have hsm {v : Π b : B, TangentSpace J b} (hv : CMDiff ∞ (T% v)) :
      ContMDiffAt J J.tangent 1 (T% v) (f x) :=
    (hv (f x)).of_le (by exact_mod_cast le_top)
  calc hD₁.curvature v₁ v₂ x = hD₁.curvature v₁' v₂ x :=
        Manifold.eq_of_contMDiff_tensorial (G := F) (W := TangentSpace J)
          (fun v ↦ hD₁.curvature v v₂ x) (f x)
          (fun hv hv' ↦ hD₁.curvature_add_left le_rfl hf₁ v₂ (hsm hv) (hsm hv'))
          (fun hg hv ↦ hD₁.curvature_smul_left le_rfl hf₁ (hg.mdifferentiableAt (by simp)) v₂
            (hsm hv))
          hv₁ hv₁' h₁
    _ = hD₁.curvature v₁' v₂' x :=
        Manifold.eq_of_contMDiff_tensorial (G := F) (W := TangentSpace J)
          (fun v ↦ hD₁.curvature v₁' v x) (f x)
          (fun hv hv' ↦ hD₁.curvature_add_right le_rfl hf₁ v₁' (hsm hv) (hsm hv'))
          (fun hg hv ↦ hD₁.curvature_smul_right le_rfl hf₁ (hg.mdifferentiableAt (by simp)) v₁'
            (hsm hv))
          hv₂ hv₂' h₂

/-- The **curvature tensor** of an Ehresmann connection `D` at `x`, for a `C^n` connection with
`1 ≤ n` and `f` of class `C^2` at `x`: the bilinear map on `TangentSpace J (f x)` whose value on
`v₁ (f x)` and `v₂ (f x)` is the curvature `hD.curvature v₁ v₂ x`, for smooth vector fields
`v₁ v₂` on the base (`curvatureTensor_apply`). -/
def curvatureTensor (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x) :
    TangentSpace J (f x) →ₗ[ℝ] TangentSpace J (f x) →ₗ[ℝ] TangentSpace I x :=
  -- The linearity laws are those of the curvature of `hD` seen as a `C^1` connection.
  have hf₁ : ContMDiffAt I J (1 + 1) f x := by rwa [one_add_one_eq_two]
  have hsm (u : TangentSpace J (f x)) :
      ContMDiffAt J J.tangent 1 (T% (FiberBundle.contMDiffExtend J F u)) (f x) :=
    (FiberBundle.contMDiff_contMDiffExtend (n := ∞) J F u (f x)).of_le
      (by exact_mod_cast le_top)
  have hc (c : ℝ) (s : Π b : B, TangentSpace J b) : c • s = (fun _ : B ↦ c) • s :=
    funext fun y ↦ by rw [Pi.smul_apply, Pi.smul_apply']
  LinearMap.mk₂ ℝ
    (fun u v ↦ hD.curvature (FiberBundle.contMDiffExtend J F u)
      (FiberBundle.contMDiffExtend J F v) x)
    (fun u u' v ↦ by
      rw [FiberBundle.contMDiffExtend_add, ← hD.curvature_of_le hn]
      exact (hD.of_le hn).curvature_add_left le_rfl hf₁ _ (hsm u) (hsm u'))
    (fun c u v ↦ by
      rw [FiberBundle.contMDiffExtend_smul, hc, ← hD.curvature_of_le hn]
      exact (hD.of_le hn).curvature_smul_left le_rfl hf₁ mdifferentiableAt_const _ (hsm u))
    (fun u v v' ↦ by
      rw [FiberBundle.contMDiffExtend_add, ← hD.curvature_of_le hn]
      exact (hD.of_le hn).curvature_add_right le_rfl hf₁ _ (hsm v) (hsm v'))
    (fun c u v ↦ by
      rw [FiberBundle.contMDiffExtend_smul, hc, ← hD.curvature_of_le hn]
      exact (hD.of_le hn).curvature_smul_right le_rfl hf₁ mdifferentiableAt_const _ (hsm v))

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
  rw [hD.curvatureTensor_apply hn hf hv₁ hv₂, ← hD.curvature_of_le hn]
  exact (hD.of_le hn).curvature_mem_ker le_rfl (by rwa [one_add_one_eq_two])
    ((hv₁ (f x)).of_le (by exact_mod_cast le_top)) ((hv₂ (f x)).of_le (by exact_mod_cast le_top))

/-- The curvature tensor is alternating. -/
@[simp]
theorem curvatureTensor_self (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    (u : TangentSpace J (f x)) : hD.curvatureTensor hn hf u u = 0 := by
  obtain ⟨v, hv, rfl⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ u
  rw [hD.curvatureTensor_apply hn hf hv hv, curvature_self, Pi.zero_apply]

/-- The curvature tensor is antisymmetric. -/
theorem curvatureTensor_swap (hn : 1 ≤ n) {x : P} (hf : ContMDiffAt I J 2 f x)
    (u v : TangentSpace J (f x)) :
    hD.curvatureTensor hn hf u v = -hD.curvatureTensor hn hf v u := by
  obtain ⟨v₁, hv₁, rfl⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ u
  obtain ⟨v₂, hv₂, rfl⟩ := FiberBundle.exists_contMDiff_section_eq J F ∞ v
  rw [hD.curvatureTensor_apply hn hf hv₁ hv₂, hD.curvatureTensor_apply hn hf hv₂ hv₁,
    curvature_swap_apply]
end Pointwise

end IsEhresmannConnection

end TauCeti
