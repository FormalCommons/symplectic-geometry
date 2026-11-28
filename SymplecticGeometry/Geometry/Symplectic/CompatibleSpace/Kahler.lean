/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.CompatibleSpace.ComplexStructure
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Symplectic.Manifold.Kahler
public import SymplecticGeometry.Topology.Algebra.Module.Trace
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Metric
import Mathlib.Tactic.NoncommRing
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import SymplecticGeometry.LinearAlgebra.Symplectic.CompatibleTangent.Basic

/-!
# The Kähler form and the metric of the space of compatible complex structures

Let `ω` be a symplectic form on a finite-dimensional real normed space `V`, and `𝒥 ω` the
manifold of `ω`-compatible complex structures, a submanifold of `V →L[ℝ] V` through
`ω.compatibleCLM`. For a tangent vector `a` at `J`, write `â` for its ambient reading, the image
of `a` under the differential of `ω.compatibleCLM`. This file gives `𝒥 ω` its Kähler form
`Ω_J(a, b) = ½ tr(â J b̂)` and its metric `g_J(a, b) = ½ tr(â b̂)`
(McDuff–Salamon, Example 4.3.6), and shows that the linear symplectomorphisms act on `𝒥 ω` by
isometries, transitively.

The form is the pull-back along `ω.compatibleCLM` of the two-form
`ContinuousLinearMap.traceTwoForm V` of `V →L[ℝ] V`, whose value at `A` is
`(X, Y) ↦ ¼ (tr (X A Y) - tr (Y A X))`. It is linear in `A`, so its exterior derivative is
constant, `(X, Y, Z) ↦ ¾ tr (X (Z Y - Y Z))`. On the tangent space at `J` the two traces of the
form are opposite, which gives the formula for `Ω`; and the exterior derivative vanishes there,
since `X` anticommutes with `J` while `Z Y - Y Z` commutes with it. As exterior differentiation
commutes with pull-backs, `Ω` is closed. This replaces the book's argument through the
Levi-Civita connection. Compatibility of `Ω` with the complex structure `Ĵ ↦ -J Ĵ` of
`compatibleSpaceComplexStructure` comes from positivity of `tr (Ĵ²)` for a nonzero tangent vector
`Ĵ` (`TauCeti.SymplecticForm.Compatible.trace_mul_self_pos`), and integrability from the global
chart, so `Ω` is a Kähler form. The metric is the metric `g(a, b) = Ω(a, j b)` of the compatible
pair, installed as the `RiemannianBundle` instance of the tangent bundle of `𝒥 ω`, as Tau Ceti
does for its model geometries (`TauCeti.Nil`).

## Main definitions and results

* `ContinuousLinearMap.traceTwoForm`: the two-form `¼ (tr (X A Y) - tr (Y A X))` of
  `V →L[ℝ] V`, with `traceTwoForm_apply`, its exterior derivative
  `mextDeriv_traceTwoForm_apply`, and its invariance under conjugation `traceTwoForm_conj`.
* `TauCeti.SymplecticForm.compatibleSpaceForm`: the form `Ω` of `𝒥 ω`, with
  `compatibleSpaceForm_apply`: `Ω_J(a, b) = ½ tr(â J b̂)`. Against the complex structure `j`,
  `Ω_J(a, j b) = ½ tr(â b̂)` (`compatibleSpaceForm_apply_compatibleSpaceComplexStructure`).
* `TauCeti.SymplecticForm.isClosed_compatibleSpaceForm`,
  `TauCeti.SymplecticForm.compatible_compatibleSpaceForm` and
  `TauCeti.SymplecticForm.isKahler_compatibleSpaceForm`: `Ω` is a Kähler form for
  `compatibleSpaceComplexStructure`.
* The `RiemannianBundle` instance of `𝒥 ω`, the metric of the pair
  (`TauCeti.SmoothTwoForm.Compatible.riemannianBundle`), with `inner_compatibleSpace_eq_eval₂`:
  `⟪a, b⟫ = Ω(a, j b)`, and `inner_compatibleSpace`: `⟪a, b⟫ = ½ tr(â b̂)`, half the pull-back of
  the trace form `ContinuousLinearMap.traceForm`
  (`inner_compatibleSpace_eq_smul_traceForm`, for the form `2⁻¹ • traceForm`).
* `TauCeti.SymplecticForm.mpullback_compatibleTransport_compatibleSpaceForm` and
  `TauCeti.SymplecticForm.compatibleTransportIsometry`: the transport by a linear
  symplectomorphism preserves `Ω` and is a Riemannian isometry; the isometry group acts
  transitively (`TauCeti.SymplecticForm.isPretransitive_isom_compatibleSpace`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], Example 4.3.6 and Exercise 4.3.7.
-/

public section

open scoped Manifold RealInnerProductSpace

namespace ContinuousLinearMap

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The trace two-form of the continuous endomorphisms -/

/-- The value of `traceTwoForm` at `A`, as a continuous linear function of `A`: the alternating
form `(X, Y) ↦ ¼ (tr (X A Y) - tr (Y A X))`. -/
noncomputable def traceTwoFormCLM :
    (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V) [⋀^Fin 2]→L[ℝ] ℝ :=
  (4⁻¹ : ℝ) • (TauCeti.ContinuousAlternatingMap.alternatizeBilinCLM ℝ (V →L[ℝ] V) ℝ ∘L
    ContinuousLinearMap.compL ℝ (V →L[ℝ] V) (V →L[ℝ] V) ((V →L[ℝ] V) →L[ℝ] ℝ) (traceForm ℝ V) ∘L
    (ContinuousLinearMap.mul ℝ (V →L[ℝ] V)).flip)

theorem traceTwoFormCLM_def :
    traceTwoFormCLM V = (4⁻¹ : ℝ) •
      (TauCeti.ContinuousAlternatingMap.alternatizeBilinCLM ℝ (V →L[ℝ] V) ℝ ∘L
        ContinuousLinearMap.compL ℝ (V →L[ℝ] V) (V →L[ℝ] V) ((V →L[ℝ] V) →L[ℝ] ℝ)
          (traceForm ℝ V) ∘L
        (ContinuousLinearMap.mul ℝ (V →L[ℝ] V)).flip) :=
  (rfl)

theorem traceTwoFormCLM_apply (A : V →L[ℝ] V) (v : Fin 2 → V →L[ℝ] V) :
    traceTwoFormCLM V A v = 4⁻¹ * (LinearMap.trace ℝ V ↑(v 0 * A * v 1) -
      LinearMap.trace ℝ V ↑(v 1 * A * v 0)) := by
  simp [traceTwoFormCLM_def, TauCeti.ContinuousAlternatingMap.alternatizeBilinCLM_apply, mul_def]

/-- The two-form of `V →L[ℝ] V` whose value at `A` is
`(X, Y) ↦ ¼ (tr (X A Y) - tr (Y A X))`. Its pull-back to the manifold of compatible complex
structures is the Kähler form `TauCeti.SymplecticForm.compatibleSpaceForm`. -/
noncomputable def traceTwoForm : TauCeti.SmoothTwoForm 𝓘(ℝ, V →L[ℝ] V) (V →L[ℝ] V) :=
  ⟨fun A => traceTwoFormCLM V A,
    (TauCeti.isSmoothForm_modelSpace_iff.2 (traceTwoFormCLM V).contDiff).mem_smoothBundleForms⟩

theorem coe_traceTwoForm : ((traceTwoForm V).val : (V →L[ℝ] V) → _) = ⇑(traceTwoFormCLM V) :=
  (rfl)

variable {V}

/-- The value of the trace two-form at `A` is `¼ (tr (X A Y) - tr (Y A X))`. -/
theorem traceTwoForm_apply (A X Y : V →L[ℝ] V) :
    (traceTwoForm V).eval₂ A X Y =
      4⁻¹ * (LinearMap.trace ℝ V ↑(X * A * Y) - LinearMap.trace ℝ V ↑(Y * A * X)) := by
  refine (TauCeti.SmoothBundleForm.eval₂_apply _ _ _ _).trans ?_
  rw [coe_traceTwoForm]
  exact traceTwoFormCLM_apply V A ![X, Y]

/-- The exterior derivative of the trace two-form is the constant three-form
`(X, Y, Z) ↦ ¾ tr (X (Z Y - Y Z))`. -/
theorem mextDeriv_traceTwoForm_apply (A X Y Z : V →L[ℝ] V) :
    TauCeti.mextDeriv (traceTwoForm V).val A ![X, Y, Z] =
      (3 / 4 : ℝ) * LinearMap.trace ℝ V ↑(X * (Z * Y - Y * Z)) := by
  -- The form is a continuous linear function of the point, so it is its own derivative.
  rw [TauCeti.mextDeriv_eq_extDeriv, coe_traceTwoForm, extDeriv, ContinuousLinearMap.fderiv]
  refine (ContinuousAlternatingMap.alternatizeUncurryFin_apply _ _).trans ?_
  simp [Fin.sum_univ_three, traceTwoFormCLM_apply, Fin.removeNth, Fin.succAbove, mul_sub]
  -- Bring the six traces to the two orders `X Z Y` and `X Y Z`.
  have h1 := LinearMap.trace_mul_cycle (R := ℝ) (Y : V →ₗ[ℝ] V) X Z
  have h2 := LinearMap.trace_mul_cycle (R := ℝ) (Z : V →ₗ[ℝ] V) X Y
  have h3 := LinearMap.trace_mul_cycle (R := ℝ) (X : V →ₗ[ℝ] V) Y Z
  have h4 := LinearMap.trace_mul_cycle (R := ℝ) (X : V →ₗ[ℝ] V) Z Y
  linear_combination (-1 / 4 : ℝ) * h1 + (1 / 4 : ℝ) * h2 + (1 / 2 : ℝ) * h3 - (1 / 2 : ℝ) * h4

/-- The trace two-form is invariant under the conjugations `A ↦ Ψ A Ψ⁻¹`. -/
theorem traceTwoForm_conj (Ψ : V ≃L[ℝ] V) (A X Y : V →L[ℝ] V) :
    (traceTwoForm V).eval₂ (Ψ.arrowCongr Ψ A) (Ψ.arrowCongr Ψ X) (Ψ.arrowCongr Ψ Y) =
      (traceTwoForm V).eval₂ A X Y := by
  -- Conjugation by `Ψ` is Mathlib's algebra equivalence `Ψ.conjContinuousAlgEquiv`, which
  -- preserves traces (`ContinuousLinearEquiv.trace_conjContinuousAlgEquiv`).
  have h (P : V →L[ℝ] V) : Ψ.arrowCongr Ψ P = Ψ.conjContinuousAlgEquiv P := by
    ext v
    simp
  simp only [traceTwoForm_apply, h, ← map_mul, ContinuousLinearEquiv.trace_conjContinuousAlgEquiv]

end ContinuousLinearMap

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V}

local notation "𝒥" => {J : AlmostComplexStructure V // ω.Compatible J}

/-! ### The Kähler form -/

variable (ω) in
/-- The Kähler form `Ω` of the manifold of `ω`-compatible complex structures: the pull-back of
the trace two-form of `V →L[ℝ] V` along the inclusion `ω.compatibleCLM`. Its value at `J` on
tangent vectors with ambient readings `â` and `b̂` is `½ tr(â J b̂)`
(`compatibleSpaceForm_apply`). -/
noncomputable def compatibleSpaceForm : SmoothTwoForm 𝓘(ℝ, ω.compatibleModel) 𝒥 :=
  SmoothForm.mpullback ω.compatibleCLM contMDiff_compatibleCLM (ContinuousLinearMap.traceTwoForm V)

theorem compatibleSpaceForm_def :
    ω.compatibleSpaceForm = SmoothForm.mpullback ω.compatibleCLM contMDiff_compatibleCLM
      (ContinuousLinearMap.traceTwoForm V) :=
  (rfl)

/-- The Kähler form at `J`, on tangent vectors with ambient readings `â` and `b̂`, is the
trace two-form at `J` on `â` and `b̂`. -/
theorem compatibleSpaceForm_eval₂ (J : 𝒥) (a b : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ω.compatibleSpaceForm.eval₂ J a b =
      (ContinuousLinearMap.traceTwoForm V).eval₂ (ω.compatibleCLM J) (dι[ω] J a) (dι[ω] J b) := by
  rw [compatibleSpaceForm_def, SmoothForm.eval₂_mpullback, mvfderiv_apply_eq_mfderiv_apply,
    mvfderiv_apply_eq_mfderiv_apply]

/-- **The Kähler form.** At `J`, on tangent vectors with ambient readings `â` and `b̂`, the form
is `Ω_J(a, b) = ½ tr(â J b̂)`. -/
theorem compatibleSpaceForm_apply (J : 𝒥) (a b : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ω.compatibleSpaceForm.bilinFormAt J a b =
      2⁻¹ * LinearMap.trace ℝ V ↑(dι[ω] J a * ω.compatibleCLM J * dι[ω] J b) := by
  rw [SmoothForm.bilinFormAt_apply, compatibleSpaceForm_eval₂,
    ContinuousLinearMap.traceTwoForm_apply]
  simp only [ContinuousLinearMap.toLinearMap_mul, toLinearMap_compatibleCLM]
  rw [AlmostComplexStructure.trace_mul_mul_eq_neg_of_mem_tangentSpace
    (mvfderiv_compatibleCLM_mem_tangentSpace J a)]
  ring

/-- **The Kähler form is closed.** The exterior derivative of the trace two-form,
`(X, Y, Z) ↦ ¾ tr (X (Z Y - Y Z))`, vanishes on tangent vectors at `J`, since `X` anticommutes
with `J` while `Z Y - Y Z` commutes with it; and exterior differentiation commutes with
pull-backs. -/
theorem isClosed_compatibleSpaceForm : ω.compatibleSpaceForm.IsClosed := by
  rw [SmoothForm.isClosed_def, compatibleSpaceForm_def, SmoothForm.coe_mpullback,
    ← mpullback_mextDeriv (contMDiff_compatibleCLM (n := 2))
      ((isSmoothBundleForm_def 1 _).2 ((ContinuousLinearMap.traceTwoForm V).contMDiff.of_le
        (by simp)))]
  funext J
  refine ContinuousAlternatingMap.ext fun v => ?_
  -- Name the ambient readings of the three tangent vectors.
  set d := dι[ω] J
  obtain ⟨X, hX⟩ : ∃ X : V →L[ℝ] V, d (v 0) = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : V →L[ℝ] V, d (v 1) = Y := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : V →L[ℝ] V, d (v 2) = Z := ⟨_, rfl⟩
  have hv : (fun i => d (v i)) = ![X, Y, Z] := by
    ext i : 1
    fin_cases i
    exacts [hX, hY, hZ]
  have hm {i : Fin 3} {W : V →L[ℝ] V} (hW : d (v i) = W) :
      (W : Module.End ℝ V) ∈ J.val.tangentSpace :=
    hW ▸ mvfderiv_compatibleCLM_mem_tangentSpace J (v i)
  rw [mpullback_apply]
  simp only [← mvfderiv_apply_eq_mfderiv_apply]
  rw [hv, Pi.zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  refine (ContinuousLinearMap.mextDeriv_traceTwoForm_apply _ X Y Z).trans ?_
  rw [ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.toLinearMap_mul,
    AlmostComplexStructure.trace_mul_eq_zero_of_mem_tangentSpace (hm hX)
      ((AlmostComplexStructure.commute_mul_of_mem_tangentSpace (hm hZ) (hm hY)).sub_left
        (AlmostComplexStructure.commute_mul_of_mem_tangentSpace (hm hY) (hm hZ))), mul_zero]

/-- The Kähler form against the complex structure: at `J`, on tangent vectors with ambient
readings `â` and `b̂`, `Ω_J(a, j b) = ½ tr(â b̂)`. -/
theorem compatibleSpaceForm_apply_compatibleSpaceComplexStructure (J : 𝒥)
    (a b : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ω.compatibleSpaceForm.bilinFormAt J a (ω.compatibleSpaceComplexStructure J b) =
      2⁻¹ * LinearMap.trace ℝ V ↑(dι[ω] J a * dι[ω] J b) := by
  rw [compatibleSpaceForm_apply, mvfderiv_compatibleCLM_compatibleSpaceComplexStructure]
  simp only [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_neg,
    toLinearMap_compatibleCLM]
  -- `X J (-J Y) = -X (J J) Y = X Y`.
  congr 2
  calc _ = -((dι[ω] J a : Module.End ℝ V) * (J.val.toLinearMap * J.val.toLinearMap) *
          dι[ω] J b) := by
        noncomm_ring
    _ = _ := by rw [AlmostComplexStructure.toLinearMap_mul_self]; noncomm_ring

/-- The Kähler form is compatible with the complex structure `Ĵ ↦ -J Ĵ` of the space of
compatible complex structures: it is invariant, and `Ω(a, j a) = ½ tr(â²) > 0` for `a ≠ 0`. -/
theorem compatible_compatibleSpaceForm :
    ω.compatibleSpaceForm.Compatible ω.compatibleSpaceComplexStructure := by
  refine ⟨SmoothTwoForm.invariant_iff.2 fun J a b => ?_, SmoothTwoForm.tames_iff.2 fun J a ha => ?_⟩
  · rw [← SmoothForm.bilinFormAt_apply, ← SmoothForm.bilinFormAt_apply,
      compatibleSpaceForm_apply_compatibleSpaceComplexStructure, compatibleSpaceForm_apply,
      mvfderiv_compatibleCLM_compatibleSpaceComplexStructure]
    have hXm := mvfderiv_compatibleCLM_mem_tangentSpace J a
    simp only [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_neg,
      toLinearMap_compatibleCLM]
    generalize ((dι[ω] J a : V →L[ℝ] V) : Module.End ℝ V) = X at hXm ⊢
    generalize ((dι[ω] J b : V →L[ℝ] V) : Module.End ℝ V) = Y
    -- `(-J X) Y = (J X J) J Y = X J Y`.
    congr 2
    calc _ = J.val.toLinearMap * X * J.val.toLinearMap * (J.val.toLinearMap * Y) := by
          rw [show J.val.toLinearMap * X * J.val.toLinearMap * (J.val.toLinearMap * Y) =
              J.val.toLinearMap * X * (J.val.toLinearMap * J.val.toLinearMap) * Y by noncomm_ring,
            AlmostComplexStructure.toLinearMap_mul_self]
          noncomm_ring
      _ = _ := by rw [AlmostComplexStructure.mul_mul_eq_of_mem_tangentSpace hXm, mul_assoc]
  · rw [← SmoothForm.bilinFormAt_apply, compatibleSpaceForm_apply_compatibleSpaceComplexStructure]
    obtain ⟨X, hX⟩ : ∃ X : V →L[ℝ] V, dι[ω] J a = X := ⟨_, rfl⟩
    have hXm : (X : Module.End ℝ V) ∈ ω.compatibleTangentSpace J.val :=
      hX ▸ mvfderiv_compatibleCLM_mem_compatibleTangentSpace J a
    -- The ambient reading of a nonzero tangent vector is nonzero.
    have hX0 : (X : Module.End ℝ V) ≠ 0 := by
      rw [Ne, ← ContinuousLinearMap.toLinearMap_zero, ContinuousLinearMap.coe_inj, ← hX]
      exact (map_ne_zero_iff _ (injective_mvfderiv_compatibleCLM J)).2 ha
    rw [hX, ContinuousLinearMap.toLinearMap_mul]
    exact mul_pos (by norm_num) (J.property.trace_mul_self_pos hXm hX0)

/-- **The space of compatible complex structures is Kähler.** The form `Ω` is closed, compatible
with the complex structure `Ĵ ↦ -J Ĵ`, and the complex structure is integrable. -/
theorem isKahler_compatibleSpaceForm :
    ω.compatibleSpaceForm.IsKahler ω.compatibleSpaceComplexStructure :=
  ⟨isClosed_compatibleSpaceForm, compatible_compatibleSpaceForm,
    nijenhuis_compatibleSpaceComplexStructure⟩

/-! ### The metric -/

open _root_.Bundle

/-- The manifold of compatible complex structures carries the metric `g(a, b) = Ω(a, j b)` of the
Kähler form `Ω` and the complex structure `j`. On tangent vectors with ambient readings `â` and
`b̂` it is `½ tr(â b̂)` (`inner_compatibleSpace`). -/
noncomputable instance : Bundle.RiemannianBundle
    (fun J : 𝒥 ↦ TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :=
  compatible_compatibleSpaceForm.riemannianBundle

/-- The metric of the manifold of compatible complex structures is smooth. -/
instance : IsContMDiffRiemannianBundle 𝓘(ℝ, ω.compatibleModel) ((⊤ : ℕ∞) : WithTop ℕ∞)
    ω.compatibleModel (fun J : 𝒥 ↦ TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :=
  compatible_compatibleSpaceForm.isContMDiffRiemannianBundle

/-- The metric of the manifold of compatible complex structures is continuous. -/
instance : IsContinuousRiemannianBundle ω.compatibleModel
    (fun J : 𝒥 ↦ TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := 𝓘(ℝ, ω.compatibleModel)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))

/-- The inner product of the manifold of compatible complex structures is the metric of the
Kähler form: `⟪a, b⟫ = Ω(a, j b)`. -/
theorem inner_compatibleSpace_eq_eval₂ (J : 𝒥) (a b : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ⟪a, b⟫ = ω.compatibleSpaceForm.eval₂ J a (ω.compatibleSpaceComplexStructure J b) :=
  compatible_compatibleSpaceForm.inner_riemannianBundle J a b

/-- **The metric.** At `J`, the inner product of tangent vectors with ambient readings `â` and
`b̂` is `⟪a, b⟫ = ½ tr(â b̂)`. -/
theorem inner_compatibleSpace (J : 𝒥) (a b : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ⟪a, b⟫ = 2⁻¹ * LinearMap.trace ℝ V ↑(dι[ω] J a * dι[ω] J b) := by
  rw [inner_compatibleSpace_eq_eval₂, ← SmoothForm.bilinFormAt_apply,
    compatibleSpaceForm_apply_compatibleSpaceComplexStructure]

/-- The metric of the manifold of compatible complex structures is the pull-back by the
inclusion of the bilinear form `½ B` of `V →L[ℝ] V`, where `B(P, Q) = tr (P Q)` is the trace
form: `⟪a, b⟫ = (½ B)(â, b̂)`. -/
theorem inner_compatibleSpace_eq_smul_traceForm (J : 𝒥)
    (a b : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ⟪a, b⟫ = ((2⁻¹ : ℝ) • ContinuousLinearMap.traceForm ℝ V)
      (dι[ω] J a) (dι[ω] J b) := by
  rw [smul_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.traceForm_apply,
    inner_compatibleSpace]

/-! ### Invariance under linear symplectomorphisms -/

variable {Ψ : V ≃L[ℝ] V} (hΨ : ω.IsSymplectomorphism ω Ψ.toLinearEquiv)
include hΨ

/-- The transport `J ↦ Ψ J Ψ⁻¹` by a linear symplectomorphism `Ψ` preserves the Kähler form. -/
theorem mpullback_compatibleTransport_compatibleSpaceForm :
    SmoothForm.mpullback (ω.compatibleTransport hΨ) (ω.compatibleTransport hΨ).contMDiff
      ω.compatibleSpaceForm = ω.compatibleSpaceForm := by
  refine SmoothBundleForm.ext_eval₂ fun J a b => ?_
  rw [SmoothForm.eval₂_mpullback, compatibleSpaceForm_eval₂, compatibleSpaceForm_eval₂]
  rw [mvfderiv_compatibleCLM_compatibleTransport, mvfderiv_compatibleCLM_compatibleTransport,
    compatibleCLM_compatibleTransport]
  exact ContinuousLinearMap.traceTwoForm_conj Ψ _ _ _

variable (ω) in
/-- The transport `J ↦ Ψ J Ψ⁻¹` by a linear symplectomorphism `Ψ`, as a Riemannian isometry of the
manifold of compatible complex structures. -/
noncomputable def compatibleTransportIsometry :
    RiemannianIsometry 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, ω.compatibleModel) 𝒥 𝒥 where
  toDiffeomorph := ω.compatibleTransport hΨ
  inner_mfderiv' J a b := by
    -- The transport preserves `Ω` and commutes with the complex structure.
    have hj := (isPseudoholomorphic_iff.1 (isPseudoholomorphic_compatibleTransport hΨ)
      J).mfderiv_apply_commute b
    rw [inner_compatibleSpace_eq_eval₂, inner_compatibleSpace_eq_eval₂, ← hj,
      ← SmoothForm.eval₂_mpullback _ (ω.compatibleTransport hΨ).contMDiff,
      mpullback_compatibleTransport_compatibleSpaceForm]

@[simp]
theorem coe_compatibleTransportIsometry :
    ⇑(ω.compatibleTransportIsometry hΨ) = ω.compatibleTransport hΨ :=
  (rfl)

omit hΨ

/-- The isometries of the manifold of compatible complex structures act transitively on it: it is
a homogeneous Riemannian manifold. Already the transports by linear symplectomorphisms act
transitively. -/
instance isPretransitive_isom_compatibleSpace :
    MulAction.IsPretransitive (Isom 𝓘(ℝ, ω.compatibleModel) 𝒥) 𝒥 := by
  refine ⟨fun J J' => ?_⟩
  obtain ⟨Ψ, hΨ, h⟩ := exists_compatibleTransport_eq J J'
  exact ⟨ω.compatibleTransportIsometry hΨ, by
    rw [RiemannianIsometry.smul_def, coe_compatibleTransportIsometry, h]⟩

end TauCeti.SymplecticForm

end
