/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import SymplecticGeometry.Geometry.Symplectic.CompatibleSpace.Kahler
public import SymplecticGeometry.Topology.ComplexStructure.Basic
import SymplecticGeometry.Geometry.Symplectic.CompatibleSpace.LeviCivita
import Mathlib.Analysis.Matrix.PosDef
import SymplecticGeometry.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import SymplecticGeometry.LinearAlgebra.Symplectic.CompatibleTangent.Basic

/-!
# The curvature of the space of compatible complex structures

Let `ω` be a symplectic form on a finite-dimensional real normed space `V`, and `𝒥 ω` the
manifold of `ω`-compatible complex structures, embedded in `V →L[ℝ] V` by `ω.compatibleCLM`, with
the metric `⟪a, b⟫ = ½ tr(â b̂)` of `Kahler.lean` and its Levi-Civita connection `∇`. Here `â` is
the ambient reading of a tangent vector `a` at `J`, its derivative
`mvfderiv 𝓘(ℝ, ω.compatibleModel) ω.compatibleCLM J a`, an element of `V →L[ℝ] V`. This file
computes the curvature of `∇` (McDuff–Salamon, Example 4.3.6 and Exercise 4.3.7):

`(R(a, b) c)^ = -¼ [[â, b̂], ĉ]`,

in Tau Ceti's sign convention `R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z` of
`CovariantDerivative.curvatureTensor` (Lee, Chapter 7). Pairing with the metric,
`⟪R(u, v) v, u⟫ = ⅛ tr([û, v̂]²)`. The commutator of two tangent vectors is skew-adjoint for the
inner product `ω(·, J ·)`, so this trace is at most zero
(`TauCeti.SymplecticForm.Compatible.trace_commutator_sq_nonpos`), and the Gram determinant is
nonnegative: the sectional curvature `⟪R(u, v) v, u⟫ / det Gram(u, v)` of Tau Ceti's
`CovariantDerivative.sectionalCurvature` is nonpositive, for every pair `u v`, dependent pairs
included.

The curvature is computed on smooth fields `X Y Z` extending `a b c`, with the ambient formula of
`LeviCivita.lean` for `∇`, `(∇_X Y)^ = D_X Ŷ - ½ J (Ŷ X̂ + X̂ Ŷ)`. Differentiating it a second time
by the product rule `mvfderiv_fun_mul_apply'` gives second derivatives of `Ẑ`, which cancel against
the term of the bracket by Tau Ceti's `mvfderiv_mlieBracket`
(`D_[X,Y] Ẑ = D_X D_Y Ẑ - D_Y D_X Ẑ`); the same lemma for `ω.compatibleCLM` gives
`[X, Y]^ = D_X Ŷ - D_Y X̂`, and the first derivatives cancel too. What remains is cubic in
`X̂ Ŷ Ẑ` and `J`, and reduces to `-¼ [[X̂, Ŷ], Ẑ]` since `J² = -1` and `J` anticommutes with
tangent vectors.

## Main results

* `TauCeti.SymplecticForm.curvatureTensor_leviCivitaConnection_compatibleSpace`: the curvature
  tensor, `(R(a, b) c)^ = -¼ [[â, b̂], ĉ]`.
* `TauCeti.SymplecticForm.inner_curvatureTensor_compatibleSpace`:
  `⟪R(u, v) v, u⟫ = ⅛ tr([û, v̂]²)`.
* `TauCeti.SymplecticForm.sectionalCurvature_compatibleSpace_nonpos`: the sectional curvature is
  nonpositive.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], Example 4.3.6 and Exercise 4.3.7.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapters 7 and 8 (the curvature tensor and the sectional curvature).
-/

public section

open scoped Manifold RealInnerProductSpace
open Bundle CovariantDerivative VectorField

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V}

local notation "𝒥" => {J : AlmostComplexStructure V // ω.Compatible J}

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "∇" => leviCivitaConnection 𝓘(ℝ, ω.compatibleModel) 𝒥

/-- The algebraic step of the curvature computation. Let `P` square to `-1` and anticommute with
`A`, `B` and `C`; in the curvature formula, `P` is the structure `J`, `A`, `B` and `C` are the
ambient readings of the three arguments, and the other elements are first and second
derivatives of ambient readings. All derivative terms cancel, and the rest is `-¼ [[A, B], C]`. -/
private theorem curvature_algebra {R : Type*} [Ring R] [Algebra ℝ R]
    {A B C P Yx Xy Zy Zx Zyx Zxy : R}
    (hPP : P * P = -1) (hPA : P * A = -(A * P)) (hPB : P * B = -(B * P))
    (hPC : P * C = -(C * P)) :
    Zyx - (2⁻¹ : ℝ) • (A * (C * B + B * C) + P * (Zx * B + C * Yx + (Yx * C + B * Zx))) -
          (2⁻¹ : ℝ) • (P * ((Zy - (2⁻¹ : ℝ) • (P * (C * B + B * C))) * A +
            A * (Zy - (2⁻¹ : ℝ) • (P * (C * B + B * C))))) -
        (Zxy - (2⁻¹ : ℝ) • (B * (C * A + A * C) + P * (Zy * A + C * Xy + (Xy * C + A * Zy))) -
          (2⁻¹ : ℝ) • (P * ((Zx - (2⁻¹ : ℝ) • (P * (C * A + A * C))) * B +
            B * (Zx - (2⁻¹ : ℝ) • (P * (C * A + A * C)))))) -
      (Zyx - Zxy - (2⁻¹ : ℝ) • (P * (C * (Yx - Xy) + (Yx - Xy) * C))) =
    -(4⁻¹ : ℝ) • ⁅⁅A, B⁆, C⁆ := by
  -- Move `P` to the right of `A`, `B` and `C`; the terms with `P` then cancel.
  have hPA' (x : R) : P * (A * x) = -(A * (P * x)) := by
    rw [← mul_assoc, hPA, neg_mul, mul_assoc]
  have hPB' (x : R) : P * (B * x) = -(B * (P * x)) := by
    rw [← mul_assoc, hPB, neg_mul, mul_assoc]
  have hPC' (x : R) : P * (C * x) = -(C * (P * x)) := by
    rw [← mul_assoc, hPC, neg_mul, mul_assoc]
  simp only [Ring.lie_def, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
    mul_assoc, smul_add, smul_sub, mul_neg, mul_one, smul_neg, neg_neg, hPA, hPB, hPC, hPP,
    hPA', hPB', hPC']
  module

/-- The derivative of the ambient reading of `∇_Y Z` along a tangent vector `a`. -/
private theorem mvfderiv_ambient_leviCivita
    {Y Z : Π J : 𝒥, TangentSpace 𝓘(ℝ, ω.compatibleModel) J}
    (hY : ContMDiff 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, ω.compatibleModel).tangent ∞
      (fun J' ↦ TotalSpace.mk' ω.compatibleModel J' (Y J')))
    (hZ : ContMDiff 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, ω.compatibleModel).tangent ∞
      (fun J' ↦ TotalSpace.mk' ω.compatibleModel J' (Z J')))
    (J : 𝒥) (a : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    mvfderiv 𝓘(ℝ, ω.compatibleModel) (fun J' : 𝒥 ↦ dι[ω] J' (∇ Z J' (Y J'))) J a =
      mvfderiv 𝓘(ℝ, ω.compatibleModel) (fun J' : 𝒥 ↦ mvfderiv 𝓘(ℝ, ω.compatibleModel)
          (fun J'' : 𝒥 ↦ dι[ω] J'' (Z J'')) J' (Y J')) J a -
        (2⁻¹ : ℝ) • (dι[ω] J a * (dι[ω] J (Z J) * dι[ω] J (Y J) + dι[ω] J (Y J) * dι[ω] J (Z J)) +
          ω.compatibleCLM J *
            (mvfderiv 𝓘(ℝ, ω.compatibleModel) (fun J' : 𝒥 ↦ dι[ω] J' (Z J')) J a * dι[ω] J (Y J) +
              dι[ω] J (Z J) * mvfderiv 𝓘(ℝ, ω.compatibleModel) (fun J' : 𝒥 ↦ dι[ω] J' (Y J')) J a +
              (mvfderiv 𝓘(ℝ, ω.compatibleModel) (fun J' : 𝒥 ↦ dι[ω] J' (Y J')) J a * dι[ω] J (Z J) +
              dι[ω] J (Y J) *
                mvfderiv 𝓘(ℝ, ω.compatibleModel) (fun J' : 𝒥 ↦ dι[ω] J' (Z J')) J a))) := by
  set P : 𝒥 → V →L[ℝ] V := ω.compatibleCLM
  set Yh : 𝒥 → V →L[ℝ] V := fun J' ↦ dι[ω] J' (Y J')
  set Zh : 𝒥 → V →L[ℝ] V := fun J' ↦ dι[ω] J' (Z J')
  have hP : ∀ J', MDifferentiableAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) P J' :=
    fun J' => (contMDiff_compatibleCLM (n := 1)).mdifferentiableAt one_ne_zero
  have hYh : MDifferentiable 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) Yh :=
    (contMDiff_mvfderiv_compatibleCLM_apply hY).mdifferentiable (by simp)
  have hZh' : ContMDiff 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V) ∞ Zh :=
    contMDiff_mvfderiv_compatibleCLM_apply hZ
  have hZh := hZh'.mdifferentiable (by simp)
  have hD : MDifferentiableAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V)
      (fun J' ↦ mvfderiv 𝓘(ℝ, ω.compatibleModel) Zh J' (Y J')) J :=
    TauCeti.mdifferentiableAt_mvfderiv_apply hZh'.contMDiffAt (by simp)
      ((hY J).mdifferentiableAt (by simp))
  have hfun : (fun J' : 𝒥 ↦ dι[ω] J' (∇ Z J' (Y J'))) = fun J' ↦
      mvfderiv 𝓘(ℝ, ω.compatibleModel) Zh J' (Y J') -
        (2⁻¹ : ℝ) • (P J' * (Zh J' * Yh J' + Yh J' * Zh J')) := by
    funext J'
    exact leviCivitaConnection_compatibleSpace_apply
      ((hZ J').mdifferentiableAt (by simp)) (Y J')
  have hS : MDifferentiableAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V)
      (fun J' ↦ Zh J' * Yh J' + Yh J' * Zh J') J :=
    ((hZh J).mul (hYh J)).add ((hYh J).mul (hZh J))
  have hPS : MDifferentiableAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V)
      (fun J' ↦ P J' * (Zh J' * Yh J' + Yh J' * Zh J')) J := (hP J).mul hS
  have hZY : MDifferentiableAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V)
      (fun J' ↦ Zh J' * Yh J') J := (hZh J).mul (hYh J)
  have hYZ : MDifferentiableAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V)
      (fun J' ↦ Yh J' * Zh J') J := (hYh J).mul (hZh J)
  have hR : MDifferentiableAt 𝓘(ℝ, ω.compatibleModel) 𝓘(ℝ, V →L[ℝ] V)
      (fun J' ↦ (2⁻¹ : ℝ) • (P J' * (Zh J' * Yh J' + Yh J' * Zh J'))) J := hPS.const_smul _
  rw [hfun, mvfderiv_fun_sub hD hR, sub_apply, TauCeti.mvfderiv_const_smul hPS, smul_apply,
    SymplecticGeometry.mvfderiv_fun_mul_apply' (hP J) hS, mvfderiv_fun_add hZY hYZ, add_apply,
    SymplecticGeometry.mvfderiv_fun_mul_apply' (hZh J) (hYh J),
    SymplecticGeometry.mvfderiv_fun_mul_apply' (hYh J) (hZh J)]

/-- **Curvature of the manifold of compatible complex structures.** For tangent vectors `a b c`
at `J`, the ambient reading of `R(a, b) c` is `-¼ [[â, b̂], ĉ]`, the double commutator of the
ambient readings in `V →L[ℝ] V`, for the curvature tensor of the Levi-Civita connection in the
convention `R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`. -/
theorem curvatureTensor_leviCivitaConnection_compatibleSpace (J : 𝒥)
    (a b c : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    dι[ω] J ((leviCivitaConnection 𝓘(ℝ, ω.compatibleModel) 𝒥).curvatureTensor J a b c) =
      -(4⁻¹ : ℝ) • ⁅⁅dι[ω] J a, dι[ω] J b⁆, dι[ω] J c⁆ := by
  obtain ⟨X, hX, rfl⟩ :=
    FiberBundle.exists_contMDiff_section_eq 𝓘(ℝ, ω.compatibleModel) ω.compatibleModel ∞ a
  obtain ⟨Y, hY, rfl⟩ :=
    FiberBundle.exists_contMDiff_section_eq 𝓘(ℝ, ω.compatibleModel) ω.compatibleModel ∞ b
  obtain ⟨Z, hZ, rfl⟩ :=
    FiberBundle.exists_contMDiff_section_eq 𝓘(ℝ, ω.compatibleModel) ω.compatibleModel ∞ c
  have hXd := fun J' => (hX J').mdifferentiableAt (n := ∞) (by simp)
  have hYd := fun J' => (hY J').mdifferentiableAt (n := ∞) (by simp)
  have hZd := fun J' => (hZ J').mdifferentiableAt (n := ∞) (by simp)
  rw [curvatureTensor_apply _ J hX hY hZ,
    curvatureOperator_apply, map_sub, map_sub,
    leviCivitaConnection_compatibleSpace_apply
      (((leviCivitaConnection _ _).contMDiff_apply hY hZ J).mdifferentiableAt (by simp)),
    leviCivitaConnection_compatibleSpace_apply
      (((leviCivitaConnection _ _).contMDiff_apply hX hZ J).mdifferentiableAt (by simp)),
    mvfderiv_ambient_leviCivita hY hZ,
    mvfderiv_ambient_leviCivita hX hZ]
  simp only [leviCivitaConnection_compatibleSpace_apply (hZd J)]
  have hL := mvfderiv_mlieBracket (contMDiff_compatibleCLM (ω := ω) (n := ∞)).contMDiffAt
    (by simp) (hXd J) (hYd J)
  have hZL := mvfderiv_mlieBracket (contMDiff_mvfderiv_compatibleCLM_apply hZ).contMDiffAt
    (by simp) (hXd J) (hYd J)
  rw [hL, hZL]
  have anti (v : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
      ω.compatibleCLM J * dι[ω] J v = -(dι[ω] J v * ω.compatibleCLM J) :=
    eq_neg_of_add_eq_zero_left (compatibleCLM_mul_mvfderiv_add_mvfderiv_mul_compatibleCLM J v)
  exact curvature_algebra (compatibleCLM_mul_self J) (anti (X J)) (anti (Y J)) (anti (Z J))

/-- For tangent vectors `u v` at `J`, `⟪R(u, v) v, u⟫ = ⅛ tr([û, v̂]²)`, the trace of the square of
the commutator of the ambient readings. -/
theorem inner_curvatureTensor_compatibleSpace (J : 𝒥)
    (u v : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    ⟪(leviCivitaConnection 𝓘(ℝ, ω.compatibleModel) 𝒥).curvatureTensor J u v v, u⟫ =
      8⁻¹ * LinearMap.trace ℝ V ↑(⁅dι[ω] J u, dι[ω] J v⁆ * ⁅dι[ω] J u, dι[ω] J v⁆) := by
  rw [inner_compatibleSpace, curvatureTensor_leviCivitaConnection_compatibleSpace]
  generalize dι[ω] J u = U
  generalize dι[ω] J v = W
  simp only [Ring.lie_def, ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_sub, smul_mul_assoc,
    map_smul]
  generalize (U : Module.End ℝ V) = A
  generalize (W : Module.End ℝ V) = B
  -- With `K = ⁅A, B⁆`: `tr(⁅K, B⁆ A) = tr(K ⁅B, A⁆) = -tr(K K)`.
  have hK : LinearMap.trace ℝ V (((A * B - B * A) * B - B * (A * B - B * A)) * A) =
      -LinearMap.trace ℝ V ((A * B - B * A) * (A * B - B * A)) := by
    rw [← map_neg, ← mul_neg, neg_sub]
    simpa [Ring.lie_def] using LinearMap.trace_lie_mul_eq ⁅A, B⁆ B A
  rw [hK, smul_eq_mul]
  ring

/-- **The space of compatible complex structures has nonpositive sectional curvature.** The
sectional curvature `⟪R(u, v) v, u⟫ / det Gram(u, v)` of the Levi-Civita connection is at most zero
for all tangent vectors `u v`, linearly independent or not. -/
theorem sectionalCurvature_compatibleSpace_nonpos
    (hcov : IsMetricCompatible (V := fun J : 𝒥 ↦ TangentSpace 𝓘(ℝ, ω.compatibleModel) J)
      (leviCivitaConnection 𝓘(ℝ, ω.compatibleModel) 𝒥))
    (J : 𝒥) (u v : TangentSpace 𝓘(ℝ, ω.compatibleModel) J) :
    (leviCivitaConnection 𝓘(ℝ, ω.compatibleModel) 𝒥).sectionalCurvature hcov J u v ≤ 0 := by
  rw [sectionalCurvature_apply, inner_curvatureTensor_compatibleSpace]
  refine div_nonpos_of_nonpos_of_nonneg ?_ (Matrix.posSemidef_gram ℝ _).det_nonneg
  have h := J.property.trace_commutator_sq_nonpos
    (mvfderiv_compatibleCLM_mem_compatibleTangentSpace J u)
    (mvfderiv_compatibleCLM_mem_compatibleTangentSpace J v)
  simp only [Ring.lie_def, ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.toLinearMap_sub] at h ⊢
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) h

end TauCeti.SymplecticForm

end
