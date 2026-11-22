/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.LinearAlgebra.Projectivization.BaseChange
import TauCeti.Geometry.Manifold.Submersion.Descent
import TauCeti.Topology.Algebra.Projectivization

/-!
# Real projective space inside complex projective space

Tau Ceti's `RingHom.mapProjective` applies a field embedding to homogeneous coordinates. For
`Complex.ofRealHom` it sends `ℝPⁿ = ℙ ℝ (Fin (n + 1) → ℝ)` into `ℂPⁿ = ℙ ℂ (Fin (n + 1) → ℂ)`,
the points with a real representative. This file shows that this map is a smooth embedding of
the underlying real manifolds.

* `Projectivization.puncturedSpaceOfReal n` is the inclusion `x ↦ (xᵢ : ℂ)ᵢ` of the nonzero
  real vectors into the nonzero complex vectors. It is smooth
  (`contMDiff_puncturedSpaceOfReal`), its derivative is again the inclusion of real vectors
  (`mfderiv_puncturedSpaceOfReal_apply`), and it lifts the change of field:
  `ofRealHom.mapProjective (mkNonzero ℝ n x) = mkNonzero ℂ n (puncturedSpaceOfReal n x)`
  (`mapProjective_ofReal_mkNonzero`).
* `Projectivization.isSmoothEmbedding_mapProjective_ofReal`: the change of field from `ℝ` to `ℂ`
  is a smooth embedding of `ℝPⁿ` into `ℂPⁿ`. Through the submersion `mkNonzero ℝ n` it is an
  immersion, by Tau Ceti's `Manifold.IsSubmersion.isImmersion_iff_ker_mfderiv_comp`, since a real
  vector lies on the complex line of a real vector `x` exactly when it lies on its real line. It
  is injective, and a closed map since `ℝPⁿ` is compact.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Exercise 4.3.5, p. 169.
-/

public section

open Function Manifold TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable (n : ℕ)

/-- The inclusion `x ↦ (xᵢ : ℂ)ᵢ` of the nonzero vectors of `ℝⁿ⁺¹` into those of `ℂⁿ⁺¹`. -/
noncomputable def puncturedSpaceOfReal (x : puncturedSpace (Fin (n + 1) → ℝ)) :
    puncturedSpace (Fin (n + 1) → ℂ) :=
  ⟨fun i ↦ ((x : Fin (n + 1) → ℝ) i : ℂ), mem_puncturedSpace.2 fun h ↦
    mem_puncturedSpace.1 x.property <| funext fun i ↦ by
      simpa using congrFun h i⟩

variable {n}

/-- `puncturedSpaceOfReal n x` is the vector `x` with its coordinates read in `ℂ`. -/
@[simp]
theorem coe_puncturedSpaceOfReal (x : puncturedSpace (Fin (n + 1) → ℝ)) :
    (puncturedSpaceOfReal n x : Fin (n + 1) → ℂ) = fun i ↦ ((x : Fin (n + 1) → ℝ) i : ℂ) :=
  (rfl)

/-- The inclusion of real nonzero vectors is the restriction of the inclusion of real vectors. -/
theorem subtypeVal_comp_puncturedSpaceOfReal :
    Subtype.val ∘ puncturedSpaceOfReal n =
      (ContinuousLinearMap.piMap fun _ : Fin (n + 1) ↦ Complex.ofRealCLM) ∘ Subtype.val :=
  (rfl)

variable (n) in
/-- The inclusion of real nonzero vectors into complex ones is smooth of every order. -/
theorem contMDiff_puncturedSpaceOfReal (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, Fin (n + 1) → ℂ) r (puncturedSpaceOfReal n) :=
  (TauCeti.ContMDiff.subtypeVal_comp_iff (n := r) _ _).1 <| by
    rw [subtypeVal_comp_puncturedSpaceOfReal]
    exact (ContinuousLinearMap.piMap fun _ : Fin (n + 1) ↦ Complex.ofRealCLM).contMDiff.comp
      contMDiff_subtypeVal

/-- The derivative of the inclusion of real nonzero vectors into complex ones is the inclusion of
real vectors into complex ones. -/
theorem mfderiv_puncturedSpaceOfReal_apply (x : puncturedSpace (Fin (n + 1) → ℝ))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ) x) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, Fin (n + 1) → ℂ) (puncturedSpaceOfReal n) x v =
      (ContinuousLinearMap.piMap fun _ : Fin (n + 1) ↦ Complex.ofRealCLM) v := by
  have h := TauCeti.Manifold.tangentSpaceOpenEquiv_mfderiv_apply
    (I := 𝓘(ℝ, Fin (n + 1) → ℝ)) (I' := 𝓘(ℝ, Fin (n + 1) → ℂ))
    subtypeVal_comp_puncturedSpaceOfReal v
  rwa [TauCeti.Manifold.tangentSpaceOpenEquiv_apply, TauCeti.Manifold.tangentSpaceOpenEquiv_apply,
    mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at h

/-- Changing the field of the line through a real vector `x` gives the complex line through `x`. -/
theorem mapProjective_ofReal_mkNonzero (x : puncturedSpace (Fin (n + 1) → ℝ)) :
    Complex.ofRealHom.mapProjective (mkNonzero ℝ n x) = mkNonzero ℂ n (puncturedSpaceOfReal n x) :=
  by rw [mkNonzero_apply, mkNonzero_apply, RingHom.mapProjective_mk]; rfl

/-- A real vector `v` lies on the complex line through a nonzero real vector `x` exactly when it
lies on the real line through `x`. -/
theorem ofReal_mem_span_singleton_iff (x : puncturedSpace (Fin (n + 1) → ℝ))
    (v : Fin (n + 1) → ℝ) :
    (fun i ↦ (v i : ℂ)) ∈ ℂ ∙ (puncturedSpaceOfReal n x : Fin (n + 1) → ℂ) ↔
      v ∈ ℝ ∙ (x : Fin (n + 1) → ℝ) := by
  simp only [Submodule.mem_span_singleton, coe_puncturedSpaceOfReal]
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ⟨a, funext fun i ↦ by simp [← ha]⟩⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (mem_puncturedSpace.1 x.property)
  have hcj : c = (v j / (x : Fin (n + 1) → ℝ) j : ℝ) := by
    have h := congrFun hc j
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [Complex.ofReal_div, ← h, mul_div_cancel_right₀ _ (by exact_mod_cast hj)]
  refine ⟨v j / (x : Fin (n + 1) → ℝ) j, funext fun i ↦ Complex.ofReal_injective ?_⟩
  have h := congrFun hc i
  simp only [Pi.smul_apply, smul_eq_mul, hcj] at h
  simpa using h

variable (n) in
/-- The change of field `ℝPⁿ → ℂPⁿ`, `[x] ↦ [x]`, is a smooth embedding of the underlying real
manifolds. -/
theorem isSmoothEmbedding_mapProjective_ofReal :
    IsSmoothEmbedding 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℂ) ∞
      (Complex.ofRealHom.mapProjective : ℙ ℝ (Fin (n + 1) → ℝ) → ℙ ℂ (Fin (n + 1) → ℂ)) := by
  have hcomp : Complex.ofRealHom.mapProjective ∘ mkNonzero ℝ n =
      mkNonzero ℂ n ∘ puncturedSpaceOfReal n :=
    funext mapProjective_ofReal_mkNonzero
  have hι := contMDiff_puncturedSpaceOfReal n ∞
  have himm : IsImmersion 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℂ) ∞
      (Complex.ofRealHom.mapProjective : ℙ ℝ (Fin (n + 1) → ℝ) → ℙ ℂ (Fin (n + 1) → ℂ)) := by
    refine ((isSubmersion_mkNonzero ℝ n).isImmersion_iff_ker_mfderiv_comp
      (surjective_mkNonzero ℝ n) (by simp)).2 ⟨?_, fun x ↦ ?_⟩
    · rw [hcomp]
      exact (contMDiff_mkNonzero ℂ n ∞).comp hι
    · ext v
      rw [hcomp, mfderiv_comp x ((contMDiff_mkNonzero ℂ n 1 _).mdifferentiableAt one_ne_zero)
        ((hι x).mdifferentiableAt (by simp))]
      have h₁ := ker_mfderiv_mkNonzero (𝕜 := ℂ) (puncturedSpaceOfReal n x)
      have h₂ := ker_mfderiv_mkNonzero (𝕜 := ℝ) x
      rw [h₂]
      refine Iff.trans ?_ (ofReal_mem_span_singleton_iff x v)
      have h := SetLike.ext_iff.1 h₁
        ((ContinuousLinearMap.piMap fun _ : Fin (n + 1) ↦ Complex.ofRealCLM) v)
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
        mfderiv_puncturedSpaceOfReal_apply]
      -- Membership in `restrictScalars ℝ` is membership in the complex line, and the tangent
      -- spaces are the model spaces.
      exact h
  exact ⟨himm, (himm.contMDiff.continuous.isClosedEmbedding
    (RingHom.mapProjective_injective _)).isEmbedding⟩

end Projectivization

end
