/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Projectivization.Hopf
public import SymplecticGeometry.Geometry.Manifold.Instances.PuncturedSpace
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
  real vectors into the nonzero complex vectors, the map `TauCeti.puncturedSpace.map` of the
  real linear inclusion `ℝⁿ⁺¹ → ℂⁿ⁺¹`. It is smooth
  (`contMDiff_puncturedSpaceOfReal`), its derivative is again the inclusion of real vectors
  (`mfderiv_puncturedSpaceOfReal_apply`), and it lifts the change of field:
  `ofRealHom.mapProjective (mkNonzero ℝ n x) = mkNonzero ℂ n (puncturedSpaceOfReal n x)`
  (`mapProjective_ofReal_mkNonzero`, `mapProjective_ofReal_comp_mkNonzero`).
* `Projectivization.isSmoothEmbedding_mapProjective_ofReal`: the change of field from `ℝ` to `ℂ`
  is a smooth embedding of `ℝPⁿ` into `ℂPⁿ`. Through the submersion `mkNonzero ℝ n` it is an
  immersion, by Tau Ceti's `Manifold.IsSubmersion.isImmersion_iff_ker_mfderiv_comp`, since a real
  vector lies on the complex line of a real vector `x` exactly when it lies on its real line
  (`Complex.ofReal_mem_span_singleton_iff`, derived from Tau Ceti's
  `RingHom.mapProjective_injective`). It is injective, and a closed map since `ℝPⁿ` is compact.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Exercise 4.3.5, p. 169.
-/

public section

open Function Manifold TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Complex

/-- A real vector `v` lies on the complex line through a real vector `x` exactly when it lies on
the real line through `x`. -/
theorem ofReal_mem_span_singleton_iff {ι : Type*} (x v : ι → ℝ) :
    (fun i ↦ (v i : ℂ)) ∈ ℂ ∙ (fun i ↦ (x i : ℂ)) ↔ v ∈ ℝ ∙ x := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [Pi.zero_apply, Complex.ofReal_zero]
    exact iff_of_true (Submodule.zero_mem _) (Submodule.zero_mem _)
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : (fun i ↦ ((0 : ι → ℝ) i : ℂ)) = 0 := funext fun _ ↦ by simp
    rw [h0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.span_singleton_eq_bot.2 rfl,
      Submodule.mem_bot, Submodule.mem_bot]
    exact iff_of_false (fun h ↦ hv (funext fun i ↦ by simpa using congrFun h i)) hv
  have h := (RingHom.mapProjective_injective Complex.ofRealHom).eq_iff
    (a := Projectivization.mk ℝ v hv) (b := Projectivization.mk ℝ x hx)
  simp only [RingHom.mapProjective_mk, Projectivization.mk_eq_mk_iff'] at h
  simp only [Submodule.mem_span_singleton, ← h]
  rfl

end Complex

namespace Projectivization

variable (n : ℕ)

/-- The inclusion `x ↦ (xᵢ : ℂ)ᵢ` of the nonzero vectors of `ℝⁿ⁺¹` into those of `ℂⁿ⁺¹`: the
map of punctured spaces induced by the injective real linear map `x ↦ (xᵢ : ℂ)ᵢ`. -/
noncomputable def puncturedSpaceOfReal :
    puncturedSpace (Fin (n + 1) → ℝ) → puncturedSpace (Fin (n + 1) → ℂ) :=
  puncturedSpace.map (ContinuousLinearMap.piMap fun _ : Fin (n + 1) ↦ Complex.ofRealCLM)
    (by exact Injective.piMap fun _ ↦ Complex.ofReal_injective)

theorem puncturedSpaceOfReal_def :
    puncturedSpaceOfReal n =
      puncturedSpace.map (ContinuousLinearMap.piMap fun _ : Fin (n + 1) ↦ Complex.ofRealCLM)
        (by exact Injective.piMap fun _ ↦ Complex.ofReal_injective) :=
  (rfl)

variable {n}

/-- `puncturedSpaceOfReal n x` is the vector `x` with its coordinates read in `ℂ`. -/
@[simp]
theorem coe_puncturedSpaceOfReal (x : puncturedSpace (Fin (n + 1) → ℝ)) :
    (puncturedSpaceOfReal n x : Fin (n + 1) → ℂ) = fun i ↦ ((x : Fin (n + 1) → ℝ) i : ℂ) := by
  ext i
  simp [puncturedSpaceOfReal_def]

variable (n) in
/-- The inclusion of real nonzero vectors into complex ones is smooth of every order. -/
theorem contMDiff_puncturedSpaceOfReal (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, Fin (n + 1) → ℂ) r (puncturedSpaceOfReal n) := by
  rw [puncturedSpaceOfReal_def]
  exact puncturedSpace.contMDiff_map _ _ r

/-- The derivative of the inclusion of real nonzero vectors into complex ones is the inclusion of
real vectors into complex ones. -/
theorem mfderiv_puncturedSpaceOfReal_apply (x : puncturedSpace (Fin (n + 1) → ℝ))
    (v : TangentSpace 𝓘(ℝ, Fin (n + 1) → ℝ) x) :
    mfderiv 𝓘(ℝ, Fin (n + 1) → ℝ) 𝓘(ℝ, Fin (n + 1) → ℂ) (puncturedSpaceOfReal n) x v =
      (ContinuousLinearMap.piMap fun _ : Fin (n + 1) ↦ Complex.ofRealCLM) v := by
  rw [puncturedSpaceOfReal_def, puncturedSpace.mfderiv_map_apply]

/-- Changing the field of the line through a real vector `x` gives the complex line through `x`. -/
theorem mapProjective_ofReal_mkNonzero (x : puncturedSpace (Fin (n + 1) → ℝ)) :
    Complex.ofRealHom.mapProjective (mkNonzero ℝ n x) = mkNonzero ℂ n (puncturedSpaceOfReal n x) :=
  by
  rw [mkNonzero_apply, mkNonzero_apply, RingHom.mapProjective_mk]
  congr 1
  ext i
  simp

/-- The change of field, read on `ℝⁿ⁺¹ ∖ 0`: it sends the real line through `x` to the complex
line through `x`. -/
theorem mapProjective_ofReal_comp_mkNonzero :
    Complex.ofRealHom.mapProjective ∘ mkNonzero ℝ n = mkNonzero ℂ n ∘ puncturedSpaceOfReal n :=
  funext mapProjective_ofReal_mkNonzero

variable (n) in
/-- The change of field `ℝPⁿ → ℂPⁿ`, `[x] ↦ [x]`, is a smooth embedding of the underlying real
manifolds. -/
theorem isSmoothEmbedding_mapProjective_ofReal :
    IsSmoothEmbedding 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℂ) ∞
      (Complex.ofRealHom.mapProjective : ℙ ℝ (Fin (n + 1) → ℝ) → ℙ ℂ (Fin (n + 1) → ℂ)) := by
  have hι := contMDiff_puncturedSpaceOfReal n ∞
  have himm : IsImmersion 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℂ) ∞
      (Complex.ofRealHom.mapProjective : ℙ ℝ (Fin (n + 1) → ℝ) → ℙ ℂ (Fin (n + 1) → ℂ)) := by
    refine ((isSubmersion_mkNonzero ℝ n).isImmersion_iff_ker_mfderiv_comp
      (surjective_mkNonzero ℝ n) (by simp)).2 ⟨?_, fun x ↦ ?_⟩
    · rw [mapProjective_ofReal_comp_mkNonzero]
      exact (contMDiff_mkNonzero ℂ n ∞).comp hι
    · ext v
      rw [mapProjective_ofReal_comp_mkNonzero,
        mfderiv_comp x ((contMDiff_mkNonzero ℂ n 1 _).mdifferentiableAt one_ne_zero)
          ((hι x).mdifferentiableAt (by simp))]
      have h₁ := ker_mfderiv_mkNonzero (𝕜 := ℂ) (puncturedSpaceOfReal n x)
      have h₂ := ker_mfderiv_mkNonzero (𝕜 := ℝ) x
      rw [h₂]
      refine Iff.trans ?_ (Complex.ofReal_mem_span_singleton_iff _ v)
      have h := SetLike.ext_iff.1 h₁
        ((ContinuousLinearMap.piMap fun _ : Fin (n + 1) ↦ Complex.ofRealCLM) v)
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
        mfderiv_puncturedSpaceOfReal_apply]
      -- Membership in `restrictScalars ℝ` is membership in the complex line, and the tangent
      -- spaces are the model spaces.
      rwa [coe_puncturedSpaceOfReal] at h
  exact ⟨himm, (himm.contMDiff.continuous.isClosedEmbedding
    (RingHom.mapProjective_injective _)).isEmbedding⟩

end Projectivization

end
