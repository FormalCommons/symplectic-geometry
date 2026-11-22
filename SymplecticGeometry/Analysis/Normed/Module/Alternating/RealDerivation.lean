/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Topology.Algebra.Module.Alternating.AlmostComplexType

/-!
# The derivation of an endomorphism on real-valued alternating forms

An endomorphism `A` of a real normed space `V` acts on the continuous alternating forms
`V [⋀^ι]→L[ℝ] ℝ` as a derivation: `(D_A ω)(v) = ∑ᵢ ω(v₁, …, A vᵢ, …, vₖ)`. Tau Ceti's
`ContinuousLinearMap.alternatingDerivation` is this derivation for forms valued in a complex
space; here it is read on real-valued forms through `ℝ → ℂ` and the real part, as Tau Ceti's
`ContMDiffSection.realAlternatingDerivation` does for smooth forms, so that the latter is this
derivation at each point.

## Main definitions

* `ContinuousLinearMap.realAlternatingDerivation`: the derivation `D_A` on real-valued forms.

## Main results

* `ContinuousLinearMap.realAlternatingDerivation_apply`: `D_A ω v = ∑ᵢ ω (update v i (A vᵢ))`.
* `ContinuousLinearMap.realAlternatingDerivation_apply_comp_equiv`: it commutes with reindexing.
* `ContinuousLinearMap.realAlternatingDerivation_wedge`: the Leibniz rule
  `D_A (φ ∧ ψ) = D_A φ ∧ ψ + φ ∧ D_A ψ`.

The proof of the Leibniz rule adapts that of Tau Ceti's
`ContinuousLinearMap.alternatingDerivation_pairedWedge` (and its auxiliary `sum_pairing_update`)
from complex-valued paired wedges to the real wedge.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 1.2.
-/

public section

noncomputable section

open Function

namespace ContinuousLinearMap

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

section Fintype

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivation induced by an endomorphism `A` of `V` on real-valued continuous alternating
forms: the sum, over all arguments, of the form with `A` applied to that argument. It is Tau
Ceti's `ContinuousLinearMap.alternatingDerivation` of the complexified form, followed by the real
part. -/
def realAlternatingDerivation (A : V →L[ℝ] V) :
    (V [⋀^ι]→L[ℝ] ℝ) →ₗ[ℝ] V [⋀^ι]→L[ℝ] ℝ where
  toFun ω := Complex.reCLM.compContinuousAlternatingMap
    (A.alternatingDerivation (Complex.ofRealCLM.compContinuousAlternatingMap ω))
  map_add' ω ω' := by
    ext v
    simp [alternatingDerivation_apply, Finset.sum_add_distrib]
  map_smul' c ω := by
    ext v
    simp [alternatingDerivation_apply, Finset.mul_sum]

/-- The derivation of a form sums the form over replacing one argument by its image under `A`. -/
theorem realAlternatingDerivation_apply (A : V →L[ℝ] V) (ω : V [⋀^ι]→L[ℝ] ℝ) (v : ι → V) :
    A.realAlternatingDerivation ω v = ∑ i, ω (update v i (A (v i))) := by
  simp [realAlternatingDerivation, alternatingDerivation_apply]

/-- On a one-form, the derivation is precomposition with `A`. -/
theorem realAlternatingDerivation_apply_vecCons_fin_one (A : V →L[ℝ] V)
    (α : V [⋀^Fin 1]→L[ℝ] ℝ) (v : V) : A.realAlternatingDerivation α ![v] = α ![A v] := by
  rw [realAlternatingDerivation_apply, Fin.sum_univ_one]
  exact congrArg α (by ext i; fin_cases i; rfl)

/-- The derivation commutes with reindexing the arguments: if `ω' v = ω (v ∘ σ)` for every `v`,
then the same holds for the derivations of `ω'` and `ω`. -/
theorem realAlternatingDerivation_apply_comp_equiv {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (A : V →L[ℝ] V) {ω : V [⋀^ι]→L[ℝ] ℝ} {ω' : V [⋀^ι']→L[ℝ] ℝ} (σ : ι ≃ ι')
    (h : ∀ v, ω' v = ω (v ∘ σ)) (v : ι' → V) :
    A.realAlternatingDerivation ω' v = A.realAlternatingDerivation ω (v ∘ σ) := by
  simp only [realAlternatingDerivation_apply, h, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg ω ?_
  rw [Function.update_comp_equiv, Equiv.symm_apply_apply, Function.comp_apply]

end Fintype

variable {k l : ℕ}

/-- Summing over the arguments of a wedge splits into the arguments of each factor. -/
private lemma sum_mul_update (A : V →L[ℝ] V) (φ : V [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : V [⋀^Fin l]→L[ℝ] ℝ) (w : Fin (k + l) → V) :
    ∑ j, (φ fun a ↦ update w j (A (w j)) (Fin.castAdd l a)) *
        (ψ fun b ↦ update w j (A (w j)) (Fin.natAdd k b)) =
      (A.realAlternatingDerivation φ fun a ↦ w (Fin.castAdd l a)) * (ψ fun b ↦ w (Fin.natAdd k b)) +
        (φ fun a ↦ w (Fin.castAdd l a)) *
          (A.realAlternatingDerivation ψ fun b ↦ w (Fin.natAdd k b)) := by
  rw [Fin.sum_univ_add, realAlternatingDerivation_apply, realAlternatingDerivation_apply,
    Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ ↦ ?_
  · rw [update_comp_eq_of_injective' w (Fin.castAdd_injective k l),
      update_comp_eq_of_forall_ne' w _ fun b h ↦ by simp [Fin.ext_iff] at h; omega]
  · rw [update_comp_eq_of_injective' w (Fin.natAdd_injective l k),
      update_comp_eq_of_forall_ne' w _ fun a h ↦ by simp [Fin.ext_iff] at h; omega]

/-- **The Leibniz rule**: the derivation induced by `A` is a derivation of the wedge product,
`D_A (φ ∧ ψ) = D_A φ ∧ ψ + φ ∧ D_A ψ`. -/
theorem realAlternatingDerivation_wedge (A : V →L[ℝ] V) (φ : V [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : V [⋀^Fin l]→L[ℝ] ℝ) :
    A.realAlternatingDerivation (φ.wedge ψ) =
      (A.realAlternatingDerivation φ).wedge ψ + φ.wedge (A.realAlternatingDerivation ψ) := by
  ext v
  rw [realAlternatingDerivation_apply, ContinuousAlternatingMap.add_apply]
  simp only [ContinuousAlternatingMap.wedge_def, ContinuousAlternatingMap.pairedWedge_apply,
    ContinuousLinearMap.mul_apply', ← smul_add, ← Finset.sum_add_distrib]
  rw [← Finset.smul_sum, Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun σ _ ↦ ?_)
  rw [← Finset.smul_sum, ← sum_mul_update A φ ψ fun m ↦ v (σ m), ← Equiv.sum_comp σ]
  simp only [update_apply, EmbeddingLike.apply_eq_iff_eq]

end ContinuousLinearMap
