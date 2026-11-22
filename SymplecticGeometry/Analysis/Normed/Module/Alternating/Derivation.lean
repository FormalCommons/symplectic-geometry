/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
import TauCeti.Analysis.Normed.Module.Alternating.Basic

/-!
# The derivation of an endomorphism on alternating forms

For `f : F [⋀^ι]→L[𝕜] G` and `g dg : E →L[𝕜] F`, Mathlib's
`ContinuousAlternatingMap.fderivCompContinuousLinearMap f g dg` is
`v ↦ ∑ᵢ f (g v₁, …, dg vᵢ, …, g vₖ)`. At `g = id` and `dg = A`, an endomorphism of `F`, it is the
action of `A` on alternating forms as a derivation, `D_A f`, as Tau Ceti's
`ContinuousAlternatingMap.fderivCompContinuousLinearMap_comp` and
`ContinuousLinearMap.alternatingDerivation_eq_fderivCompContinuousLinearMap` use it. This file
adds the facts about it that the Kähler identities need.

## Main results

* `ContinuousAlternatingMap.fderivCompContinuousLinearMap_id_apply`:
  `D_A f v = ∑ᵢ f (update v i (A vᵢ))`.
* `ContinuousAlternatingMap.fderivCompContinuousLinearMap_ofSubsingleton`: on a one-form
  `f`, the derivative is `f ∘ dg`.
* `ContinuousAlternatingMap.fderivCompContinuousLinearMap_apply_comp_equiv`: it commutes with
  reindexing the arguments.
* `ContinuousAlternatingMap.fderivCompContinuousLinearMap_wedge`: the Leibniz rule
  `D_A (φ ∧ ψ) = D_A φ ∧ ψ + φ ∧ D_A ψ` for real-valued forms.
* `ContinuousAlternatingMap.fderivCompContinuousLinearMap_compContinuousLinearMap`: the derivative
  of the pullback at a pullback `f ∘ g`.
* `ContinuousAlternatingMap.compContinuousLinearMap_fderivCompContinuousLinearMap_id`: pullback
  along a map intertwining two endomorphisms carries one derivation to the other.

The proof of the Leibniz rule adapts that of Tau Ceti's
`ContinuousLinearMap.alternatingDerivation_pairedWedge` (and its auxiliary `sum_pairing_update`)
from complex-valued paired wedges to the real wedge.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 1.2.
-/

public section

open Function

namespace ContinuousAlternatingMap

section General

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 G]

/-- At the identity, the derivative of the pullback in the direction `A` sums `f` over replacing
one argument `vᵢ` by `A vᵢ`. -/
theorem fderivCompContinuousLinearMap_id_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : F [⋀^ι]→L[𝕜] G) (A : F →L[𝕜] F) (v : ι → F) :
    f.fderivCompContinuousLinearMap (.id 𝕜 F) A v = ∑ i, f (update v i (A (v i))) := by
  rw [fderivCompContinuousLinearMap_apply]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg f (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [update_of_ne hj]

/-- On a one-form, the derivative of the pullback at `g` in the direction `dg` is the pullback
along `dg`. -/
@[simp]
theorem fderivCompContinuousLinearMap_ofSubsingleton {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Subsingleton ι] (i : ι) (f : F →L[𝕜] G) (g dg : E →L[𝕜] F) :
    (ofSubsingleton 𝕜 F G i f).fderivCompContinuousLinearMap g dg =
      ofSubsingleton 𝕜 E G i (f ∘L dg) := by
  ext v
  simp [Fintype.sum_subsingleton _ i]

/-- On a one-form `α`, the derivative of the pullback at `g` in the direction `dg` takes `v` to
`α (dg v)`. -/
theorem fderivCompContinuousLinearMap_apply_vecCons_fin_one (α : F [⋀^Fin 1]→L[𝕜] G)
    (g dg : E →L[𝕜] F) (v : E) : α.fderivCompContinuousLinearMap g dg ![v] = α ![dg v] := by
  rw [fderivCompContinuousLinearMap_apply, Fin.sum_univ_one]
  exact congrArg α (by ext i; fin_cases i; rfl)

/-- The derivative of the pullback commutes with reindexing the arguments: if `f' v = f (v ∘ σ)`
for every `v`, then the same holds for their derivatives. -/
theorem fderivCompContinuousLinearMap_apply_comp_equiv {ι ι' : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] {f : F [⋀^ι]→L[𝕜] G} {f' : F [⋀^ι']→L[𝕜] G}
    (σ : ι ≃ ι') (h : ∀ v, f' v = f (v ∘ σ)) (g dg : E →L[𝕜] F) (v : ι' → E) :
    f'.fderivCompContinuousLinearMap g dg v = f.fderivCompContinuousLinearMap g dg (v ∘ σ) := by
  simp only [fderivCompContinuousLinearMap_apply, h, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg f (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [update_of_ne hj, update_of_ne (σ.injective.ne hj)]

end General

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] {k l : ℕ}

/-- Summing over the arguments of a wedge splits into the arguments of each factor. -/
private lemma sum_mul_update (A : V →L[ℝ] V) (φ : V [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : V [⋀^Fin l]→L[ℝ] ℝ) (w : Fin (k + l) → V) :
    ∑ j, (φ fun a ↦ update w j (A (w j)) (Fin.castAdd l a)) *
        (ψ fun b ↦ update w j (A (w j)) (Fin.natAdd k b)) =
      (φ.fderivCompContinuousLinearMap (.id ℝ V) A fun a ↦ w (Fin.castAdd l a)) *
          (ψ fun b ↦ w (Fin.natAdd k b)) +
        (φ fun a ↦ w (Fin.castAdd l a)) *
          (ψ.fderivCompContinuousLinearMap (.id ℝ V) A fun b ↦ w (Fin.natAdd k b)) := by
  rw [fderivCompContinuousLinearMap_id_apply, fderivCompContinuousLinearMap_id_apply,
    Fin.sum_univ_add, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ ↦ ?_
  · rw [update_comp_eq_of_injective' w (Fin.castAdd_injective k l),
      update_comp_eq_of_forall_ne' w _ fun b h ↦ by simp [Fin.ext_iff] at h; omega]
  · rw [update_comp_eq_of_injective' w (Fin.natAdd_injective l k),
      update_comp_eq_of_forall_ne' w _ fun a h ↦ by simp [Fin.ext_iff] at h; omega]

/-- **The Leibniz rule**: the derivation induced by an endomorphism `A` on real-valued forms is a
derivation of the wedge product, `D_A (φ ∧ ψ) = D_A φ ∧ ψ + φ ∧ D_A ψ`. -/
theorem fderivCompContinuousLinearMap_wedge (A : V →L[ℝ] V) (φ : V [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : V [⋀^Fin l]→L[ℝ] ℝ) :
    (φ.wedge ψ).fderivCompContinuousLinearMap (.id ℝ V) A =
      (φ.fderivCompContinuousLinearMap (.id ℝ V) A).wedge ψ +
        φ.wedge (ψ.fderivCompContinuousLinearMap (.id ℝ V) A) := by
  ext v
  rw [fderivCompContinuousLinearMap_id_apply, add_apply]
  simp only [wedge_def, pairedWedge_apply, ContinuousLinearMap.mul_apply',
    ← smul_add, ← Finset.sum_add_distrib]
  rw [← Finset.smul_sum, Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun σ _ ↦ ?_)
  rw [← Finset.smul_sum, ← sum_mul_update A φ ψ fun m ↦ v (σ m), ← Equiv.sum_comp σ]
  simp only [update_apply, EmbeddingLike.apply_eq_iff_eq]


section Pullback

variable {𝕜 E E' F G ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι] [DecidableEq ι]

/-- The derivative of the pullback, taken at a pullback `f ∘ g`, is that of `f` at the composites
with `g`: `D(f ∘ g)(h)(dh) = Df(g ∘ h)(g ∘ dh)`. -/
theorem fderivCompContinuousLinearMap_compContinuousLinearMap (f : F [⋀^ι]→L[𝕜] G)
    (g : E →L[𝕜] F) (h dh : E' →L[𝕜] E) :
    (f.compContinuousLinearMap g).fderivCompContinuousLinearMap h dh =
      f.fderivCompContinuousLinearMap (g ∘L h) (g ∘L dh) := by
  ext v
  simp only [fderivCompContinuousLinearMap_apply, compContinuousLinearMap_apply]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg f (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [update_of_ne hj]

/-- Pullback along a map `g` that intertwines `A'` with `A`, `A ∘ g = g ∘ A'`, carries the
derivation `D_A` to `D_{A'}`: `(D_A f) ∘ g = D_{A'} (f ∘ g)`. -/
theorem compContinuousLinearMap_fderivCompContinuousLinearMap_id (f : F [⋀^ι]→L[𝕜] G)
    {g : E →L[𝕜] F} {A : F →L[𝕜] F} {A' : E →L[𝕜] E} (h : A ∘L g = g ∘L A') :
    (f.fderivCompContinuousLinearMap (.id 𝕜 F) A).compContinuousLinearMap g =
      (f.compContinuousLinearMap g).fderivCompContinuousLinearMap (.id 𝕜 E) A' := by
  rw [← fderivCompContinuousLinearMap_comp, h,
    fderivCompContinuousLinearMap_compContinuousLinearMap, ContinuousLinearMap.comp_id]

end Pullback

end ContinuousAlternatingMap
