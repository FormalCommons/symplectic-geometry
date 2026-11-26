/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Basic

/-!
# Paired wedges: degree transport in the right factor, and vanishing on a subspace

If the right factor `A` of a paired wedge `φ ∧ A` agrees with `c • B` once its arguments are
relabelled along `Fin.cast h`, then `φ ∧ A` is `c • (φ ∧ B)`, evaluated on the relabelled tuple.
This lets one rewrite a factor whose degree is only propositionally equal to the expected one.

The statement and its proof are the right-hand counterpart of Tau Ceti's
`ContinuousAlternatingMap.pairedWedge_apply_of_left_eq_smul_cast`, whose proof they follow step
by step.

If a one-form `α` vanishes on a subspace `K` and a two-form `ψ` vanishes on pairs of vectors of
`K`, then `α ∧ ψ` vanishes on every triple whose first two vectors lie in `K`. This refines Tau
Ceti's `ContinuousAlternatingMap.pairedWedge_apply_eq_zero_of_forall`, which asks `α` to vanish
on every vector of the tuple, and its proof extends that one.

## Main results

* `ContinuousAlternatingMap.pairedWedge_apply_of_right_eq_smul_cast`: degree transport in the
  right factor of a paired wedge.
* `ContinuousAlternatingMap.pairedWedge_apply_eq_zero_of_mem`: the wedge of a one-form vanishing
  on `K` with a two-form vanishing on `K × K` vanishes on `(η₁, η₂, v)` for `η₁ η₂ ∈ K`.
-/

public section

namespace ContinuousAlternatingMap

variable {E F₁ F₂ F₃ : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
  [AddCommGroup F₃] [Module ℝ F₃] [TopologicalSpace F₃] [IsTopologicalAddGroup F₃]
  [ContinuousConstSMul ℝ F₃]

/-- Degree transport in the second factor of a paired wedge: if `A`, of degree `b`, agrees with
`c • B` after reindexing its arguments along `Fin.cast h : Fin a → Fin b`, then the wedge of `φ`
and `A` is `c •` the wedge of `φ` and `B`, evaluated on the correspondingly transported tuple. -/
theorem pairedWedge_apply_of_right_eq_smul_cast {a b k : ℕ}
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) (h : a = b)
    {A : E [⋀^Fin b]→L[ℝ] F₂} {B : E [⋀^Fin a]→L[ℝ] F₂} (c : ℝ)
    (hAB : ∀ w, A w = c • B (w ∘ Fin.cast h)) (φ : E [⋀^Fin k]→L[ℝ] F₁) (x : Fin (k + b) → E) :
    pairedWedge μ hμ φ A x = c • pairedWedge μ hμ φ B (x ∘ Fin.cast (by omega)) := by
  subst h
  simp only [pairedWedge_apply, hAB, map_smul, smul_comm _ c, Finset.smul_sum]
  -- After `subst`, the transport `Fin.cast` is the identity on values, so both tuples agree.
  rfl

/-- Let `α` be a one-form vanishing on a submodule `K`, and `ψ` a two-form vanishing on every
pair of vectors of `K`. Then the paired wedge `α ∧ ψ` vanishes on `(η₁, η₂, v)` for all
`η₁ η₂ ∈ K` and every `v`. -/
theorem pairedWedge_apply_eq_zero_of_mem (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) {K : Submodule ℝ E}
    {α : E [⋀^Fin 1]→L[ℝ] F₁} {ψ : E [⋀^Fin 2]→L[ℝ] F₂} (hα : ∀ u ∈ K, α ![u] = 0)
    (hψ : ∀ u ∈ K, ∀ w ∈ K, ψ ![u, w] = 0) {η₁ η₂ : E} (h₁ : η₁ ∈ K) (h₂ : η₂ ∈ K) (v : E) :
    pairedWedge μ hμ α ψ ![η₁, η₂, v] = 0 := by
  set w : Fin 3 → E := ![η₁, η₂, v]
  -- Every vector of the triple but the last lies in `K`.
  have hw (i : Fin 3) (hi : i ≠ 2) : w i ∈ K := by
    fin_cases i
    exacts [h₁, h₂, absurd rfl hi]
  rw [pairedWedge_apply]
  refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun σ _ ↦ ?_)
  have hα' : (fun i : Fin 1 ↦ w (σ (Fin.castAdd 2 i))) = ![w (σ 0)] := by
    ext i
    fin_cases i
    rfl
  by_cases h0 : σ 0 = 2
  · -- `α` receives `v`, so `ψ` receives the two vectors of `K`.
    have hne (i : Fin 3) (hi : i ≠ 0) : σ i ≠ 2 := fun h ↦ hi (σ.injective (h.trans h0.symm))
    have hψσ : (fun j : Fin 2 ↦ w (σ (Fin.natAdd 1 j))) = ![w (σ 1), w (σ 2)] := by
      ext j
      fin_cases j <;> rfl
    simp [hψσ, hψ _ (hw _ (hne 1 (by decide))) _ (hw _ (hne 2 (by decide)))]
  · -- `α` receives a vector of `K`.
    simp [hα', hα _ (hw _ h0)]

end ContinuousAlternatingMap

end
