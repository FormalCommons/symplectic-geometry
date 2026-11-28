/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Curry

/-!
# Paired wedges: degree transport, vanishing on a subspace, and vectors the left factor kills

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

If a `k`-form `φ` vanishes on every tuple having one of the vectors `b₁, …, b_m` as an entry,
then `φ ∧ ψ` on `(a₁, …, a_{k+l}, b₁, …, b_m)` is the shuffle sum over the `a` alone, with the
`b` fixed in the last arguments of `ψ`: a summand that hands some `b j` to `φ` vanishes. For
one vector `u`, moving it to the front makes the wedge its contraction with `u`, which Tau Ceti's
`ContinuousAlternatingMap.curryLeftTopological_pairedWedge` splits into a term with `ι_u φ = 0`
and a term with `ι_u ψ`; induction on `m` gives the general case. This is the right-hand,
partial counterpart of Tau Ceti's `ContinuousAlternatingMap.pairedWedge_apply_append_of_forall`,
where `ψ` kills every vector handed to `φ`. It evaluates the wedge of a form pulled back from the
base of a product with any form, on a tuple of lifted base vectors followed by vertical vectors.

## Main results

* `ContinuousAlternatingMap.pairedWedge_apply_of_right_eq_smul_cast`: degree transport in the
  right factor of a paired wedge.
* `ContinuousAlternatingMap.pairedWedge_apply_eq_zero_of_mem`: the wedge of a one-form vanishing
  on `K` with a two-form vanishing on `K × K` vanishes on `(η₁, η₂, v)` for `η₁ η₂ ∈ K`.
* `ContinuousAlternatingMap.pairedWedge_apply_snoc_of_forall`: one last vector `u` that `φ`
  kills, `(φ ∧ ψ)(a, u) = (-1) ^ l • (φ ∧ ι_u ψ)(a)`.
* `ContinuousAlternatingMap.pairedWedge_apply_append_eq_sum_of_forall`: last vectors `b` that `φ`
  kills, as a shuffle sum over `a`.
-/

public section

open Equiv

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
  have hα' : (fun i : Fin 1 ↦ w (σ (Fin.castAdd 2 i))) = ![w (σ 0)] :=
    (FinVec.etaExpand_eq _).symm
  by_cases h0 : σ 0 = 2
  · -- `α` receives `v`, so `ψ` receives the two vectors of `K`.
    have hne (i : Fin 3) (hi : i ≠ 0) : σ i ≠ 2 := fun h ↦ hi (σ.injective (h.trans h0.symm))
    have hψσ : (fun j : Fin 2 ↦ w (σ (Fin.natAdd 1 j))) = ![w (σ 1), w (σ 2)] :=
      (FinVec.etaExpand_eq _).symm
    simp [hψσ, hψ _ (hw _ (hne 1 (by decide))) _ (hw _ (hne 2 (by decide)))]
  · -- `α` receives a vector of `K`.
    simp [hα', hα _ (hw _ h0)]

/-- **A paired wedge on a tuple ending in a vector that the first factor kills.** Let `φ` be a
`k`-form vanishing on every tuple that has `u` as an entry, and `ψ` an `(l + 1)`-form. Then
`(φ ∧ ψ)(a₁, …, a_{k+l}, u) = (-1) ^ l • (φ ∧ ι_u ψ)(a₁, …, a_{k+l})`, where
`ι_u ψ = ContinuousAlternatingMap.curryLeftTopological ψ u` puts `u` first. -/
theorem pairedWedge_apply_snoc_of_forall [ContinuousAdd F₁] [ContinuousConstSMul ℝ F₁]
    [ContinuousAdd F₂] [ContinuousConstSMul ℝ F₂]
    {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) (φ : E [⋀^Fin k]→L[ℝ] F₁)
    (ψ : E [⋀^Fin (l + 1)]→L[ℝ] F₂) (a : Fin (k + l) → E) (u : E)
    (hφ : ∀ (z : Fin k → E) (i : Fin k), z i = u → φ z = 0) :
    pairedWedge μ hμ φ ψ (Fin.snoc a u) =
      (-1 : ℝ) ^ l • pairedWedge μ hμ φ (curryLeftTopological ψ u) a := by
  cases k with
  | zero =>
    have h : (Fin.snoc a u ∘ Fin.cast (Nat.zero_add (l + 1)).symm : Fin (l + 1) → E) =
        Fin.insertNth (Fin.last l) u (a ∘ Fin.cast (Nat.zero_add l).symm) := by
      rw [Fin.insertNth_last']
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [Fin.snoc]
    rw [pairedWedge_apply_zero_left, pairedWedge_apply_zero_left, h, map_insertNth',
      curryLeftTopological_apply_apply, Fin.val_last, ← Int.cast_smul_eq_zsmul ℝ, map_smul]
    simp
  | succ k =>
    -- The contraction of `φ` with `u` vanishes.
    have hφu : curryLeftTopological φ u = 0 := by
      ext z
      simpa [curryLeftTopological_apply_apply] using hφ (Matrix.vecCons u z) 0 rfl
    rw [← Fin.insertNth_last', map_insertNth', ← curryLeftTopological_apply_apply,
      curryLeftTopological_pairedWedge, hφu, pairedWedge_zero_left, coe_zero, Pi.zero_apply,
      zero_add, Fin.val_last, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    congr 1
    push_cast
    rw [← pow_add, Nat.add_eq, show k + 1 + l + (k + 1) = l + 2 * (k + 1) by omega, pow_add,
      pow_mul]
    simp

/-- **A paired wedge on a tuple ending in vectors that the first factor kills.** Let `φ` be a
`k`-form vanishing on every tuple that has one of the vectors `b₁, …, b_m` as an entry, and `ψ`
an `(l + m)`-form. On the tuple `(a₁, …, a_{k+l}, b₁, …, b_m)`, the wedge `φ ∧ ψ` is the shuffle
sum over the `a` alone, with `b` fixed in the last arguments of `ψ`:
`(k! l!)⁻¹ • ∑ σ, sign σ • μ (φ (a_{σ 1}, …, a_{σ k})) (ψ (a_{σ (k+1)}, …, a_{σ (k+l)}, b))`. -/
theorem pairedWedge_apply_append_eq_sum_of_forall [ContinuousAdd F₁] [ContinuousConstSMul ℝ F₁]
    [ContinuousAdd F₂] [ContinuousConstSMul ℝ F₂]
    {k l m : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) (φ : E [⋀^Fin k]→L[ℝ] F₁)
    (ψ : E [⋀^Fin (l + m)]→L[ℝ] F₂) (a : Fin (k + l) → E) (b : Fin m → E)
    (hφ : ∀ (z : Fin k → E) (i : Fin k) (j : Fin m), z i = b j → φ z = 0) :
    pairedWedge μ hμ φ ψ (fun i ↦ Fin.append a b (Fin.cast (Nat.add_assoc k l m).symm i)) =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Perm (Fin (k + l)), Perm.sign σ •
          μ (φ fun i ↦ a (σ (Fin.castAdd l i)))
            (ψ (Fin.append (fun j ↦ a (σ (Fin.natAdd k j))) b)) := by
  induction m generalizing l with
  | zero =>
    rw [pairedWedge_apply]
    refine congrArg _ (Finset.sum_congr rfl fun σ _ ↦ ?_)
    have h (z : Fin l → E) : Fin.append z b = z := by
      rw [Fin.append_right_nil z b rfl]
      funext i
      simp
    simp only [h, Fin.append_right_nil a b rfl, Function.comp_apply, Fin.cast_eq_self]
    -- What is left differs only by `Fin.castAdd (l + 0)` against `Fin.castAdd l`.
    rfl
  | succ m ih =>
    have hlast : Fin.cast (Nat.add_assoc k l (m + 1)).symm (Fin.last (k + (l + m))) =
        Fin.last (k + l + m) := Fin.ext (by simp; omega)
    have hb : (fun i ↦ Fin.append a b (Fin.cast (Nat.add_assoc k l (m + 1)).symm i)) =
        Fin.snoc (fun i ↦ Fin.append a (Fin.init b) (Fin.cast (Nat.add_assoc k l m).symm i))
          (b (Fin.last m)) := by
      conv_lhs => rw [← Fin.snoc_init_self b, Fin.append_snoc]
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) (show Fin (k + (l + m) + 1) from i)
      · rw [hlast]
        simp [Fin.snoc]
      · simp
    have hψ (z : Fin (l + m) → E) :
        ((-1 : ℝ) ^ (l + m) • curryLeftTopological ψ (b (Fin.last m))) z =
          ψ (Fin.snoc z (b (Fin.last m))) := by
      rw [← Fin.insertNth_last', map_insertNth', smul_apply, curryLeftTopological_apply_apply,
        Fin.val_last, ← Int.cast_smul_eq_zsmul ℝ]
      push_cast
      -- `map_insertNth'` writes the exponent `l + m` as `Nat.add l m`.
      rfl
    rw [hb, pairedWedge_apply_snoc_of_forall (l := l + m) μ hμ φ ψ _ _
      fun z i h ↦ hφ z i (Fin.last m) h, ← smul_apply, ← pairedWedge_smul_right,
      ih _ a (Fin.init b) fun z i j h ↦ hφ z i j.castSucc h]
    simp only [hψ, ← Fin.append_snoc, Fin.snoc_init_self]

end ContinuousAlternatingMap

end
