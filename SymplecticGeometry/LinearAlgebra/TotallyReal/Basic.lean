/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Normed.Operator.Bilinear
public import TauCeti.LinearAlgebra.TotallyReal.Basic

/-!
# Quadratic forms positive off a totally real subspace

Let `L` be a subspace of a real vector space `E` that is totally real for an endomorphism `J`
(Tau Ceti's `TauCeti.IsTotallyReal`). This file shows that a continuous bilinear form `B` with
`B v v > 0` for every `v ∉ L` has `B v v + B (J v) (J v) > 0` for every `v ≠ 0`, once `J` is
injective. This is the linear algebra behind criteria for strict plurisubharmonicity whose
Hessian degenerates along a totally real subspace.

## Main results

* `TauCeti.IsTotallyReal.apply_eq_zero_of_mem_of_apply_mem`: if `v` and `J v` both lie in `L`,
  then `J v = 0`.
* `TauCeti.IsTotallyReal.add_pos_of_forall_notMem_pos`: the positivity statement above. The form
  `B` is nonnegative everywhere by `ContinuousLinearMap.nonneg_of_forall_notMem_nonneg`, and by
  the previous lemma at most one of `v` and `J v` lies in `L`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace TauCeti

namespace IsTotallyReal

section Semiring

variable {R E : Type*} [Semiring R] [AddCommMonoid E] [Module R E] {J : E →ₗ[R] E}
  {L : Submodule R E}

/-- If `v` and `J v` both lie in a totally real subspace `L`, then `J v = 0`. -/
theorem apply_eq_zero_of_mem_of_apply_mem (hL : IsTotallyReal J L) {v : E} (hv : v ∈ L)
    (hJv : J v ∈ L) : J v = 0 :=
  Submodule.disjoint_def.1 hL.disjoint _ hJv ⟨v, hv, rfl⟩

end Semiring

variable {J : E →ₗ[ℝ] E} {L : Submodule ℝ E}

/-- Let `L` be totally real for an injective `J`. If a continuous bilinear form `B` satisfies
`B v v > 0` for every `v ∉ L`, then `B v v + B (J v) (J v) > 0` for every `v ≠ 0`. -/
theorem add_pos_of_forall_notMem_pos (hL : IsTotallyReal J L) (hJ : Function.Injective J)
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hpos : ∀ v ∉ L, 0 < B v v) {v : E} (hv : v ≠ 0) :
    0 < B v v + B (J v) (J v) := by
  have hnonneg (w : E) (hw : w ∉ L) (u : E) : 0 ≤ B u u :=
    B.nonneg_of_forall_notMem_nonneg (L := L) (fun h ↦ hw (h ▸ Submodule.mem_top))
      (fun v hv ↦ (hpos v hv).le) u
  by_cases h₁ : v ∈ L
  · have h₂ : J v ∉ L := fun h ↦
      hv (hJ ((hL.apply_eq_zero_of_mem_of_apply_mem h₁ h).trans J.map_zero.symm))
    exact add_pos_of_nonneg_of_pos (hnonneg _ h₂ v) (hpos _ h₂)
  · exact add_pos_of_pos_of_nonneg (hpos v h₁) (hnonneg v h₁ _)

end IsTotallyReal

end TauCeti

end
