/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Alternating maps of few vectors and on multiples of one vector

An alternating map of one vector is determined by its values on the one-element families `![w]`
(`AlternatingMap.ext_fin_one`), and one of two vectors by its values on the pairs `![v, w]`
(`AlternatingMap.ext_fin_two`). A proof that two such maps agree can then work with vectors
instead of families `Fin 1 → M` or `Fin 2 → M`.

An alternating map vanishes on a family two of whose members are multiples of the same vector
(`AlternatingMap.map_eq_zero_of_eq_smul`). This generalizes `AlternatingMap.map_eq_zero_of_eq`,
the case of two equal members, to which the proof reduces by linearity in those two arguments.

Adding to the first `r` arguments of an alternating map of degree `r + m` vectors of a subspace
`V` of dimension at most `m` does not change its value, provided that its last `m` arguments lie
in `V` (`AlternatingMap.map_append_add_of_mem`): each term of the multilinear expansion that
contains an added vector has `m + 1` arguments in `V`, which are linearly dependent, so it
vanishes by `AlternatingMap.map_linearDependent`.
-/

public section

namespace AlternatingMap

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- Two alternating maps of one vector are equal when they agree on every one-element family
`![w]`. -/
@[ext]
theorem ext_fin_one {f g : M [⋀^Fin 1]→ₗ[R] N} (h : ∀ w, f ![w] = g ![w]) : f = g :=
  ext fun v ↦ by
    rw [← FinVec.etaExpand_eq v]
    exact h (v 0)

/-- Two alternating maps of two vectors are equal when they agree on every pair `![v, w]`. -/
@[ext]
theorem ext_fin_two {f g : M [⋀^Fin 2]→ₗ[R] N} (h : ∀ v w, f ![v, w] = g ![v, w]) : f = g :=
  ext fun u ↦ by
    rw [← FinVec.etaExpand_eq u]
    exact h (u 0) (u 1)

/-- An alternating map vanishes on a family `v` whose members `v i` and `v j`, for `i ≠ j`, are
multiples `a • x` and `b • x` of the same vector `x`. -/
theorem map_eq_zero_of_eq_smul (f : M [⋀^ι]→ₗ[R] N) {v : ι → M} {i j : ι} (hij : i ≠ j)
    {x : M} {a b : R} (hi : v i = a • x) (hj : v j = b • x) : f v = 0 := by
  classical
  have hv : v = Function.update (Function.update v j (b • x)) i (a • x) := by
    rw [← hi, ← hj, Function.update_eq_self, Function.update_eq_self]
  rw [hv, f.map_update_smul, ← Function.update_comm hij, f.map_update_smul,
    f.map_eq_zero_of_eq _ (i := i) (j := j) (by simp [hij]) hij, smul_zero, smul_zero]

/-- Let `V` be a subspace of `W` of dimension at most `m`. An alternating map `f` of `r + m`
vectors takes the same value on `Fin.append (v + u) w` and on `Fin.append v w` when every `u i`
and every `w j` lies in `V`: adding vectors of `V` to the first `r` arguments does not change `f`
once its last `m` arguments lie in `V`. -/
theorem map_append_add_of_mem {K W N : Type*} [DivisionRing K] [AddCommGroup W] [Module K W]
    [AddCommGroup N] [Module K N] {r m : ℕ} (f : W [⋀^Fin (r + m)]→ₗ[K] N) {V : Submodule K W}
    [FiniteDimensional K V] (hV : Module.finrank K V ≤ m) (v : Fin r → W) {u : Fin r → W}
    (hu : ∀ i, u i ∈ V) {w : Fin m → W} (hw : ∀ j, w j ∈ V) :
    f (Fin.append (v + u) w) = f (Fin.append v w) := by
  classical
  -- A family with `u i` at position `i` and `w` in its last `m` places is sent to zero.
  have key : ∀ x : Fin (r + m) → W, ∀ i : Fin r, x (Fin.castAdd m i) = u i →
      (∀ j, x (Fin.natAdd r j) = w j) → f x = 0 := by
    intro x i hi hj
    refine f.map_linearDependent x fun hx ↦ ?_
    let e : Option (Fin m) → Fin (r + m) := fun o ↦ o.elim (Fin.castAdd m i) (Fin.natAdd r)
    have he : Function.Injective e := by
      rintro (_ | a) (_ | b) h <;> simp_all [e, Fin.ext_iff] <;> omega
    have hmem : ∀ o, x (e o) ∈ V := by
      rintro (_ | j)
      · simpa [e, hi] using hu i
      · simpa [e, hj] using hw j
    have hli : LinearIndependent K (fun o ↦ (⟨x (e o), hmem o⟩ : V)) :=
      LinearIndependent.of_comp V.subtype (hx.comp e he)
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_option, Fintype.card_fin] at this
    omega
  have hsplit : Fin.append (v + u) w = Fin.append u 0 + Fin.append v w := by
    ext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;> simp [add_comm]
  rw [hsplit, f.map_add_univ, ← Finset.sum_erase_add _ _ (Finset.mem_univ ∅),
    Finset.piecewise_empty, Finset.sum_eq_zero, zero_add]
  intro s hs
  obtain ⟨k, hk⟩ := Finset.ne_empty_iff_nonempty.1 (Finset.ne_of_mem_erase hs)
  by_cases h : ∃ j, Fin.natAdd r j ∈ s
  · obtain ⟨j, hj⟩ := h
    exact f.map_coord_zero (Fin.natAdd r j) (by simp [hj])
  · push Not at h
    induction k using Fin.addCases with
    | left i => exact key _ i (by simp [hk]) fun j ↦ by simp [h j]
    | right j => exact absurd hk (h j)

end AlternatingMap

end
