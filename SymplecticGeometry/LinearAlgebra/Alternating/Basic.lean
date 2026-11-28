/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.FinCases

/-!
# Alternating maps of few vectors, on multiples of one vector, and on small submodules

An alternating map of one vector is determined by its values on the one-element families `![w]`
(`AlternatingMap.ext_fin_one`), and one of two vectors by its values on the pairs `![v, w]`
(`AlternatingMap.ext_fin_two`). A proof that two such maps agree can then work with vectors
instead of families `Fin 1 → M` or `Fin 2 → M`.

An alternating map vanishes on a family two of whose members are multiples of the same vector
(`AlternatingMap.map_eq_zero_of_eq_smul`). This generalizes `AlternatingMap.map_eq_zero_of_eq`,
the case of two equal members, to which the proof reduces by linearity in those two arguments.

An alternating map of three vectors takes the same value on `![a, b, c]` and on its cyclic
rotation `![b, c, a]` (`AlternatingMap.map_vecCons_rotate`): by `AlternatingMap.map_perm` the two
values differ by the sign of a cyclic permutation of three elements, which is `1`.

An alternating map vanishes on a family that has more members in a finite submodule `V` than the
rank of `V` (`AlternatingMap.map_eq_zero_of_finrank_lt`), since those members are linearly
dependent (`AlternatingMap.map_linearDependent`). This is a relative form of Tau Ceti's
`ContinuousAlternatingMap.eq_zero_of_finrank_lt`, the case `V = ⊤`.

Adding to the first `r` arguments of an alternating map of degree `r + m` vectors of a submodule
`V` of rank at most `m` does not change its value, provided that its last `m` arguments lie
in `V` (`AlternatingMap.map_append_add_of_mem`): each term of the multilinear expansion that
contains an added vector has `m + 1` arguments in `V`, so it vanishes by
`AlternatingMap.map_eq_zero_of_finrank_lt`.

An alternating map of three vectors of a product `M₁ × M₂` is zero once it vanishes on the
triples with two members in `M₂`, on those with two members in `M₁` followed by one in `M₂`, and on
those with three members in `M₁` (`AlternatingMap.eq_zero_of_forall_prod_fin_three`). Each member
splits into its parts in `M₁` and in `M₂`; after expanding by multilinearity, every term is, up to
the sign of a permutation of its arguments, one of these three kinds.
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

/-- An alternating map of three vectors takes the same value on `![a, b, c]` and on its cyclic
rotation `![b, c, a]`, as a cyclic permutation of three arguments is even. -/
theorem map_vecCons_rotate {N : Type*} [AddCommGroup N] [Module R N] (f : M [⋀^Fin 3]→ₗ[R] N)
    (a b c : M) : f ![a, b, c] = f ![b, c, a] := by
  have h : ![a, b, c] = ![b, c, a] ∘ (finRotate 3).symm := by
    ext i
    fin_cases i <;> rfl
  rw [h, map_perm, Equiv.Perm.sign_symm, sign_finRotate]
  simp

/-- An alternating map vanishes on a family `x` that has more members in a finite submodule `V`
than the rank of `V`: if `x (e k)` lies in `V` for an injective `e : κ → ι` and
`finrank K V < Fintype.card κ`, then `f x = 0`. -/
theorem map_eq_zero_of_finrank_lt {K M N κ : Type*} [Ring K] [IsDomain K] [StrongRankCondition K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [Module.IsTorsionFree K N]
    [Fintype κ] (f : M [⋀^ι]→ₗ[K] N) {x : ι → M} {V : Submodule K M} [Module.Finite K V]
    {e : κ → ι} (he : Function.Injective e) (hx : ∀ k, x (e k) ∈ V)
    (h : Module.finrank K V < Fintype.card κ) : f x = 0 :=
  f.map_linearDependent x fun hli ↦
    ((LinearIndependent.of_comp V.subtype (hli.comp e he) :
      LinearIndependent K fun k ↦ (⟨x (e k), hx k⟩ : V)).fintype_card_le_finrank).not_gt h

/-- Let `V` be a submodule of `W` of rank at most `m`. An alternating map `f` of `r + m`
vectors takes the same value on `Fin.append (v + u) w` and on `Fin.append v w` when every `u i`
and every `w j` lies in `V`: adding vectors of `V` to the first `r` arguments does not change `f`
once its last `m` arguments lie in `V`. -/
theorem map_append_add_of_mem {K W N : Type*} [Ring K] [IsDomain K] [StrongRankCondition K]
    [AddCommGroup W] [Module K W] [AddCommGroup N] [Module K N] [Module.IsTorsionFree K N]
    {r m : ℕ} (f : W [⋀^Fin (r + m)]→ₗ[K] N) {V : Submodule K W} [Module.Finite K V]
    (hV : Module.finrank K V ≤ m) (v : Fin r → W) {u : Fin r → W}
    (hu : ∀ i, u i ∈ V) {w : Fin m → W} (hw : ∀ j, w j ∈ V) :
    f (Fin.append (v + u) w) = f (Fin.append v w) := by
  classical
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
    | left i =>
      -- Positions `castAdd m i` and `natAdd r j` carry `u i` and the `w j`: `m + 1` members of `V`.
      let e : Option (Fin m) → Fin (r + m) := fun o ↦ o.elim (Fin.castAdd m i) (Fin.natAdd r)
      have he : Function.Injective e := by
        rintro (_ | a) (_ | b) h <;> simp_all [e, Fin.ext_iff] <;> omega
      refine f.map_eq_zero_of_finrank_lt he ?_ (by simpa using Nat.lt_succ_of_le hV)
      rintro (_ | j)
      · simpa [e, hk] using hu i
      · simpa [e, h j] using hw j
    | right j => exact absurd hk (h j)

section Prod

variable {M₁ M₂ N : Type*} [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
  [AddCommGroup N] [Module R N]

/-- An alternating map `f` of three vectors of a product `M₁ × M₂` is zero when it vanishes on
the triples of three kinds: those whose first two members lie in `M₂` (written `(0, w)`), those
whose first two members lie in `M₁` (written `(a, 0)`) and whose third lies in `M₂`, and those
whose three members lie in `M₁`. -/
theorem eq_zero_of_forall_prod_fin_three (f : (M₁ × M₂) [⋀^Fin 3]→ₗ[R] N)
    (hff : ∀ (w₁ w₂ : M₂) (v : M₁ × M₂), f ![(0, w₁), (0, w₂), v] = 0)
    (hbbf : ∀ (a b : M₁) (w : M₂), f ![(a, 0), (b, 0), (0, w)] = 0)
    (hbbb : ∀ a b c : M₁, f ![(a, 0), (b, 0), (c, 0)] = 0) : f = 0 := by
  have add₀ (x x' y z : M₁ × M₂) : f ![x + x', y, z] = f ![x, y, z] + f ![x', y, z] := by
    simpa using f.toMultilinearMap.cons_add ![y, z] x x'
  have add₁ (x y y' z : M₁ × M₂) : f ![x, y + y', z] = f ![x, y, z] + f ![x, y', z] := by
    rw [f.map_vecCons_rotate x (y + y') z, add₀, ← f.map_vecCons_rotate x y z,
      ← f.map_vecCons_rotate x y' z]
  have add₂ (x y z z' : M₁ × M₂) : f ![x, y, z + z'] = f ![x, y, z] + f ![x, y, z'] := by
    rw [← f.map_vecCons_rotate (z + z') x y, add₀, f.map_vecCons_rotate z x y,
      f.map_vecCons_rotate z' x y]
  have swap (x y z : M₁ × M₂) : f ![x, z, y] = -f ![x, y, z] := by
    have h : ![x, z, y] = ![x, y, z] ∘ Equiv.swap 1 2 := by
      funext i
      fin_cases i <;> rfl
    rw [h, f.map_swap _ (by decide)]
  have split (x : M₁ × M₂) : x = (x.1, 0) + (0, x.2) := by simp
  ext v
  obtain ⟨x, y, z, rfl⟩ : ∃ x y z, v = ![x, y, z] :=
    ⟨v 0, v 1, v 2, funext fun i ↦ by fin_cases i <;> rfl⟩
  rw [split x, split y, split z, add₀, add₁, add₁, add₂, add₂, add₂, add₂]
  simp only [hff, hbbf, hbbb, zero_apply]
  rw [swap (x.1, 0) (z.1, 0) (0, y.2), hbbf, f.map_vecCons_rotate (x.1, 0), hff,
    f.map_vecCons_rotate (0, x.2), hbbf, swap (0, x.2) (0, z.2) (y.1, 0), hff]
  simp

end Prod

end AlternatingMap

end
