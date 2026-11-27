/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.Geometry.Manifold.Morse.Bott.Inequalities
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
import SymplecticGeometry.Geometry.Manifold.Morse.BettiNumber

/-!
# The Euler characteristic of a manifold from a Morse–Bott function

Let the family of smooth embeddings `i j : S j → M` exhibit `f` as a Morse–Bott function on a
compact boundaryless manifold `M`, the piece `S j` having Morse index `r j`. Then
`χ(M) = ∑ⱼ (-1)^{r j} χ(S j)`. This is Euler's equality for Morse–Bott functions in
characteristic two, Tau Ceti's
`TauCeti.IsMorseBottFamily.sum_range_neg_one_pow_mul_bettiNumber_eq_sum` over `ZMod 2`, read
through the Euler–Poincaré formula `TauCeti.eulerChar_eq_sum_range_bettiNumber` for `M` and for
each piece, in a degree large enough for all of them. Working over `ZMod 2` needs no orientation
of the negative normal bundles.

## Main results

* `TauCeti.IsMorseBottFamily.eulerChar_eq_sum`: `χ(M) = ∑ⱼ (-1)^{r j} χ(S j)`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Theorem 2.44.
-/

public section

open Module Set
open scoped Manifold ContDiff

namespace TauCeti

namespace IsMorseBottFamily

variable {E : Type} {H : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  {ι : Type*} [Fintype ι] {E' H' : ι → Type*} {S : ι → Type}
  [∀ j, NormedAddCommGroup (E' j)] [∀ j, NormedSpace ℝ (E' j)] [∀ j, FiniteDimensional ℝ (E' j)]
  [∀ j, TopologicalSpace (H' j)] {J : ∀ j, ModelWithCorners ℝ (E' j) (H' j)}
  [∀ j, (J j).Boundaryless] [∀ j, TopologicalSpace (S j)] [∀ j, ChartedSpace (H' j) (S j)]
  [∀ j, IsManifold (J j) ∞ (S j)] {f : M → ℝ} {i : ∀ j, SmoothEmbedding (J j) I ∞ (S j) M}

/-- **The Euler characteristic from a Morse–Bott function.** Let the family `i j : S j → M`
exhibit `f` as a Morse–Bott function on a compact boundaryless manifold `M`, the piece `S j`
having Morse index `r j`. Then `χ(M) = ∑ⱼ (-1)^{r j} χ(S j)`. The finite CW types of `M` and of
the pieces are instance arguments; `TauCeti.FiniteCWType.of_isManifold` supplies them. -/
theorem eulerChar_eq_sum [FiniteCWType M] [∀ j, FiniteCWType (S j)] (h : IsMorseBottFamily i f)
    {r : ι → ℕ} (hr : ∀ j s, manifoldMorseIndex I f (i j s) = r j) :
    eulerChar M = ∑ j, (-1 : ℤ) ^ r j * eulerChar (S j) := by
  -- A degree above the dimension of `M` and above `r j + dim S j` for every piece.
  set n := finrank ℝ E + ∑ j, (r j + finrank ℝ (E' j))
  have hle (j : ι) : r j + finrank ℝ (E' j) ≤ n :=
    (Finset.single_le_sum (f := fun j ↦ r j + finrank ℝ (E' j)) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ j)).trans (Nat.le_add_left _ _)
  have (j : ι) : T2Space (S j) := (i j).isEmbedding.t2Space
  have (j : ι) : CompactSpace (S j) :=
    h.compactSpace_of_range_subset isCompact_univ (subset_univ _)
  rw [eulerChar_eq_sum_range_bettiNumber I (ZMod 2) (n := n) (Nat.le_add_right _ _),
    h.sum_range_neg_one_pow_mul_bettiNumber_eq_sum (ZMod 2) rfl hr (Nat.le_add_right _ _)]
  push_cast
  simp_rw [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- The degrees below `r j` do not contribute; shift the others down by `r j`.
  rw [eulerChar_eq_sum_range_bettiNumber (J j) (ZMod 2) (n := n - r j) (by have := hle j; omega),
    show n + 1 = r j + (n - r j + 1) by have := hle j; omega, Finset.sum_range_add,
    Finset.sum_eq_zero fun k hk ↦ by simp [Finset.mem_range.1 hk], zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [pow_add, mul_assoc]

end IsMorseBottFamily

end TauCeti

end
