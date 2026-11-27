/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Complex.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Real dimensions of complex vector spaces

A complex vector space of complex dimension `r + 1` has real dimension `2 r + 2`. Index types
of real orientations and degrees of cohomology classes of such spaces, and of complex vector
bundles and manifolds modelled on them, are often written `Fin (2 * r + 1 + 1)` and `2 * r + 2`,
so this file states the dimension in the form `2 * r + 1 + 1`.

## Main results

* `finrank_real_of_finrank_complex_eq_add_one`: from `finrank ℂ V = r + 1`, for any real
  structure on `V` compatible with the complex one, `finrank ℝ V = 2 * r + 1 + 1`. It is Tau
  Ceti's `TauCeti.finrank_real_eq_two_mul_finrank_complex` in complex dimension `r + 1`.
* `Complex.fact_finrank_real_eq_two_mul_finrank`: the real dimension of a complex vector space
  `E` is twice its complex dimension, Mathlib's `finrank_real_of_complex`, as a `Fact`: the form
  in which complex structures on vector bundles with model fibre `E` take it.
* `Complex.finrank_real_complex_eq_two_mul_finrank_fact`: its case `E = ℂ`, which files on
  complex structures with model fibre `ℂ` make a local instance.
* `Complex.finrank_real_eq_finrank_pi_succ_sub`: the real dimension `2` of `ℂ` is the difference
  of the real dimensions of `Fin (n + 1) → ℂ` and `Fin n → ℂ`.
* `Complex.finrank_real_eq_finrank_prod_sub`: it is also the difference of the real dimensions
  of `E × F` and `F`, for a real vector space `E` of dimension two.
* `Complex.finrank_real_eq_finrank_prod_complex_sub`: it is the difference of the real
  dimensions of `F × ℂ` and `F`.
* `Complex.finrank_real_eq_finrank_sub_of_finrank_eq_four_of_finrank_eq_two`: it is the
  difference of the real dimensions of a space of dimension four and one of dimension two.

These are codimension hypotheses with model fibre `ℂ`, in the form that Tau Ceti's normal bundles
of smooth embeddings (`TauCeti.SmoothEmbedding.normalSpaceFiberBundle`) take them.
-/

public section

namespace Complex

open Module

/-- The real dimension of a complex vector space `E`, as a real vector space by restriction of
scalars, is twice its complex dimension, as a `Fact`: the dimension convention of complex
structures on vector bundles with model fibre `E`. -/
theorem fact_finrank_real_eq_two_mul_finrank (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Fact (finrank ℝ E = 2 * finrank ℂ E) :=
  ⟨finrank_real_of_complex E⟩

/-- The real dimension of `ℂ` is twice its complex dimension: the dimension convention of
complex structures on vector bundles with model fibre `ℂ`, as a `Fact` to enable locally as an
instance. -/
theorem finrank_real_complex_eq_two_mul_finrank_fact :
    Fact (finrank ℝ ℂ = 2 * finrank ℂ ℂ) :=
  fact_finrank_real_eq_two_mul_finrank ℂ

/-- The real dimension `2` of `ℂ` is the difference of the real dimensions of `Fin (n + 1) → ℂ`
and `Fin n → ℂ`. -/
theorem finrank_real_eq_finrank_pi_succ_sub (n : ℕ) :
    finrank ℝ ℂ = finrank ℝ (Fin (n + 1) → ℂ) - finrank ℝ (Fin n → ℂ) := by
  simp only [finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- If `E` is a real vector space of dimension two, the real dimension `2` of `ℂ` is the difference
of the real dimensions of `E × F` and `F`, for any finite-dimensional `F`. -/
theorem finrank_real_eq_finrank_prod_sub {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F] (hE : finrank ℝ E = 2) :
    finrank ℝ ℂ = finrank ℝ (E × F) - finrank ℝ F := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  rw [finrank_prod, Nat.add_sub_cancel, hE, Complex.finrank_real_complex]

/-- The real dimension of `ℂ` is the difference of the real dimensions of `F × ℂ` and `F`, for
any finite-dimensional real vector space `F`. -/
theorem finrank_real_eq_finrank_prod_complex_sub {F : Type*} [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ F] : finrank ℝ ℂ = finrank ℝ (F × ℂ) - finrank ℝ F := by
  rw [finrank_prod, Nat.add_sub_cancel_left]

/-- The real dimension `2` of `ℂ` is the difference of the real dimensions of a real vector space
`E` of dimension four and a real vector space `F` of dimension two. -/
theorem finrank_real_eq_finrank_sub_of_finrank_eq_four_of_finrank_eq_two {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] (hE : finrank ℝ E = 4)
    (hF : finrank ℝ F = 2) : finrank ℝ ℂ = finrank ℝ E - finrank ℝ F := by
  rw [Complex.finrank_real_complex, hE, hF]

end Complex

namespace SymplecticGeometry

open Module

/-- A complex vector space of complex dimension `r + 1`, with a compatible real structure, has
real dimension `2 r + 2`, written `2 * r + 1 + 1`. -/
theorem finrank_real_of_finrank_complex_eq_add_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Module ℂ V] [IsScalarTower ℝ ℂ V] {r : ℕ} (hV : finrank ℂ V = r + 1) :
    finrank ℝ V = 2 * r + 1 + 1 := by
  rw [TauCeti.finrank_real_eq_two_mul_finrank_complex, hV]; ring

end SymplecticGeometry

end
