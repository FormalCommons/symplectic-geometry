/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm

/-!
# Alternating forms on a real inner product space: the inner product of `0`-forms

This file is a part of Tau Ceti's `TauCeti/Analysis/InnerProductSpace/AlternatingForm.lean`,
copied from Tau Ceti's main branch at commit `ed5dead80b23387a876edd02b323547b57379929`, which
the pinned version of Tau Ceti does not have yet. It contains one declaration,
`TauCeti.alternatingFormInner_zero_apply`: the inner product of two `0`-forms is the product of
their values on the empty tuple.

Apart from this module docstring, nothing is changed from Tau Ceti's text.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1.
-/

public section

noncomputable section

open Module exteriorPower Set
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti

/-- **The inner product of `0`-forms** is the product of their values: a `0`-form is a constant,
evaluated on the empty tuple `v`. -/
theorem alternatingFormInner_zero_apply (α β : V [⋀^Fin 0]→L[ℝ] ℝ) (v : Fin 0 → V) :
    alternatingFormInner V 0 α β = α v * β v := by
  rw [alternatingFormInner_eq_sum (stdOrthonormalBasis ℝ V)]
  simp only [Subsingleton.elim _ v, Finset.sum_const, Finset.card_univ]
  simp

end TauCeti
