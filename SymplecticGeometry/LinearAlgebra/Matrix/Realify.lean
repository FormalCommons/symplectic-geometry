/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Realify

/-!
# Realification and reindexing

Tau Ceti's `Matrix.realify` turns a matrix over `ℝ` or `ℂ` into the real block matrix
`[[Re A, -Im A], [Im A, Re A]]`, indexed by `m ⊕ m` and `n ⊕ n`. This file shows that it commutes
with taking submatrices, and so with reindexing: the rows and columns of each block are
selected in the same way.

## Main results

* `Matrix.realify_submatrix`: `(A.submatrix f g).realify` is `A.realify` with rows selected by
  `Sum.map f f` and columns by `Sum.map g g`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.1 (the identification of `ℂⁿ` with `ℝ²ⁿ`).
-/

public section

namespace Matrix

variable {m n m' n' 𝕜 : Type*} [RCLike 𝕜]

/-- Realification commutes with submatrices: selecting rows by `f` and columns by `g` before
realifying is selecting them by `Sum.map f f` and `Sum.map g g` after. -/
theorem realify_submatrix (A : Matrix m n 𝕜) (f : m' → m) (g : n' → n) :
    (A.submatrix f g).realify = A.realify.submatrix (Sum.map f f) (Sum.map g g) := by
  ext (i | i) (j | j) <;> simp

end Matrix

end
