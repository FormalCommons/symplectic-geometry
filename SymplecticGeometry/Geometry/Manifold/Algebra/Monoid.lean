/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Left multiplication as a bundled `C^n` map

For a monoid `G` whose multiplication is `C^n` (`ContMDiffMul I n G`), left multiplication
`h ↦ g * h` by a fixed `g` is a bundled `C^n` map `ContMDiffMap.mulLeft g : C^n⟮I, G; I, G⟯`, and
its additive version is `ContMDiffMap.addLeft`. This is the version for any `n` of Mathlib's
`smoothLeftMul`, which is stated for `n = ∞` only; its definition is that of `smoothLeftMul`.

## Main definitions

* `ContMDiffMap.mulLeft`: left multiplication by `g`, as a `C^n` map.

## Main results

* `ContMDiffMap.mulLeft_mul`: in a semigroup, left multiplication by `g * h` is left
  multiplication by `h` followed by left multiplication by `g`. It is the version for any `n` of
  Mathlib's `L_mul`, and has its proof.
-/

public section

open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞}

section Mul

variable {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I n G]

/-- Left multiplication `h ↦ g * h` by `g`, as a `C^n` map of `G` into itself, for a `G` whose
multiplication is `C^n`. -/
@[to_additive /-- Left addition `h ↦ g + h` of `g`, as a `C^n` map of `G` into itself, for a `G`
whose addition is `C^n`. -/]
def mulLeft (g : G) : C^n⟮I, G; I, G⟯ :=
  ⟨(g * ·), contMDiff_mul_left⟩

@[to_additive (attr := simp)]
theorem mulLeft_apply (g h : G) : mulLeft (I := I) (n := n) g h = g * h :=
  (rfl)

@[to_additive (attr := simp)]
theorem coe_mulLeft (g : G) : ⇑(mulLeft (I := I) (n := n) g) = (g * ·) :=
  (rfl)

end Mul

/-- Left multiplication by `g * h` is left multiplication by `h` followed by left multiplication
by `g`. -/
@[to_additive (attr := simp) /-- Left addition of `g + h` is left addition of `h` followed by
left addition of `g`. -/]
theorem mulLeft_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G]
    [ContMDiffMul I n G] (g h : G) :
    mulLeft (I := I) (n := n) (g * h) = (mulLeft g).comp (mulLeft h) := by
  ext
  simp [mul_assoc]

end ContMDiffMap

end
