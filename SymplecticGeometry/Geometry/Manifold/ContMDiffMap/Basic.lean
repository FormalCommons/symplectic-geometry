/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Basic lemmas on bundled `C^n` maps

The functions underlying a composite and the identity (`ContMDiffMap.coe_comp`,
`ContMDiffMap.coe_id`), for rewriting a bundled map where it stands as a function rather than
applied to a point.

Evaluation of a composite `g.comp ⟨f, hf⟩` of bundled `C^n` maps whose inner map is written with
the anonymous constructor (`ContMDiffMap.comp_mk_apply`). Such a term has the bare subtype
`{ f // ContMDiff I I' n f }` as the type of its inner map, so neither `ContMDiffMap.comp_apply`
nor `ContMDiffMap.coeFn_mk` rewrites it, and `simp` needs this lemma to evaluate it.

The file has the name of Tau Ceti's `Geometry/Manifold/ContMDiffMap/Basic.lean`, which evaluates
other bundled `C^n` maps pointwise, so that the two can join.
-/

public section

open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {n : WithTop ℕ∞}

/-- The function underlying a composite of bundled `C^n` maps is the composite of their
functions. -/
@[simp]
theorem coe_comp (g : C^n⟮I', M'; I'', M''⟯) (f : C^n⟮I, M; I', M'⟯) :
    ⇑(g.comp f) = ⇑g ∘ ⇑f :=
  (rfl)

/-- The function underlying the bundled identity `C^n` map is the identity. -/
@[simp]
theorem coe_id : ⇑(ContMDiffMap.id : C^n⟮I, M; I, M⟯) = _root_.id :=
  (rfl)

/-- The composite `g ∘ f` of a bundled `C^n` map `g` with a `C^n` map `f`, bundled by the
anonymous constructor, takes the value `g (f x)` at `x`. -/
@[simp, grind =]
theorem comp_mk_apply (g : C^n⟮I', M'; I'', M''⟯) (f : M → M') (hf : ContMDiff I I' n f)
    (x : M) : (g.comp ⟨f, hf⟩) x = g (f x) :=
  rfl

end ContMDiffMap

end
