/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group

/-!
# Families of self-diffeomorphisms that are jointly smooth on a set

A family `f : P → TauCeti.Diff I M n` of self-diffeomorphisms of `M` is jointly `C^m` on `s ⊆ P`
when its uncurried map `(x, v) ↦ f x v` is `C^m` on `s ×ˢ univ`. Tau Ceti's
`TauCeti/Geometry/Diffeomorphism/Group.lean` treats families that are jointly smooth on all of
`P`; this file gives the forms of two of its facts on a set.

## Main results

* `Diffeomorph.contMDiffOn_mul_apply`: the pointwise product of two families that are jointly
  `C^m` on `s` is jointly `C^m` on `s`. It is `Diffeomorph.contMDiff_mul_apply` on a set, with
  the same proof.
* `Diffeomorph.contMDiffOn_apply_of_eqOn_one`: a family equal to `1` on `s` is jointly `C^m` on
  `s`.
-/

public section

open Set
open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {P : Type*} [TopologicalSpace P]
  [ChartedSpace H' P] {m : ℕ∞ω} {s : Set P}

/-- The pointwise product of two families of self-diffeomorphisms that are jointly `C^m` on
`s ×ˢ univ` is jointly `C^m` on `s ×ˢ univ`. -/
theorem contMDiffOn_mul_apply {f g : P → M ≃ₘ^n⟮I, I⟯ M}
    (hf : ContMDiffOn (I'.prod I) I m (fun q : P × M ↦ f q.1 q.2) (s ×ˢ univ))
    (hg : ContMDiffOn (I'.prod I) I m (fun q : P × M ↦ g q.1 q.2) (s ×ˢ univ)) :
    ContMDiffOn (I'.prod I) I m (fun q : P × M ↦ (f q.1 * g q.1) q.2) (s ×ˢ univ) :=
  hf.comp (contMDiffOn_fst.prodMk hg) fun _ hq ↦ ⟨hq.1, trivial⟩

/-- A family of self-diffeomorphisms that is `1` on `s` is jointly `C^m` on `s ×ˢ univ`. -/
theorem contMDiffOn_apply_of_eqOn_one {f : P → M ≃ₘ^n⟮I, I⟯ M} (hf : EqOn f 1 s) :
    ContMDiffOn (I'.prod I) I m (fun q : P × M ↦ f q.1 q.2) (s ×ˢ univ) :=
  contMDiffOn_snd.congr fun q hq ↦ by rw [hf hq.1, Pi.one_apply, one_apply]

end Diffeomorph

end
