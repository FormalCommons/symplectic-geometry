/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Automorphism
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Biholomorphisms of the Riemann sphere as elements of `PSL(2, ℂ)`

Every biholomorphism of the Riemann sphere `OnePoint ℂ` is `x ↦ g • x` for some `g` in
`PSL(2, ℂ)` (`Diffeomorph.exists_coe_eq_psl_smul`). This is Tau Ceti's
`Diffeomorph.exists_coe_eq_smul`, which gives such a `g` in `GL(2, ℂ)`, combined with
`Matrix.GeneralLinearGroup.exists_psl_forall_smul_eq_smul`: since `ℂ` is algebraically closed,
every invertible matrix acts on the projective line as an element of `PSL(2, ℂ)`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §2, for the Möbius transformations of the Riemann sphere.
-/

public section

open scoped Manifold MatrixGroups

namespace Diffeomorph

variable {n : WithTop ℕ∞}

/-- Every biholomorphism of the Riemann sphere is `x ↦ g • x` for some `g ∈ PSL(2, ℂ)`. -/
theorem exists_coe_eq_psl_smul (f : OnePoint ℂ ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ OnePoint ℂ)
    (hn : n ≠ 0) :
    ∃ g : PSL(2, ℂ), ⇑f = fun x ↦ g • x := by
  obtain ⟨g, hg⟩ := f.exists_coe_eq_smul hn
  obtain ⟨h, hh⟩ := Matrix.GeneralLinearGroup.exists_psl_forall_smul_eq_smul g
  exact ⟨h, hg.trans (funext fun x ↦ (hh x).symm)⟩

end Diffeomorph

end
