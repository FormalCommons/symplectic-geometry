/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Map

/-!
# Constant maps on de Rham cohomology

This file is a part of Tau Ceti's file `TauCeti/Geometry/Manifold/DeRham/Map.lean`, as of the
commit `b952d20066` of Tau Ceti's main branch. It contains only the lemma that this commit adds
there, `TauCeti.deRhamCohomology.map_const_eq_zero`: a constant map induces zero on de Rham
cohomology in positive degrees.

It is stated under its Tau Ceti name and namespace, with Tau Ceti's statement, proof, docstring
and variables. The one change is to the imports: in place of Tau Ceti's file, this file imports the
pinned version of it.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

section Pullback

variable {E H E' H' E'' H'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {I'' : ModelWithCorners ℝ E'' H''}
  {M M' M'' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 2 M']
  [TopologicalSpace M''] [ChartedSpace H'' M''] [IsManifold I'' 2 M'']

namespace deRhamCohomology

/-- A constant map induces zero on de Rham cohomology in positive degrees: its derivative
vanishes, so it pulls every form of positive degree back to zero. -/
theorem map_const_eq_zero {k : ℕ} (hk : k ≠ 0) (c : M') :
    map (I := I) (I' := I') (M := M) (fun _ ↦ c) contMDiff_const k = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  refine LinearMap.ext fun a ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective I' k.succ a
  have h : closedForms.mpullback (I := I) (M := M) (fun _ ↦ c) contMDiff_const (k + 1) φ = 0 := by
    ext : 2
    simp [closedForms.coe_mpullback, SmoothForm.coe_mpullback]
  rw [map_mk, LinearMap.zero_apply, mk_eq_zero_iff, h, Submodule.coe_zero]
  exact Submodule.zero_mem _

end deRhamCohomology

end Pullback

end TauCeti
