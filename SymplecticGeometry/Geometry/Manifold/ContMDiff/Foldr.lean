/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothness of a fold of a list of smooth families of maps

Let `φ i : E' → M → M`, for `i : ι`, be families of maps of a manifold `M` indexed by a normed
space `E'`, each jointly `C^n` in the parameter and the point. Applying them in turn along a list
`l`, the `i`-th with parameter `s i`, gives a map of `(ι → E') × M` to `M` that is again `C^n`.

## Main results

* `List.contMDiff_foldr`: the map `(s, z) ↦ l.foldr (fun i w ↦ φ i (s i) w) z` is `C^n`.
-/

public section

open scoped Manifold

namespace List

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

/-- Applying in turn the maps `φ i (s i)`, for `i` in a list `l`, depends jointly `C^n`-smoothly
on `s` and the starting point when each `φ i` does. -/
theorem contMDiff_foldr {ι : Type*} [Fintype ι] {φ : ι → E' → M → M}
    (hφ : ∀ i, ContMDiff (𝓘(𝕜, E').prod I) I n fun q : E' × M ↦ φ i q.1 q.2) (l : List ι) :
    ContMDiff (𝓘(𝕜, ι → E').prod I) I n
      fun q : (ι → E') × M ↦ l.foldr (fun i w ↦ φ i (q.1 i) w) q.2 := by
  induction l with
  | nil => exact contMDiff_snd
  | cons i l ih =>
    have hi : ContMDiff (𝓘(𝕜, ι → E').prod I) 𝓘(𝕜, E') n fun q : (ι → E') × M ↦ q.1 i :=
      (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ E') i).contMDiff.comp contMDiff_fst
    exact (hφ i).comp (hi.prodMk ih)

end List

end
