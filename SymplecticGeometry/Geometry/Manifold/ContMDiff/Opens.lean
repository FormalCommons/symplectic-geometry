/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Smooth maps and open subsets

Let `U` be an open subset of a manifold `M`, `n` a smoothness order, `Φ : P × U → U` a `C^n` map,
and `k : P × M → N` a map that is `C^n` on `P × U`. This file shows that the map equal to
`(p, x) ↦ k (p, Φ (p, x))` on `P × U` and to `k` elsewhere is `C^n` on `P × U`
(`ContMDiffOn.dite_comp_of_opens`). The case used in the library is that of a diffeotopy `Φ` of
`U`, with `P = [0, 1]` and `n = ∞`.

## Main results

* `ContMDiffOn.dite_comp_of_opens`: the map above is `C^n` on `P × U`.
-/

public section

open Set TopologicalSpace
open scoped Manifold

variable {EP HP P E H M E' H' N : Type*}
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  [TopologicalSpace P] [ChartedSpace HP P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

open Classical in
/-- Let `U` be an open subset of `M`, `Φ : P × U → U` a `C^n` map, and `k : P × M → N` a map that
is `C^n` on `P × U`. The map equal to `(p, x) ↦ k (p, Φ (p, x))` on `P × U` and to `k` elsewhere
is `C^n` on `P × U`. -/
theorem ContMDiffOn.dite_comp_of_opens {n : WithTop ℕ∞} {U : Opens M} {Φ : P × U → U}
    (hΦ : ContMDiff (IP.prod J) J n Φ) {k : P × M → N}
    (hk : ContMDiffOn (IP.prod J) I' n k (univ ×ˢ U)) :
    ContMDiffOn (IP.prod J) I' n
      (fun p ↦ if h : p.2 ∈ U then k (p.1, Φ (p.1, ⟨p.2, h⟩)) else k p) (univ ×ˢ U) := by
  have hg : ContMDiff (IP.prod J) I' n (fun p : P × U ↦ k (p.1, Φ p)) :=
    hk.comp_contMDiff (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp hΦ))
      fun p ↦ ⟨mem_univ _, (Φ p).property⟩
  -- On the open set `W = P × U`, the map is `g` composed with `(p, x) ↦ (p, ⟨x, _⟩)`.
  let W : Opens (P × M) := ⟨univ ×ˢ U, isOpen_univ.prod U.isOpen⟩
  have hψ : ContMDiff (IP.prod J) J n (fun p : W ↦ (⟨p.val.2, p.property.2⟩ : U)) :=
    fun p ↦
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := U) _ _ _).1
        ((contMDiff_snd.comp contMDiff_subtypeVal) p)
  intro p hp
  refine (contMDiffAt_subtype_iff (U := W) (x := ⟨p, hp⟩)).1 ?_ |>.contMDiffWithinAt
  exact ((hg.comp ((contMDiff_fst.comp contMDiff_subtypeVal).prodMk hψ)) ⟨p, hp⟩
    ).congr_of_eventuallyEq (Filter.Eventually.of_forall fun q ↦ dite_eq_left q.property.2)

end
