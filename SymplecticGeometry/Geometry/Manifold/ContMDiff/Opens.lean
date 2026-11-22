/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Smooth maps and open subsets

Let `U` be an open subset of a manifold `M` and `n` a smoothness order. A map `f : P × M → N` that
agrees on `P × U` with a `C^n` map `g : P × U → N` is `C^n` on `P × U`
(`ContMDiff.contMDiffOn_prod_opens_of_eq`): on the open subset `P × U` of `P × M`, read as a
manifold, `f` is `g` composed with `(p, x) ↦ (p, ⟨x, _⟩)`.

As a consequence, for a `C^n` map `Φ : P × U → U` and a map `k : P × M → N` that is `C^n` on
`P × U`, the map equal to `(p, x) ↦ k (p, Φ (p, x))` on `P × U` and to `k` elsewhere is `C^n` on
`P × U` (`ContMDiffOn.dite_comp_of_opens`). The case used in the library is that of a diffeotopy
`Φ` of `U`, with `P = [0, 1]` and `n = ∞`.

## Main results

* `ContMDiff.contMDiffOn_prod_opens_of_eq`: a map that agrees on `P × U` with a `C^n` map on
  `P × U` is `C^n` on `P × U`.
* `ContMDiffOn.dite_comp_of_opens`: the map above, built from `Φ` and `k`, is `C^n` on `P × U`.
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

/-- Let `U` be an open subset of `M` and `g : P × U → N` a `C^n` map. A map `f : P × M → N` with
`f (p, x) = g (p, ⟨x, _⟩)` for every `p` and every `x ∈ U` is `C^n` on `P × U`. -/
theorem ContMDiff.contMDiffOn_prod_opens_of_eq {n : WithTop ℕ∞} {U : Opens M} {g : P × U → N}
    (hg : ContMDiff (IP.prod J) I' n g) {f : P × M → N}
    (hfg : ∀ (p : P) (x : M) (hx : x ∈ U), f (p, x) = g (p, ⟨x, hx⟩)) :
    ContMDiffOn (IP.prod J) I' n f (univ ×ˢ U) := by
  -- On the open set `W = P × U`, `f` is `g` composed with `(p, x) ↦ (p, ⟨x, _⟩)`.
  let W : Opens (P × M) := ⟨univ ×ˢ U, isOpen_univ.prod U.isOpen⟩
  have hψ : ContMDiff (IP.prod J) J n (fun p : W ↦ (⟨p.val.2, p.property.2⟩ : U)) :=
    fun p ↦
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := U) _ _ _).1
        ((contMDiff_snd.comp contMDiff_subtypeVal) p)
  intro p hp
  refine (contMDiffAt_subtype_iff (U := W) (x := ⟨p, hp⟩)).1 ?_ |>.contMDiffWithinAt
  exact ((hg.comp ((contMDiff_fst.comp contMDiff_subtypeVal).prodMk hψ)) ⟨p, hp⟩
    ).congr_of_eventuallyEq (Filter.Eventually.of_forall fun q ↦ hfg (q : P × M).1 _ q.property.2)

open Classical in
/-- Let `U` be an open subset of `M`, `Φ : P × U → U` a `C^n` map, and `k : P × M → N` a map that
is `C^n` on `P × U`. The map equal to `(p, x) ↦ k (p, Φ (p, x))` on `P × U` and to `k` elsewhere
is `C^n` on `P × U`. -/
theorem ContMDiffOn.dite_comp_of_opens {n : WithTop ℕ∞} {U : Opens M} {Φ : P × U → U}
    (hΦ : ContMDiff (IP.prod J) J n Φ) {k : P × M → N}
    (hk : ContMDiffOn (IP.prod J) I' n k (univ ×ˢ U)) :
    ContMDiffOn (IP.prod J) I' n
      (fun p ↦ if h : p.2 ∈ U then k (p.1, Φ (p.1, ⟨p.2, h⟩)) else k p) (univ ×ˢ U) :=
  ContMDiff.contMDiffOn_prod_opens_of_eq
    (hk.comp_contMDiff (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp hΦ))
      fun p ↦ ⟨mem_univ _, (Φ p).property⟩) fun _ _ hx ↦ dite_eq_left hx

end
