/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smooth maps and open subsets

A map `f : M → N` is `C^n` on an open subset `U` of `M` exactly when its restriction to `U`, read
as a manifold, is `C^n` (`contMDiff_subtype_iff`). A map into `N` that is `C^n` at a point `x`
and sends `x` into an open subset `W` of `N` lifts, near `x`, to a map into `W` that is `C^n` at
`x` (`ContMDiffAt.exists_subtypeVal_comp_eventuallyEq`).

Let `U` be an open subset of a manifold `M` and `n` a smoothness order. Let `g : P × U → N`
be a map that is `C^n` at `(p, x)`, and `f : P × M → N` a map that agrees with it on `P × U`.
Then `f` is `C^n` at `(p, x)` (`ContMDiffAt.prod_opens_of_eq`): on the open subset `P × U` of
`P × M`, read as a manifold, `f` is `g` composed with `(p', x') ↦ (p', ⟨x', _⟩)`. The same holds
with the factors swapped, on `U × P` (`ContMDiffAt.opens_prod_of_eq`). So a map that agrees on
`P × U` with a `C^n` map on `P × U` is `C^n` on `P × U`
(`ContMDiff.contMDiffOn_prod_opens_of_eq`), and likewise on `U × P`
(`ContMDiff.contMDiffOn_opens_prod_of_eq`).

As a consequence, for a `C^n` map `Φ : P × U → U` and a map `k : P × M → N` that is `C^n` on
`P × U`, the map equal to `(p, x) ↦ k (p, Φ (p, x))` on `P × U` and to `k` elsewhere is `C^n` on
`P × U` (`ContMDiffOn.dite_comp_of_opens`). The case used in the library is that of a diffeotopy
`Φ` of `U`, with `P = [0, 1]` and `n = ∞`.

## Main results

* `contMDiff_subtype_iff`: a map is `C^n` on an open subset exactly when its restriction to that
  subset is `C^n`.
* `ContMDiffAt.exists_subtypeVal_comp_eventuallyEq`: a map that is `C^n` at a point and sends it
  into an open subset lifts, near that point, to a map into that subset that is `C^n` there.
* `ContMDiffAt.prod_opens_of_eq`: a map that agrees on `P × U` with a map on `P × U` that is
  `C^n` at a point is `C^n` at that point.
* `ContMDiffAt.opens_prod_of_eq`: the same on `U × P`.
* `ContMDiff.contMDiffOn_prod_opens_of_eq`: a map that agrees on `P × U` with a `C^n` map on
  `P × U` is `C^n` on `P × U`.
* `ContMDiff.contMDiffOn_opens_prod_of_eq`: the same on `U × P`.
* `ContMDiffOn.dite_comp_of_opens`: the map above, built from `Φ` and `k`, is `C^n` on `P × U`.
-/

public section

open Set TopologicalSpace Filter Topology
open scoped Manifold

section Restrict

variable {𝕜 E H M E' H' N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Let `U` be an open subset of `M`. The restriction to `U` of a map `f : M → N`, as a map on the
manifold `U`, is `C^n` if and only if `f` is `C^n` on `U`. -/
theorem contMDiff_subtype_iff {n : WithTop ℕ∞} {U : Opens M} {f : M → N} :
    ContMDiff I I' n (fun x : U ↦ f x) ↔ ContMDiffOn I I' n f U :=
  ⟨fun h x hx ↦ (contMDiffAt_subtype_iff (x := ⟨x, hx⟩)).1 (h _) |>.contMDiffWithinAt,
    fun h x ↦ contMDiffAt_subtype_iff.2 <|
      (h x x.property).contMDiffAt (U.isOpen.mem_nhds x.property)⟩

/-- Let `f : M → N` be `C^n` at `x`, with `f x` in an open subset `W` of `N`. Then `f` lifts to
`W` near `x`: there is a map `g : M → W` that is `C^n` at `x` and agrees with `f`, read in `N`,
on a neighbourhood of `x`. -/
theorem ContMDiffAt.exists_subtypeVal_comp_eventuallyEq {n : WithTop ℕ∞} {f : M → N} {x : M}
    (hf : ContMDiffAt I I' n f x) {W : Opens N} (hx : f x ∈ W) :
    ∃ g : M → W, ContMDiffAt I I' n g x ∧ Subtype.val ∘ g =ᶠ[𝓝 x] f := by
  classical
  -- Take `f y` where it lies in `W`, and `f x` elsewhere.
  let g : M → W := fun y ↦ if h : f y ∈ W then ⟨f y, h⟩ else ⟨f x, hx⟩
  have hg : Subtype.val ∘ g =ᶠ[𝓝 x] f :=
    mem_of_superset (hf.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds hx)) fun y hy ↦ by
      simp [g, dite_eq_left (show f y ∈ W from hy)]
  exact ⟨g, (TauCeti.ContMDiffAt.subtypeVal_comp_iff W g x).1 (hf.congr_of_eventuallyEq hg), hg⟩

end Restrict

variable {EP HP P E H M E' H' N : Type*}
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  [TopologicalSpace P] [ChartedSpace HP P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Let `U` be an open subset of `M` and `g : P × U → N` a map that is `C^n` at `(p, x)`. A map
`f : P × M → N` with `f (p', x') = g (p', ⟨x', _⟩)` for every `p'` and every `x' ∈ U` is `C^n`
at `(p, x)`. -/
theorem ContMDiffAt.prod_opens_of_eq {n : WithTop ℕ∞} {U : Opens M} {g : P × U → N} {p : P}
    {x : U} (hg : ContMDiffAt (IP.prod J) I' n g (p, x)) {f : P × M → N}
    (hfg : ∀ (p' : P) (x' : M) (hx : x' ∈ U), f (p', x') = g (p', ⟨x', hx⟩)) :
    ContMDiffAt (IP.prod J) I' n f (p, (x : M)) := by
  -- On the open set `W = P × U`, `f` is `g` composed with `(p', x') ↦ (p', ⟨x', _⟩)`.
  let W : Opens (P × M) := ⟨univ ×ˢ U, isOpen_univ.prod U.isOpen⟩
  have hψ : ContMDiff (IP.prod J) J n (fun q : W ↦ (⟨q.val.2, q.property.2⟩ : U)) :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff U _).1 (contMDiff_snd.comp contMDiff_subtypeVal)
  let w : W := ⟨(p, (x : M)), mem_univ p, x.property⟩
  refine (contMDiffAt_subtype_iff (U := W) (x := w)).1 ?_
  exact (ContMDiffAt.comp w hg ((contMDiff_fst.comp contMDiff_subtypeVal w).prodMk (hψ w)))
    |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q ↦ hfg _ _ q.property.2)

/-- Let `U` be an open subset of `M` and `g : U × P → N` a map that is `C^n` at `(x, p)`. A map
`f : M × P → N` with `f (x', p') = g (⟨x', _⟩, p')` for every `x' ∈ U` and every `p'` is `C^n`
at `(x, p)`. -/
theorem ContMDiffAt.opens_prod_of_eq {n : WithTop ℕ∞} {U : Opens M} {g : U × P → N} {x : U}
    {p : P} (hg : ContMDiffAt (J.prod IP) I' n g (x, p)) {f : M × P → N}
    (hfg : ∀ (x' : M) (hx : x' ∈ U) (p' : P), f (x', p') = g (⟨x', hx⟩, p')) :
    ContMDiffAt (J.prod IP) I' n f ((x : M), p) := by
  -- Swap the factors, and apply `ContMDiffAt.prod_opens_of_eq`.
  have h := ContMDiffAt.prod_opens_of_eq (g := fun q ↦ g (q.2, q.1))
    (f := fun q ↦ f (q.2, q.1)) (ContMDiffAt.comp (p, x) hg
      (contMDiff_snd.prodMk contMDiff_fst (p, x))) fun p' x' hx ↦ hfg x' hx p'
  exact ContMDiffAt.comp (f := fun q : M × P ↦ (q.2, q.1)) ((x : M), p) h
    (contMDiff_snd.prodMk contMDiff_fst _)

/-- Let `U` be an open subset of `M` and `g : P × U → N` a `C^n` map. A map `f : P × M → N` with
`f (p, x) = g (p, ⟨x, _⟩)` for every `p` and every `x ∈ U` is `C^n` on `P × U`. -/
theorem ContMDiff.contMDiffOn_prod_opens_of_eq {n : WithTop ℕ∞} {U : Opens M} {g : P × U → N}
    (hg : ContMDiff (IP.prod J) I' n g) {f : P × M → N}
    (hfg : ∀ (p : P) (x : M) (hx : x ∈ U), f (p, x) = g (p, ⟨x, hx⟩)) :
    ContMDiffOn (IP.prod J) I' n f (univ ×ˢ U) := fun q hq ↦
  ((hg (q.1, ⟨q.2, hq.2⟩)).prod_opens_of_eq hfg).contMDiffWithinAt

/-- Let `U` be an open subset of `M` and `g : U × P → N` a `C^n` map. A map `f : M × P → N` with
`f (x, p) = g (⟨x, _⟩, p)` for every `x ∈ U` and every `p` is `C^n` on `U × P`. -/
theorem ContMDiff.contMDiffOn_opens_prod_of_eq {n : WithTop ℕ∞} {U : Opens M} {g : U × P → N}
    (hg : ContMDiff (J.prod IP) I' n g) {f : M × P → N}
    (hfg : ∀ (x : M) (hx : x ∈ U) (p : P), f (x, p) = g (⟨x, hx⟩, p)) :
    ContMDiffOn (J.prod IP) I' n f (U ×ˢ univ) := fun q hq ↦
  ((hg (⟨q.1, hq.1⟩, q.2)).opens_prod_of_eq hfg).contMDiffWithinAt

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
