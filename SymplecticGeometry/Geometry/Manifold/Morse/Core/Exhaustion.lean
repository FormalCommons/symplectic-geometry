/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.Core.Basic
public import TauCeti.Geometry.Manifold.Morse.Basic
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Geometry.Manifold.Morse.Core.Compression
import SymplecticGeometry.Geometry.Manifold.Morse.OpenManifold
import SymplecticGeometry.Order.Filter.AtTopBot.Archimedean

/-!
# The band cores of an open manifold

Let `M` be a boundaryless Hausdorff σ-compact manifold of finite dimension other than one, none
of whose connected components is compact. Then `M` carries a smooth proper Morse function `g`
and levels `d 0 < e 0 < d 1 < e 1 < ⋯` tending to `+∞`, with `g > e 0` everywhere, such that
for every `k` the function `g` has a band core for the levels `d k`, `e k`, `e (k + 1)`
(`SymplecticGeometry.exists_isMorse_bandCore_seq`).

The function `g` is `TauCeti.exists_isMorse_isProperMap_manifoldMorseIndex_lt`: proper, bounded
below by some `m`, with all its critical points of index less than the dimension. Its critical
values below each level are finitely many, so together with `m - 1` and `m - 2` they lie in the
range of a strictly increasing sequence `v` tending to `+∞`, with `v 0 = m - 2` and
`v 1 = m - 1` (`exists_strictMono_tendsto_atTop_subset_range`). The levels `d k` and `e k`
are the points at one third and two thirds of the way from `v k` to `v (k + 1)`. Then the only
value of `v` in `[d k, e (k + 1)]` is `v (k + 1)`, which lies in `(e k, e (k + 1))`, so every
critical point of `g` in `g⁻¹[d k, e (k + 1)]` lies on the level `v (k + 1)`, and
`TauCeti.IsMorse.exists_bandCore` gives the band core.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3.
* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open Filter Set
open scoped ContDiff Manifold

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- **The band cores of an open manifold.** On a boundaryless Hausdorff σ-compact manifold of
finite dimension other than one, none of whose connected components is compact, there are a
smooth proper Morse function `g` and levels `d k < e k < d (k + 1)`, with `d k` tending to `+∞`
and `g > e 0` everywhere, such that `g` has a band core for the levels `d k`, `e k`, `e (k + 1)`
for every `k`. -/
theorem exists_isMorse_bandCore_seq (hE : Module.finrank ℝ E ≠ 1)
    (hM : ∀ x : M, ¬ IsCompact (connectedComponent x)) :
    ∃ (g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (d e : ℕ → ℝ), TauCeti.IsMorse I g ∧ IsProperMap g ∧
      (∀ x, e 0 < g x) ∧ (∀ k, d k < e k ∧ e k < d (k + 1)) ∧
      Tendsto d atTop atTop ∧ ∀ k, Nonempty (BandCore I g (d k) (e k) (e (k + 1))) := by
  obtain ⟨g, hg, hp, ⟨m, hm⟩, hind⟩ :=
    TauCeti.exists_isMorse_isProperMap_manifoldMorseIndex_lt (I := I) hE hM
  have hm' (x : M) : m ≤ g x := hm (mem_range_self x)
  -- The critical values below each level are finitely many, and lie above `m - 1`.
  have hfin (r : ℝ) : (g '' TauCeti.criticalPoints I g ∩ Iic r).Finite := by
    rw [← image_inter_preimage]
    exact (hg.finite_criticalPoints_inter_preimage_Iic hp ⟨m, hm⟩ r).image g
  obtain ⟨u, hu, hutop, hu0, hcrit⟩ := exists_strictMono_tendsto_atTop_subset_range hfin
    (a := m - 1) (by rintro _ ⟨x, -, rfl⟩; linarith [hm' x])
  -- The sequence `v` is `u` preceded by `m - 2`.
  set v : ℕ → ℝ := fun k ↦ Nat.casesOn k (m - 2) u
  have hv0 : v 0 = m - 2 := rfl
  have hvs (k : ℕ) : v (k + 1) = u k := rfl
  have hvm : StrictMono v := strictMono_nat_of_lt_succ fun k ↦ by
    cases k with
    | zero => rw [hv0, hvs, hu0]; linarith
    | succ k => rw [hvs, hvs]; exact hu k.lt_succ_self
  have hvtop : Tendsto v atTop atTop := (tendsto_add_atTop_iff_nat 1).1 hutop
  refine ⟨g, fun k ↦ v k + (v (k + 1) - v k) / 3, fun k ↦ v k + 2 * (v (k + 1) - v k) / 3, hg,
    hp, fun x ↦ ?_, fun k ↦ ?_, ?_, fun k ↦ ?_⟩
  · have := hm' x
    beta_reduce
    rw [hv0, hvs, hu0]
    linarith
  · have h1 := hvm k.lt_succ_self
    have h2 := hvm (k + 1).lt_succ_self
    constructor <;> linarith
  · refine tendsto_atTop_mono (fun k ↦ ?_) hvtop
    linarith [hvm k.lt_succ_self]
  -- The only value of `v` in `[d k, e (k + 1)]` is `v (k + 1)`.
  have h1 := hvm k.lt_succ_self
  have h2 := hvm (k + 1).lt_succ_self
  refine TauCeti.IsMorse.exists_bandCore hg hp ⟨m, hm⟩ (v := v (k + 1)) (by linarith)
    (by linarith) (by linarith) fun x hx hdx hxe ↦ ⟨?_, hind x hx⟩
  obtain ⟨j, hj⟩ := hcrit ⟨x, hx, rfl⟩
  rw [← hvs] at hj
  have hkj : k < j + 1 := hvm.lt_iff_lt.1 (by linarith)
  have hjk : j + 1 < k + 2 := hvm.lt_iff_lt.1 (by linarith)
  rw [← hj, show j + 1 = k + 1 by omega]

end SymplecticGeometry

end
