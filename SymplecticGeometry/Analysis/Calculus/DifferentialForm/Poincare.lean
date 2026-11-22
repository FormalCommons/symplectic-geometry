/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Convex.Star
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.NhdsSet
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.DifferentialForm.Poincare

/-!
# Global primitives that vanish on a compact set

Let `s` be an open subset of a finite-dimensional real normed space `E`, star-convex about `x₀`,
and `K ⊆ s` a compact set, star-convex about the same point. A closed form `ω` of positive degree
on `s` that vanishes on `K` has a primitive near `K` that is defined and smooth on all of `E` and
vanishes on `K` (`StarConvex.exists_contDiff_eqOn_zero_eventually_extDeriv_eq`).

The primitive is Tau Ceti's Poincaré homotopy operator `TauCeti.poincareHomotopy x₀ ω`, multiplied
by a smooth cutoff that is `1` near `K` and supported in `s`. It vanishes on `K` because every
segment from `x₀` to a point of `K` lies in `K`, where `ω` vanishes.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §4 (the
  Poincaré lemma).
-/

public section

open Filter Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {n : ℕ}

namespace StarConvex

/-- Let `s` be open and star-convex about `x₀`, and `K ⊆ s` compact and star-convex about `x₀`.
A `C^r` form `ω` of degree `n + 1` on `s`, with `1 ≤ r`, that is closed on `s` and vanishes on
`K` has a primitive near `K` that vanishes on `K`: a form `α`, `C^r` on all of `E`, with `α = 0`
on `K` and `d α = ω` near `K`. -/
theorem exists_contDiff_eqOn_zero_eventually_extDeriv_eq {x₀ : E} {s K : Set E}
    (hs : StarConvex ℝ x₀ s) (hso : IsOpen s) (hK : IsCompact K) (hKs : K ⊆ s)
    (hKx₀ : StarConvex ℝ x₀ K) {r : ℕ∞} (hr : 1 ≤ r) {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (hω : ContDiffOn ℝ r ω s) (hclosed : ∀ y ∈ s, extDeriv ω y = 0) (hωK : EqOn ω 0 K) :
    ∃ α : E → E [⋀^Fin n]→L[ℝ] F, ContDiff ℝ r α ∧ EqOn α 0 K ∧
      ∀ᶠ x in 𝓝ˢ K, extDeriv α x = ω x := by
  set β := TauCeti.poincareHomotopy x₀ ω with hβ
  have hβK : EqOn β 0 K := fun x hx ↦ by
    rw [hβ, TauCeti.poincareHomotopy_congr (ω₂ := 0) fun y hy ↦ hωK (hKx₀.segment_subset hx hy),
      TauCeti.poincareHomotopy_zero, Pi.zero_apply]
  obtain ⟨χ, hχ, -, hχK, -, hχs⟩ := hK.exists_contDiff_cutoff hso hKs
  refine ⟨fun x ↦ χ x • β x,
    (hs.contDiffOn_poincareHomotopy hso hω).contDiff_smul_of_tsupport_subset hso
      (hχ.of_le (by exact_mod_cast le_top)).contDiffOn hχs,
    fun x hx ↦ by simp [hβK hx], eventually_nhdsSet_iff_forall.2 fun x hx ↦ ?_⟩
  filter_upwards [isOpen_interior.mem_nhds (hχK hx), hso.mem_nhds (hKs hx)] with y hy hys
  have hαβ : (fun x ↦ χ x • β x) =ᶠ[𝓝 y] β := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    rw [interior_subset hz, one_smul]
  rw [hαβ.extDeriv_eq,
    hs.extDeriv_poincareHomotopy hso (hω.of_le (by exact_mod_cast hr)) hclosed hys]

end StarConvex

end
