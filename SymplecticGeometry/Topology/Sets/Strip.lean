/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Normed.Group.Real
import TauCeti.Topology.Compactness.Normed

/-!
# Symmetric strips in a product with the real line

For a topological space `X` and `ε : ℝ`, `SymplecticGeometry.symmStrip X ε` is the open set
`(-ε, ε) × X` of `ℝ × X`, that is, the points `(r, x)` with `|r| < ε`. Such strips are the
domains of collars and of normal forms near the slice `{0} × X`. When `X` is compact, every open
set containing `{0} × X` contains a strip of positive width
(`SymplecticGeometry.exists_symmStrip_le`), by the tube lemma.

## Main definitions

* `SymplecticGeometry.symmStrip X ε`: the open set `Ioo (-ε) ε ×ˢ univ` of `ℝ × X`.
* `SymplecticGeometry.symmStripMk`: the point `(r, x)` of the strip, for `|r| < ε`.

## Main results

* `SymplecticGeometry.mem_symmStrip_iff`: `(r, x)` lies in the strip of width `ε` exactly when
  `|r| < ε`.
* `SymplecticGeometry.exists_symmStrip_le`: for compact `X`, an open neighbourhood of
  `{0} × X` contains a strip of positive width.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000, Lemma 26.8 (the tube lemma)
-/

public section

open Set TopologicalSpace

namespace SymplecticGeometry

variable (X : Type*) [TopologicalSpace X]

/-- The **symmetric strip** of width `ε` in `ℝ × X`: the open set `(-ε, ε) × X`. -/
def symmStrip (ε : ℝ) : Opens (ℝ × X) :=
  ⟨Ioo (-ε) ε ×ˢ univ, isOpen_Ioo.prod isOpen_univ⟩

variable {X}

@[simp]
theorem coe_symmStrip (ε : ℝ) : (symmStrip X ε : Set (ℝ × X)) = Ioo (-ε) ε ×ˢ univ :=
  (rfl)

/-- A point `(r, x)` lies in the symmetric strip of width `ε` exactly when `|r| < ε`. -/
@[simp]
theorem mem_symmStrip_iff {ε : ℝ} {p : ℝ × X} : p ∈ symmStrip X ε ↔ |p.1| < ε := by
  rw [← SetLike.mem_coe, coe_symmStrip, mem_prod, mem_Ioo, abs_lt]
  simp

/-- The point `(r, x)` of the symmetric strip of width `ε`, for `|r| < ε`. As a map of `x`, it is
the inclusion of the slice `{r} × X` into the strip. -/
def symmStripMk {ε r : ℝ} (hr : |r| < ε) (x : X) : symmStrip X ε :=
  ⟨(r, x), mem_symmStrip_iff.2 hr⟩

@[simp]
theorem coe_symmStripMk {ε r : ℝ} (hr : |r| < ε) (x : X) :
    (symmStripMk hr x : ℝ × X) = (r, x) :=
  (rfl)

/-- Followed by the inclusion of the strip, the slice map at `r` is `x ↦ (r, x)`. -/
theorem val_comp_symmStripMk {ε r : ℝ} (hr : |r| < ε) :
    Subtype.val ∘ symmStripMk (X := X) hr = Prod.mk r :=
  (rfl)

/-- The slice map of a symmetric strip is continuous. -/
theorem continuous_symmStripMk {ε r : ℝ} (hr : |r| < ε) : Continuous (symmStripMk (X := X) hr) :=
  (continuous_const.prodMk continuous_id).subtype_mk _

/-- Symmetric strips grow with their width. -/
theorem symmStrip_mono {ε δ : ℝ} (h : ε ≤ δ) : symmStrip X ε ≤ symmStrip X δ := fun _ hp ↦
  mem_symmStrip_iff.2 ((mem_symmStrip_iff.1 hp).trans_le h)

/-- The slice `{0} × X` lies in every symmetric strip of positive width. -/
theorem zero_mk_mem_symmStrip {ε : ℝ} (hε : 0 < ε) (x : X) : ((0 : ℝ), x) ∈ symmStrip X ε :=
  mem_symmStrip_iff.2 (by simpa using hε)

/-- **Tube lemma for symmetric strips.** For compact `X`, an open set of `ℝ × X` containing the
slice `{0} × X` contains the symmetric strip of some positive width. -/
theorem exists_symmStrip_le [CompactSpace X] {U : Opens (ℝ × X)}
    (hU : ∀ x : X, ((0 : ℝ), x) ∈ U) : ∃ ε > 0, symmStrip X ε ≤ U := by
  obtain ⟨ε, hε, hball⟩ := isCompact_univ.exists_pos_forall_norm_lt (H := ℝ)
    (Q := fun r x ↦ (r, x) ∈ U) fun x _ ↦ U.isOpen.mem_nhds (hU x)
  refine ⟨ε, hε, fun p hp ↦ hball ?_ p.2 (mem_univ _)⟩
  rw [Real.norm_eq_abs]
  exact mem_symmStrip_iff.1 hp

end SymplecticGeometry

end
