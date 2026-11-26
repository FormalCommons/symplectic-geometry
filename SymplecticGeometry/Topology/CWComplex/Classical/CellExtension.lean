/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Skeleton.Induction
public import TauCeti.Topology.Homotopy.Extension.Ball

/-!
# Extending a map over the cells of one dimension

Let `C` be a relative CW complex and `f` a map from the skeleton `skeletonLT C n` to a space `Y`.
If, for each `n`-cell, the composition of `f` with the attaching map of the cell (the restriction
of its characteristic map to the unit sphere of `Fin n → ℝ`) is null-homotopic, then `f` extends
to the next skeleton `skeletonLT C (n + 1)`. Each null-homotopic composition extends over the
closed ball (`ContinuousMap.nullhomotopic_iff_exists_extension_closedBall`), and these extensions
glue (`TauCeti.exists_continuousMap_prod_skeletonLT_succ`).

Tau Ceti's extension lemma `TauCeti.exists_extension_skeletonLT_of_nullhomotopic` asks that every
map from the sphere to `Y` be null-homotopic, in all dimensions from `n` on. The statement here
asks it only of the attaching maps of the `n`-cells composed with `f`, as is needed when `Y` has
a nontrivial homotopy group in dimension `n - 1`. Its proof adapts the private step
`TauCeti.exists_extension_skeletonLT_succ` of Tau Ceti's file
`TauCeti/Topology/CWComplex/Classical/Extension.lean`.

## Main definitions and results

* `Topology.RelCWComplex.attachingMap`: the attaching map of an `n`-cell, from the unit sphere of
  `Fin n → ℝ` to `skeletonLT C n`.
* `Topology.RelCWComplex.nullhomotopic_inclusion_comp_attachingMap`: the attaching map followed by
  the inclusion of the skeleton into the complex is null-homotopic.
* `Topology.RelCWComplex.exists_extension_skeletonLT_succ_of_nullhomotopic`: the extension over
  the closed `n`-cells.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.1, Lemma 4.7 (the
  extension lemma).
-/

public section

open Metric Set Topology

namespace Topology.RelCWComplex

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Y : Type*} [TopologicalSpace Y]

/-- The attaching map of an `n`-cell `j`: its characteristic map restricted to the unit sphere of
`Fin n → ℝ`, as a continuous map into the skeleton `skeletonLT C n`. -/
def attachingMap {n : ℕ} (j : cell C n) :
    C(sphere (0 : Fin n → ℝ) 1, skeletonLT C n) :=
  ⟨fun y ↦ ⟨map n j y, cellFrontier_subset_skeletonLT n j ⟨y, y.property, rfl⟩⟩,
    ((TauCeti.continuous_map_closedBall j).comp
      (continuous_inclusion sphere_subset_closedBall)).subtype_mk _⟩

/-- The value of `Topology.RelCWComplex.attachingMap` as a point of the skeleton. -/
lemma attachingMap_apply {n : ℕ} (j : cell C n) (y : sphere (0 : Fin n → ℝ) 1) :
    attachingMap j y = ⟨map n j y, cellFrontier_subset_skeletonLT n j ⟨y, y.property, rfl⟩⟩ :=
  (rfl)

/-- The value of `Topology.RelCWComplex.attachingMap` in the ambient space is the characteristic
map. -/
@[simp]
lemma coe_attachingMap_apply {n : ℕ} (j : cell C n) (y : sphere (0 : Fin n → ℝ) 1) :
    (attachingMap j y : X) = map n j y :=
  (rfl)

/-- The attaching map of a cell, followed by the inclusion of the skeleton into the complex, is
null-homotopic: it extends over the closed ball by the characteristic map
`TauCeti.cellMap`. -/
theorem nullhomotopic_inclusion_comp_attachingMap {n : ℕ} (j : cell C n) :
    ((ContinuousMap.inclusion (skeletonLT C n).subset_complex).comp
      (attachingMap j)).Nullhomotopic :=
  (ContinuousMap.nullhomotopic_iff_exists_extension_closedBall _).2
    ⟨TauCeti.cellMap j, fun _ ↦ Subtype.ext (TauCeti.coe_cellMap_apply j _)⟩

/-- **Extension over the closed `n`-cells.** A continuous map `f` on the skeleton
`skeletonLT C n` of a relative CW complex extends to a continuous map on `skeletonLT C (n + 1)`
when, for each `n`-cell `j`, the composition of `f` with the attaching map of `j` is
null-homotopic. -/
theorem exists_extension_skeletonLT_succ_of_nullhomotopic {n : ℕ}
    (f : C((skeletonLT C n : Set X), Y))
    (h : ∀ j : cell C n, (f.comp (attachingMap j)).Nullhomotopic) :
    ∃ F : C((skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), Y),
      ∀ (x : X) (hx : x ∈ (skeletonLT C n : Set X)),
        F ⟨x, skeletonLT_mono (by exact_mod_cast n.le_succ) hx⟩ = f ⟨x, hx⟩ := by
  let f' : C(Unit × (skeletonLT C n : Set X), Y) := f.comp ⟨Prod.snd, continuous_snd⟩
  have hext (j : cell C n) : ∃ K : C(Unit × closedBall (0 : Fin n → ℝ) 1, Y),
      ∀ z (y : closedBall (0 : Fin n → ℝ) 1) (hy : (y : Fin n → ℝ) ∈ sphere 0 1),
        K (z, y) = f' (z, ⟨map n j y, cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩⟩) := by
    -- The attaching map of `j` followed by `f` is null-homotopic, so it extends over the ball.
    obtain ⟨G, hG⟩ := (ContinuousMap.nullhomotopic_iff_exists_extension_closedBall _).1 (h j)
    exact ⟨G.comp ⟨Prod.snd, continuous_snd⟩, fun () y hy ↦ hG ⟨y, hy⟩⟩
  choose K hK using hext
  obtain ⟨F, hF, -⟩ := TauCeti.exists_continuousMap_prod_skeletonLT_succ f' K hK
  exact ⟨F.comp ⟨fun x ↦ ((), x), by fun_prop⟩, fun x hx ↦ hF () x hx⟩

end Topology.RelCWComplex

end
