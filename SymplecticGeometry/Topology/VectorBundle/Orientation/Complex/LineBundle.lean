/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.LineBundle
public import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars
public import TauCeti.Topology.VectorBundle.Orientation.Complex.Basic
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars

/-!
# The canonical orientation of a complex line bundle read through a nonzero vector

Let `L` be a complex vector bundle of rank one. A nonzero vector `v` of a fibre `L x` gives the
complex-linear equivalence `c ↦ c • v` from `ℂ` onto `L x` (`VectorBundle.toSpanSingletonEquiv`).
Being complex-linear, it carries `Complex.orientation` to the canonical orientation of `L x` as a
complex vector space (`TauCeti.VectorBundleOrientation.map_toSpanSingletonEquiv`). A nowhere-zero
section of `L` over a set is thus an oriented frame of `L` there, for the orientation of `L` as a
complex line.

## Main results

* `TauCeti.VectorBundleOrientation.map_toSpanSingletonEquiv`: the map `c ↦ c • v` carries the
  orientation of `ℂ` to the canonical orientation of the fibre.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the canonical orientation of a complex vector bundle).
-/

public section

noncomputable section

open Bundle Module

namespace TauCeti.VectorBundleOrientation

variable {B : Type*} [TopologicalSpace B]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [FiniteDimensional ℂ G]
  {L : B → Type*} [TopologicalSpace (TotalSpace G L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℝ (L x)] [∀ x, Module ℂ (L x)] [∀ x, IsScalarTower ℝ ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle G L] [VectorBundle ℂ G L]

open scoped VectorBundle.ComplexToReal

/-- In a complex line bundle `L`, the map `c ↦ c • v` from `ℂ` onto the fibre `L x` containing a
nonzero vector `v` carries `Complex.orientation` to the canonical orientation of `L x` as a
complex vector space, indexed by `Fin 2`. -/
theorem map_toSpanSingletonEquiv (hG : finrank ℂ G = 1) {x : B} (v : L x) (hv : v ≠ 0) :
    Orientation.map (Fin 2)
        ((VectorBundle.toSpanSingletonEquiv G hG v hv).restrictScalars' ℝ).toLinearEquiv
        Complex.orientation =
      reindex (finCongr (by rw [hG])) (complex G L) x := by
  have h := map_complex (F := G) (E := L) (F' := ℂ) (E' := Bundle.Trivial B ℂ) (b' := x) (b := x)
    (VectorBundle.toSpanSingletonEquiv G hG v hv).toLinearEquiv
  rw [complex_trivial, trivial_apply] at h
  rw [← reindex_complexOrientation_complex, ContinuousLinearEquiv.restrictScalars'_toLinearEquiv,
    Orientation.map_reindex, h, reindex_apply, Orientation.reindex_finCongr_reindex_finCongr]

end TauCeti.VectorBundleOrientation
