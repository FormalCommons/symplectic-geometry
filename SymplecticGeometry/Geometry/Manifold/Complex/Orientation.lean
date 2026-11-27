/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Orientation.Complex
public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.Orientation.Sign
public import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.RestrictScalars

/-!
# The canonical orientation of a complex manifold, reindexed

Tau Ceti's `TauCeti.complexManifoldOrientation E M` orients a complex manifold `M` modelled on
`𝓘(ℂ, E)` as a real manifold, with index type `Fin (2 * finrank ℂ E)`. Statements about real
manifolds often use another index type, such as `Fin (n + 1)` for the real dimension `n + 1`.
For any reindexing:

* `TauCeti.orientationAt_reindex_complexManifoldOrientation`: at every point, the reindexed
  orientation is the complex orientation `TauCeti.complexOrientation E` of the model, reindexed;
* `TauCeti.map_orientationAt_reindex_complexManifoldOrientation`: a complex-linear isomorphism
  `E ≃L[ℂ] G` carries it to the complex orientation of `G`, reindexed.

For a real-differentiable map `f : M → N` of complex manifolds,
`TauCeti.orientationSign_complexManifoldOrientation_eq_comp_chart` computes its orientation
sign for the complex orientations in holomorphic charts `e` at `x` and `e'` at `f x`, as that of
`e' ∘ f ∘ e.symm` for the complex orientation of the model.

For a complex curve,
`finrank ℂ E = 1`, statements about real surfaces use the index type `Fin 2` instead. This file
reindexes the canonical orientation once, for every such `E` and `M`:

* `SymplecticGeometry.complexCurveOrientation`: the canonical orientation of a complex curve,
  indexed by `Fin 2`, with `SymplecticGeometry.complexCurveOrientation_def`;
* `SymplecticGeometry.orientationAt_complexCurveOrientation`: at every point it is Tau Ceti's
  complex orientation `TauCeti.complexOrientation E` of the model, reindexed to `Fin 2`;
* `SymplecticGeometry.complexCurveOrientation_complex`: on `ℂ` itself it is the standard
  orientation `TauCeti.Manifold.Orientation.complex`;
* `Diffeomorph.isOrientationPreservingAt_complexCurveOrientation`: biholomorphisms preserve it.

More generally, for complex dimension `finrank ℂ E = r + 1`, statements about real manifolds of
dimension `2 r + 2` use the index type `Fin (2 * r + 1 + 1)`, and the real dimension
`finrank ℝ E = 2 * r + 1 + 1` (`finrank_real_of_finrank_complex_eq_add_one`, in
`SymplecticGeometry/LinearAlgebra/Complex/Finrank.lean`):

* `SymplecticGeometry.complexManifoldOrientationOfFinrank`: the canonical orientation, indexed by
  `Fin (2 * r + 1 + 1)`, with `SymplecticGeometry.complexManifoldOrientationOfFinrank_def`;
* `SymplecticGeometry.orientationAt_complexManifoldOrientationOfFinrank`: at every point it is the
  complex orientation `TauCeti.complexOrientation E` of the model, reindexed;
* `SymplecticGeometry.map_orientationAt_complexManifoldOrientationOfFinrank`: a complex-linear
  isomorphism `E ≃L[ℂ] G` carries it to the complex orientation of `G`, reindexed;
* `SymplecticGeometry.complexCurveOrientation_eq_complexManifoldOrientationOfFinrank`: its case
  `r = 0` is `SymplecticGeometry.complexCurveOrientation`.

Tau Ceti's `TauCeti.complexHomologicalOrientation` (in
`TauCeti/Geometry/Manifold/Complex/FundamentalClass.lean`) reindexes the same orientation to
`Fin 2` for Riemann surfaces modelled on `ℂ`, as a homological orientation.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §3 (orienting a
  manifold by an atlas whose transition maps have positive Jacobian determinant).
* D. Huybrechts, *Complex Geometry: An Introduction*, §1.2 (a complex vector space is oriented
  as a real vector space, and complex linear isomorphisms preserve that orientation).
-/

public section

open Module TauCeti
open scoped Manifold ContDiff TauCeti.ComplexManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]

namespace TauCeti

/-- At every point, a reindexing of the complex orientation of `M` is the complex orientation of
the model space `E`, reindexed in the same way. -/
theorem orientationAt_reindex_complexManifoldOrientation {ι : Type*} [Fintype ι]
    (e : Fin (2 * finrank ℂ E) ≃ ι) (x : M) :
    ((complexManifoldOrientation E M).reindex e).orientationAt x =
      Orientation.reindex ℝ (TangentSpace 𝓘(ℝ, E) x) e (complexOrientation E) := by
  rw [Manifold.Orientation.orientationAt_reindex,
    orientationAt_complexManifoldOrientation_eq_complexOrientation]

/-- A complex-linear isomorphism `A : E ≃L[ℂ] G` carries the tangent orientation at any point of
the complex orientation of `M`, reindexed to `Fin m`, to the complex orientation of `G`,
reindexed to `Fin m`. -/
theorem map_orientationAt_reindex_complexManifoldOrientation
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
    [FiniteDimensional ℂ G] {m : ℕ} (h : 2 * finrank ℂ E = m) (h' : 2 * finrank ℂ G = m)
    (A : E ≃L[ℂ] G) (z : M) :
    (((complexManifoldOrientation E M).reindex (finCongr h)).orientationAt z).map (Fin m)
        (A.restrictScalars' ℝ).toLinearEquiv =
      Orientation.reindex ℝ G (finCongr h') (complexOrientation G) := by
  -- The same statement, with the tangent space at `z` read as `E` (its definition), as
  -- `Orientation.map` reads it here and as `Orientation.map_reindex` needs.
  have hoz : (((complexManifoldOrientation E M).reindex (finCongr h)).orientationAt z :
      Orientation ℝ E (Fin m)) = Orientation.reindex ℝ E (finCongr h) (complexOrientation E) :=
    orientationAt_reindex_complexManifoldOrientation (finCongr h) z
  refine (congrArg (Orientation.map (Fin m) (A.restrictScalars' ℝ).toLinearEquiv) hoz).trans
    ?_
  rw [Orientation.map_reindex, ContinuousLinearEquiv.restrictScalars'_toLinearEquiv,
    LinearEquiv.map_complexOrientation, ← Orientation.reindex_trans]
  exact congrArg (Orientation.reindex ℝ G · (complexOrientation G)) (Equiv.ext fun _ ↦ by simp)

/-- The orientation sign of a real-differentiable map `f : M → N` of complex manifolds at `x`, for
their complex orientations, is that of its expression `e' ∘ f ∘ e.symm` in charts at `e x`, for
the complex orientation of `E`, when `e` and `e'` are charts of the maximal holomorphic atlases
of `M` and `N` at `x` and `f x`. -/
theorem orientationSign_complexManifoldOrientation_eq_comp_chart
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℂ, E) 1 N]
    {f : M → N} {x : M} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) f x)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 1 M)
    (hx : x ∈ e.source) {e' : OpenPartialHomeomorph N E}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) 1 N) (hfx : f x ∈ e'.source) :
    Manifold.Orientation.orientationSign (complexManifoldOrientation E M)
        (complexManifoldOrientation E N) f x =
      Manifold.Orientation.orientationSign (complexManifoldOrientation E E)
        (complexManifoldOrientation E E) (e' ∘ f ∘ e.symm) (e x) := by
  -- The charts are local biholomorphisms, so they preserve the complex orientations.
  have he₁ := e.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas he (e.map_source hx)
  have he₂ := e'.isLocalDiffeomorphAt_of_mem_maximalAtlas he' hfx
  rw [← Function.comp_assoc, (he₁.restrictScalars ℝ).orientationSign_comp one_ne_zero _
      (complexManifoldOrientation E M),
    Manifold.Orientation.orientationSign_of_isOrientationPreservingAt
      (he₁.isOrientationPreservingAt_complexManifoldOrientation 1), mul_one, e.left_inv hx,
    Manifold.Orientation.orientationSign_comp ((he₂.restrictScalars ℝ).mdifferentiableAt
      one_ne_zero) hf (o' := complexManifoldOrientation E N),
    Manifold.Orientation.orientationSign_of_isOrientationPreservingAt
      (he₂.isOrientationPreservingAt_complexManifoldOrientation 1), one_mul]

end TauCeti

namespace SymplecticGeometry

variable (E M) in
/-- The canonical orientation of a complex curve `M`, a complex manifold modelled on `𝓘(ℂ, E)`
with `finrank ℂ E = 1`, as an orientation of the underlying real surface indexed by `Fin 2`: Tau
Ceti's `complexManifoldOrientation E M`, reindexed from `Fin (2 * finrank ℂ E)`. When `h` is
omitted, `simp` proves it, as it does for `ℂ` and `Fin 1 → ℂ`. -/
noncomputable def complexCurveOrientation (h : finrank ℂ E = 1 := by simp) :
    Manifold.Orientation 𝓘(ℝ, E) M (Fin 2) :=
  (complexManifoldOrientation E M).reindex (finCongr (by rw [h]))

theorem complexCurveOrientation_def (h : finrank ℂ E = 1) :
    complexCurveOrientation E M h =
      (complexManifoldOrientation E M).reindex (finCongr (by rw [h])) :=
  (rfl)

/-- At every point of a complex curve, `complexCurveOrientation` is the complex orientation of
the model space `E`, reindexed to `Fin 2`. -/
@[simp]
theorem orientationAt_complexCurveOrientation (h : finrank ℂ E = 1) (x : M) :
    (complexCurveOrientation E M h).orientationAt x =
      Orientation.reindex ℝ (TangentSpace 𝓘(ℝ, E) x) (finCongr (by rw [h]))
        (complexOrientation E) := by
  rw [complexCurveOrientation_def, orientationAt_reindex_complexManifoldOrientation]

/-- On `ℂ`, as a complex curve, `complexCurveOrientation` is the standard orientation
`Manifold.Orientation.complex` of `ℂ`, the constant orientation given by `Complex.orientation`,
the orientation of the basis `(1, i)`. -/
theorem complexCurveOrientation_complex :
    complexCurveOrientation ℂ ℂ = Manifold.Orientation.complex := by
  ext x
  rw [complexCurveOrientation_def, Manifold.Orientation.orientationAt_complex]
  exact orientationAt_reindex_complexManifoldOrientation_complex _ x

/-- A biholomorphism `Φ : M → N` of complex curves (a `C^n` diffeomorphism for the complex
models, `n ≠ 0`) carries `complexCurveOrientation` of `M` to that of `N` at every point. -/
theorem _root_.Diffeomorph.isOrientationPreservingAt_complexCurveOrientation
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℂ, E) 1 N]
    (h : finrank ℂ E = 1) (n : ℕ∞ω) [NeZero n] (Φ : M ≃ₘ^n⟮𝓘(ℂ, E), 𝓘(ℂ, E)⟯ N) (x : M) :
    Manifold.Orientation.IsOrientationPreservingAt (complexCurveOrientation E M h)
      (complexCurveOrientation E N h) Φ x := by
  rw [complexCurveOrientation_def, complexCurveOrientation_def]
  exact (Φ.isOrientationPreservingAt_complexManifoldOrientation n x).reindex _

variable (E M) in
/-- The canonical orientation of a complex manifold `M` modelled on `𝓘(ℂ, E)`, of complex
dimension `finrank ℂ E = r + 1`, as an orientation of the underlying real manifold of dimension
`2 r + 2` indexed by `Fin (2 * r + 1 + 1)`: Tau Ceti's `complexManifoldOrientation E M`,
reindexed from `Fin (2 * finrank ℂ E)`. -/
noncomputable def complexManifoldOrientationOfFinrank {r : ℕ} (hE : finrank ℂ E = r + 1) :
    Manifold.Orientation 𝓘(ℝ, E) M (Fin (2 * r + 1 + 1)) :=
  (complexManifoldOrientation E M).reindex (finCongr (by rw [hE]; ring))

theorem complexManifoldOrientationOfFinrank_def {r : ℕ} (hE : finrank ℂ E = r + 1) :
    complexManifoldOrientationOfFinrank E M hE =
      (complexManifoldOrientation E M).reindex (finCongr (by rw [hE]; ring)) :=
  (rfl)

/-- At every point of a complex manifold of complex dimension `r + 1`,
`complexManifoldOrientationOfFinrank` is the complex orientation of the model space `E`,
reindexed to `Fin (2 * r + 1 + 1)`. -/
@[simp]
theorem orientationAt_complexManifoldOrientationOfFinrank {r : ℕ} (hE : finrank ℂ E = r + 1)
    (x : M) :
    (complexManifoldOrientationOfFinrank E M hE).orientationAt x =
      Orientation.reindex ℝ (TangentSpace 𝓘(ℝ, E) x) (finCongr (by rw [hE]; ring))
        (complexOrientation E) := by
  rw [complexManifoldOrientationOfFinrank_def, orientationAt_reindex_complexManifoldOrientation]

/-- A complex-linear isomorphism `A : E ≃L[ℂ] G` carries the tangent orientation of
`complexManifoldOrientationOfFinrank` at any point to the complex orientation of `G`, reindexed to
`Fin (2 * r + 1 + 1)`. -/
theorem map_orientationAt_complexManifoldOrientationOfFinrank
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
    [FiniteDimensional ℂ G] {r : ℕ} (hE : finrank ℂ E = r + 1) (hG : finrank ℂ G = r + 1)
    (A : E ≃L[ℂ] G) (z : M) :
    ((complexManifoldOrientationOfFinrank E M hE).orientationAt z).map (Fin (2 * r + 1 + 1))
        (A.restrictScalars' ℝ).toLinearEquiv =
      Orientation.reindex ℝ G (finCongr (by rw [hG]; ring)) (complexOrientation G) :=
  map_orientationAt_reindex_complexManifoldOrientation _ _ A z

/-- `complexCurveOrientation` is the case `r = 0` of `complexManifoldOrientationOfFinrank`. -/
theorem complexCurveOrientation_eq_complexManifoldOrientationOfFinrank (h : finrank ℂ E = 1) :
    complexCurveOrientation E M h = complexManifoldOrientationOfFinrank E M (r := 0) h :=
  (rfl)

end SymplecticGeometry

end
