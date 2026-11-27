/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.Genus
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.Orientation.Euclidean
public import TauCeti.Geometry.Symplectic.Manifold.Surface
import SymplecticGeometry.Geometry.Manifold.ConnectedSum.OrientationPreserving
import SymplecticGeometry.Geometry.Manifold.Orientation.Diffeomorph
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving
import TauCeti.Geometry.Manifold.Orientation.Sphere
import TauCeti.Geometry.Manifold.Orientation.Torus

/-!
# The orientation and the area forms of the closed surface of genus `g`

The closed surface `SymplecticGeometry.ClosedSurface g` is orientable, and so carries a
symplectic form, an area form.

The proof is by induction on `g`. The surface of genus `0` is the unit sphere `S²`, which is
orientable (`TauCeti.orientable_sphere`). The surface of genus `g + 1` is the connected sum
(`SymplecticGeometry.ClosedSurface.succDiffeomorph`) of the torus, along its coordinate ball
`SymplecticGeometry.EuclideanTorus.ball`, with the surface of genus `g`, along its ball `0`, and
a connected sum of oriented manifolds along any such balls has an orientation
(`TauCeti.ConnectedSum.nonempty_orientation`).

The orientations for which a single ball preserves or reverses orientation at every point, from
the standard orientation of the plane, come from
`IsLocalDiffeomorph.exists_orientation_forall_isOrientationPreservingAt` and
`IsLocalDiffeomorph.exists_orientation_forall_isOrientationReversingAt`: the plane is connected,
so negating a given orientation where needed suffices.

A Hausdorff σ-compact surface is orientable exactly when it carries a symplectic form (Tau Ceti's
`TauCeti.orientable_iff_exists_isSymplectic_of_finrank_eq_two`, whose proof takes the area form
of an orientation from `TauCeti.exists_isSymplectic_orientation_eq_of_finrank_eq_two`).

## Main results

* `SymplecticGeometry.EuclideanTorus.exists_orientation_isOrientationPreservingAt_ball`: the
  torus has an orientation for which its coordinate ball preserves orientation.
* `SymplecticGeometry.ClosedSurface.nonempty_orientation`: the closed surface of genus `g` has an
  orientation.
* `SymplecticGeometry.ClosedSurface.exists_orientation_isOrientationReversingAt_ball`: for each
  `j`, the closed surface of genus `g` has an orientation for which its ball `j` reverses
  orientation.
* The instance `TauCeti.Orientable (𝓡 2) (ClosedSurface g)`.
* `SymplecticGeometry.ClosedSurface.exists_isSymplectic`: the closed surface of genus `g` carries
  a symplectic form.

## References

* [A. A. Kosinski, *Differential Manifolds*][Kosinski1993] (the connected sum of oriented
  manifolds).
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001] (area forms on
  oriented surfaces).
-/

public section

open TauCeti TauCeti.Manifold.Orientation
open scoped Manifold ContDiff

namespace SymplecticGeometry

namespace EuclideanTorus

/-- The torus has an orientation for which its coordinate ball preserves orientation, from the
standard orientation of the plane, at every point. -/
theorem exists_orientation_isOrientationPreservingAt_ball :
    ∃ o : Manifold.Orientation (𝓡 2) EuclideanTorus (Fin 2),
      ∀ v, IsOrientationPreservingAt (euclideanSpace 2) o ball v := by
  obtain ⟨o, -, ho⟩ := isLocalDiffeomorph_ball.exists_orientation_forall_isOrientationPreservingAt
    (by simp) (euclideanSpace 2)
    ((torusOrientation fun _ : Fin 2 ↦ (1 : ℝ)).map diffeomorph.symm (by simp) (by simp))
  exact ⟨o, ho⟩

end EuclideanTorus

namespace ClosedSurface

/-- The closed surface of genus `g` has an orientation. -/
theorem nonempty_orientation (g : ℕ) :
    Nonempty (Manifold.Orientation (𝓡 2) (ClosedSurface g) (Fin 2)) := by
  induction g with
  | zero =>
    have := Fact.mk (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2 + 1))
    obtain ⟨⟨o⟩⟩ := orientable_sphere (n := 2) (E := EuclideanSpace ℝ (Fin 3))
    exact ⟨((o.reindex (finCongr (finrank_euclideanSpace_fin))).map zeroDiffeomorph.symm
      (by simp) (by simp))⟩
  | succ g ih =>
    let := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin 2))
      EuclideanTorus.isOpenEmbedding_ball (isOpenEmbedding_ball (g := g) 0)
    have dT := EuclideanTorus.isLocalDiffeomorph_ball.of_le (n := ∞) (m := 1) (by simp)
    have dS := (isLocalDiffeomorph_ball (g := g) 0).of_le (n := ∞) (m := 1) (by simp)
    have := ConnectedSum.isManifold EuclideanTorus.isOpenEmbedding_ball
      (isOpenEmbedding_ball (g := g) 0) dT dS
    obtain ⟨o⟩ := ConnectedSum.nonempty_orientation EuclideanTorus.isOpenEmbedding_ball
      (isOpenEmbedding_ball 0) dT dS
      (EuclideanTorus.exists_orientation_isOrientationPreservingAt_ball.choose) ih.some
      (euclideanSpace 2)
    exact ⟨o.map succDiffeomorph.symm (by simp) (by simp)⟩

/-- For each `j`, the closed surface of genus `g` has an orientation for which its ball `j`
reverses orientation, from the standard orientation of the plane, at every point. -/
theorem exists_orientation_isOrientationReversingAt_ball (g j : ℕ) :
    ∃ o : Manifold.Orientation (𝓡 2) (ClosedSurface g) (Fin 2),
      ∀ v, IsOrientationReversingAt (euclideanSpace 2) o (ball g j) v := by
  obtain ⟨o, -, ho⟩ :=
    (isLocalDiffeomorph_ball j).exists_orientation_forall_isOrientationReversingAt
    (by simp) (euclideanSpace 2) (nonempty_orientation g).some
  exact ⟨o, ho⟩

/-- The closed surface of genus `g` is orientable. -/
instance (g : ℕ) : Orientable (𝓡 2) (ClosedSurface g) :=
  ⟨⟨(nonempty_orientation g).some.reindex (finCongr finrank_euclideanSpace_fin.symm)⟩⟩

/-- **The closed surface of genus `g` carries an area form**: a symplectic form, which exists since
the surface is orientable. -/
theorem exists_isSymplectic (g : ℕ) :
    ∃ σ : SmoothTwoForm (𝓡 2) (ClosedSurface g), σ.IsSymplectic :=
  (orientable_iff_exists_isSymplectic_of_finrank_eq_two finrank_euclideanSpace_fin).1
    inferInstance

end ClosedSurface

end SymplecticGeometry

end
