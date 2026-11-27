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
import SymplecticGeometry.Geometry.Manifold.Orientation.Diffeomorph
import SymplecticGeometry.Geometry.Manifold.Orientation.Preserving
import TauCeti.Geometry.Manifold.ConnectedSum.Orientation
import TauCeti.Geometry.Manifold.Orientation.Sphere
import TauCeti.Geometry.Manifold.Orientation.Torus

/-!
# The orientation and the area forms of the closed surface of genus `g`

The closed surface `SymplecticGeometry.ClosedSurface g` is orientable, and so carries a
symplectic form, an area form.

The proof is by induction on `g`. The surface of genus `0` is the unit sphere `S²`, which is
orientable (`TauCeti.orientable_sphere`). The surface of genus `g + 1` is the connected sum
(`SymplecticGeometry.ClosedSurface.succDiffeomorph`) of the torus, along its coordinate ball
`SymplecticGeometry.EuclideanTorus.ball`, with the surface of genus `g`, along its ball `0`.
Both balls are local diffeomorphisms out of the connected plane, so each preserves orientation
everywhere or reverses it everywhere, from the standard orientation of the plane
(`IsLocalDiffeomorph.forall_isOrientationPreservingAt_or_forall_isOrientationReversingAt`).
Reversing the orientation of a summand where needed, the torus ball preserves and the other ball
reverses orientation, and Tau Ceti's `TauCeti.ConnectedSum.orientation` orients the connected sum.

A Hausdorff σ-compact surface is orientable exactly when it carries a symplectic form (Tau Ceti's
`TauCeti.orientable_iff_exists_isSymplectic_of_finrank_eq_two`, whose proof takes the area form
of an orientation from `TauCeti.exists_isSymplectic_orientation_eq_of_finrank_eq_two`).

## Main results

* `SymplecticGeometry.EuclideanTorus.exists_orientation_isOrientationPreservingAt_ball`: the
  torus has an orientation for which its coordinate ball preserves orientation.
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

noncomputable section

open TauCeti TauCeti.Manifold.Orientation
open scoped Manifold ContDiff

namespace SymplecticGeometry

namespace EuclideanTorus

/-- The torus has an orientation for which its coordinate ball preserves orientation, from the
standard orientation of the plane, at every point. -/
theorem exists_orientation_isOrientationPreservingAt_ball :
    ∃ o : Manifold.Orientation (𝓡 2) EuclideanTorus (Fin 2),
      ∀ v, IsOrientationPreservingAt (euclideanSpace 2) o ball v := by
  let o : Manifold.Orientation (𝓡 2) EuclideanTorus (Fin 2) :=
    (torusOrientation fun _ : Fin 2 ↦ (1 : ℝ)).map diffeomorph.symm (by simp) (by simp)
  rcases IsLocalDiffeomorph.forall_isOrientationPreservingAt_or_forall_isOrientationReversingAt
    isLocalDiffeomorph_ball (by simp) (euclideanSpace 2) o with h | h
  · exact ⟨o, h⟩
  · exact ⟨-o, fun v ↦ (isOrientationPreservingAt_neg_right _ _ _ _).2 (h v)⟩

end EuclideanTorus

namespace ClosedSurface

/-- Reversing a given orientation where needed, the closed surface of genus `g` has an orientation
for which its ball `j` reverses orientation at every point. -/
private theorem exists_orientation_isOrientationReversingAt_ball_of_orientation {g : ℕ}
    (o : Manifold.Orientation (𝓡 2) (ClosedSurface g) (Fin 2)) (j : ℕ) :
    ∃ o : Manifold.Orientation (𝓡 2) (ClosedSurface g) (Fin 2),
      ∀ v, IsOrientationReversingAt (euclideanSpace 2) o (ball g j) v := by
  rcases IsLocalDiffeomorph.forall_isOrientationPreservingAt_or_forall_isOrientationReversingAt
    (isLocalDiffeomorph_ball j) (by simp) (euclideanSpace 2) o with h | h
  · exact ⟨-o, fun v ↦ (isOrientationReversingAt_neg_right _ _ _ _).2 (h v)⟩
  · exact ⟨o, h⟩

/-- The closed surface of genus `g` has an orientation. -/
private theorem nonempty_orientation (g : ℕ) :
    Nonempty (Manifold.Orientation (𝓡 2) (ClosedSurface g) (Fin 2)) := by
  induction g with
  | zero =>
    have := Fact.mk (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2 + 1))
    obtain ⟨⟨o⟩⟩ := orientable_sphere (n := 2) (E := EuclideanSpace ℝ (Fin 3))
    exact ⟨((o.reindex (finCongr (finrank_euclideanSpace_fin))).map zeroDiffeomorph.symm
      (by simp) (by simp))⟩
  | succ g ih =>
    -- Orient the torus and the surface of genus `g` so that the two balls along which they are
    -- summed induce opposite orientations of the plane, and glue.
    obtain ⟨oT, hT⟩ := EuclideanTorus.exists_orientation_isOrientationPreservingAt_ball
    obtain ⟨oS, hS⟩ := exists_orientation_isOrientationReversingAt_ball_of_orientation ih.some 0
    let := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin 2))
      EuclideanTorus.isOpenEmbedding_ball (isOpenEmbedding_ball (g := g) 0)
    have dT := EuclideanTorus.isLocalDiffeomorph_ball.of_le (n := ∞) (m := 1) (by simp)
    have dS := (isLocalDiffeomorph_ball (g := g) 0).of_le (n := ∞) (m := 1) (by simp)
    have := ConnectedSum.isManifold EuclideanTorus.isOpenEmbedding_ball
      (isOpenEmbedding_ball (g := g) 0) dT dS
    exact ⟨(ConnectedSum.orientation EuclideanTorus.isOpenEmbedding_ball
      (isOpenEmbedding_ball 0) dT dS oT oS (euclideanSpace 2)
      (fun v _ ↦ hT v) (fun v _ ↦ hS v)).map succDiffeomorph.symm (by simp) (by simp)⟩

/-- For each `j`, the closed surface of genus `g` has an orientation for which its ball `j`
reverses orientation, from the standard orientation of the plane, at every point. -/
theorem exists_orientation_isOrientationReversingAt_ball (g j : ℕ) :
    ∃ o : Manifold.Orientation (𝓡 2) (ClosedSurface g) (Fin 2),
      ∀ v, IsOrientationReversingAt (euclideanSpace 2) o (ball g j) v :=
  exists_orientation_isOrientationReversingAt_ball_of_orientation (nonempty_orientation g).some j

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
