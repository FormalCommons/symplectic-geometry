/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Homotopy.HomotopyGroup
import SymplecticGeometry.Topology.Homotopy.Extension.Convex
import TauCeti.Topology.Homotopy.Extension.Cube

/-!
# Extending maps from the boundary of a cube into a star-convex set

A map from the boundary of the cube `I^N` into a set `C` of a real topological vector space that
is star-convex about a point `c ∈ C` extends to a continuous map on the whole cube with values
in `C`. This is the case `A = Cube.boundary N` of
`StarConvex.exists_continuousMap_eqOn_of_hasHomotopyExtensionProperty`: the boundary of the cube
is closed and has the homotopy extension property
(`TauCeti.hasHomotopyExtensionProperty_cubeBoundary`).

## Main results

* `StarConvex.exists_continuousMap_eqOn_cubeBoundary`: for `C` star-convex about `c ∈ C`, every
  map that is continuous on `Cube.boundary N` and sends it into `C` agrees there with a
  continuous map `I^N → V` with range in `C`.
* `Convex.exists_continuousMap_eqOn_cubeBoundary`: the same for `C` convex and nonempty.
* `Convex.exists_continuousMap_eqOn_cubeBoundary_of_nonempty`: the same for `C` convex and a
  nonempty index type `N`, where `C` is nonempty because it contains the image of the boundary.
-/

public section

open Set TauCeti
open scoped unitInterval Topology

variable {V : Type*} [AddCommMonoid V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousSMul ℝ V] {N : Type*} [Finite N] {C : Set V} {f : (I^N) → V}

namespace StarConvex

/-- A map `f` that is continuous on the boundary of the cube `I^N` and sends it into a set `C`
that is star-convex about a point `c ∈ C` agrees on the boundary with a continuous map
`g : I^N → V` whose range lies in `C`. -/
theorem exists_continuousMap_eqOn_cubeBoundary {c : V} (hC : StarConvex ℝ c C) (hc : c ∈ C)
    (hf : ContinuousOn f (Cube.boundary N)) (hfC : MapsTo f (Cube.boundary N) C) :
    ∃ g : C(I^N, V), EqOn g f (Cube.boundary N) ∧ range g ⊆ C :=
  hC.exists_continuousMap_eqOn_of_hasHomotopyExtensionProperty hc Cube.isClosed_boundary
    hasHomotopyExtensionProperty_cubeBoundary hf hfC

end StarConvex

namespace Convex

/-- A map `f` that is continuous on the boundary of the cube `I^N` and sends it into a nonempty
convex set `C` agrees on the boundary with a continuous map `g : I^N → V` whose range lies
in `C`. -/
theorem exists_continuousMap_eqOn_cubeBoundary (hC : Convex ℝ C) (hC₀ : C.Nonempty)
    (hf : ContinuousOn f (Cube.boundary N)) (hfC : MapsTo f (Cube.boundary N) C) :
    ∃ g : C(I^N, V), EqOn g f (Cube.boundary N) ∧ range g ⊆ C :=
  let ⟨_, hc⟩ := hC₀
  (hC hc).exists_continuousMap_eqOn_cubeBoundary hc hf hfC


/-- For a nonempty index type `N`, a map `f` that is continuous on the boundary of the cube `I^N`
and sends it into a convex set `C` agrees on the boundary with a continuous map `g : I^N → V`
whose range lies in `C`. -/
theorem exists_continuousMap_eqOn_cubeBoundary_of_nonempty [Nonempty N] (hC : Convex ℝ C)
    (hf : ContinuousOn f (Cube.boundary N)) (hfC : MapsTo f (Cube.boundary N) C) :
    ∃ g : C(I^N, V), EqOn g f (Cube.boundary N) ∧ range g ⊆ C :=
  hC.exists_continuousMap_eqOn_cubeBoundary
    ⟨f fun _ ↦ 0, hfC ⟨Classical.arbitrary N, Or.inl rfl⟩⟩ hf hfC

end Convex

end
