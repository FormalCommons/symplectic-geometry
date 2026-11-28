/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Homotopy.HomotopyGroup
import SymplecticGeometry.Topology.Homotopy.Cube.Radius

/-!
# Extending maps from the boundary of a cube into a convex set

A map from the boundary of the cube `I^N` into a convex subset `C` of a real topological vector
space extends to a continuous map on the whole cube with values in `C`. The extension is a cone
from the centre of the cube: with `ρ = TauCeti.cubeRadius` the normalized sup-distance from the
centre and `r z = TauCeti.cubeScale (ρ z)⁻¹ z` the radial projection onto the boundary, it is
`z ↦ ψ z • f (r z) + (1 - ψ z) • c`, where `c ∈ C` is fixed and `ψ = max 0 (2 ρ - 1)`. The
weight `ψ` takes values in `[0, 1]`, is `1` on the boundary and vanishes where `ρ ≤ 1 / 2`, so
the extension is constant near the centre, where the radial projection is undefined.

## Main results

* `Convex.exists_continuousMap_eqOn_cubeBoundary`: for `C` convex and nonempty, every map that is
  continuous on `Cube.boundary N` and sends it into `C` agrees there with a continuous map
  `I^N → V` with range in `C`.
* `Convex.exists_continuousMap_eqOn_cubeBoundary_of_nonempty`: the same for a nonempty index type
  `N`, where `C` is nonempty because it contains the image of the boundary.
-/

public section

open Set Filter TauCeti
open scoped unitInterval Topology

namespace Convex

variable {V : Type*} [AddCommMonoid V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousSMul ℝ V] {N : Type*} [Finite N] {C : Set V} {f : (I^N) → V}

/-- A map `f` that is continuous on the boundary of the cube `I^N` and sends it into a nonempty
convex set `C` agrees on the boundary with a continuous map `g : I^N → V` whose range lies
in `C`. -/
theorem exists_continuousMap_eqOn_cubeBoundary (hC : Convex ℝ C) (hC₀ : C.Nonempty)
    (hf : ContinuousOn f (Cube.boundary N)) (hfC : MapsTo f (Cube.boundary N) C) :
    ∃ g : C(I^N, V), EqOn g f (Cube.boundary N) ∧ range g ⊆ C := by
  have := Fintype.ofFinite N
  obtain ⟨c, hc⟩ := hC₀
  set ψ : (I^N) → ℝ := fun z ↦ max 0 (2 * cubeRadius z - 1)
  have hψc : Continuous ψ :=
    continuous_const.max ((continuous_const.mul continuous_cubeRadius).sub continuous_const)
  have hψ₀ {z : I^N} (hz : cubeRadius z ≤ 1 / 2) : ψ z = 0 := max_eq_left (by linarith)
  set g : (I^N) → V := fun z ↦ ψ z • f (cubeScale (cubeRadius z)⁻¹ z) + (1 - ψ z) • c
  have hgc : Continuous g := by
    refine continuous_iff_continuousAt.2 fun z ↦ ?_
    by_cases hz : cubeRadius z = 0
    · have hlt : ∀ᶠ y in 𝓝 z, cubeRadius y < 1 / 2 :=
        continuous_cubeRadius.continuousAt.eventually (gt_mem_nhds (by rw [hz]; norm_num))
      refine (continuousAt_const (y := c)).congr (Filter.EventuallyEq.symm ?_)
      filter_upwards [hlt] with y hy
      simp [g, hψ₀ hy.le]
    · have hopen : IsOpen {y : I^N | cubeRadius y ≠ 0} :=
        isOpen_ne_fun continuous_cubeRadius continuous_const
      have hfr : ContinuousOn (fun y ↦ f (cubeScale (cubeRadius y)⁻¹ y))
          {y | cubeRadius y ≠ 0} :=
        hf.comp continuousOn_cubeScale_inv_cubeRadius
          fun _ hy ↦ cubeScale_inv_cubeRadius_mem_boundary hy
      exact ((hψc.continuousOn.smul hfr).add ((continuous_const.sub hψc).continuousOn.smul
        continuousOn_const)).continuousAt (hopen.mem_nhds hz)
  refine ⟨⟨g, hgc⟩, fun z hz ↦ ?_, ?_⟩
  · have h1 : cubeRadius z = 1 := (cubeRadius_eq_one_iff z).2 hz
    have hψ1 : ψ z = 1 := by norm_num [ψ, h1]
    simp [g, hψ1, h1, cubeScale_one]
  · rintro _ ⟨z, rfl⟩
    by_cases hz : cubeRadius z = 0
    · simpa [g, hψ₀ (hz.le.trans (by norm_num))] using hc
    · have hψ1 : ψ z ≤ 1 := max_le zero_le_one (by linarith [cubeRadius_le_one z])
      exact hC (hfC (cubeScale_inv_cubeRadius_mem_boundary hz)) hc (le_max_left _ _)
        (by linarith) (by ring)

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
