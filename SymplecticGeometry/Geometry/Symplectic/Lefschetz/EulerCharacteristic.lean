/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.LocalAtTarget
public import TauCeti.Geometry.Manifold.Submersion.Split
public import TauCeti.Topology.Maps.Proper.Basic
public import SymplecticGeometry.Geometry.Manifold.RegularValue.RestrictPreimage
public import SymplecticGeometry.Geometry.Manifold.Submersion.FiberDiffeomorph
public import SymplecticGeometry.Geometry.Symplectic.Lefschetz.Basic

/-!
# The regular fibres of a Lefschetz fibration

For a Lefschetz fibration `π : X → ℂℙ¹` of a compact manifold, the regular values form an open
connected set `R` (`SymplecticGeometry.IsLefschetzFibration.isOpen_regularValue`,
`SymplecticGeometry.IsLefschetzFibration.isConnected_regularValue`). Over `R` the map
`π⁻¹(R) → R` is a proper smooth submersion, so by Ehresmann's fibration theorem
(`Manifold.IsSubmersion.nonempty_diffeomorph_mapFiber`) its fibres are pairwise diffeomorphic.
Its fibres are those of `π` over the points of `R`, with the same regular-fibre atlas
(`TauCeti.regularFiberRestrictPreimageDiffeomorph`).

## Main results

* `SymplecticGeometry.IsLefschetzFibration.nonempty_diffeomorph_fiber`: any two regular fibres of
  a Lefschetz fibration on a compact manifold are diffeomorphic.

## References

* R. E. Gompf, A. I. Stipsicz, *4-Manifolds and Kirby Calculus*, Graduate Studies in
  Mathematics 20, AMS (1999), §8.2.
-/

public section

open Set TopologicalSpace TauCeti Module
open scoped Manifold LinearAlgebra.Projectivization

namespace SymplecticGeometry

namespace IsLefschetzFibration

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I (⊤ : ℕ∞) X] [T2Space X] [CompactSpace X]
  {ω : SmoothTwoForm I X} {J : SmoothAlmostComplexStructure I X} {π : X → ℙ ℂ (Fin 2 → ℂ)}

/-- **The regular fibres of a Lefschetz fibration are diffeomorphic.** Let `π : X → ℂℙ¹` be a
Lefschetz fibration of a compact Hausdorff manifold without boundary, modelled on a
finite-dimensional space. Give the fibre `{x // π x = y}` over each regular value `y` its
regular-fibre atlas `TauCeti.regularFiberChartedSpace`. Then the fibres over any two regular
values are smoothly diffeomorphic.

The fibres may be empty; then all regular fibres are, since the regular values are connected. -/
theorem nonempty_diffeomorph_fiber (h : IsLefschetzFibration ω J π) {y₀ y₁ : ℙ ℂ (Fin 2 → ℂ)}
    (h₀ : IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π y₀) (h₁ : IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π y₁) :
    letI := regularFiberChartedSpace (m := (⊤ : ℕ∞)) (by simp) h.contMDiff
      BoundarylessManifold.isInteriorPoint h₀
    letI := regularFiberChartedSpace (m := (⊤ : ℕ∞)) (by simp) h.contMDiff
      BoundarylessManifold.isInteriorPoint h₁
    Nonempty (Diffeomorph 𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ (Fin 1 → ℂ)) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ (Fin 1 → ℂ)) → ℝ) {x // π x = y₀} {x // π x = y₁}
      (⊤ : ℕ∞)) := by
  let R : Opens (ℙ ℂ (Fin 2 → ℂ)) := ⟨_, h.isOpen_regularValue⟩
  have hπ := h.contMDiff
  -- The restriction of `π` over the regular values.
  let P : Opens X := ⟨π ⁻¹' R, R.isOpen.preimage hπ.continuous⟩
  let g : P → R := (R : Set (ℙ ℂ (Fin 2 → ℂ))).restrictPreimage π
  have hg : Manifold.IsSubmersion I 𝓘(ℝ, Fin 1 → ℂ) (⊤ : ℕ∞) g :=
    ((hπ.restrictPreimage R).isSubmersionOfComplement_of_surjective_mfderiv (by simp)
      fun x ↦ isRegularPoint_iff.1 ((isRegularPoint_restrictPreimage_iff hπ.continuous R).2
        (isRegularValue_iff.1 x.property x rfl))).isSubmersion
  have hgp : IsProperMap g := hπ.continuous.isProperMap.restrictPreimage _
  have : PreconnectedSpace R := isPreconnected_iff_preconnectedSpace.1
    h.isConnected_regularValue.isPreconnected
  -- `R` is σ-compact, as an open subset of the compact manifold `ℂℙ¹`, and so is `P`.
  have := ChartedSpace.secondCountable_of_sigmaCompact (Fin 1 → ℂ) (ℙ ℂ (Fin 2 → ℂ))
  have := ChartedSpace.locallyCompactSpace (Fin 1 → ℂ) R
  have : SigmaCompactSpace P := hgp.sigmaCompactSpace
  let := regularFiberChartedSpace (m := (⊤ : ℕ∞)) (by simp) hπ
    BoundarylessManifold.isInteriorPoint h₀
  let := regularFiberChartedSpace (m := (⊤ : ℕ∞)) (by simp) hπ
    BoundarylessManifold.isInteriorPoint h₁
  let := regularFiberChartedSpace (m := (⊤ : ℕ∞)) (by simp) hg.contMDiff
    BoundarylessManifold.isInteriorPoint (hg.isRegularValue (by simp) ⟨y₀, h₀⟩)
  let := regularFiberChartedSpace (m := (⊤ : ℕ∞)) (by simp) hg.contMDiff
    BoundarylessManifold.isInteriorPoint (hg.isRegularValue (by simp) ⟨y₁, h₁⟩)
  obtain ⟨φ⟩ := hg.nonempty_diffeomorph_mapFiber hgp ⟨y₀, h₀⟩ ⟨y₁, h₁⟩
  exact ⟨((regularFiberRestrictPreimageDiffeomorph (by simp) hπ
    BoundarylessManifold.isInteriorPoint h₀ R h₀).symm.trans φ).trans
    (regularFiberRestrictPreimageDiffeomorph (by simp) hπ BoundarylessManifold.isInteriorPoint
      h₁ R h₁)⟩

end IsLefschetzFibration

end SymplecticGeometry

end
