/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Submersion.FiberDiffeomorph
public import SymplecticGeometry.Geometry.Symplectic.Lefschetz.Basic

/-!
# The regular fibres of a Lefschetz fibration

For a Lefschetz fibration `π : X → ℂℙ¹` of a compact manifold, the regular values form an open
connected set `R` (`SymplecticGeometry.IsLefschetzFibration.isOpen_regularValue`,
`SymplecticGeometry.IsLefschetzFibration.isConnected_regularValue`), and `π` is proper, since `X`
is compact. So the fibres of `π` over the points of `R` are pairwise diffeomorphic
(`ContMDiff.nonempty_diffeomorph_fiber_of_isProperMap`, a form of Ehresmann's fibration theorem).

## Main results

* `SymplecticGeometry.IsLefschetzFibration.nonempty_diffeomorph_fiber`: any two regular fibres of
  a Lefschetz fibration on a compact manifold are diffeomorphic.

## References

* R. E. Gompf, A. I. Stipsicz, *4-Manifolds and Kirby Calculus*, Graduate Studies in
  Mathematics 20, AMS (1999), §8.2.
-/

public section

open TauCeti Module
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
      (⊤ : ℕ∞)) :=
  h.contMDiff.nonempty_diffeomorph_fiber_of_isProperMap h.contMDiff.continuous.isProperMap
    ⟨_, h.isOpen_regularValue⟩ h.isConnected_regularValue.isPreconnected (fun _ hy ↦ hy) h₀ h₁

end IsLefschetzFibration

end SymplecticGeometry

end
