/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import SymplecticGeometry.AlgebraicTopology.Singular.SurfaceGenus
public import SymplecticGeometry.Geometry.Manifold.Morse.Bott.EulerCharacteristic
public import SymplecticGeometry.Geometry.Manifold.Submersion.FiberDiffeomorph
public import SymplecticGeometry.Geometry.Symplectic.Lefschetz.MorseBott
import SymplecticGeometry.Geometry.Manifold.Diffeomorph.RestrictScalars
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.Projectivization.ProjectiveLine

/-!
# The Euler characteristic of a Lefschetz fibration

For a Lefschetz fibration `π : X → ℂℙ¹` of a compact manifold, the regular values form an open
connected set `R` (`SymplecticGeometry.IsLefschetzFibration.isOpen_regularValue`,
`SymplecticGeometry.IsLefschetzFibration.isConnected_regularValue`), and `π` is proper, since `X`
is compact. So the fibres of `π` over the points of `R` are pairwise diffeomorphic
(`ContMDiff.nonempty_diffeomorph_fiber_of_isProperMap`, a form of Ehresmann's fibration theorem).

From this and the Morse–Bott function `μ ∘ π` of `Lefschetz/MorseBott.lean` follows the Euler
characteristic count `χ(X) = 2 χ(F) + ℓ` for a regular fibre `F` and `ℓ` critical points, when
the regular fibres are connected. Neither library has the multiplicativity of the Euler
characteristic in fibre bundles, so the count is made with Euler's equality for Morse–Bott
functions:

1. a projective transformation `g` of `ℂℙ¹` moves two regular values of `π`, the value under `F`
   among them, to the coordinate points `[1 : 0]` and `[0 : 1]`
   (`SymplecticGeometry.IsLefschetzFibration.exists_smul_isRegularValue`); the map
   `x ↦ g • π x` is again a Lefschetz fibration
   (`SymplecticGeometry.IsLefschetzFibration.comp_projectivizationMap`), with the same critical
   set (`SymplecticGeometry.criticalSet_smul`);
2. for it, the two fibres over the coordinate points and the critical points exhibit `μ ∘ π` as a
   Morse–Bott function, of index `0`, `2` and `2`
   (`SymplecticGeometry.IsLefschetzFibration.isMorseBottFamily_momentPullback`), so
   `χ(X) = χ(F₀) + χ(F₁) + ℓ` (`TauCeti.IsMorseBottFamily.eulerChar_eq_sum`);
3. both fibres are homeomorphic to `F`, by the diffeomorphism of regular fibres.

In real dimension four the fibres are closed surfaces; when `F` is homologically oriented,
`χ(F) = 2 - 2g` (`TauCeti.HomologicalOrientation.eulerChar_eq_two_sub_two_mul_surfaceGenus`), and
the count reads `χ(X) = 4 - 4g + ℓ`.

## Main results

* `SymplecticGeometry.IsLefschetzFibration.nonempty_diffeomorph_fiber`: any two regular fibres of
  a Lefschetz fibration on a compact manifold are diffeomorphic.
* `SymplecticGeometry.IsLefschetzFibration.eulerChar_eq`: `χ(X) = 2 χ(F) + ℓ` for a connected
  regular fibre `F` and `ℓ` critical points.
* `SymplecticGeometry.IsLefschetzFibration.eulerChar_eq_four_sub_four_mul_surfaceGenus`: in real
  dimension four, `χ(X) = 4 - 4g + ℓ` for `g` the genus of a homologically oriented connected
  regular fibre.

## References

* R. E. Gompf, A. I. Stipsicz, *4-Manifolds and Kirby Calculus*, Graduate Studies in
  Mathematics 20, AMS (1999), §8.2.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Section 7.4.
-/

public section

open Set TauCeti Module Projectivization
open scoped Manifold LinearAlgebra.Projectivization

namespace SymplecticGeometry

section Smul

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  (g : GL (Fin 2) ℂ) (π : X → ℙ ℂ (Fin 2 → ℂ))

/-- The diffeomorphism `g • ·` of `ℂℙ¹` for a projective transformation `g`, on the underlying
real manifold. -/
private noncomputable def smulDiffeomorph :
    ℙ ℂ (Fin 2 → ℂ) ≃ₘ^⊤⟮𝓘(ℝ, Fin 1 → ℂ), 𝓘(ℝ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ) :=
  (Diffeomorph.constSmul 𝓘(ℂ, Fin 1 → ℂ) ⊤ g :
    ℙ ℂ (Fin 2 → ℂ) ≃ₘ^⊤⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ)).restrictScalars' ℝ

private theorem coe_smulDiffeomorph : ⇑(smulDiffeomorph g) = (g • ·) := by
  rw [smulDiffeomorph, Diffeomorph.coe_restrictScalars', Diffeomorph.coe_constSmul]

/-- Moving a map into `ℂℙ¹` by a projective transformation `g` does not change its critical
set. -/
theorem criticalSet_smul :
    criticalSet I 𝓘(ℝ, Fin 1 → ℂ) (fun x ↦ g • π x) = criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π := by
  simpa [coe_smulDiffeomorph, Function.comp_def] using
    (smulDiffeomorph g).criticalSet_comp (I := I) (by simp) π

/-- Moving a map `π` into `ℂℙ¹` by a projective transformation `g` moves its regular values:
`g • y` is a regular value of `x ↦ g • π x` exactly when `y` is one of `π`. -/
theorem isRegularValue_smul_iff {y : ℙ ℂ (Fin 2 → ℂ)} :
    IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) (fun x ↦ g • π x) (g • y) ↔
      IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π y := by
  simpa [coe_smulDiffeomorph, Function.comp_def] using
    (smulDiffeomorph g).comp_isRegularValue_iff (I := I) (f := π) (y := y) (by simp)

end Smul

namespace IsLefschetzFibration

section Fiber

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

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space X] in
/-- **Moving two regular values to the coordinate points.** For a Lefschetz fibration `π` of a
compact manifold and a regular value `y`, some projective transformation `g` of `ℂℙ¹` sends `y`
to `[1 : 0]` and makes both coordinate points `[1 : 0]` and `[0 : 1]` regular values of
`x ↦ g • π x`. The critical values of `π` are finite, so `π` has a regular value besides `y`, and
`g` sends it to `[0 : 1]`. -/
theorem exists_smul_isRegularValue (h : IsLefschetzFibration ω J π) {y : ℙ ℂ (Fin 2 → ℂ)}
    (hy : IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π y) :
    ∃ g : GL (Fin 2) ℂ, g • y = MomentPullback.coordinatePoint 0 ∧
      ∀ k, IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) (fun x ↦ g • π x)
        (MomentPullback.coordinatePoint k) := by
  have : Infinite (ℙ ℂ (Fin 2 → ℂ)) :=
    Infinite.of_injective (ProjectiveLine.affineParam 0) fun s t hst ↦ by
      simpa using congrFun (congrArg (affineChart (K := ℂ) (n := 1) 0) hst) 0
  obtain ⟨b, hb⟩ := ((h.finite_criticalPoints.image π).insert y).infinite_compl.nonempty
  rw [mem_compl_iff, mem_insert_iff, not_or] at hb
  have hb' : b ∈ {y | IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π y} := by
    rw [setOf_isRegularValue_eq_compl_image, ← criticalSet_def]
    exact hb.2
  -- `SL₂(ℂ)` acts two-transitively on `ℂℙ¹`.
  obtain ⟨g, hg₀, hg₁⟩ := MulAction.is_two_pretransitive_iff.1
    (inferInstance : MulAction.IsMultiplyPretransitive (Matrix.SpecialLinearGroup (Fin 2) ℂ)
      (ℙ ℂ (Fin 2 → ℂ)) 2) (Ne.symm hb.1)
    (MomentPullback.coordinatePoint_injective.ne (by decide : (0 : Fin 2) ≠ 1))
  have hg (x : ℙ ℂ (Fin 2 → ℂ)) : Matrix.SpecialLinearGroup.toGL g • x = g • x := by
    induction x using Projectivization.ind with
    | h v hv => rw [smul_mk, smul_mk]; rfl
  refine ⟨Matrix.SpecialLinearGroup.toGL g, by rw [hg, hg₀], fun k ↦ ?_⟩
  match k with
  | 0 => rwa [← hg₀, ← hg, isRegularValue_smul_iff]
  | 1 => rwa [← hg₁, ← hg, isRegularValue_smul_iff]

end Fiber

section EulerCharacteristic

open MomentPullback

variable {E : Type} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {X : Type}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I (⊤ : ℕ∞) X] [T2Space X] [CompactSpace X]
  [FiniteCWType X] {ω : SmoothTwoForm I X} {J : SmoothAlmostComplexStructure I X}
  {π : X → ℙ ℂ (Fin 2 → ℂ)}

/-- **The Euler characteristic of a Lefschetz fibration.** Let `π : X → ℂℙ¹` be a Lefschetz
fibration of a compact Hausdorff manifold without boundary, modelled on a finite-dimensional
space, and let `y` be a regular value of `π` whose fibre `F = {x // π x = y}` is connected (in
particular nonempty). Then `χ(X) = 2 χ(F) + ℓ`, where `ℓ` is the number of critical points of
`π`. The finite CW types of `X` and `F` are instance arguments;
`TauCeti.FiniteCWType.of_isManifold` supplies them. -/
theorem eulerChar_eq (h : IsLefschetzFibration ω J π) {y : ℙ ℂ (Fin 2 → ℂ)}
    (hy : IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π y) (hconn : IsConnected (π ⁻¹' {y}))
    [FiniteCWType {x // π x = y}] :
    eulerChar X = 2 * eulerChar {x // π x = y} + (criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π).ncard := by
  obtain ⟨g, hgy, hreg⟩ := h.exists_smul_isRegularValue hy
  set π' : X → ℙ ℂ (Fin 2 → ℂ) := fun x ↦ g • π x
  have h' : IsLefschetzFibration ω J π' := h.comp_projectivizationMap g
  -- The fibre of `π'` over `c 0` is that of `π` over `y`, and by the diffeomorphism of regular
  -- fibres the fibre over `c 1` is homeomorphic to it.
  have e₀ : {x // π' x = coordinatePoint 0} ≃ₜ {x // π x = y} :=
    (Homeomorph.refl X).subtype fun x ↦ by simp [π', ← hgy]
  have e₁ : {x // π' x = coordinatePoint 1} ≃ₜ {x // π x = y} := by
    letI := regularFiberChartedSpace (m := (⊤ : ℕ∞)) (by simp) h'.contMDiff
      BoundarylessManifold.isInteriorPoint (hreg 0)
    letI := regularFiberChartedSpace (m := (⊤ : ℕ∞)) (by simp) h'.contMDiff
      BoundarylessManifold.isInteriorPoint (hreg 1)
    exact (h'.nonempty_diffeomorph_fiber (hreg 1) (hreg 0)).some.toHomeomorph.trans e₀
  have hconn' (k : Fin 2) : IsConnected (π' ⁻¹' {coordinatePoint k}) := by
    have : ConnectedSpace {x // π x = y} := isConnected_iff_connectedSpace.1 hconn
    refine isConnected_iff_connectedSpace.2 ?_
    match k with
    | 0 => exact e₀.symm.surjective.connectedSpace e₀.symm.continuous
    | 1 => exact e₁.symm.surjective.connectedSpace e₁.symm.continuous
  -- The Morse–Bott family of `μ ∘ π'`, and the finite CW types of its pieces.
  have : Fintype (criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π') := h'.finite_criticalPoints.fintype
  have := I.secondCountableTopology
  have := ChartedSpace.secondCountable_of_sigmaCompact H X
  let := MomentPullback.chartedSpace h'.contMDiff hreg
  have hMB := h'.isMorseBottFamily_momentPullback hreg hconn'
  have := MomentPullback.isManifold h'.contMDiff hreg
  have : ∀ j, T2Space (Piece I π' j) := fun j ↦
    (embedding h'.contMDiff hreg j).isEmbedding.t2Space
  have : ∀ j, CompactSpace (Piece I π' j) := fun _ ↦
    hMB.compactSpace_of_range_subset isCompact_univ (subset_univ _)
  have : ∀ j, FiniteCWType (Piece I π' j) := fun j ↦
    FiniteCWType.of_isManifold _ 𝓘(ℝ, Fin (dim I π' j) → ℝ)
  have e₀' : Piece I π' (.inl 0) ≃ₜ {x // π x = y} := e₀
  have e₁' : Piece I π' (.inl 1) ≃ₜ {x // π x = y} := e₁
  rw [hMB.eulerChar_eq_sum (h'.manifoldMorseIndex_momentPullback hreg), Fintype.sum_sum_type,
    Fin.sum_univ_two, e₀'.eulerChar_eq, e₁'.eulerChar_eq]
  simp only [index_inl, index_inr, eulerChar_of_contractibleSpace]
  rw [← criticalSet_smul g π, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  simp
  ring

/-- **The Euler characteristic of a Lefschetz fibration, with the genus of the fibre.** Let
`π : X → ℂℙ¹` be a Lefschetz fibration of a compact Hausdorff manifold of real dimension four
without boundary, and let `y` be a regular value of `π` whose fibre `F = {x // π x = y}` is
connected, with its regular-fibre atlas `TauCeti.regularFiberChartedSpace` and a homological
orientation `o`. Then `χ(X) = 4 - 4g + ℓ`, where `g = TauCeti.surfaceGenus F` is the genus of
`F` and `ℓ` is the number of critical points of `π`. -/
theorem eulerChar_eq_four_sub_four_mul_surfaceGenus (h : IsLefschetzFibration ω J π)
    (hE : finrank ℝ E = 4) {y : ℙ ℂ (Fin 2 → ℂ)} (hy : IsRegularValue I 𝓘(ℝ, Fin 1 → ℂ) π y)
    (hconn : IsConnected (π ⁻¹' {y})) [FiniteCWType {x // π x = y}]
    (o :
      letI := regularFiberChartedSpace (m := (⊤ : ℕ∞)) (by simp) h.contMDiff
        BoundarylessManifold.isInteriorPoint hy
      HomologicalOrientation {x // π x = y} (Fin (finrank ℝ E - finrank ℝ (Fin 1 → ℂ)) → ℝ) 2) :
    eulerChar X = 4 - 4 * surfaceGenus {x // π x = y} +
      (criticalSet I 𝓘(ℝ, Fin 1 → ℂ) π).ncard := by
  let := regularFiberChartedSpace (m := (⊤ : ℕ∞)) (by simp) h.contMDiff
    BoundarylessManifold.isInteriorPoint hy
  have : CompactSpace {x // π x = y} := isCompact_iff_compactSpace.1
    (isClosed_singleton.preimage h.contMDiff.continuous).isCompact
  have : ConnectedSpace {x // π x = y} := isConnected_iff_connectedSpace.1 hconn
  rw [h.eulerChar_eq hy hconn, o.eulerChar_eq_two_sub_two_mul_surfaceGenus
    (by simp [hE, Module.finrank_pi_fintype, Complex.finrank_real_complex])]
  ring

end EulerCharacteristic

end IsLefschetzFibration

end SymplecticGeometry

end
