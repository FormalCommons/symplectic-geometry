/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear

/-!
# Bounds on the derivatives of Christoffel symbols

Let `g : E → E →L[ℝ] E →L[ℝ] ℝ` be a field of bilinear forms on a real normed space `E`. Its
Christoffel symbols of the second kind `Γ = TauCeti.Manifold.christoffelSecondKind g` are, at each
point `w`, the image of the pair `((g w)⁻¹, Dg(w))` under one fixed continuous bilinear map, since
Tau Ceti's Christoffel formula `TauCeti.Manifold.christoffelSecondKindOfJet` is linear in the
inverse of the metric value and in the derivative of the metric. The Leibniz rule for a bilinear
map (`ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_contDiffAt`) then bounds the
`n`-th derivative of `Γ` at `w` by a constant, depending only on `E`, times
`∑ i ≤ n, (n choose i) ‖Dⁱ (g⁻¹)(w)‖ ‖D^(n - i + 1) g(w)‖`; with constant bounds on those
derivatives, Tau Ceti's `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_forall_le`
collapses the sum.

## Main results

* `SymplecticGeometry.christoffelSecondKindOfJetBilin`: the fixed continuous bilinear map, and
  `SymplecticGeometry.christoffelSecondKindOfJet_eq_christoffelSecondKindOfJetBilin`: the
  Christoffel formula on jets is that map applied to the inverse of the metric value and to the
  derivative of the metric.
* `SymplecticGeometry.christoffelSecondKindOfJetBilinNorm`: its operator norm, the constant of the
  bounds below.
* `SymplecticGeometry.norm_iteratedFDeriv_christoffelSecondKind_le`: the bound above.
* `SymplecticGeometry.norm_iteratedFDeriv_christoffelSecondKind_le_of_forall_le`: the bound
  `K * 2 ^ n * M₁ * M₂` when the derivatives of order at most `n` of `g⁻¹` are at most `M₁` and
  those of order `1` to `n + 1` of `g` are at most `M₂`.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press (1983),
  Chapter 3: the Christoffel symbols of a nondegenerate metric.
-/

public section

open ContinuousLinearMap TauCeti.Manifold


namespace SymplecticGeometry

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Caching these instances lets synthesis reach the spaces of maps into bilinear and trilinear
-- forms below, as in Tau Ceti's
-- `ContinuousLinearMap.IsInvertible.contDiffAt_christoffelSecondKindOfJet`.
/-- The normed additive group of bilinear forms on `E`, cached for the spaces of maps into it. -/
noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The real normed space of bilinear forms on `E`, cached for the spaces of maps into it. -/
noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The normed additive group of trilinear forms on `E`, cached for the spaces of maps into it. -/
noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The real normed space of trilinear forms on `E`, cached for the spaces of maps into it. -/
noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The normed additive group of maps from linear forms on `E` to `E`, cached for the spaces of
maps out of it. -/
noncomputable local instance : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance

/-- The real normed space of maps from linear forms on `E` to `E`, cached for the spaces of maps
out of it. -/
noncomputable local instance : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance

/-- The normed additive group of bilinear maps on `E`, cached for the spaces of maps into it. -/
noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- The real normed space of bilinear maps on `E`, cached for the spaces of maps into it. -/
noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- The normed additive group of maps from trilinear forms to bilinear maps, cached for the
space of maps into it. -/
noncomputable local instance :
    NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- The real normed space of maps from trilinear forms to bilinear maps, cached for the space of
maps into it. -/
noncomputable local instance :
    NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- The continuous bilinear map that sends `(a', h)`, for `a'` a map from linear forms on `E` to
`E` and `h` a trilinear form on `E`, to the bilinear map
`(u, v) ↦ a' (2⁻¹ • (h u v + h v u - h (·) u v))`. Applied to `a' = a⁻¹`, it is the Christoffel
formula on the metric first jet `(a, h)`
(`SymplecticGeometry.christoffelSecondKindOfJet_eq_christoffelSecondKindOfJetBilin`). -/
noncomputable def christoffelSecondKindOfJetBilin :
    ((E →L[ℝ] ℝ) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  -- Naming the spaces lets elaboration match the instances of the spaces of maps.
  (compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E)).bilinearComp
    (E'' := (E →L[ℝ] ℝ) →L[ℝ] E) (F'' := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (compL ℝ E (E →L[ℝ] ℝ) E)
    ((2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ +
      (flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap -
      compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E →L[ℝ] ℝ)
          (flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap))

theorem christoffelSecondKindOfJetBilin_def :
    christoffelSecondKindOfJetBilin E =
      (compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E)).bilinearComp
        (E'' := (E →L[ℝ] ℝ) →L[ℝ] E) (F'' := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (compL ℝ E (E →L[ℝ] ℝ) E)
        ((2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ +
          (flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap -
          compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E →L[ℝ] ℝ)
              (flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap ∘L
            (flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap)) :=
  (rfl)

-- Outside this file, synthesis does not find the norm on the space of
-- `christoffelSecondKindOfJetBilin E` (it needs the local instances above), so the constant of the
-- bounds below has a name of its own.
/-- The operator norm of `christoffelSecondKindOfJetBilin E`, the constant in the Leibniz bounds
for the Christoffel symbols on `E`. -/
noncomputable def christoffelSecondKindOfJetBilinNorm : ℝ := ‖christoffelSecondKindOfJetBilin E‖

theorem christoffelSecondKindOfJetBilinNorm_def :
    christoffelSecondKindOfJetBilinNorm E = ‖christoffelSecondKindOfJetBilin E‖ :=
  (rfl)

theorem christoffelSecondKindOfJetBilinNorm_nonneg : 0 ≤ christoffelSecondKindOfJetBilinNorm E :=
  norm_nonneg _

variable {E}

@[simp]
theorem christoffelSecondKindOfJetBilin_apply (a : (E →L[ℝ] ℝ) →L[ℝ] E)
    (h : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v : E) :
    christoffelSecondKindOfJetBilin E a h u v =
      a ((2⁻¹ : ℝ) • (h u v + h v u - (h.flip u).flip v)) := by
  simp [christoffelSecondKindOfJetBilin_def]

/-- The Christoffel formula on a metric first jet `j = (a, h)` is the image of `(a⁻¹, h)` under
the continuous bilinear map `christoffelSecondKindOfJetBilin E`. -/
theorem christoffelSecondKindOfJet_eq_christoffelSecondKindOfJetBilin
    (j : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) :
    christoffelSecondKindOfJet j = christoffelSecondKindOfJetBilin E j.1.inverse j.2 := by
  ext u v
  simp [christoffelSecondKindOfJet_apply]

/-- The Christoffel symbols of a field of bilinear forms `g` are the image of `(g⁻¹, Dg)`, at each
point, under `christoffelSecondKindOfJetBilin E`. -/
theorem christoffelSecondKind_eq_christoffelSecondKindOfJetBilin (g : E → E →L[ℝ] E →L[ℝ] ℝ) :
    christoffelSecondKind g =
      fun y ↦ christoffelSecondKindOfJetBilin E (g y).inverse (fderiv ℝ g y) :=
  funext fun y ↦ (christoffelSecondKind_def g y).trans
    (christoffelSecondKindOfJet_eq_christoffelSecondKindOfJetBilin _)

/-- **The Leibniz bound for the Christoffel symbols.** If a field of bilinear forms `g` on `E` is
`C^N` at `w`, with `w ↦ (g w)⁻¹` also `C^N` at `w`, then for every `n` with `n + 1 ≤ N` the
`n`-th derivative at `w` of the Christoffel symbols `Γ` of `g` satisfies
`‖Dⁿ Γ(w)‖ ≤ K * ∑ i ≤ n, (n choose i) ‖Dⁱ (g⁻¹)(w)‖ ‖D^(n - i + 1) g(w)‖`, where
`K = christoffelSecondKindOfJetBilinNorm E` depends only on `E`. -/
theorem norm_iteratedFDeriv_christoffelSecondKind_le {g : E → E →L[ℝ] E →L[ℝ] ℝ} {w : E}
    {N : WithTop ℕ∞} {n : ℕ} (hg : ContDiffAt ℝ N g w)
    (hinv : ContDiffAt ℝ N (fun y ↦ (g y).inverse) w) (hn : (n + 1 : ℕ) ≤ N) :
    ‖iteratedFDeriv ℝ n (christoffelSecondKind g) w‖ ≤
      christoffelSecondKindOfJetBilinNorm E * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y ↦ (g y).inverse) w‖ *
          ‖iteratedFDeriv ℝ (n - i + 1) g w‖ := by
  have hn' : (n : WithTop ℕ∞) + 1 ≤ N := by exact_mod_cast hn
  rw [christoffelSecondKindOfJetBilinNorm_def,
    christoffelSecondKind_eq_christoffelSecondKindOfJetBilin]
  refine ((christoffelSecondKindOfJetBilin E).norm_iteratedFDeriv_le_of_bilinear_of_contDiffAt
    (hinv.of_le (le_self_add.trans hn')) (hg.fderiv_right hn') le_rfl).trans_eq ?_
  simp_rw [norm_iteratedFDeriv_fderiv]

/-- **The Leibniz bound for the Christoffel symbols, with constant bounds.** If a field of
bilinear forms `g` on `E` is `C^N` at `w`, with `w ↦ (g w)⁻¹` also `C^N` at `w`, if `n + 1 ≤ N`,
and if `‖Dⁱ (g⁻¹)(w)‖ ≤ M₁` and `‖D^(i + 1) g(w)‖ ≤ M₂` for all `i ≤ n`, then the `n`-th
derivative at `w` of the Christoffel symbols `Γ` of `g` satisfies
`‖Dⁿ Γ(w)‖ ≤ christoffelSecondKindOfJetBilinNorm E * 2 ^ n * M₁ * M₂`. -/
theorem norm_iteratedFDeriv_christoffelSecondKind_le_of_forall_le
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {w : E} {N : WithTop ℕ∞} {n : ℕ} (hg : ContDiffAt ℝ N g w)
    (hinv : ContDiffAt ℝ N (fun y ↦ (g y).inverse) w) (hn : (n + 1 : ℕ) ≤ N) {M₁ M₂ : ℝ}
    (h₁ : ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun y ↦ (g y).inverse) w‖ ≤ M₁)
    (h₂ : ∀ i ≤ n, ‖iteratedFDeriv ℝ (i + 1) g w‖ ≤ M₂) :
    ‖iteratedFDeriv ℝ n (christoffelSecondKind g) w‖ ≤
      christoffelSecondKindOfJetBilinNorm E * 2 ^ n * M₁ * M₂ := by
  have hn' : (n : WithTop ℕ∞) + 1 ≤ N := by exact_mod_cast hn
  rw [christoffelSecondKindOfJetBilinNorm_def,
    christoffelSecondKind_eq_christoffelSecondKindOfJetBilin]
  exact (christoffelSecondKindOfJetBilin E).norm_iteratedFDeriv_le_of_bilinear_of_forall_le
    (hinv.of_le (le_self_add.trans hn')) (hg.fderiv_right hn') h₁
    fun i hi ↦ by rw [norm_iteratedFDeriv_fderiv]; exact h₂ i hi

end SymplecticGeometry

end
