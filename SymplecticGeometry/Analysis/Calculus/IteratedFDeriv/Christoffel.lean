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
`∑ i ≤ n, (n choose i) ‖Dⁱ (g⁻¹)(w)‖ ‖D^(n - i + 1) g(w)‖`.

## Main results

* `SymplecticGeometry.exists_christoffelSecondKindOfJet_eq`: the Christoffel formula on jets is a
  continuous bilinear map of the inverse of the metric value and of the derivative of the metric.
* `SymplecticGeometry.exists_norm_iteratedFDeriv_christoffelSecondKind_le`: the bound above.

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

/-- The Christoffel formula on a metric first jet `j = (a, h)` is the image of the pair
`(a⁻¹, h)` under a continuous bilinear map that depends only on `E`. -/
theorem exists_christoffelSecondKindOfJet_eq :
    ∃ B : ((E →L[ℝ] ℝ) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E,
      ∀ j : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ),
        christoffelSecondKindOfJet j = B j.1.inverse j.2 := by
  let C := compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E)
  let c := compL ℝ E (E →L[ℝ] ℝ) E
  let φ := (flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let ψ := (flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearEquiv.toContinuousLinearMap
  let L := compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E →L[ℝ] ℝ) φ
  let L' : (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ + ψ - L ∘L ψ)
  -- Naming the spaces lets elaboration match the instances of the spaces of maps.
  let B := C.bilinearComp (E'' := (E →L[ℝ] ℝ) →L[ℝ] E)
    (F'' := E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) c L'
  refine ⟨B, fun j ↦ ?_⟩
  ext u v
  simp [christoffelSecondKindOfJet_apply, B, C, c, φ, ψ, L, L']

variable {E}

/-- **The Leibniz bound for the Christoffel symbols.** There is a constant `K ≥ 0`, depending
only on `E`, such that for every field of bilinear forms `g` on `E` that is `C^N` at `w`, with
`w ↦ (g w)⁻¹` also `C^N` at `w`, and every `n` with `n + 1 ≤ N`, the `n`-th derivative at `w` of
the Christoffel symbols `Γ` of `g` satisfies
`‖Dⁿ Γ(w)‖ ≤ K * ∑ i ≤ n, (n choose i) ‖Dⁱ (g⁻¹)(w)‖ ‖D^(n - i + 1) g(w)‖`. -/
theorem exists_norm_iteratedFDeriv_christoffelSecondKind_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E) {N : WithTop ℕ∞} {n : ℕ},
      ContDiffAt ℝ N g w → ContDiffAt ℝ N (fun y ↦ (g y).inverse) w → (n + 1 : ℕ) ≤ N →
        ‖iteratedFDeriv ℝ n (christoffelSecondKind g) w‖ ≤
          K * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y ↦ (g y).inverse) w‖ *
              ‖iteratedFDeriv ℝ (n - i + 1) g w‖ := by
  obtain ⟨B, hB⟩ := exists_christoffelSecondKindOfJet_eq E
  refine ⟨‖B‖, norm_nonneg _, fun g w N n hg hinv hn ↦ ?_⟩
  have hΓ : christoffelSecondKind g = fun y ↦ B (g y).inverse (fderiv ℝ g y) :=
    funext fun y ↦ (christoffelSecondKind_def g y).trans (hB _)
  have hn' : (n : WithTop ℕ∞) + 1 ≤ N := by exact_mod_cast hn
  rw [hΓ]
  refine (B.norm_iteratedFDeriv_le_of_bilinear_of_contDiffAt
    (hinv.of_le (le_self_add.trans hn')) (hg.fderiv_right hn') le_rfl).trans_eq ?_
  simp_rw [norm_iteratedFDeriv_fderiv]

end SymplecticGeometry

end
