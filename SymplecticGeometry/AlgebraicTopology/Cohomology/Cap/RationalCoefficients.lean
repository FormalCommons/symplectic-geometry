/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import SymplecticGeometry.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Coefficients
public import TauCeti.AlgebraicTopology.Singular.BettiNumber

import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field
import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Consequences of rational Poincaré duality

Let `M` be a compact homologically oriented `n`-manifold without boundary, and write
`[M]_ℚ = TauCeti.HomologicalOrientation.fundamentalClassOver ℚ` for the image of its fundamental
class in `Hₙ(M; ℚ)`. Tau Ceti proves rational Poincaré duality: capping with `[M]_ℚ` is a
bijection `Hᵖ(M; ℚ) → H_q(M; ℚ)` for `p + q = n`
(`TauCeti.HomologicalOrientation.bijective_singularCapLinearMap_fundamentalClassOver`), and the
cup pairing against `[M]_ℚ` is nondegenerate
(`TauCeti.HomologicalOrientation.nondegenerate_singularCupPairing_fundamentalClassOver`). This
file draws consequences of these two theorems.

* `TauCeti.HomologicalOrientation.bettiNumber_eq_bettiNumber`: the rational Betti numbers satisfy
  `b_q = b_p` for `p + q = n`, by Tau Ceti's
  `TopCat.finrank_singularHomology_eq_of_bijective_singularCapLinearMap`.
* `TauCeti.HomologicalOrientation.intersectionForm`: for `p + p = n`, the cup pairing
  `(α, β) ↦ ⟨α ⌣ β, [M]_ℚ⟩` on `Hᵖ(M; ℚ)`;
  `TauCeti.HomologicalOrientation.intersectionQuadraticForm` is its quadratic form, and
  `TauCeti.HomologicalOrientation.signature` is the signature `QuadraticForm.signature`, the
  difference `sigPos - sigNeg` of the indices of inertia, of that quadratic form.
* `TauCeti.HomologicalOrientation.nondegenerate_intersectionForm`: the intersection form is
  nondegenerate. For `p` even it is symmetric, so its quadratic form is nondegenerate too
  (`TauCeti.HomologicalOrientation.nondegenerate_intersectionQuadraticForm`), and the indices of
  inertia add up to `b_p`
  (`TauCeti.HomologicalOrientation.sigPos_add_sigNeg_intersectionQuadraticForm`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (Theorem 3.30,
  Poincaré duality, and Proposition 3.38, the cup product pairing).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

namespace TauCeti.HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : Module.finrank ℝ E = n)

include o hn in
/-- **Poincaré duality for rational Betti numbers.** For a compact homologically oriented
`n`-manifold `M` and `p + q = n`, the `q`-th and the `p`-th Betti numbers of `M` with rational
coefficients agree. -/
theorem bettiNumber_eq_bettiNumber [CompactSpace M] {p q : ℕ} (h : p + q = n) :
    bettiNumber ℚ M q = bettiNumber ℚ M p := by
  rw [bettiNumber_def, bettiNumber_def]
  -- `bettiNumber` takes coefficients `ModuleCat.of ℚ ℚ`, which is `𝟙_ (ModuleCat ℚ)` by the
  -- definition of the monoidal structure; Mathlib states no lemma for it.
  exact (TopCat.of M).finrank_singularHomology_eq_of_bijective_singularCapLinearMap ℚ h _
    (o.bijective_singularCapLinearMap_fundamentalClassOver hn ℚ h)

section IntersectionForm

variable [CompactSpace M] {p : ℕ} (h : p + p = n)

/-- The rational **intersection form** of a compact homologically oriented `n`-manifold `M` in
degree `p`, for `p + p = n`: the cup pairing `(α, β) ↦ ⟨α ⌣ β, [M]_ℚ⟩` on `Hᵖ(M; ℚ)`, for
`[M]_ℚ ∈ Hₙ(M; ℚ)` the fundamental class over `ℚ`.

Tau Ceti's `TauCeti.HomologicalOrientation.cupPairing` is the integral counterpart, on
`Hᵖ(M; ℤ)`. -/
def intersectionForm :
    LinearMap.BilinForm ℚ ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ _) p) :=
  (TopCat.of M).singularCupPairing ℚ h (o.fundamentalClassOver hn ℚ)

theorem intersectionForm_def :
    o.intersectionForm hn h = (TopCat.of M).singularCupPairing ℚ h (o.fundamentalClassOver hn ℚ) :=
  (rfl)

/-- The intersection form of `α` and `β` is the cup pairing of `α` and `β` on the fundamental
class over `ℚ`, which `TopCat.singularCupPairing_apply` evaluates to `⟨α ⌣ β, [M]_ℚ⟩`. -/
@[simp]
theorem intersectionForm_apply
    (α β : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ _) p) :
    o.intersectionForm hn h α β =
      (TopCat.of M).singularCupPairing ℚ h (o.fundamentalClassOver hn ℚ) α β :=
  (rfl)

/-- For `p` even, the intersection form is symmetric. -/
theorem isSymm_intersectionForm (hp : Even p) : LinearMap.IsSymm (o.intersectionForm hn h) := by
  rw [intersectionForm_def]
  exact (TopCat.of M).isSymm_singularCupPairing ℚ hp h _

/-- The quadratic form `α ↦ ⟨α ⌣ α, [M]_ℚ⟩` on `Hᵖ(M; ℚ)` of the intersection form
`TauCeti.HomologicalOrientation.intersectionForm`. -/
def intersectionQuadraticForm :
    QuadraticForm ℚ ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ _) p) :=
  LinearMap.BilinMap.toQuadraticMap (o.intersectionForm hn h)

theorem intersectionQuadraticForm_def :
    o.intersectionQuadraticForm hn h =
      LinearMap.BilinMap.toQuadraticMap (o.intersectionForm hn h) :=
  (rfl)

@[simp]
theorem intersectionQuadraticForm_apply
    (α : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ _) p) :
    o.intersectionQuadraticForm hn h α = o.intersectionForm hn h α α :=
  (rfl)

/-- The **signature** of a compact homologically oriented `n`-manifold `M` in degree `p`, for
`p + p = n`: the signature `sigPos - sigNeg` of the quadratic form of the intersection form on
`Hᵖ(M; ℚ)`. The signature of a `4k`-manifold is the case `p = 2k`. -/
def signature : ℤ :=
  (o.intersectionQuadraticForm hn h).signature

theorem signature_def : o.signature hn h = (o.intersectionQuadraticForm hn h).signature :=
  (rfl)

/-- **Poincaré duality for the cup pairing.** For a compact homologically oriented `n`-manifold
`M` and `p` with `p + p = n`, the intersection form on `Hᵖ(M; ℚ)` is nondegenerate. -/
theorem nondegenerate_intersectionForm : (o.intersectionForm hn h).Nondegenerate :=
  o.nondegenerate_singularCupPairing_fundamentalClassOver hn h

/-- **The intersection form of a compact manifold is nondegenerate.** For a compact homologically
oriented `n`-manifold `M` and an even `p` with `p + p = n`, the quadratic form
`α ↦ ⟨α ⌣ α, [M]_ℚ⟩` of the intersection form on `Hᵖ(M; ℚ)` is nondegenerate. -/
theorem nondegenerate_intersectionQuadraticForm (hp : Even p) :
    (o.intersectionQuadraticForm hn h).Nondegenerate := by
  rw [intersectionQuadraticForm_def]
  exact LinearMap.BilinForm.Nondegenerate.toQuadraticMap (o.nondegenerate_intersectionForm hn h)
    (LinearMap.isSymm_iff_eq_flip.1 (o.isSymm_intersectionForm hn h hp)).symm

/-- **The indices of inertia of the intersection form add up to the middle Betti number.** For a
compact homologically oriented `n`-manifold `M` and an even `p` with `p + p = n`, the positive
and negative indices of inertia of the quadratic form of the intersection form on `Hᵖ(M; ℚ)` add
up to the `p`-th rational Betti number. -/
theorem sigPos_add_sigNeg_intersectionQuadraticForm (hp : Even p) :
    sigPos (o.intersectionQuadraticForm hn h) + sigNeg (o.intersectionQuadraticForm hn h) =
      bettiNumber ℚ M p := by
  rw [QuadraticForm.sigPos_add_sigNeg_of_nondegenerate _
    (o.nondegenerate_intersectionQuadraticForm hn h hp), bettiNumber_def]
  -- `bettiNumber` takes coefficients `ModuleCat.of ℚ ℚ`, which is `𝟙_ (ModuleCat ℚ)` by the
  -- definition of the monoidal structure; Mathlib states no lemma for it.
  exact (TopCat.of M).finrank_singularCohomology p

end IntersectionForm

end TauCeti.HomologicalOrientation

end
