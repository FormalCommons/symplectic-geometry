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
# Consequences of Poincaré duality over a field

Let `M` be a compact homologically oriented `n`-manifold without boundary, let `k` be a
commutative ring, and write `[M]_k = TauCeti.HomologicalOrientation.fundamentalClassOver k` for
the image of its fundamental class in `Hₙ(M; k)`. Tau Ceti proves Poincaré duality over `k`:
capping with `[M]_k` is a bijection `Hᵖ(M; k) → H_q(M; k)` for `p + q = n`
(`TauCeti.HomologicalOrientation.bijective_singularCapLinearMap_fundamentalClassOver`), and, for
`k` a field, the cup pairing against `[M]_k` is nondegenerate
(`TauCeti.HomologicalOrientation.nondegenerate_singularCupPairing_fundamentalClassOver`). This
file draws consequences of these two theorems.

* `TauCeti.HomologicalOrientation.bettiNumber_eq_bettiNumber`: over a field `k`, the Betti numbers
  satisfy `b_q = b_p` for `p + q = n`, by Tau Ceti's
  `TopCat.finrank_singularHomology_eq_of_bijective_singularCapLinearMap`.
* `TauCeti.HomologicalOrientation.intersectionForm`: for `p + p = n`, the cup pairing
  `(α, β) ↦ ⟨α ⌣ β, [M]_k⟩` on `Hᵖ(M; k)`;
  `TauCeti.HomologicalOrientation.intersectionQuadraticForm` is its quadratic form, and, for `k`
  linearly ordered, `TauCeti.HomologicalOrientation.signature` is the signature
  `QuadraticForm.signature`, the difference `sigPos - sigNeg` of the indices of inertia, of that
  quadratic form.
* `TauCeti.HomologicalOrientation.nondegenerate_intersectionForm`: over a field the intersection
  form is nondegenerate. For `p` even it is symmetric, so its quadratic form is nondegenerate
  too where `2` is invertible
  (`TauCeti.HomologicalOrientation.nondegenerate_intersectionQuadraticForm`), and over an ordered
  field the indices of inertia add up to `b_p`
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
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : Module.finrank ℝ E = n) (k : Type)

include o hn in
/-- **Poincaré duality for Betti numbers.** For a compact homologically oriented `n`-manifold `M`,
a field `k` and `p + q = n`, the `q`-th and the `p`-th Betti numbers of `M` with coefficients in
`k` agree. -/
theorem bettiNumber_eq_bettiNumber [Field k] [CompactSpace M] {p q : ℕ} (h : p + q = n) :
    bettiNumber k M q = bettiNumber k M p := by
  rw [bettiNumber_def, bettiNumber_def]
  -- `bettiNumber` takes coefficients `ModuleCat.of k k`, which is `𝟙_ (ModuleCat k)` by the
  -- definition of the monoidal structure; Mathlib states no lemma for it.
  exact (TopCat.of M).finrank_singularHomology_eq_of_bijective_singularCapLinearMap k h _
    (o.bijective_singularCapLinearMap_fundamentalClassOver hn k h)

section IntersectionForm

variable [CompactSpace M] {p : ℕ} (h : p + p = n)

section CommRing

variable [CommRing k]

/-- The **intersection form** over a commutative ring `k` of a compact homologically oriented
`n`-manifold `M` in degree `p`, for `p + p = n`: the cup pairing `(α, β) ↦ ⟨α ⌣ β, [M]_k⟩` on
`Hᵖ(M; k)`, for `[M]_k ∈ Hₙ(M; k)` the fundamental class over `k`.

Tau Ceti's `TauCeti.HomologicalOrientation.cupPairing` is the integral counterpart, on
`Hᵖ(M; ℤ)`. -/
def intersectionForm :
    LinearMap.BilinForm k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} k)) k (𝟙_ _) p) :=
  (TopCat.of M).singularCupPairing k h (o.fundamentalClassOver hn k)

theorem intersectionForm_def :
    o.intersectionForm hn k h =
      (TopCat.of M).singularCupPairing k h (o.fundamentalClassOver hn k) :=
  (rfl)

/-- The intersection form of `α` and `β` is the cup pairing of `α` and `β` on the fundamental
class over `k`, which `TopCat.singularCupPairing_apply` evaluates to `⟨α ⌣ β, [M]_k⟩`. -/
@[simp]
theorem intersectionForm_apply
    (α β : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} k)) k (𝟙_ _) p) :
    o.intersectionForm hn k h α β =
      (TopCat.of M).singularCupPairing k h (o.fundamentalClassOver hn k) α β :=
  (rfl)

/-- For `p` even, the intersection form is symmetric. -/
theorem isSymm_intersectionForm (hp : Even p) :
    LinearMap.IsSymm (o.intersectionForm hn k h) := by
  rw [intersectionForm_def]
  exact (TopCat.of M).isSymm_singularCupPairing k hp h _

/-- The quadratic form `α ↦ ⟨α ⌣ α, [M]_k⟩` on `Hᵖ(M; k)` of the intersection form
`TauCeti.HomologicalOrientation.intersectionForm`. -/
def intersectionQuadraticForm :
    QuadraticForm k ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} k)) k (𝟙_ _) p) :=
  LinearMap.BilinMap.toQuadraticMap (o.intersectionForm hn k h)

theorem intersectionQuadraticForm_def :
    o.intersectionQuadraticForm hn k h =
      LinearMap.BilinMap.toQuadraticMap (o.intersectionForm hn k h) :=
  (rfl)

@[simp]
theorem intersectionQuadraticForm_apply
    (α : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} k)) k (𝟙_ _) p) :
    o.intersectionQuadraticForm hn k h α = o.intersectionForm hn k h α α :=
  (rfl)

/-- The **signature** over a linearly ordered commutative ring `k` of a compact homologically
oriented `n`-manifold `M` in degree `p`, for `p + p = n`: the signature `sigPos - sigNeg` of the
quadratic form of the intersection form on `Hᵖ(M; k)`. The signature of a `4k`-manifold is the
case `p = 2k`, usually over `ℚ` or `ℝ`. -/
def signature [LinearOrder k] : ℤ :=
  (o.intersectionQuadraticForm hn k h).signature

theorem signature_def [LinearOrder k] :
    o.signature hn k h = (o.intersectionQuadraticForm hn k h).signature :=
  (rfl)

end CommRing

section Field

variable [Field k]

/-- **Poincaré duality for the cup pairing.** For a compact homologically oriented `n`-manifold
`M`, a field `k` and `p` with `p + p = n`, the intersection form on `Hᵖ(M; k)` is
nondegenerate. -/
theorem nondegenerate_intersectionForm : (o.intersectionForm hn k h).Nondegenerate :=
  o.nondegenerate_singularCupPairing_fundamentalClassOver hn h

/-- **The intersection form of a compact manifold is nondegenerate.** For a compact homologically
oriented `n`-manifold `M`, a field `k` in which `2` is invertible and an even `p` with
`p + p = n`, the quadratic form `α ↦ ⟨α ⌣ α, [M]_k⟩` of the intersection form on `Hᵖ(M; k)` is
nondegenerate. -/
theorem nondegenerate_intersectionQuadraticForm [Invertible (2 : k)] (hp : Even p) :
    (o.intersectionQuadraticForm hn k h).Nondegenerate := by
  rw [intersectionQuadraticForm_def]
  exact LinearMap.BilinForm.Nondegenerate.toQuadraticMap (o.nondegenerate_intersectionForm hn k h)
    (LinearMap.isSymm_iff_eq_flip.1 (o.isSymm_intersectionForm hn k h hp)).symm

/-- **The indices of inertia of the intersection form add up to the middle Betti number.** For a
compact homologically oriented `n`-manifold `M`, an ordered field `k` and an even `p` with
`p + p = n`, the positive and negative indices of inertia of the quadratic form of the
intersection form on `Hᵖ(M; k)` add up to the `p`-th Betti number of `M` with coefficients in
`k`. -/
theorem sigPos_add_sigNeg_intersectionQuadraticForm [LinearOrder k] [IsStrictOrderedRing k]
    (hp : Even p) :
    sigPos (o.intersectionQuadraticForm hn k h) + sigNeg (o.intersectionQuadraticForm hn k h) =
      bettiNumber k M p := by
  let : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
  rw [QuadraticForm.sigPos_add_sigNeg_of_nondegenerate _
    (o.nondegenerate_intersectionQuadraticForm hn k h hp), bettiNumber_def]
  -- `bettiNumber` takes coefficients `ModuleCat.of k k`, which is `𝟙_ (ModuleCat k)` by the
  -- definition of the monoidal structure; Mathlib states no lemma for it.
  exact (TopCat.of M).finrank_singularCohomology p

end Field

end IntersectionForm

end TauCeti.HomologicalOrientation

end
