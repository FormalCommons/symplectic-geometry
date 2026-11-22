/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Codifferential

/-!
# The Hodge star against `d^* d` and `d d^*`

On an oriented manifold with a smooth metric, the Hodge star of smooth forms is injective, since
`⋆⋆` is a sign, and it carries the two second-order operators `d^* d` and `d d^*` to each other:
`⋆ d^* d = d d^* ⋆` and `⋆ d d^* = d^* d ⋆`. The signs that Tau Ceti's
`TauCeti.SmoothForm.hodgeStar_codifferential` and `TauCeti.SmoothForm.hodgeStar_mextDeriv`
introduce cancel in pairs. The two conjugation formulas are the two local steps of the proof of
Tau Ceti's `TauCeti.SmoothForm.hodgeStar_hodgeLaplacian`, stated separately.

## Main results

* `TauCeti.SmoothForm.hodgeStar_injective`: the Hodge star of smooth forms is injective.
* `TauCeti.SmoothForm.hodgeStar_codifferential_mextDerivₗ`: `⋆ d^* d β = d d^* ⋆β`.
* `TauCeti.SmoothForm.hodgeStar_mextDerivₗ_codifferential`: `⋆ d d^* α = d^* d ⋆α`.
-/

public section

open Bundle
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] {k l m : ℕ}

namespace TauCeti.SmoothForm

/-- The Hodge star of smooth forms is injective, since `⋆⋆` is a sign. -/
theorem hodgeStar_injective (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    Function.Injective (hodgeStar o hkl) := fun α β h ↦ by
  have := congrArg (hodgeStar o (show l + k = m by omega)) h
  rwa [hodgeStar_hodgeStar, hodgeStar_hodgeStar,
    smul_right_inj (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))] at this

/-- The Hodge star carries `d*d` to `dd*`: `⋆ d* dβ = d d* ⋆β` for a `k`-form `β`. -/
theorem hodgeStar_codifferential_mextDerivₗ (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (hkl' : k + (l + 1) = m) (hlk : l + 1 + k = m)
    (β : SmoothForm I M ℝ k) :
    hodgeStar o hkl' (codifferential o hkl (mextDerivₗ I k β)) =
      mextDerivₗ I l (codifferential o hlk (hodgeStar o hkl' β)) := by
  rw [hodgeStar_codifferential o hkl hkl', hodgeStar_mextDeriv o hkl' hlk hkl, map_smul,
    smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- The Hodge star carries `dd*` to `d*d`: `⋆ d d*α = d* d ⋆α` for a `(k + 1)`-form `α`. -/
theorem hodgeStar_mextDerivₗ_codifferential (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (hlk : l + 1 + k = m) (α : SmoothForm I M ℝ (k + 1)) :
    hodgeStar o hkl (mextDerivₗ I k (codifferential o hkl α)) =
      codifferential o hlk (mextDerivₗ I l (hodgeStar o hkl α)) := by
  have hkl' : k + (l + 1) = m := by omega
  rw [hodgeStar_mextDeriv o hkl' hlk hkl, hodgeStar_codifferential o hkl hkl', map_smul,
    smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

end TauCeti.SmoothForm

end
