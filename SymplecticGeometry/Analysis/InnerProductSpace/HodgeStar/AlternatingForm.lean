/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Lie.ExteriorPower
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import SymplecticGeometry.Analysis.Normed.Module.Alternating.Uncurry.Fin
import SymplecticGeometry.Analysis.Normed.Module.Alternating.Derivation

/-!
# Derivations, exterior multiplication and the Hodge star on alternating forms

Let `V` be a finite-dimensional real inner product space. Tau Ceti's `alternatingFormEquiv`
identifies `⋀ᵏ V` with the alternating forms `V [⋀^Fin k]→L[ℝ] ℝ`, and `formHodgeStar` is the
Hodge star on the forms. This file reads operations of `⋀ V` on the forms.

* For a skew-adjoint endomorphism `A`, the derivation action `exteriorPower.lieMap` of `A` on
  `⋀ᵏ V` is minus the derivation `D_A` of `A` on forms, which is Mathlib's
  `ContinuousAlternatingMap.fderivCompContinuousLinearMap` at the identity in the direction `A`.
  This is the argument of Tau Ceti's
  `SmoothAlmostComplexStructure.alternatingFormEquiv_symm_neg_realAlternatingDerivation_two`, in
  every degree and for every skew-adjoint `A`.
* Summed over an orthonormal basis `b`, the sign `(-1) ^ (m (k + 2) + 1)` of Tau Ceti's
  `codifferential`, in dimension `m`, times `⋆ Alt (⋆ ∘ B)`, for `B` linear from `V` to the
  `(k + 1)`-forms and `Alt` Mathlib's `alternatizeUncurryFin`, is `-∑ i, ι_{b i} (B (b i))`, with
  `ι` the interior product: the symbol of `d*` at a general first-order term. Each term is Tau
  Ceti's `Orientation.neg_one_pow_smul_formHodgeStar_wedgeCovector_formHodgeStar`, the symbol
  `(-1) ^ (m (k + 2) + 1) ⋆ ε_u ⋆ = -ι_u` of `d*` at `⟪u, ·⟫`.

## Main results

* `TauCeti.alternatingFormEquiv_lieMap`: `lieMap A` on `⋀ᵏ V` is `-D_A` on forms, for a
  skew-adjoint `A`.
* `Orientation.smul_formHodgeStar_alternatizeUncurryFin_comp_formHodgeStar`: the symbol of `d*`
  at a linear map `B`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §7.
-/

public section

noncomputable section

open Module exteriorPower ContinuousAlternatingMap
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace ContinuousAlternatingMap

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι]

/-- `alternatizeUncurryFin f` is the sum over an orthonormal basis `b` of the alternatizations of
`⟪b i, ·⟫ • f (b i)`, as `f = ∑ i, ⟪b i, ·⟫ • f (b i)`. -/
theorem alternatizeUncurryFin_eq_sum_innerSL_smulRight (b : OrthonormalBasis ι 𝕜 E) {n : ℕ}
    (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    alternatizeUncurryFin f =
      ∑ i, alternatizeUncurryFin ((innerSL 𝕜 (b i)).smulRight (f (b i))) := by
  have : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  have hb (i : ι) : LinearMap.toContinuousLinearMap (b.toBasis.coord i) = innerSL 𝕜 (b i) := by
    ext v
    simp [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  simpa [hb] using alternatizeUncurryFin_eq_sum_coord_smulRight b.toBasis f

end ContinuousAlternatingMap

namespace TauCeti

/-- **The two derivations agree up to sign**: for a skew-adjoint `A`, the form of `lieMap A x`,
the derivation action of `A` on `x ∈ ⋀ᵏ V`, is minus the derivation of `A` on the form of `x`. -/
theorem alternatingFormEquiv_lieMap {k : ℕ} {A : V →L[ℝ] V}
    (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫) (x : ⋀[ℝ]^k V) :
    alternatingFormEquiv V k (lieMap k (A : V →ₗ[ℝ] V) x) =
      -((alternatingFormEquiv V k x).fderivCompContinuousLinearMap (.id ℝ V) A) := by
  have hA' : ∀ u w, ⟪(A : V →ₗ[ℝ] V) u, w⟫ = -⟪u, (A : V →ₗ[ℝ] V) w⟫ := by
    simpa only [ContinuousLinearMap.coe_coe] using hA
  ext v
  rw [alternatingFormEquiv_apply, inner_lieMap_left hA', lieMap_apply_ιMulti, inner_sum,
    ContinuousAlternatingMap.neg_apply, fderivCompContinuousLinearMap_id_apply]
  simp [alternatingFormEquiv_apply]

end TauCeti

namespace Orientation

open TauCeti

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- **The symbol of the codifferential at a linear map**: for `B` from `V` to the
`(k + 1)`-forms and an orthonormal basis `b`, `(-1) ^ (m (k + 2) + 1) ⋆ Alt (⋆ ∘ B)` is
`-∑ i, ι_{b i} (B (b i))`, where `Alt` is `alternatizeUncurryFin` and `ι` the interior product.
In a chart where the Hodge star operator has zero derivative at a point, this is the value there of
Tau Ceti's `codifferential` of a form whose derivative there is `B`. -/
theorem smul_formHodgeStar_alternatizeUncurryFin_comp_formHodgeStar {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {k l : ℕ} (hkl : k + 1 + l = finrank ℝ V)
    (hlk : l + 1 + k = finrank ℝ V) (B : V →L[ℝ] V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    (-1 : ℝ) ^ (finrank ℝ V * (k + 2) + 1) • o.formHodgeStar hlk
        (alternatizeUncurryFin
          ((o.formHodgeStar hkl).toContinuousLinearEquiv.toContinuousLinearMap ∘L B)) =
      -∑ i, (B (b i)).curryLeft (b i) := by
  rw [alternatizeUncurryFin_eq_sum_innerSL_smulRight b, _root_.map_sum, Finset.smul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsign : (-1 : ℝ) ^ (finrank ℝ V * (k + 2) + 1) = (-1) ^ (n * (k + 2) + 1) := by
    rw [Fact.out (p := finrank ℝ V = n)]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearEquiv.coe_toContinuousLinearEquiv', alternatizeUncurryFin_innerSL_smulRight, hsign,
    o.neg_one_pow_smul_formHodgeStar_wedgeCovector_formHodgeStar _ hkl hlk,
    curryLeftFlipL_apply_apply]

end Orientation
