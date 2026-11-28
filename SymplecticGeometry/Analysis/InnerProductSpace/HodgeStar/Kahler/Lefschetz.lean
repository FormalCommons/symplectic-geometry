/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import SymplecticGeometry.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Uncurry
import SymplecticGeometry.Analysis.Normed.Module.Alternating.Derivation

/-!
# The Lefschetz operator and the linear Kähler identity

Let `V` be a finite-dimensional real inner product space and `J` an orthogonal almost complex
structure on it, with Kähler form `ω(v, w) = ⟪J v, w⟫`. On the alternating forms
`V [⋀^Fin k]→L[ℝ] ℝ`, the fibres of the bundle of differential forms, this file defines the
Lefschetz operator `L α = α ∧ ω` and proves the constant-coefficient Kähler identity.

For a vector `u`, write `ε_u α = ⟪u, ·⟫ ∧ α`, as `alternatizeUncurryFin` of `⟪u, ·⟫ • α` (the
symbol of the exterior derivative at the covector `⟪u, ·⟫`), `ι_u` for the interior product
`ContinuousAlternatingMap.curryLeft` by `u`, and `𝒥` for the derivation of `J` on forms, Mathlib's
`ContinuousAlternatingMap.fderivCompContinuousLinearMap` at the identity in the direction `J`. The
identity is `L ι_u - ι_u L = 𝒥 ε_u - ε_u 𝒥`. The symbol of the codifferential `d*` at
`⟪u, ·⟫` is `δ_u = -ι_u`, by Tau Ceti's
`Orientation.neg_one_pow_smul_formHodgeStar_wedgeCovector_formHodgeStar` and
`TauCeti.alternatizeUncurryFin_innerSL_smulRight`.
So the identity reads `L δ_u - δ_u L = -(𝒥 ε_u - ε_u 𝒥)`, the pointwise form of
`[L, d*] = -[𝒥, d]`.

Both sides are computed directly: `ι_u` is an antiderivation and `ι_u ω = ⟪J u, ·⟫`, while `𝒥`
is a derivation and `𝒥 ⟪u, ·⟫ = -⟪J u, ·⟫`, so both sides are `-(⟪J u, ·⟫ ∧ α)`.

A first-order term is more generally a linear map `B` from `V` to the `(k + 1)`-forms, the
derivative of a form at a point. With `Alt` Mathlib's `alternatizeUncurryFin` and
`δ B = ± ⋆ Alt (⋆ ∘ B)` with the sign of Tau Ceti's `codifferential`, the identity becomes
`L (δ B) - δ (L ∘ B) = -(𝒥 (Alt B) - Alt (𝒥 ∘ B))`. It follows from the one for covectors by
writing `B = ∑ i, ⟪e i, ·⟫ • B (e i)` in an orthonormal basis `e`. Two edge cases are stated
apart: if `m = dim V < k + 3`, then `L ∘ B = 0` and only `L (δ B)` remains, and on `0`-forms
`δ B` is not defined and `𝒥 ∘ B = 0`, so the identity reads `δ (L ∘ B) = 𝒥 (Alt B)`.

The Hodge star commutes with the derivation of every skew-adjoint endomorphism, in particular
with `𝒥` (`Orientation.formHodgeStar_fderivCompContinuousLinearMap`); this is Tau Ceti's
`Orientation.hodgeStar_lieMap` read on forms.

## Main definitions

* `TauCeti.AlmostComplexStructure.formLefschetz`: the Lefschetz operator `α ↦ α ∧ ω` on continuous
  alternating forms. Tau Ceti's `TauCeti.AlmostComplexStructure.lefschetz` is left multiplication
  by `ω` on the exterior power `⋀[ℝ]^k V`, not on forms.

## Main results

* `Orientation.formHodgeStar_fderivCompContinuousLinearMap`: `⋆ D_A = D_A ⋆` for skew-adjoint
  `A`.
* `TauCeti.AlmostComplexStructure.formLefschetz_curryLeft_sub`: the linear Kähler identity
  `L ι_u - ι_u L = 𝒥 ε_u - ε_u 𝒥`.
* `TauCeti.AlmostComplexStructure.formLefschetz_smul_formHodgeStar_alternatizeUncurryFin_sub`: the
  linear Kähler identity for a first-order symbol `B`, with its edge cases
  `formLefschetz_smul_formHodgeStar_alternatizeUncurryFin_of_lt` and
  `smul_formHodgeStar_alternatizeUncurryFin_formLefschetz_fin_zero`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §7.
* [J.-P. Demailly, *Complex Analytic and Differential Geometry*][Demailly2012], Chapter VI.
-/

public section

noncomputable section

open Module exteriorPower ContinuousAlternatingMap
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace Orientation

open TauCeti

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- **The Hodge star commutes with skew-adjoint derivations**: for a skew-adjoint endomorphism
`A` of `V`, `⋆ (D_A α) = D_A (⋆ α)` for the derivation `D_A` of `A` on forms. -/
theorem formHodgeStar_fderivCompContinuousLinearMap {k l : ℕ} (hkl : k + l = finrank ℝ V)
    {A : V →L[ℝ] V} (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    o.formHodgeStar hkl (α.fderivCompContinuousLinearMap (.id ℝ V) A) =
      (o.formHodgeStar hkl α).fderivCompContinuousLinearMap (.id ℝ V) A := by
  obtain ⟨x, rfl⟩ := (alternatingFormEquiv V k).surjective α
  have hA' : ∀ u w, ⟪(A : V →ₗ[ℝ] V) u, w⟫ = -⟪u, (A : V →ₗ[ℝ] V) w⟫ := by
    simpa only [ContinuousLinearMap.coe_coe] using hA
  rw [← neg_neg (fderivCompContinuousLinearMap _ _ A), ← alternatingFormEquiv_lieMap hA, map_neg,
    formHodgeStar_alternatingFormEquiv, o.hodgeStar_lieMap hkl hA', alternatingFormEquiv_lieMap hA,
    neg_neg, formHodgeStar_alternatingFormEquiv]

end Orientation

namespace TauCeti.AlmostComplexStructure

variable (J : AlmostComplexStructure V)

/-- The **Lefschetz operator** of an almost complex structure `J` on alternating forms: the wedge
`α ↦ α ∧ ω` with the Kähler form `ω`, the form of the Kähler two-vector `J.kahlerForm`. As `ω`
has even degree, this is also `ω ∧ α` (`formLefschetz_apply_apply`). -/
def formLefschetz {k : ℕ} : (V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V [⋀^Fin (k + 2)]→L[ℝ] ℝ :=
  (pairedWedgeCLM (ContinuousLinearMap.mul ℝ ℝ)).flip (alternatingFormEquiv V 2 J.kahlerForm)

/-- The Lefschetz operator is the wedge with the Kähler form. -/
theorem formLefschetz_apply {k : ℕ} (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    J.formLefschetz α = α.wedge (alternatingFormEquiv V 2 J.kahlerForm) := by
  simp [formLefschetz, wedge_def]

/-- The Lefschetz operator is the wedge with the Kähler form on the left, up to the identification
of the degrees `2 + k` and `k + 2`. -/
theorem formLefschetz_apply_apply {k : ℕ} (α : V [⋀^Fin k]→L[ℝ] ℝ) (v : Fin (k + 2) → V) :
    J.formLefschetz α v =
      (alternatingFormEquiv V 2 J.kahlerForm).wedge α (v ∘ Fin.cast (Nat.add_comm 2 k)) := by
  rw [formLefschetz_apply, wedge_comm, Even.neg_one_pow (⟨k, by ring⟩ : Even (k * 2)), one_smul]

/-- On `0`-forms, the Lefschetz operator is multiplication of the Kähler form by the value of the
form. -/
theorem formLefschetz_fin_zero (β : V [⋀^Fin 0]→L[ℝ] ℝ) :
    J.formLefschetz β = β 0 • alternatingFormEquiv V 2 J.kahlerForm := by
  ext v
  rw [formLefschetz_apply, wedge_def, pairedWedge_apply_zero_left]
  simp

variable {J} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

/-- For an orthogonal `J`, the interior product of the Kähler form by `u` is the covector
`⟪J u, ·⟫`. -/
theorem curryLeft_alternatingFormEquiv_kahlerForm (u : V) :
    (alternatingFormEquiv V 2 J.kahlerForm).curryLeft u =
      ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ (J u)) := by
  ext w
  simp [alternatingFormEquiv_apply, ← inner_kahlerForm_ιMulti hJ]

/-- **The linear Kähler identity**: for an orthogonal almost complex structure `J`, a vector `u`
and a `(k + 1)`-form `α`, `L ι_u α - ι_u L α = 𝒥 ε_u α - ε_u 𝒥 α`, where `L` is the Lefschetz
operator, `ι_u` the interior product by `u`, `ε_u` the wedge with `⟪u, ·⟫` (as
`alternatizeUncurryFin` of `⟪u, ·⟫ • ·`, the symbol of `d`) and `𝒥` the derivation of `J`. Since
the symbol of `d*` is `-ι_u`
(Tau Ceti's `Orientation.neg_one_pow_smul_formHodgeStar_wedgeCovector_formHodgeStar`), this is the
constant-coefficient form of `[L, d*] = -[𝒥, d]`. -/
theorem formLefschetz_curryLeft_sub {k : ℕ} (u : V) (α : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    J.formLefschetz (α.curryLeft u) - (J.formLefschetz α).curryLeft u =
      (alternatizeUncurryFin ((innerSL ℝ u).smulRight α)).fderivCompContinuousLinearMap
          (.id ℝ V) J.toLinearMap.toContinuousLinearMap -
        alternatizeUncurryFin ((innerSL ℝ u).smulRight
          (α.fderivCompContinuousLinearMap (.id ℝ V) J.toLinearMap.toContinuousLinearMap)) := by
  set A := J.toLinearMap.toContinuousLinearMap
  set ω := alternatingFormEquiv V 2 J.kahlerForm
  set θJ := ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ (J u))
  have hc : 1 + (k + 1) = k + 1 + 1 := by omega
  ext v
  -- The left side: `ι_u` is an antiderivation, so only `± α ∧ ι_u ω` survives.
  have hL : (J.formLefschetz α).curryLeft u v =
      J.formLefschetz (α.curryLeft u) v + (-1 : ℝ) ^ (k + 1) • α.wedge (ω.curryLeft u) v := by
    simp only [formLefschetz_apply, curryLeft_eq_curryLeftTopological, wedge_def]
    exact curryLeftTopological_pairedWedge (k := k) (l := 1) _ _ α ω u v
  -- The right side: `𝒥` is a derivation, so only `𝒥 ⟪u, ·⟫ ∧ α = -⟪J u, ·⟫ ∧ α` survives.
  have hR (β : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) (w : Fin (k + 1 + 1) → V) :
      alternatizeUncurryFin ((innerSL ℝ u).smulRight β) w =
        (ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ u)).wedge β (w ∘ finCongr hc) := by
    rw [alternatizeUncurryFin_smulRight_apply_eq_wedge]
    simp only [Function.comp_def, finCongr_apply]
  have hA : ∀ v w, ⟪A v, w⟫ = -⟪v, A w⟫ := by
    simpa only [A, LinearMap.coe_toContinuousLinearMap'] using inner_apply_left hJ
  have hθ : (ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ u)).fderivCompContinuousLinearMap
      (.id ℝ V) A = -θJ := by
    ext w
    simp only [fderivCompContinuousLinearMap_ofSubsingleton, θJ, ContinuousAlternatingMap.neg_apply,
      ofSubsingleton_apply_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    rw [← neg_eq_iff_eq_neg, ← hA]
    simp [A]
  rw [curryLeft_alternatingFormEquiv_kahlerForm hJ u] at hL
  rw [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.sub_apply, hL,
    fderivCompContinuousLinearMap_apply_comp_equiv (finCongr hc) (hR α), hR,
    fderivCompContinuousLinearMap_wedge, hθ, wedge_comm α θJ,
    ContinuousAlternatingMap.add_apply, ← neg_one_smul ℝ θJ, wedge_smul_left]
  simp only [ContinuousAlternatingMap.smul_apply, Function.comp_def, finCongr_apply, smul_eq_mul]
  have hs : (-1 : ℝ) ^ (k + 1) * (-1) ^ ((k + 1) * 1) = 1 := by
    rw [mul_one, ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩]
  linear_combination (-(θJ.wedge α) fun x ↦ v (Fin.cast hc x)) * hs

/-- **The linear Kähler identity on `0`-forms**: for an orthogonal almost complex structure `J`, a
vector `u` and a `0`-form `β`, `ι_u L β = -𝒥 ε_u β`. This is `formLefschetz_curryLeft_sub`
one degree lower: there is no interior product of a `0`-form, and `𝒥 β = 0`. -/
theorem curryLeft_formLefschetz_fin_zero (u : V) (β : V [⋀^Fin 0]→L[ℝ] ℝ) :
    (J.formLefschetz β).curryLeft u =
      -(alternatizeUncurryFin ((innerSL ℝ u).smulRight β)).fderivCompContinuousLinearMap
          (.id ℝ V) J.toLinearMap.toContinuousLinearMap := by
  have hA := inner_apply_left hJ
  rw [formLefschetz_fin_zero, curryLeft_smul, _root_.smul_apply,
    curryLeft_alternatingFormEquiv_kahlerForm hJ u]
  ext w
  rw [ContinuousAlternatingMap.neg_apply, fderivCompContinuousLinearMap_apply_vecCons_fin_one]
  simp [alternatizeUncurryFin_apply, hA, mul_comm]

section Symbol

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- **The constant-coefficient Kähler identity for a first-order symbol**: for an orthogonal
almost complex structure `J` on an oriented space of dimension `m` and `B` from `V` to the
`(k + 1)`-forms, `L (δ B) - δ (L ∘ B) = -(𝒥 (Alt B) - Alt (𝒥 ∘ B))`, where `Alt` is
`alternatizeUncurryFin`, `L` the Lefschetz operator, `𝒥` the derivation of `J`, and
`δ B = (-1) ^ (m (j + 2) + 1) ⋆ Alt (⋆ ∘ B)` on `B` with values in `(j + 1)`-forms. In a chart where
the Hodge star operator has zero derivative at a point, `δ B` is the value there of Tau Ceti's
`codifferential` of a form whose derivative there is `B`, and `Alt B` that of its exterior
derivative. The hypotheses `hkl`, `hlk`, `hkl'` and `hlk'` are those of Tau Ceti's
`codifferential_apply` in the degrees `k + 1` and `k + 3`. -/
theorem formLefschetz_smul_formHodgeStar_alternatizeUncurryFin_sub {k l l' : ℕ}
    (hkl : k + 1 + l = finrank ℝ V) (hlk : l + 1 + k = finrank ℝ V)
    (hkl' : k + 2 + 1 + l' = finrank ℝ V) (hlk' : l' + 1 + (k + 2) = finrank ℝ V)
    (B : V →L[ℝ] V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    J.formLefschetz ((-1 : ℝ) ^ (finrank ℝ V * (k + 2) + 1) • o.formHodgeStar hlk
        (alternatizeUncurryFin
          ((o.formHodgeStar hkl).toContinuousLinearEquiv.toContinuousLinearMap ∘L B))) -
      (-1 : ℝ) ^ (finrank ℝ V * (k + 2 + 2) + 1) • o.formHodgeStar hlk'
        (alternatizeUncurryFin
          ((o.formHodgeStar hkl').toContinuousLinearEquiv.toContinuousLinearMap ∘L
            J.formLefschetz ∘L B)) =
      -((alternatizeUncurryFin B).fderivCompContinuousLinearMap (.id ℝ V)
          J.toLinearMap.toContinuousLinearMap -
        alternatizeUncurryFin ((fderivCompContinuousLinearMapCLM ℝ (.id ℝ V)).flip
          J.toLinearMap.toContinuousLinearMap ∘L B)) := by
  set b := stdOrthonormalBasis ℝ V
  rw [o.smul_formHodgeStar_alternatizeUncurryFin_comp_formHodgeStar b hkl hlk,
    o.smul_formHodgeStar_alternatizeUncurryFin_comp_formHodgeStar b hkl' hlk',
    alternatizeUncurryFin_eq_sum_innerSL_smulRight b B,
    alternatizeUncurryFin_eq_sum_innerSL_smulRight b, ← fderivCompContinuousLinearMapCLM_apply,
    _root_.map_sum, _root_.sum_apply, map_neg, _root_.map_sum, sub_neg_eq_add,
    ← Finset.sum_sub_distrib, neg_add_eq_sub, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ContinuousLinearMap.comp_apply, ← neg_sub, formLefschetz_curryLeft_sub hJ]
  simp

/-- **The constant-coefficient Kähler identity in the top two degrees**: if `m < k + 3`, that is
if the `(k + 1)`-forms have degree `m - 1` or `m`, then the Lefschetz operator sends them to
zero, and `formLefschetz_smul_formHodgeStar_alternatizeUncurryFin_sub` becomes
`L (δ B) = -(𝒥 (Alt B) - Alt (𝒥 ∘ B))` for `B` from `V` to the `(k + 1)`-forms. -/
theorem formLefschetz_smul_formHodgeStar_alternatizeUncurryFin_of_lt {k l : ℕ}
    (hkl : k + 1 + l = finrank ℝ V) (hlk : l + 1 + k = finrank ℝ V) (hk : finrank ℝ V < k + 3)
    (B : V →L[ℝ] V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    J.formLefschetz ((-1 : ℝ) ^ (finrank ℝ V * (k + 2) + 1) • o.formHodgeStar hlk
        (alternatizeUncurryFin
          ((o.formHodgeStar hkl).toContinuousLinearEquiv.toContinuousLinearMap ∘L B))) =
      -((alternatizeUncurryFin B).fderivCompContinuousLinearMap (.id ℝ V)
          J.toLinearMap.toContinuousLinearMap -
        alternatizeUncurryFin ((fderivCompContinuousLinearMapCLM ℝ (.id ℝ V)).flip
          J.toLinearMap.toContinuousLinearMap ∘L B)) := by
  set b := stdOrthonormalBasis ℝ V
  rw [o.smul_formHodgeStar_alternatizeUncurryFin_comp_formHodgeStar b hkl hlk,
    alternatizeUncurryFin_eq_sum_innerSL_smulRight b B,
    alternatizeUncurryFin_eq_sum_innerSL_smulRight b, ← fderivCompContinuousLinearMapCLM_apply,
    _root_.map_sum, _root_.sum_apply, map_neg, _root_.map_sum, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h := formLefschetz_curryLeft_sub hJ (b i) (B (b i))
  rw [ContinuousAlternatingMap.eq_zero_of_finrank_lt (J.formLefschetz (B (b i)))
      (by rw [Fintype.card_fin]; omega), curryLeft_zero, zero_apply, sub_zero] at h
  simpa using h

/-- **The constant-coefficient Kähler identity in degree zero**: for `B` from `V` to the
`0`-forms, `δ (L ∘ B) = 𝒥 (Alt B)`, with `δ` and `Alt` as in
`formLefschetz_smul_formHodgeStar_alternatizeUncurryFin_sub`. This is that identity one degree
lower, where `δ B` is not defined and `𝒥 ∘ B` vanishes, as `𝒥` is zero on `0`-forms. The hypotheses
are those of Tau Ceti's `codifferential_apply` in degree `2`. -/
theorem smul_formHodgeStar_alternatizeUncurryFin_formLefschetz_fin_zero {l : ℕ}
    (hkl : 1 + 1 + l = finrank ℝ V) (hlk : l + 1 + 1 = finrank ℝ V)
    (B : V →L[ℝ] V [⋀^Fin 0]→L[ℝ] ℝ) :
    (-1 : ℝ) ^ (finrank ℝ V * (1 + 2) + 1) • o.formHodgeStar hlk
        (alternatizeUncurryFin
          ((o.formHodgeStar hkl).toContinuousLinearEquiv.toContinuousLinearMap ∘L
            J.formLefschetz ∘L B)) =
      (alternatizeUncurryFin B).fderivCompContinuousLinearMap (.id ℝ V)
        J.toLinearMap.toContinuousLinearMap := by
  set b := stdOrthonormalBasis ℝ V
  rw [o.smul_formHodgeStar_alternatizeUncurryFin_comp_formHodgeStar b hkl hlk,
    alternatizeUncurryFin_eq_sum_innerSL_smulRight b B, ← fderivCompContinuousLinearMapCLM_apply,
    _root_.map_sum, _root_.sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ContinuousLinearMap.comp_apply, curryLeft_formLefschetz_fin_zero hJ, neg_neg,
    fderivCompContinuousLinearMapCLM_apply]

end Symbol

end TauCeti.AlmostComplexStructure
