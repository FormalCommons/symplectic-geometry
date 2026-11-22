/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import SymplecticGeometry.Analysis.Normed.Module.Alternating.RealDerivation
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Uncurry

/-!
# The Lefschetz operator and the linear Kähler identity

Let `V` be a finite-dimensional real inner product space and `J` an orthogonal almost complex
structure on it, with Kähler form `ω(v, w) = ⟪J v, w⟫`. On the alternating forms
`V [⋀^Fin k]→L[ℝ] ℝ`, the fibres of the bundle of differential forms, this file defines the
Lefschetz operator `L α = α ∧ ω` and proves the constant-coefficient Kähler identity.

For a vector `u`, write `ε_u α = ⟪u, ·⟫ ∧ α`, as `alternatizeUncurryFin` of `⟪u, ·⟫ • α` (the
symbol of the exterior derivative at the covector `⟪u, ·⟫`), `ι_u` for the interior product
`ContinuousAlternatingMap.curryLeft` by `u`, and `𝒥` for the derivation of `J` on forms. The
identity is `L ι_u - ι_u L = 𝒥 ε_u - ε_u 𝒥`. The symbol of the codifferential `d*` at
`⟪u, ·⟫` is `δ_u = -ι_u`: by `Orientation.smul_formHodgeStar_alternatizeUncurryFin_formHodgeStar`
it is `(-1) ^ (m (k + 2) + 1) ⋆ ε_u ⋆` on `(k + 1)`-forms of an `m`-dimensional oriented space,
the formula by which Tau Ceti defines `codifferential`. So the identity reads
`L δ_u - δ_u L = -(𝒥 ε_u - ε_u 𝒥)`, the pointwise form of `[L, d*] = -[𝒥, d]`.

Both sides are computed directly: `ι_u` is an antiderivation and `ι_u ω = ⟪J u, ·⟫`, while `𝒥`
is a derivation and `𝒥 ⟪u, ·⟫ = -⟪J u, ·⟫`, so both sides are `-(⟪J u, ·⟫ ∧ α)`.

The Hodge star commutes with the derivation of every skew-adjoint endomorphism, in particular
with `𝒥` (`Orientation.formHodgeStar_realAlternatingDerivation`); this is Tau Ceti's
`Orientation.hodgeStar_lieMap` read on forms.

## Main definitions

* `TauCeti.AlmostComplexStructure.lefschetz`: the Lefschetz operator `α ↦ α ∧ ω`.

## Main results

* `TauCeti.alternatingFormEquiv_lieMap`: the derivation action of a skew-adjoint endomorphism on
  `⋀ᵏ V` is minus its derivation on forms.
* `Orientation.formHodgeStar_realAlternatingDerivation`: `⋆ D_A = D_A ⋆` for skew-adjoint `A`.
* `Orientation.smul_formHodgeStar_alternatizeUncurryFin_formHodgeStar`: the symbol of `d*`.
* `TauCeti.AlmostComplexStructure.lefschetz_curryLeft_sub`: the linear Kähler identity
  `L ι_u - ι_u L = 𝒥 ε_u - ε_u 𝒥`.

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

namespace TauCeti

/-- **The two derivations agree up to sign**: for a skew-adjoint `A`, the form of `D_A x`, the
derivation action of `A` on `x ∈ ⋀ᵏ V`, is minus the derivation of `A` on the form of `x`. -/
theorem alternatingFormEquiv_lieMap {k : ℕ} {A : V →L[ℝ] V}
    (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫) (x : ⋀[ℝ]^k V) :
    alternatingFormEquiv V k (lieMap k (A : V →ₗ[ℝ] V) x) =
      -A.realAlternatingDerivation (alternatingFormEquiv V k x) := by
  have hA' : ∀ u w, ⟪(A : V →ₗ[ℝ] V) u, w⟫ = -⟪u, (A : V →ₗ[ℝ] V) w⟫ := by
    simpa only [ContinuousLinearMap.coe_coe] using hA
  ext v
  rw [alternatingFormEquiv_apply, inner_lieMap_left hA',
    lieMap_apply_ιMulti, inner_sum, ContinuousAlternatingMap.neg_apply,
    ContinuousLinearMap.realAlternatingDerivation_apply]
  simp [alternatingFormEquiv_apply]

/-- **Exterior multiplication is the symbol of `d`**: the form of `u ∧ x` for `x ∈ ⋀ᵏ V` is
`alternatizeUncurryFin` of `⟪u, ·⟫ • α`, with `α` the form of `x`. -/
theorem alternatingFormEquiv_wedgeLeft (u : V) {k : ℕ} (x : ⋀[ℝ]^k V) :
    alternatingFormEquiv V (k + 1) (ExteriorAlgebra.wedgeLeft u k x) =
      alternatizeUncurryFin ((innerSL ℝ u).smulRight (alternatingFormEquiv V k x)) := by
  ext v
  rw [alternatingFormEquiv_wedgeLeft_apply, alternatizeUncurryFin_smulRight_apply_eq_wedge]

end TauCeti

namespace Orientation

open TauCeti

variable {n : ℕ} [Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n))

/-- **The Hodge star commutes with skew-adjoint derivations**: for a skew-adjoint endomorphism
`A` of `V`, `⋆ (D_A α) = D_A (⋆ α)` for the derivation `D_A` of `A` on forms. -/
theorem formHodgeStar_realAlternatingDerivation {k l : ℕ} (hkl : k + l = finrank ℝ V)
    {A : V →L[ℝ] V} (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    o.formHodgeStar hkl (A.realAlternatingDerivation α) =
      A.realAlternatingDerivation (o.formHodgeStar hkl α) := by
  obtain ⟨x, rfl⟩ := (alternatingFormEquiv V k).surjective α
  have hA' : ∀ u w, ⟪(A : V →ₗ[ℝ] V) u, w⟫ = -⟪u, (A : V →ₗ[ℝ] V) w⟫ := by
    simpa only [ContinuousLinearMap.coe_coe] using hA
  rw [← neg_neg (A.realAlternatingDerivation _), ← alternatingFormEquiv_lieMap hA, map_neg,
    formHodgeStar_alternatingFormEquiv, o.hodgeStar_lieMap hkl hA', alternatingFormEquiv_lieMap hA,
    neg_neg, formHodgeStar_alternatingFormEquiv]

/-- **The symbol of the codifferential**: on `(k + 1)`-forms of an `m`-dimensional oriented space,
`(-1) ^ (m (k + 2) + 1) ⋆ ε_u ⋆ = -ι_u`, where `ε_u` is `alternatizeUncurryFin` of `⟪u, ·⟫ • ·`
and `ι_u` the interior product by `u`. The sign is that of Tau Ceti's `codifferential`; by Tau
Ceti's `coe_codifferential_funSMulₗ`, `-ι_u β` is `d* (f β) - f d* β` where `f` has gradient
`u`. -/
theorem smul_formHodgeStar_alternatizeUncurryFin_formHodgeStar (u : V) {k l : ℕ}
    (hkl : k + 1 + l = finrank ℝ V) (hlk : l + 1 + k = finrank ℝ V)
    (β : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    (-1 : ℝ) ^ (finrank ℝ V * (k + 2) + 1) • o.formHodgeStar hlk
        (alternatizeUncurryFin ((innerSL ℝ u).smulRight (o.formHodgeStar hkl β))) =
      -β.curryLeft u := by
  obtain ⟨x, rfl⟩ := (alternatingFormEquiv V (k + 1)).surjective β
  rw [formHodgeStar_alternatingFormEquiv, ← alternatingFormEquiv_wedgeLeft,
    formHodgeStar_alternatingFormEquiv, ← alternatingFormEquiv_koszulDifferential,
    o.koszulDifferential_eq_smul_hodgeStar_wedgeLeft_hodgeStar u hkl hlk, map_smul,
    ← neg_smul]
  congr 1
  rw [pow_succ, mul_neg_one, neg_inj, mul_add, pow_add,
    Even.neg_one_pow (⟨finrank ℝ V, by ring⟩ : Even (finrank ℝ V * 2)), mul_one]

end Orientation

namespace ContinuousLinearMap

omit [FiniteDimensional ℝ V] in
/-- For a skew-adjoint `A`, the derivation of `A` on the covector `⟪u, ·⟫` is `-⟪A u, ·⟫`. -/
theorem realAlternatingDerivation_ofSubsingleton_innerSL {A : V →L[ℝ] V}
    (hA : ∀ u w, ⟪A u, w⟫ = -⟪u, A w⟫) (u : V) :
    A.realAlternatingDerivation (ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ u)) =
      -ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ (A u)) := by
  ext v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv, realAlternatingDerivation_apply_vecCons_fin_one]
  simp [hA]

end ContinuousLinearMap

namespace TauCeti.AlmostComplexStructure

variable (J : AlmostComplexStructure V)

/-- The **Lefschetz operator** of an almost complex structure `J` on alternating forms: the wedge
`α ↦ α ∧ ω` with the Kähler form `ω`, the form of the Kähler two-vector `J.kahlerForm`. As `ω`
has even degree, this is also `ω ∧ α` (`lefschetz_apply_apply`). -/
def lefschetz {k : ℕ} : (V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] V [⋀^Fin (k + 2)]→L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun α := α.wedge (alternatingFormEquiv V 2 J.kahlerForm)
      map_add' α β := wedge_add_left α β _
      map_smul' c α := wedge_smul_left c α _ }

/-- The Lefschetz operator is the wedge with the Kähler form. -/
theorem lefschetz_apply {k : ℕ} (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    J.lefschetz α = α.wedge (alternatingFormEquiv V 2 J.kahlerForm) :=
  (rfl)

/-- The Lefschetz operator is the wedge with the Kähler form on the left, up to the identification
of the degrees `2 + k` and `k + 2`. -/
theorem lefschetz_apply_apply {k : ℕ} (α : V [⋀^Fin k]→L[ℝ] ℝ) (v : Fin (k + 2) → V) :
    J.lefschetz α v =
      (alternatingFormEquiv V 2 J.kahlerForm).wedge α (v ∘ Fin.cast (Nat.add_comm 2 k)) := by
  rw [lefschetz_apply, wedge_comm, Even.neg_one_pow (⟨k, by ring⟩ : Even (k * 2)), one_smul]

variable {J} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

/-- For an orthogonal `J`, the interior product of the Kähler form by `u` is the covector
`⟪J u, ·⟫`. -/
theorem curryLeft_alternatingFormEquiv_kahlerForm (u : V) :
    (alternatingFormEquiv V 2 J.kahlerForm).curryLeft u =
      ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ (J u)) := by
  ext v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv]
  simp [alternatingFormEquiv_apply, ← inner_kahlerForm_ιMulti hJ]

/-- **The linear Kähler identity**: for an orthogonal almost complex structure `J`, a vector `u`
and a `(k + 1)`-form `α`, `L ι_u α - ι_u L α = 𝒥 ε_u α - ε_u 𝒥 α`, where `L` is the Lefschetz
operator, `ι_u` the interior product by `u`, `ε_u` the wedge with `⟪u, ·⟫` (as
`alternatizeUncurryFin` of `⟪u, ·⟫ • ·`, the symbol of `d`) and `𝒥` the derivation of `J`. Since
the symbol of `d*` is `-ι_u`
(`Orientation.smul_formHodgeStar_alternatizeUncurryFin_formHodgeStar`), this is the
constant-coefficient form of `[L, d*] = -[𝒥, d]`. -/
theorem lefschetz_curryLeft_sub {k : ℕ} (u : V) (α : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    J.lefschetz (α.curryLeft u) - (J.lefschetz α).curryLeft u =
      J.toLinearMap.toContinuousLinearMap.realAlternatingDerivation
          (alternatizeUncurryFin ((innerSL ℝ u).smulRight α)) -
        alternatizeUncurryFin ((innerSL ℝ u).smulRight
          (J.toLinearMap.toContinuousLinearMap.realAlternatingDerivation α)) := by
  set A := J.toLinearMap.toContinuousLinearMap
  set ω := alternatingFormEquiv V 2 J.kahlerForm
  set θJ := ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ (J u))
  have hc : 1 + (k + 1) = k + 1 + 1 := by omega
  ext v
  -- The left side: `ι_u` is an antiderivation, so only `± α ∧ ι_u ω` survives.
  have hL : (J.lefschetz α).curryLeft u v =
      J.lefschetz (α.curryLeft u) v + (-1 : ℝ) ^ (k + 1) • α.wedge (ω.curryLeft u) v := by
    simp only [lefschetz_apply, curryLeft_eq_curryLeftTopological, wedge_def]
    exact curryLeftTopological_pairedWedge (k := k) (l := 1) _ _ α ω u v
  -- The right side: `𝒥` is a derivation, so only `𝒥 ⟪u, ·⟫ ∧ α = -⟪J u, ·⟫ ∧ α` survives.
  have hR (β : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) (w : Fin (k + 1 + 1) → V) :
      alternatizeUncurryFin ((innerSL ℝ u).smulRight β) w =
        (ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ u)).wedge β (w ∘ finCongr hc) := by
    rw [alternatizeUncurryFin_smulRight_apply_eq_wedge]
    simp only [Function.comp_def, finCongr_apply]
  have hA : ∀ v w, ⟪A v, w⟫ = -⟪v, A w⟫ := by
    simpa only [A, LinearMap.coe_toContinuousLinearMap'] using inner_apply_left hJ
  have hθ : A.realAlternatingDerivation (ofSubsingleton ℝ V ℝ (0 : Fin 1) (innerSL ℝ u)) = -θJ :=
    ContinuousLinearMap.realAlternatingDerivation_ofSubsingleton_innerSL hA u
  rw [curryLeft_alternatingFormEquiv_kahlerForm hJ u] at hL
  rw [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.sub_apply, hL,
    A.realAlternatingDerivation_apply_comp_equiv (finCongr hc) (hR α), hR,
    ContinuousLinearMap.realAlternatingDerivation_wedge, hθ, wedge_comm α θJ,
    ContinuousAlternatingMap.add_apply, ← neg_one_smul ℝ θJ, wedge_smul_left]
  simp only [ContinuousAlternatingMap.smul_apply, Function.comp_def, finCongr_apply, smul_eq_mul]
  have hs : (-1 : ℝ) ^ (k + 1) * (-1) ^ ((k + 1) * 1) = 1 := by
    rw [mul_one, ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩]
  linear_combination (-(θJ.wedge α) fun x ↦ v (Fin.cast hc x)) * hs

end TauCeti.AlmostComplexStructure
