/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.Algebra.Projectivization

/-!
# The model blowup of `ℂⁿ⁺¹` at the origin

For `n : ℕ` and `E := Fin (n + 1) → ℂ`, the blowup of `E` at `0` is the incidence set of the pairs
`(ℓ, z) ∈ ℙ ℂ E × E` with `z` on the line `ℓ`, as in McDuff–Salamon (7.1.1). It comes with the
projection `pr` to `ℙ ℂ E` and the blowdown map to `E`; the blowdown is a bijection off the
exceptional divisor, the fibre `ℙ ℂ E × {0}` over the origin.

This file sets up the incidence set with its subspace topology, the two projections and the
exceptional divisor. The charts and the complex manifold structure come later.

## Main definitions and results

* `SymplecticGeometry.blowupModel n`: the incidence set in `ℙ ℂ E × E`, and
  `SymplecticGeometry.isClosed_blowupModel`: it is closed (Tau Ceti's
  `Projectivization.isClosed_setOfPred_mem_submodule`).
* `SymplecticGeometry.BlowupModel n`: the incidence set as a type, with the subspace topology.
* `SymplecticGeometry.BlowupModel.pr` and `SymplecticGeometry.BlowupModel.blowdown`: the
  continuous projections to `ℙ ℂ E` and to `E`.
* `SymplecticGeometry.BlowupModel.exceptionalDivisor n`: the fibre of the blowdown over `0`,
  which is the range of the zero section `SymplecticGeometry.BlowupModel.zeroSection`
  (`SymplecticGeometry.BlowupModel.exceptionalDivisor_eq_range`).
* `SymplecticGeometry.BlowupModel.dense_exceptionalDivisor_compl`: the complement of the
  exceptional divisor is dense, since `(ℓ, t • v)` tends to `(ℓ, 0)` as `t → 0`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1.
* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 1, §4.
-/

public section

open Projectivization Filter Topology
open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry

variable (n : ℕ)

/-- The incidence set of the blowup of `ℂⁿ⁺¹` at the origin: the pairs `(ℓ, z)` of a complex line
`ℓ` through the origin and a vector `z` on it. -/
def blowupModel : Set (ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)) :=
  {p | p.2 ∈ p.1.submodule}

variable {n} in
theorem mem_blowupModel_iff {p : ℙ ℂ (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)} :
    p ∈ blowupModel n ↔ p.2 ∈ p.1.submodule :=
  Iff.rfl

/-- The incidence set of the blowup is closed in `ℙ ℂ E × E`. -/
theorem isClosed_blowupModel : IsClosed (blowupModel n) :=
  isClosed_setOfPred_mem_submodule

/-- The blowup of `ℂⁿ⁺¹` at the origin, as the incidence set `blowupModel n` with the subspace
topology. -/
abbrev BlowupModel : Type := blowupModel n

namespace BlowupModel

variable {n}

/-- The projection of the blowup to the projective space: `(ℓ, z) ↦ ℓ`. -/
def pr (p : BlowupModel n) : ℙ ℂ (Fin (n + 1) → ℂ) :=
  p.val.fst

/-- The blowdown map of the blowup to `ℂⁿ⁺¹`: `(ℓ, z) ↦ z`. -/
def blowdown (p : BlowupModel n) : Fin (n + 1) → ℂ :=
  p.val.snd

@[simp]
theorem pr_mk (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) (z : Fin (n + 1) → ℂ) (h : (ℓ, z) ∈ blowupModel n) :
    pr ⟨(ℓ, z), h⟩ = ℓ :=
  (rfl)

@[simp]
theorem blowdown_mk (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) (z : Fin (n + 1) → ℂ)
    (h : (ℓ, z) ∈ blowupModel n) : blowdown ⟨(ℓ, z), h⟩ = z :=
  (rfl)

theorem blowdown_mem_submodule (p : BlowupModel n) : p.blowdown ∈ p.pr.submodule :=
  p.property

/-- A point of the blowup is determined by its projection and its blowdown. -/
theorem ext {p q : BlowupModel n} (h₁ : p.pr = q.pr) (h₂ : p.blowdown = q.blowdown) : p = q :=
  Subtype.ext (Prod.ext h₁ h₂)

@[fun_prop, continuity]
theorem continuous_pr : Continuous (pr : BlowupModel n → ℙ ℂ (Fin (n + 1) → ℂ)) :=
  continuous_fst.comp continuous_subtypeVal

@[fun_prop, continuity]
theorem continuous_blowdown : Continuous (blowdown : BlowupModel n → Fin (n + 1) → ℂ) :=
  continuous_snd.comp continuous_subtypeVal

variable (n) in
/-- The exceptional divisor of the blowup: the fibre `{(ℓ, 0)}` of the blowdown over the
origin. -/
def exceptionalDivisor : Set (BlowupModel n) :=
  {p | p.blowdown = 0}

@[simp]
theorem mem_exceptionalDivisor_iff {p : BlowupModel n} :
    p ∈ exceptionalDivisor n ↔ p.blowdown = 0 :=
  Iff.rfl

theorem isClosed_exceptionalDivisor : IsClosed (exceptionalDivisor n) :=
  isClosed_eq continuous_blowdown continuous_const

/-- The zero section of the blowup over the projective space: `ℓ ↦ (ℓ, 0)`. -/
def zeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) : BlowupModel n :=
  ⟨(ℓ, 0), ℓ.submodule.zero_mem⟩

@[simp]
theorem pr_zeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) : (zeroSection ℓ).pr = ℓ :=
  (rfl)

@[simp]
theorem blowdown_zeroSection (ℓ : ℙ ℂ (Fin (n + 1) → ℂ)) : (zeroSection ℓ).blowdown = 0 :=
  (rfl)

theorem zeroSection_injective :
    Function.Injective (zeroSection : ℙ ℂ (Fin (n + 1) → ℂ) → BlowupModel n) :=
  fun ℓ ℓ' h => by simpa using congrArg pr h

@[fun_prop, continuity]
theorem continuous_zeroSection :
    Continuous (zeroSection : ℙ ℂ (Fin (n + 1) → ℂ) → BlowupModel n) :=
  (continuous_id.prodMk continuous_const).subtype_mk _

/-- The exceptional divisor is the image of the zero section. -/
theorem exceptionalDivisor_eq_range : exceptionalDivisor n = Set.range zeroSection := by
  ext p
  refine ⟨fun hp => ⟨p.pr, ?_⟩, ?_⟩
  · exact ext rfl (mem_exceptionalDivisor_iff.1 hp).symm
  · rintro ⟨ℓ, rfl⟩
    exact blowdown_zeroSection ℓ

/-- The complement of the exceptional divisor is dense in the blowup: a point `(ℓ, 0)` is the
limit of `(ℓ, t • v)` as `t → 0`, for `v` spanning `ℓ`. -/
theorem dense_exceptionalDivisor_compl : Dense (exceptionalDivisor n)ᶜ := by
  intro p
  by_cases hp : p.blowdown = 0
  · have hrep : p.pr.rep ∈ p.pr.submodule := mem_submodule_iff.2 fun _ => mk_rep _
    let γ : ℂ → BlowupModel n := fun t => ⟨(p.pr, t • p.pr.rep), p.pr.submodule.smul_mem t hrep⟩
    have hγ : Continuous γ :=
      (continuous_const.prodMk (continuous_id.smul continuous_const)).subtype_mk _
    have h0 : γ 0 = p := ext rfl (by simp [γ, hp])
    rw [← h0]
    refine mem_closure_of_tendsto (hγ.continuousAt.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    exact fun h => smul_ne_zero ht p.pr.rep_ne_zero
      ((blowdown_mk _ _ _).symm.trans (mem_exceptionalDivisor_iff.1 h))
  · exact subset_closure hp

end BlowupModel

end SymplecticGeometry

end
