/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.Instances.Icc

/-!
# Weinstein homotopies

A *Weinstein homotopy* on a boundaryless manifold `M` is a family `t ↦ (ω t, X t, f t)` of
Weinstein structures (`SymplecticGeometry.IsWeinsteinStructure`) indexed by `t : unitInterval`,
smooth in `(t, x)` on `unitInterval × M`, whose functions satisfy a condition at infinity: there
are smooth functions `c₀ < c₁ < c₂ < ⋯` on `[0, 1]`, tending to infinity uniformly, such that
`c k t` is a regular value of `f t` for all `k` and `t`. The condition keeps critical points of
`f t` from escaping to infinity as `t` moves; on a compact manifold it always holds.

## Main declarations

* `SymplecticGeometry.IsWeinsteinHomotopy`: the predicate on a family `(ω, X, f)`, with
  `SymplecticGeometry.isWeinsteinHomotopy_iff`.
* `SymplecticGeometry.IsWeinsteinHomotopy.refl`: the constant family of a Weinstein structure.
* `SymplecticGeometry.IsWeinsteinHomotopy.comp`: a Weinstein homotopy reparametrized by a smooth
  map `[0, 1] → [0, 1]`.
* `SymplecticGeometry.IsWeinsteinHomotopy.symm`: a Weinstein homotopy run backwards, by
  `unitInterval.symm`.
* `SymplecticGeometry.IsWeinsteinHomotopy.pullback`: the pull-back of a Weinstein homotopy along a
  diffeomorphism.
* `SymplecticGeometry.IsWeinsteinHomotopy.of_isCompact`: on a compact manifold, every smooth
  family of Weinstein structures is a Weinstein homotopy.

## Implementation notes

The forms are a smooth family in the sense of `SymplecticGeometry.IsSmoothFamily`, over
`unitInterval` with the model `𝓡∂ 1`. The fields are jointly smooth as sections of the tangent
bundle along the projection `unitInterval × M → M`, in the form of the hypothesis of
`SymplecticGeometry.isSmoothFamily_interiorₗ`. The functions are jointly smooth on
`unitInterval × M`.

The functions `c k` are smooth on `[0, 1]`, with the model `𝓡∂ 1`, as Cieliebak and Eliashberg
ask, so that a statement that a Weinstein homotopy exists says as much as theirs. They ask for
`c k t → ∞` at each `t`; for continuous `c k`, increasing in `k`, the convergence is then uniform,
since `[0, 1]` is compact, and the predicate asks for the uniform form.

For a single Weinstein structure, the regular values `c k ∈ (k, k + 1)` exist because a proper
generalized Morse function has finitely many critical values in each compact interval
(`TauCeti.IsGeneralizedMorse.exists_isRegularValue_mem_Ioo`). On a compact manifold the functions
`f t` are bounded above, uniformly in `t`, by some `B`, and the constants `B + k + 1` are values
outside their ranges, so they are regular values (`TauCeti.isRegularValue_of_notMem_range`). The
field pulled back along a diffeomorphism `Φ` is the image of `X t` under the tangent map of `Φ⁻¹`
(`Diffeomorph.tangentMap_symm_mk`), so it stays jointly smooth.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  §11.6, Definition 11.19 and the definition of Morse homotopies after it
-/

public section

open Bundle Filter Set TauCeti
open scoped Manifold

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]

/-- A **Weinstein homotopy** on `M` is a family `t ↦ (ω t, X t, f t)`, `t ∈ [0, 1]`, of Weinstein
structures that depends smoothly on `(t, x) ∈ [0, 1] × M`, together with smooth functions
`c₀ < c₁ < ⋯` on `[0, 1]`, tending to infinity uniformly, with `c k t` a regular value of `f t`
for all `k` and `t`. -/
structure IsWeinsteinHomotopy (ω : unitInterval → SmoothTwoForm 𝓘(ℝ, E) M)
    (X : unitInterval → (x : M) → TangentSpace 𝓘(ℝ, E) x) (f : unitInterval → M → ℝ) :
    Prop where
  /-- The forms are a smooth family. -/
  isSmoothFamily : IsSmoothFamily (𝓡∂ 1) ω
  /-- The fields are jointly smooth in the parameter and the point. -/
  contMDiff_field : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E).tangent (⊤ : ℕ∞)
    fun p : unitInterval × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle 𝓘(ℝ, E) M)
  /-- The functions are jointly smooth in the parameter and the point. -/
  contMDiff_function : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ) (⊤ : ℕ∞)
    fun p : unitInterval × M ↦ f p.1 p.2
  /-- Each member of the family is a Weinstein structure. -/
  isWeinsteinStructure (t : unitInterval) : IsWeinsteinStructure (ω t) (X t) (f t)
  /-- The condition at infinity: smooth functions `c k`, strictly increasing in `k` and
  tending to infinity uniformly in `t`, with `c k t` a regular value of `f t`. -/
  exists_isRegularValue : ∃ c : ℕ → unitInterval → ℝ,
    (∀ k, ContMDiff (𝓡∂ 1) 𝓘(ℝ) (⊤ : ℕ∞) (c k)) ∧
    (∀ t, StrictMono fun k ↦ c k t) ∧ (∀ C : ℝ, ∀ᶠ k in atTop, ∀ t, C ≤ c k t) ∧
    ∀ k t, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (f t) (c k t)

variable {ω : unitInterval → SmoothTwoForm 𝓘(ℝ, E) M}
  {X : unitInterval → (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : unitInterval → M → ℝ}

/-- The conditions of `SymplecticGeometry.IsWeinsteinHomotopy`, as a conjunction. -/
theorem isWeinsteinHomotopy_iff :
    IsWeinsteinHomotopy ω X f ↔
      IsSmoothFamily (𝓡∂ 1) ω ∧
      ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E).tangent (⊤ : ℕ∞)
        (fun p : unitInterval × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ) (⊤ : ℕ∞) (fun p : unitInterval × M ↦ f p.1 p.2) ∧
      (∀ t, IsWeinsteinStructure (ω t) (X t) (f t)) ∧
      ∃ c : ℕ → unitInterval → ℝ, (∀ k, ContMDiff (𝓡∂ 1) 𝓘(ℝ) (⊤ : ℕ∞) (c k)) ∧
        (∀ t, StrictMono fun k ↦ c k t) ∧ (∀ C : ℝ, ∀ᶠ k in atTop, ∀ t, C ≤ c k t) ∧
        ∀ k t, IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (f t) (c k t) :=
  ⟨fun h ↦ ⟨h.isSmoothFamily, h.contMDiff_field, h.contMDiff_function, h.isWeinsteinStructure,
      h.exists_isRegularValue⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

namespace IsWeinsteinHomotopy

/-- **The constant Weinstein homotopy.** The constant family of a Weinstein structure is a
Weinstein homotopy. -/
protected theorem refl {ω : SmoothTwoForm 𝓘(ℝ, E) M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    {f : M → ℝ} (hW : IsWeinsteinStructure ω X f) :
    IsWeinsteinHomotopy (fun _ ↦ ω) (fun _ ↦ X) (fun _ ↦ f) := by
  -- A regular value of `f` in each interval `(k, k + 1)`.
  have hex (k : ℕ) : ∃ c ∈ Ioo (k : ℝ) (k + 1), IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) f c :=
    hW.isGeneralizedMorse.exists_isRegularValue_mem_Ioo (by linarith)
      (hW.isProperMap.isCompact_preimage isCompact_Icc)
  choose c hc hreg using hex
  refine ⟨isSmoothFamily_const ω, hW.contMDiff_field.comp contMDiff_snd,
    hW.isGeneralizedMorse.contMDiff.comp contMDiff_snd, fun _ ↦ hW,
    ⟨fun k _ ↦ c k, fun _ ↦ contMDiff_const, fun _ ↦ ?_, fun C ↦ ?_, fun k _ ↦ hreg k⟩⟩
  · exact strictMono_nat_of_lt_succ fun k ↦ (hc k).2.trans (by simpa using (hc (k + 1)).1)
  · filter_upwards [eventually_ge_atTop ⌈C⌉₊] with k hk _
    exact (Nat.ceil_le.1 hk).trans (hc k).1.le

/-- **Reparametrizing a Weinstein homotopy.** Composing the parameter of a Weinstein homotopy with
a smooth map `φ : [0, 1] → [0, 1]` gives a Weinstein homotopy. -/
protected theorem comp (h : IsWeinsteinHomotopy ω X f) (φ : unitInterval → unitInterval)
    (hφ : ContMDiff (𝓡∂ 1) (𝓡∂ 1) (⊤ : ℕ∞) φ) :
    IsWeinsteinHomotopy (fun t ↦ ω (φ t)) (fun t ↦ X (φ t)) (fun t ↦ f (φ t)) := by
  obtain ⟨c, hcont, hmono, htend, hreg⟩ := h.exists_isRegularValue
  have hσ : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) ((𝓡∂ 1).prod 𝓘(ℝ, E)) (⊤ : ℕ∞)
      fun p : unitInterval × M ↦ (φ p.1, p.2) :=
    (hφ.comp contMDiff_fst).prodMk contMDiff_snd
  refine ⟨h.isSmoothFamily.comp φ hφ, h.contMDiff_field.comp hσ,
    h.contMDiff_function.comp hσ, fun t ↦ h.isWeinsteinStructure _,
    ⟨fun k t ↦ c k (φ t), fun k ↦ (hcont k).comp hφ,
      fun t ↦ hmono _, fun C ↦ ?_, fun k t ↦ hreg k _⟩⟩
  filter_upwards [htend C] with k hk t using hk _

/-- **A Weinstein homotopy run backwards** is a Weinstein homotopy: reparametrize the family by
`t ↦ 1 - t`. -/
protected theorem symm (h : IsWeinsteinHomotopy ω X f) :
    IsWeinsteinHomotopy (fun t ↦ ω (unitInterval.symm t)) (fun t ↦ X (unitInterval.symm t))
      (fun t ↦ f (unitInterval.symm t)) :=
  h.comp _ unitInterval.contMDiff_symm

/-- **Weinstein homotopies pull back along diffeomorphisms.** If `t ↦ (ω t, X t, f t)` is a
Weinstein homotopy on `M` and `Φ : M' → M` is a diffeomorphism, then the family of pulled-back
Weinstein structures `t ↦ (Φ^* ω t, Φ^* X t, f t ∘ Φ)` is a Weinstein homotopy on `M'`. -/
theorem pullback (h : IsWeinsteinHomotopy ω X f) {M' : Type*} [TopologicalSpace M']
    [ChartedSpace E M'] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M']
    (Φ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M' M (⊤ : ℕ∞)) :
    IsWeinsteinHomotopy (fun t ↦ SmoothForm.mpullback Φ Φ.contMDiff (ω t))
      (fun t ↦ VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (X t)) (fun t ↦ f t ∘ Φ) := by
  obtain ⟨c, hcont, hmono, htend, hreg⟩ := h.exists_isRegularValue
  have hΦ : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) ((𝓡∂ 1).prod 𝓘(ℝ, E)) (⊤ : ℕ∞)
      fun p : unitInterval × M' ↦ (p.1, Φ p.2) :=
    contMDiff_fst.prodMk (Φ.contMDiff.comp contMDiff_snd)
  -- The pulled-back field is the image of `X t` under the tangent map of `Φ⁻¹`.
  have hfield : (fun p : unitInterval × M' ↦ (⟨p.2, VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) Φ
      (X p.1) p.2⟩ : TangentBundle 𝓘(ℝ, E) M')) =
      tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) Φ.symm ∘
        fun p : unitInterval × M' ↦ (⟨Φ p.2, X p.1 (Φ p.2)⟩ : TangentBundle 𝓘(ℝ, E) M) :=
    funext fun p ↦ by
      rw [Function.comp_apply,Φ.tangentMap_symm_mk (by simp), VectorField.mpullback_apply]
  refine ⟨h.isSmoothFamily.mpullback Φ Φ.contMDiff, ?_, h.contMDiff_function.comp hΦ,
    fun t ↦ (h.isWeinsteinStructure t).pullback Φ,
    ⟨c, hcont, hmono, htend, fun k t ↦ (Φ.isRegularValue_comp_iff (by simp)).2 (hreg k t)⟩⟩
  rw [hfield]
  exact (Φ.symm.contMDiff.contMDiff_tangentMap le_rfl).comp (h.contMDiff_field.comp hΦ)

/-- **Weinstein homotopies on a compact manifold.** On a compact manifold, a family of Weinstein
structures whose forms, fields and functions depend smoothly on the parameter and the point is a
Weinstein homotopy: the condition at infinity holds automatically. -/
theorem of_isCompact [CompactSpace M] (hω : IsSmoothFamily (𝓡∂ 1) ω)
    (hX : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, E).tangent (⊤ : ℕ∞)
      fun p : unitInterval × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle 𝓘(ℝ, E) M))
    (hf : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ) (⊤ : ℕ∞) fun p : unitInterval × M ↦ f p.1 p.2)
    (hW : ∀ t, IsWeinsteinStructure (ω t) (X t) (f t)) : IsWeinsteinHomotopy ω X f := by
  -- A bound `B` for all the functions; the levels `B + k + 1` are empty.
  obtain ⟨B, hB⟩ := (isCompact_range hf.continuous).bddAbove
  have hlt (k : ℕ) (t : unitInterval) (x : M) : f t x < B + k + 1 := by
    have := hB (mem_range_self (t, x))
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    dsimp only at *
    linarith
  refine ⟨hω, hX, hf, hW, ⟨fun k _ ↦ B + k + 1, fun _ ↦ contMDiff_const,
    fun _ ↦ strictMono_nat_of_lt_succ fun k ↦ by push_cast; linarith, fun C ↦ ?_,
    fun k t ↦ isRegularValue_of_notMem_range fun ⟨x, hx⟩ ↦ (hlt k t x).ne hx⟩⟩
  filter_upwards [eventually_ge_atTop ⌈C - B⌉₊] with k hk _
  have := Nat.ceil_le.1 hk
  linarith

end IsWeinsteinHomotopy

end SymplecticGeometry

end
